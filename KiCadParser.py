# KiCadParser.py
#
# Ver: 1.1.0
#
# Author: Brian N Norman
# Date: 9/3/17
#
# Processes CSV data strings. Replaces place holders (%...%) in template files
# returns the result for output to the kicad_pcb file
#
#

import copy
import math
import re
import traceback
import sys

#
#
# This class is just a list of variables which are pushed onto a stack (list)
# when executing methods which may be re-entered
#

class StateVars():
    def __init__(self):
        self.groupList=[]           # groups within groups is possible
        self.repeatList=[]          # nested repeats is possible
        self.ringList=[]            # nested rings are possible
        self.groupId=""             # current group Id
        self.repeatId=""
        self.ringId=""
        self.ringX=0.0              # X/Y on perimeter of ring
        self.ringY=0.0              # used for relative positioning
        self.ringCx=0.0             # centre of ring rotation
        self.ringCy=0.0             #
        self.ringRad=0.0            # ring radius
        self.ringAngle=0.0          # radial component rotation
        self.xOrigin=0.0            # rename as Origin????
        self.yOrigin=0.0
        self.angleOrigin=0.0
        self.repeatX=0.0            # for step and repeat operations
        self.repeatY=0.0
        self.repeatAngle=0.0
        self.groupX=0.0
        self.groupY=0.0
        self.groupAngle=0.0
        self.localVars={}           # available in repeat loops etc
#
# KiCadParser class
#
# processes a CSV string which contains positional and template information,
# replaces %..% placeholders with required values returns the template
# for output to the kicad_pcb file
#
# if not output is retired None is returne

class KiCadParser():


    def __init__(self):

        self.template={}        # dictionary holds the templates
        self.asis={}            # dictionary for static stuff
        self.srcLine=0          # for reporting where something went wrong

        # groups of components
        self.group={}           # group definitions
        self.makingGroup=False
        self.processingGroup=False

        # rings of components
        self.makingRing=False
        self.ring={}            # ring definitions
        self.processingRing=False

        # repeat of components
        self.repeat={}          # repeat definitions
        self.makingRepeat=False
        self.processingRepeat=False

        self.groupRefStyle='-'  # used when appending to REFs
        self.ref={}             # per-component reference numbers

        # state variables are held in another class so it can be pushed on to the stateStack
        # and restored as necessary
        self.state = StateVars() # the state variables
        self.stateStack=[]       # used for nesting

        # lists of parameters - currently not nestable
        self.list={}            # dictionary contains all loaded lists
        self.useList=[]         # current list of commands between USELIST,X....ENDUSELIST
        self.makingUseList=False
        self.useListId=""

        # global variables
        self.globalVars={}
        self.globalVars["xOrigin"]=0    # until ORIGIN command changes it
        self.globalVars["yOrigin"]=0
        #
        self.saveXYVars={}      # used for linking segments in rings etc
        # formatting strings
        self.fmtFloat="{:.4f}"  # used for building X,Y coords strings

        self.directionX=1       # Kicad X direction is left to right
        self.directionY=-1      # Kicad Y direction is top down
        #self.directionArc="CW"  # kicad is reverse of normal

        self.numWarnings=0
        self.numErrors=0
        #
        # used to evaluate simple expressions see evalNumericParam
        #
        self.reInt=re.compile('[+-]?\d+')                   # +12234 or -1234 or 1234
        self.reFloat=re.compile('[+-]?\d*\.\d+')            # could be like .5  but 99. is not acceptable
        self.reItem=re.compile('[+-]?[0-9A-Za-z_.]*')       # almost anything - used to dissect an expression
        self.reVarName=re.compile('[A-Za-z]+[0-9A-Za-z_]*') # var named MUST start with a letter for the sake of sanity
        #
        self.zoneTemplate="ZONE" # changes if KEEPOUT is called

        # action jump table - gets rid of a long if-elif chain
        self.actions={}
        self.actions["TEMPLATE"]=self.loadTemplate
        self.actions["ASIS"]=self.loadAsis
        self.actions["ORIGIN"]=self.origin
        self.actions["DEFGROUP"]=self.defGroup
        self.actions["ENDGROUP"]=self.endGroup
        self.actions["GROUP"] = self.processGroup
        self.actions["DEFREPEAT"]=self.defRepeat
        self.actions["ENDREPEAT"]=self.endRepeat
        self.actions["REPEAT"] = self.processRepeat
        self.actions["DEFRING"]=self.defRing
        self.actions["ENDRING"]=self.endRing
        self.actions["RING"] = self.processRing
        self.actions["TRACK"]=self.segment
        self.actions["SEGMENT"]=self.segment
        self.actions["GRAPHIC"]=self.graphic
        self.actions["TARGET"]=self.target
        self.actions["VIA"]=self.via
        self.actions["FIDUCIAL"]=self.fiducial
        self.actions["MOUNT"]=self.mounting
        self.actions["ZONE"]=self.zone      # zones and keepouts do the same thing
        self.actions["KEEPOUT"]=self.zone   # just use different templates
        self.actions["SETDIRECTION"]=self.setDirection
        self.actions["LIST"] = self.loadList
        self.actions["USELIST"] = self.beginUseList
        self.actions["ENDUSELIST"] = self.endUseList
        self.actions["ECHO"] = self.echo
        self.actions["SETG"] = self.setGlobal
        self.actions["SETL"] = self.setLocal
        self.actions["CLRL"] = self.clrLocal
        self.actions["CLRG"] = self.clrGlobal
        self.actions["SAVEXY"]=self.saveXY
        self.actions["SAVEONCEXY"]=self.saveOnceXY
        self.actions["SHOWVARS"]=self.showVars
        self.actions["KICADPCB"]=self.loadKicadPcb





    # parse routes the data to the appropriate routine
    # using the jump table all calls go through here first

    def parse(self,srcLine,id,params):
        # wrapper so we can catch errors from in here
        try:
            return self._parse(srcLine,id,params)

        except Exception as e:
            self.numErrors=self.numErrors+1
            print("Error in KicadParser.py :-")
            print(e.args)
            exc_type, exc_value, exc_traceback = sys.exc_info()
            traceback.print_tb(exc_traceback)
            traceback.print_exception(exc_type, exc_value, exc_traceback,
                                      limit=10, file=sys.stdout)
            print("Caused by source line ",srcLine)

    def _parse(self,srcLine,id,params):

        # clean up
        id=id.strip()

        # for status messages
        self.srcLine=srcLine

        # if the item is in the asis lists just return it unchanged
        if id in self.asis: return self.asis[id]

        # gather up commands into lists for these
        # till the END tag is seen
        if self.makingGroup:
            if id!="ENDGROUP":
                # add the data as a tuple
                self.state.groupList.append((srcLine,id,params))
                return None

        if self.makingRepeat:
            if id!="ENDREPEAT":
                self.state.repeatList.append((srcLine,id,params))
                return None

        if self.makingRing:
            if id != "ENDRING":
                self.state.ringList.append((srcLine,id,params))
                return None

        if self.makingUseList:
            if id!="ENDUSELIST":
                # not nestable
                self.useList.append((srcLine,id,params))
                return None


        # check for defined actions first

        if id in self.actions:
            return self.actions[id](id,params)

        # user defined components all have the same parameters
        else:
            # otherwise process as a user defined template
            return self.component(id,params)
    ########################################################################
    #
    # Error
    #
    # error,info and warning message mmessage formatting
    #
    # could be improved using decorators
    #
    ########################################################################
    def Error(self,msg):
        self.numErrors=self.numErrors+1
        print("ERROR at line",self.srcLine,msg)

    def Warning(self,msg):
        self.numWarnings=self.numWarnings+1
        print("WARNING at line",self.srcLine,msg)

    def Info(self, msg):
        print("INFO at line", self.srcLine, msg)

    def getStatus(self):
        print("Warnings: ",self.numWarnings,"\nErrors: ",self.numErrors)

    #######################################################################
    #
    # debugging aids
    #
    #######################################################################

    # command=SHOWVARS

    def showVars(self,unused,param):
        print("SHOWVARS:-")
        print("Local Vars=",self.state.localVars)
        print("Global Vars=", self.globalVars)
        print("Save XY Vars=", self.saveXYVars)


    #######################################################################
    #
    # variables and parameter evaluation
    #
    #######################################################################

    # check is value is a number or a string representation of an int or float
    def isNumber(self,value):
        if type(value) is float or type(value) is int:
            return True

        if self.reFloat.match(value):
            return True

        if self.reInt.match(value):
            return True
        return False

    # isExpression returns true if param contains either '+' or '-'
    def isExpression(self,param):
        if '+' in param or '-' in param: return True
        return False

    def isVarName(self,param):
        if self.reVarName.match(param): return True
        return False

    # anyIsNone is used to check a bunch of
    def anyIsNone(self,*args):
        isNone=False

        for x in range(len(args)):
            if args[x] is None:
                isNone=True
                self.Warning("Parameter "+str(x)+" on line "+str(self.srcLine)+" resolved as None. Possibly an unassigned variable. The line will be skipped.")
        return isNone

    # getVariable - used to add precedence to variables
    # saveXY masks local which masks global

    def getVariable(self,varName):
        if varName in self.saveXYVars:
            return self.saveXYVars[varName]
        if varName in self.state.localVars:
            return self.state.localVars[varName]
        if varName in self.globalVars:
            return self.globalVars[varName]
        return None


    # eval parm decides if the parameter is a number
    # if not it uses it as a variable name
    # only to be used for numeric parameters like X and Y
    # methods call this before transforming coordinates


    def evalNumericParam(self,param):
        # have we been passed an expression or a numeric value
        mathSign=""
        result=None

        # first check if param is simply a number already

        if type(param) is float or type(param) is int:
            # all numeric values intiially resolve to floats
            # items needing 'Net' numbers use int() to correct this
            # but it saves a heap of problems elsewhere to use
            # a single number format
            return float(param)

        param=param.strip() # the expressions may come in as strings

        # tokenise the parameters
        itemList=self.reItem.findall(param)

        # scan all the parameters
        # try to get values for variables

        for x in itemList:

            if x=="":
                # empty string can occur at end of the list
                return result

            if x[0] in "-+":
                mathSign=x[0]
                x=x[1:]
            else:
                mathSign="+" # just prevents subtraction

            # check if it's a number first - mostly likely case
            if self.isNumber(x):
                x=float(x)
                if mathSign=="-": x=-1*x
                if result is None: result = 0.0
                result=result+x

            elif self.reVarName.match(x):

                val=self.getVariable(x)

                # if a variable contains a string it isn't useable in
                # the context of a numeric expression
                if val is None or type(val) is str:
                    # can this be deliberate?
                    self.Warning("Unable to evaluate variable "+x+" perhaps you haven't defined it yet.")
                    return None

                if type(val) is float or type(val) is int:
                    if mathSign == "-": val = -1 * val  # precaution in case text
                    if result is None: result=0.0
                    result=result+val
            else:
                self.Warning("Unable to resolve expression "+x)

        # final result
        return result


    # eval string parameter is called when a parameter is expected to be a string
    # if it's the name of a local or global variable we return the value
    # otherwise assume it's a string literal
    
    def evalStringParam(self, param):
        param = param.strip()

        # check if it's a defined variable first
        r=self.getVariable(param)
        if r is None:
            # assume it's a string literal
            return param

        return r

    # try to make sense of a parameter
    def getValue(self,strValue):
        # value could be an expression including a variable
        if self.isExpression(strValue):
            val = self.evalNumericParam(strValue)  # returns a float or None
            if val is None:
                self.Warning("Unable to resolve parameter. Looks like an expression.")
                return None
            # should we store it anyway?
            val = strValue
        elif self.isNumber(strValue):
            val = float(strValue)
        else:
            # new string value or copying a previous?
            val=self.getVariable(strValue)
            if val is None: val = strValue
        return val

# setGlobal
    # can set a string or numerical value

    def setGlobal(self,id,params):
        varName,strValue=params.split(",")

        if type(varName) is not str:
            self.Warning("Variable names should be strings. Ignored")
            return None

        varName=varName.strip()
        strValue=strValue.strip()

        self.globalVars[varName] = self.getValue(strValue)

        return None

    def getGlobalVar(self,varName):
        try:
            return self.globalVars[varName]
        except KeyError:
            return None

    def getLocalVar(self, varName):
        try:
            return self.state.localVars[varName]
        except KeyError:
            return None

    def setLocal(self,id,params):
        varName,strValue=params.split(",")
        varName=varName.strip()

        if type(varName) is not str:
            self.Warning("Variable names should be strings. Ignored")
            return None

        varName=varName.strip()
        strValue=strValue.strip()

        self.state.localVars[varName] = self.getValue(strValue)

        return None


    def clrGlobal(self,unused,varName):
        if type(varName) is not str:
            self.Warning("Variable names should be strings. Ignored")
        else:
            varName=varName.strip()
            del self.globalVars[varName]

        return None

    def clrLocal(self,unused,varName):
        if type(varName) is not str:
            self.Warning("Variable names should be strings. Ignored")
        else:
            varName=varName.strip()
            del self.state.localVars[varName]

        return None


    #######################################################################
    #
    # code to handle parameter lists
    #
    #######################################################################

    # loadList
    def loadList(self,unused,params):
        Id,Sep,Filename=params.split(",")
        # line format is TEMPLATE,id,filename
        Id=Id.strip().upper()
        Sep=Sep.strip()
        Filename=Filename.strip()

        # already loaded?
        if Id in self.list:
            self.Warning("List " + Id + " already loaded. Ignored.")
            return None

        try:
            file = open(Filename, "r")

            theList=[]  # start clean

            # load each line and split it into a list of params
            # append each line to the
            lines = file.readlines()
            for line in lines:
                # split the line into separate parameters
                # and lose any white space
                # clean up input
                line = line.strip()
                # ignore comments and blank lines
                # ORDER MATTERS !
                if (line == "") or (line[0] == "#"): continue
                entry=line.split(Sep)
                entry=[x.strip() for x in entry]
                theList.append(entry)
            file.close()

            self.list[Id]=theList

            self.Info("LIST ID=[" + Id + "]. Loaded ok.")

        except Exception as e:
            self.Error("Cannot load list [" + id + "]\n" + e.args)
        finally:
            return None

    # useList simply triggers the building of a list
    def beginUseList(self,unused,params):
        self.makingUseList=True
        self.useList=[]
        self.useListId=params.strip()
        pass

    # endlist - executes the commands from a list
    # and substitues placeholders with parameters
    def endUseList(self,id,params):
        if not self.makingUseList:
            self.Warning("Orphaned ENDUSELIST encountered.")
            return

        self.makingUseList=False
        self.Info("Processing LIST "+self.useListId)
        # retrieve the list of parameters
        thisList=self.list[self.useListId]

        result=""
        # foreach parameter
        for p in thisList:
            # do these commands
            for l in self.useList:
                srcLine,id,params=l
                r=self.parse(srcLine,id,self.useListHelper(params,p))
                if r is not None:
                    result=result+"\n"+r
        return result

    # useListHelper replaces %0%,%1% with corresponding parameters from the list
    def useListHelper(self,line,p):
        for x in range(len(p)):
            line=line.replace("%"+str(x)+"%",p[x])
        return line

    #######################################################################
    #
    # code to handle creating rings of components
    #
    #######################################################################

    #DEFRING
    #
    # id is 'DEFRING' - not used
    def defRing(self,unused,params):
        self.makingRing=True

        self.state.ringId = params.strip()  # should only be one

        if self.state.ringId in self.repeat:
            self.Warning("Ring with Id " + self.state.ringId + " will be redefined.")
        return None

    # ENDRING
    def endRing(self,unused1,unused2):

        if self.makingRing:
            self.makingRing = False
            self.ring[self.state.ringId] = self.state.ringList
            self.state.ringList = []
        else:
            self.Warning("Orphaned ENDRING encountered.")

        return None

    # processRing
    # deals with the RING call
    #
    # Id is 'REPEAT' - not used

    def processRing(self, unused, params):
        # X,Y and Angle are the co-ords and rotation angle for the group
        # Counter is how many time to iterate the block
        ringId, Xpos, Ypos, Radius,Mode,startAngle,Counter,stepAngle= params.split(",")

        ringId=ringId.strip()
        # make sure numeric params have variables subsituted and are float
        stepAngle=self.evalNumericParam(stepAngle)

        if Mode.upper()=="NONE":
            # we don't want component rotation
            Mode=None
        else:
            Mode = self.evalNumericParam(Mode)  # rotation angle 0->radial alignment,-/+90 gives tangential

        Xpos=self.evalNumericParam(Xpos)
        Ypos=self.evalNumericParam(Ypos)
        Radius=self.evalNumericParam(Radius)
        startAngle=self.evalNumericParam(startAngle)
        Counter=self.evalNumericParam(Counter)

        if self.anyIsNone(Xpos, Ypos, Radius,startAngle,Counter,stepAngle):
            self.Warning("One or more RING parameters did not resolve as a number. Ring ignored.")
            return None

        if stepAngle==0:
            self.Warning("Ring ID " + ringId + " has no step angle. Ring ignored.")
            return None

        if ringId in self.ring:
            self.state.ringList = self.ring[ringId]
        else:
            self.Warning("Ring ID " + ringId + " hasn't been defined. Ring ignored.")
            return None

        self.processingRing = True

        self.pushState()

        # tarnsformXY may need to know this
        self.state.ringCx=Xpos
        self.state.ringCy=Ypos
        self.state.ringRad=Radius

        thisAngle = startAngle
        self.state.ringId = ringId

        result = ""

        for i in range(int(Counter)):
            # get 0,0 position of the component/group
            self.state.ringX,self.state.ringY=self.getCircleXY(self.state.ringCx,self.state.ringCy,self.state.ringRad,thisAngle)
            self.state.ringAngle=thisAngle

            # do we want the components rotated?
            if Mode is None: self.state.ringAngle=0
            else: self.state.ringAngle=thisAngle+Mode

            for c in self.state.ringList:
                (lineNum, id, params) = c
                r = self.parse(lineNum, id, params)
                if r is None: continue
                result = result + r
            thisAngle=thisAngle+stepAngle
        self.popState()
        self.processingRing = False
        return result

    #########################################################################################
    #
    # code to handle repeating components
    #
    # these can be horizontsal, vertical of sloping lines of components
    #
    #########################################################################################

    #DEFREPEAT
    #
    # id is 'DEFGROUP' - not used
    def defRepeat(self,unused,params):
        self.makingRepeat=True

        self.state.repeatId = params.strip()  # should only be one

        if self.state.repeatId in self.repeat:
            self.Warning("Repeat with Id " + self.state.repeatId + " will be redefined.")
        return None

    # ENDREPEAT
    def endRepeat(self,unused1,unused2):
        if self.makingRepeat:
            self.makingRepeat = False
            self.repeat[self.state.repeatId] = self.state.repeatList
            self.state.repeatList = []
        else:
            self.Warning("Orphaned ENDREPEAT encountered.")

        return None

    # processRepeat
    # deals with the REPEAT call
    #
    # Id is 'REPEAT' - not used
    def processRepeat(self,unused,params):
        # X,Y and Angle are the co-ords and rotation angle for the group
        # Counter is how many time to iterate the block
        repeatId, Xpos,Ypos,startAngle,Counter,stepX,stepY, stepAngle = params.split(",")

        repeatId=repeatId.strip()
        # resolve numeric values
        Xpos=self.evalNumericParam(Xpos)
        Ypos=self.evalNumericParam(Ypos)
        startAngle=self.evalNumericParam(startAngle)
        Counter=self.evalNumericParam(Counter)
        stepX=self.evalNumericParam(stepX)
        stepY=self.evalNumericParam(stepY)
        stepAngle=self.evalNumericParam(stepAngle)

        if repeatId in self.repeat:
            self.state.repeatList= self.repeat[repeatId]
        else:
            self.Warning("Repeat ID " + repeatId + " hasn't been defined. Repeat ignored.")
            return None

        self.processingRepeat=True

        self.pushState()

        self.state.repeatX=Xpos
        self.state.repeatY=Ypos
        self.state.repeatAngle=startAngle
        self.state.repeatId=repeatId

        result=""

        for i in range(int(Counter)):
            # update the repeat counter here
            for c in self.state.repeatList:
                (lineNum, id, params) = c
                r = self.parse(lineNum, id, params)
                if r is None: continue
                result = result + r
            # move the X/Y and Angle forward
            # at the end of the repeat list
            self.state.repeatX=self.state.repeatX+stepX
            self.state.repeatY=self.state.repeatY+stepY
            self.state.repeatAngle=self.state.repeatAngle+stepAngle

        self.popState()
        self.processingRepeat=False
        return result

    ##################################################################################################
    #
    # code for managing grouping of components - you can form groups of arbitrary lists of components
    # which may include other groups  then stamp them down any which way you like
    #
    ##################################################################################################

    # DEFGROUP
    #
    # id is 'DEFGROUP' - we don't use it
    def defGroup(self,unused,params):
        if self.makingGroup:
            self.Warning("You cannot use DEFGROUP within a DEFGROUP. Previous ENDGROUP may be missing.")
            return None
        if self.makingRepeat:
            self.Warning("You cannot use DEFGROUP within a DEFREPEAT. Previous ENDREPEAT may be missing.")
            return None

        self.makingGroup = True
        self.state.groupId = params.strip()  # should only be one

        if self.state.groupId in self.group:
            self.Warning("Group with Id " + self.state.groupId + " will be redefined.")
        return None

    # ENDGROUP
    def endGroup(self,unused1,unused2):
        if self.makingGroup:
            self.makingGroup = False
            self.group[self.state.groupId] = self.state.groupList
            self.state.groupList = []
        else:
            self.Warning("Orphaned ENDGROUP encountered.")

        return None


    # processGroup
    # deals with the GROUP call
    #
    # id passed in is just 'GROUP' - we don't use it

    def processGroup(self, unused, params):

        # X,Y and Angle are the co-ords and rotaion angle for the group
        groupId, Xpos, Ypos, Angle = params.split(",")

        # clean it up
        groupId=groupId.strip()
        Xpos=self.evalNumericParam(Xpos)
        Ypos=self.evalNumericParam(Ypos)
        Angle=self.evalNumericParam(Angle)


        if groupId in self.group:
            # remember these so we can restore them later
            self.pushState()
            groupList = self.group[groupId]
        else:
            self.Warning("Group ID " + groupId + " hasn't been defined. Group ignored.")
            return None

        # flag used to amend references
        self.processingGroup = True;
        self.state.groupId = groupId  # used by others to get the reference postfix

        # set the new offsets for this group
        self.state.groupX = Xpos
        self.state.groupY = Ypos
        self.state.groupAngle = Angle

        result = ""
        for x in groupList:
            # lineNum will be the line number from the position data file
            # this helps to identify which line within a group failed (if any)
            (lineNum, id, params) = x
            r = self.parse(lineNum, id, params)
            if r is None: continue
            # add linefeeds for tidy output
            result = result + "\n"+ r

        # restore offsets
        self.popState()

        self.processingGroup = False
        return result

    #####################################################################################
    #
    # miscellaneous helpers
    #
    #####################################################################################

    # routines used to tidy output
    # no need having floating point to a zillion decimal places

    # strFloat - used to create coordinates limited to dp decimal places
    # defaults to 4dp which give an accuracy of (1/10000) units (mm/in?)
    def strFloat(self,value):
        if value is None:
            self.Warning("strFloat was passed a None value. This will show up in the kicad_pcb file as 'NONE'. pcb_new will complain if you try to open it!")
            return "NONE"
        if type(value) is str:
            return value
        return self.fmtFloat.format(value)

    #strInt
    def strInt(self,value):
        if type(value) is str: return value
        return "{}".format(int(value))


    # echo
    # prints XY coordintes adjusted for transforms
    # useful for getting coords when an track is rotated

    def echo(self,unused,params):
        userTag,X,Y=params.split(",")
        userTag=userTag.strip()
        X=self.evalNumericParam(X)
        Y=self.evalNumericParam(Y)

        if self.anyIsNone(X,Y):
            self.Warning("ECHO - one or more parameteers were unresolved. Ignored")
            return None

        X, Y = self.transformXY(X, Y)
        X=X-self.state.xOrigin
        Y=Y-self.state.yOrigin
        X=X*self.directionX
        Y=Y*self.directionY

        print("ECHO Id=",userTag,"X,Y=",self.strFloat(X),",",self.strFloat(Y))

    # swapSigns
    # changes + to - and vice versa
    # this is used for calcs using saveXY variables to compensate for
    # the currect direction of X and Y
    def swapSigns(self,A):
        B = []
        for x in range(len(A)):
            ch = A[x]
            if ch == "+":
                ch = "-"
            elif ch == "-":
                ch = "+"
            B.append(ch)

        return "".join(B)

    # resolveCoords
    #
    # if the coords are expressions containing saveXY variables
    # then the calculated xy values should not be transformed
    # other than for X,Y coordinate direction
    #
    def resolveCoords(self,X,Y):

        # saveXY variables are already transformed
        # we have just calculated the absolute coords
        if self.varContainsSaveXYVar(X) and self.directionX==-1:
            X=self.swapSigns(X)
        x=self.evalNumericParam(X)

        if self.varContainsSaveXYVar(Y) and self.directionY==-1:
            Y=self.swapSigns(Y)
        y=self.evalNumericParam(Y)

        # saveXY variables are already transformed
        # we have just calculated the absolute coords
        # so return them
        if self.varContainsSaveXYVar(X) and  self.varContainsSaveXYVar(Y):
            return x,y

        #
        if self.anyIsNone(x,y):
            return x,y

        # do the transform but restore the one whcih shouldn't be

        x1,y1=self.transformXY(x,y)

        if self.varContainsSaveXYVar(X): x1=x
        if self.varContainsSaveXYVar(Y): y1=y

        return x1,y1

    # varContainsSaveXYVar
    #
    # check if the parameter is a saveXY variable or an expression containing one
    #
    def varContainsSaveXYVar(self,param):

        if self.isNumber(param): return False

        #param could be the name of a variable like DIN_X as in SAVEXY,RINGIN,DIN_X,DIN_Y+10

        # quick check first for simple variable name on it's own
        if param in self.saveXYVars:
            return True

        # see if the expression contains the svaeXY vars
        for v in self.saveXYVars:
            p=re.compile(v)
            if p.match(param):
                return True

        return False

    # saveXY
    # saves the current real-world coordinates

    def saveXY(self,unused,params):

        varName,X,Y=params.split(",")

        varName=varName.strip()

        x,y=self.resolveCoords(X,Y)

        if self.anyIsNone(x,y):
            self.Warning("saveXY parameters were unresolved. Unable to save "+varName)
            return None

        varX=varName + "_X" # cannot use an expression for the key, apparently
        varY=varName + "_Y"
        self.saveXYVars[varX] = x
        self.saveXYVars[varY] = y
        return None

    # saveOnceXy
    # used to remember XY coords at the START of a repeat or ring
    #
    def saveOnceXY(self,unused,params):

        varName, X, Y = params.split(",")

        varName = varName.strip()

        varName=varName+"_X"
        #if it already exists it has been saved once already
        # so ignore it
        if varName in self.saveXYVars:
            return None

        return self.saveXY(unused,params)

    # getCircleXY returns the co-ords of a point on a circle
    # just a useful routine to help with Altzheimer's
    # i.e. forgetting which way around the cos and sin are LOL
    # cords are based on angle inclreasing anti-clockwise

    def getCircleXY(self, cx, cy, radius, angle):
        assert type(cx) is float, "getCircleXY() cx is not a float."
        assert type(cy) is float, "getCircleXY cy is not a float."
        assert type(angle) is float, "getCircleXY() angle is not a float."
        assert type(radius) is float, "getCircleXY() Radius is not a float."

        if radius<0:
            self.Error("GetCircle radius cannot be negative radius=",radius)
            radius=abs(radius)

        angle = angle * math.pi / 180  # must be in radians

        x, y = cx + radius * math.cos(angle), cy + radius * math.sin(angle)

        return x,y

    # returns the angle (degrees) of the point XY assumed
    # to be on a circle centred at 0,0
    # kicad uses degrees in the data file not radians
    # mostly used when calculating rotation of grouped items

    def getAngleRadiusXY(self, X, Y):
        # no point continuing if the x/y is at the origin
        if X==0.0 and Y==0.0: return 0.0,0.0

        r = math.sqrt(X * X + Y * Y)

        # simple cases at 0,90,180,270
        # default if either X or Y is zero
        # note that X or Y may be negative so raturn value must be abs
        if X==0 or Y==0:
            if Y==0:
                if X>0: return 0.0,abs(X)
                return 180.0,abs(X)
            if X==0:
                if Y>0: return 90,abs(Y)
                return 270.0,abs(Y)

        # get the angle in degrees
        # this can return the +a and -a
        a=math.asin(Y / r)*180.0/math.pi

        # angle could be in one of 4 quadrants
        #
        if X>0:
            # a will be + or -
            return a,r
        if X<0:
            return 180.0-a,r


        self.Error("getAngleRadiusXY() failed to resolve angle")
        return 0.0,0.0

    # transformXY(X,Y)
    #

    # final transformation of XY to real world coordinates based on originX,originY and angleOrigin
    # getXY returns the XY co-ords of a point at an Angle assuming X/Y lie
    # on a circle centred at 0,0.
    # this is called to transform coords about to be written to the output

    def transformXY(self, X, Y):
        assert type(X) is float, "transformXY() X must be a float."
        assert type(Y) is float, "transformXY() Y must be a float."

        # deal with translation and compound rotation
        if self.processingGroup or self.processingRepeat or self.processingRing:
            # components XY values are offsets from zero
            angle,radius=self.getAngleRadiusXY(X,Y)

            # the group centre is at 0,0
            # we only need to change components in the group if not at 0,0
            if radius != 0:

                combinedRotation=angle+self.state.groupAngle+self.state.repeatAngle+self.state.ringAngle
                X, Y = self.getCircleXY(0.0, 0.0, radius,combinedRotation )

        # a group in a ring will be at groupX=ringX etc - must not add twice
        if self.processingGroup:
            X, Y = X + self.state.groupX, Y + self.state.groupY
        if self.processingRepeat:
            X, Y = X + self.state.repeatX, Y + self.state.repeatY
        if self.processingRing:
            X, Y = X + self.state.ringX, Y + self.state.ringY

        # adjust for plotting direction
        X=X*self.directionX
        Y=Y*self.directionY

        # has the origin been turned?
        rotAngle=self.state.angleOrigin

        if rotAngle:
            cosA = math.cos(rotAngle * math.pi / 180)
            sinA = math.sin(rotAngle * math.pi / 180)
            X1,Y1= X * cosA + Y * sinA, -X * sinA + Y * cosA
        else:
            X1,Y1=X,Y
        # now compensate for the origin being somewhere whacky
        X1 = X1 + self.state.xOrigin #
        Y1 = Y1 + self.state.yOrigin #
        return X1, Y1

    # transformAngle
    #
    # all components design coordinates are based on an unrotated shape
    # this returns the new angle allowing for changes to the origin, group, repeat or ring
    # angleOrigin is no longer changeable by the user

    def transformAngle(self, Angle):
        assert type(Angle) is float, "getComponentAngle() Angle must be a float (degrees)."
        r= Angle + self.state.angleOrigin + self.state.groupAngle + self.state.repeatAngle + self.state.ringAngle
        return r


    # get the XY coords of a point on an ellipse
    # not yet used
    def getEllipseXY(self,cx,cy,a,b,angle):
        assert type(cx) is float, "getEllipseXY() cx is not a float."
        assert type(cy) is float, "getEllipseXY cy is not a float."
        assert type(angle) is float, "getEllipseXY() angle is not a float."
        assert type(a) is float, "getEllipseXY() a is not a float."
        assert type(b) is float, "getEllipseXY() b is not a float."

        return cx+a*math.cos(angle),cy+b*math.sin(angle)


    # showState
    # used for debugging - prints the state variables
    def showState(self):
        print(self.state);

    # pushState
    #
    # saves current state variables on the stateStack
    # since the state variables are in an object I use deepcopy()
    # otherwise it'll just push a pointer to the object

    def pushState(self):
        self.stateStack.append(copy.deepcopy(self.state))

    # popState
    #
    # restores state variables object
    def popState(self):
        self.state=self.stateStack.pop()

    # getTemplate
    #
    # does what it says. The templates are listed at the start of the
    # datafile
    def getTemplate(self,id):
        id=id.strip()
        if id in self.template: return self.template[id]
        self.Warning("No template loaded for ID="+id+" check your data file")
        return None

    # refNum=getRef(id,ref)
    #
    # formats the reference string by appending a global usage count
    # The usage count is maintained per Id for parts which
    # use them so all WS2812B devices are sequentially numbered as are
    # any other components

    def getRef(self,id,ref):
        id=id.strip()
        if id in self.ref:
            self.ref[id]=self.ref[id]+1
        else:
            self.ref[id]=1
        return ref+str(self.ref[id])

    # template=validateTemplate(self,id,typeWanted)
    # loads template with id
    # checks template begins with the typeWanted e.g. '(gr_text'
    # if all ok returns the template otherwise None
    def validateTemplate(self,id,typeWanted):
        template = self.getTemplate(id)
        if template is None: return None

        # templates start (type .... so grab the text
        # after the first (
        lst=re.findall('^\s*\((\S+)[\s\(]', template)

        if lst[0].upper()==typeWanted.upper(): return template

        self.Warning("Requested template "+id+" doesn't appear to be of type "+typeWanted+". Ignored.")
        return None


    ########################################################################
    #
    # Standard template handling
    #
    # these are all passed the Id and parameter lists. In some cases id is
    # not used but to simplify coding it is passed anyway and if not used
    # the parameter name will be 'unused'
    #
    # The methods should return a template string with placeholders
    # substituted or None. If None is returned the loop in makePCB.py
    # will not write anything to the output file.
    #
    # ######################################################################

    # TEMPLATE,Id,filename
    # loads a specified template from disk
    def loadTemplate(self,unused,params):
        # line format is TEMPLATE,id,filename
        id,filename=params.split(",")
        # attempt to load the designated template
        id=id.strip()
        try:
            # already loaded?
            if id in self.template: return None

            file = open(filename, "r")
            self.template[id] = file.read()
            file.close()
            self.Info("TEMPLATE ID=["+id+"]. Loaded ok.")
        except Exception as e:
            self.Error("Cannot load template [" + id + "]\n" + e.args)
        finally:
            return None


    # ASIS,templateId,filename
    # loads a specified AS-IS template from disk
    # these template have no placeholders so require no processing
    def loadAsis(self,unused,params):
        # line format is TEMPLATE,id,filename
        id,filename=params.split(",")
        # attempt to load the designated template

        try:
            # already loaded?
            if id in self.asis: return None

            file = open(filename, "r")
            self.asis[id] = file.read()
            file.close()
            self.Info("ASIS ID=["+id+"]. Loaded ok.")
        except Exception as e:
            self.Error("Cannot load asis template [" + id + "]\n" + e.args)
        finally:
            return None

    # a kiCad_pcb file has opening and closing brackets we need to get rid of
    # they don't include place holders so they are added to the self.asis dictionary

    def loadKicadPcb(self,unused,params):
        # line format is TEMPLATE,id,filename
        id, filename = params.split(",")
        # attempt to load the designated template

        try:
            # already loaded?
            if id in self.asis:
                self.Warning("KICADPCB id=",id)
                return None

            file = open(filename, "r")
            data= file.read()
            file.close()

            # does the document begin with '(kicad_pcb'?
            # note that there could be white space before and after the bracket
            result = re.match('^\s*\(\s*kicad_pcb',data)
            if not result:
                self.Warning("KICADPCB filename "+filename+" doesn't look like a kicad_pcb file. Ignored")
                return None


            # scan for closing and opening brackets then remove them
            x=0
            lenData=len(data)
            y = lenData-1

            while (x<lenData) and (data[x]!="("): x=x+1
            while (y > x) and (data[y]!=")"):  y = y - 1

            # just store what's in between - makePCB will add the starting and ending
            # brackets to the output file
            self.asis[id]=data[x+1:y-1]

            self.Info("KiCad pcb id=[" + id + "]. Loaded ok.")

        except Exception as e:
            self.Error("Cannot load KiCad pcb document template [" + id + "]\n" + e.args)
        finally:
            return None



    # SETDIRECTION,X,Y
    def setDirection(self,unused,params):
        X,Y=params.split(",")

        # evalNumericParam does variable gathering
        X=self.evalNumericParam(X)
        Y=self.evalNumericParam(Y)

        if self.anyIsNone(X,Y):
            self.Warning("Cannot SETDIRECTION X or Y parameters are unresolved. Ignored.")
            return None

        # only +ve or -ve are allowed
        # if zero we don't make a change
        if X<0:     self.directionX=-1
        elif X>0:   self.directionX=1

        if Y<0:     self.directionY=-1
        elif Y>0:   self.directionY=1

        self.Info("Co-ordinate directions set to X="+str(self.directionX)+" Y="+str(self.directionY))
        return None

    # cannotAdd
    # just emits a standard warning

    def cannotAdd(self,what):
        self.Warning("Cannot add "+what+" because one or more parameters are unresolved. Ignored.")

    # ORIGIN,X,Y (,angle - removed)
    # updates the current value of the drawing origin
    # using ORIGIN enables you to move the entire drawing up/down/left/right
    # KiCad's drawing origin is somewhere just outside the top-left of the drawing
    #

    def origin(self,unused,params):
        xOrigin,yOrigin=params.split(",")

        xOrigin=self.evalNumericParam(xOrigin)
        yOrigin=self.evalNumericParam(yOrigin)

        if self.anyIsNone(xOrigin,yOrigin):
            self.Warning("Unable to set the ORIGIN because X or Y is unresolved. Ignored.")
            return None

        self.state.xOrigin=xOrigin
        self.state.yOrigin=yOrigin

        # also make this available globally
        self.globalVars["xOrigin"]=xOrigin
        self.globalVars["yOrigin"]=yOrigin

        self.Info("Origin changed to X="+str(xOrigin)+" Y="+str(yOrigin))
        return None

    # VIA,X,Y,Size,Drill,LayerF,LayerB,Net
    #
    # places a via where specified
    #

    def via(self, id, params):
        id=id.strip()
        template = self.validateTemplate(id,"via")
        if template is None: return None

        Xpos, Ypos, Size, Drill, LayerF, LayerB, Net=params.split(",")

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos)

        Size=self.evalNumericParam(Size)
        Drill=self.evalNumericParam(Drill)
        Net=int(self.evalNumericParam(Net))     # numerical only, or a variable?
        LayerF=self.evalStringParam(LayerF)
        LayerB=self.evalStringParam(LayerB)

        if self.anyIsNone(Xpos,Ypos,Size,Drill,LayerF,LayerB,Net):
            self.cannotAdd("VIA")
            return None

        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%SIZE%", self.strFloat(Size))
        template = template.replace("%DRILL%", self.strFloat(Drill))
        template = template.replace("%LAYERF%", LayerF)
        template = template.replace("%LAYERB%", LayerB)
        template = template.replace("%NET%", self.strInt(Net))

        return template

    # FIDUCIAL,Ref,Xpos,Ypos,Clearance,Width,Layer
    #
    # creates a fiducial at the required location
    # normally put in three corners of the layout (even though PCB may not be rectangular
    #

    def fiducial(self,id,params):
        template = self.getTemplate(id)
        if template is None: return None

        Ref, Xpos, Ypos, Clearance, Width, Layer = params.split(",")
        Ref=Ref.strip()

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos)
        Clearance=self.evalNumericParam(Clearance)
        Width=self.evalNumericParam(Width)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos,Ypos,Clearance,Width,Layer):
            self.cannotAdd("FIDUCIAL")
            return None

        #(Xpos,Ypos) = self.transformXY(Xpos,Ypos) done by resolveCoords

        template = template.replace("%REF%", self.getRef(id,Ref))
        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%CLEARANCE%", self.strFloat(Clearance))
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%LAYER%", Layer)

        return template

    # TARGET,Shape,Xpos,Ypos,Size,Width,Layer
    # place a target at X/Y
    # shape can be 'plus' or 'x' - without the quotes

    def target(self,id,params):

        template = self.getTemplate(id)
        if template is None: return None

        Shape, Xpos, Ypos, Size, Width, Layer = params.split(",")
        Shape=Shape.strip()

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos) # does 2D transform too
        Size=self.evalNumericParam(Size)
        Width=self.evalNumericParam(Width)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos,Ypos,Size,Width,Layer):
            self.cannotAdd("TARGET")
            return None

        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%SHAPE%", Shape)
        template = template.replace("%SIZE%", self.strFloat(Size))
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%LAYER%", Layer)

        return template

    # MOUNT,Ref,Xpos,Ypos,Drill,OuterRadius,InnerWidth,OuterWidth
    #
    # a mounting point - a hole with some copper around it (difefrence between
    # Drill and OuterRadius, InnerWidtha dn OuterWidth are line dimensions
    # Mounting holes can have references.
    #
    def mounting(self,id,params):

        template = self.getTemplate(id)
        if template is None: return None
        
        Ref, Xpos, Ypos, Drill, OuterRadius, InnerWidth, OuterWidth = params.split(",")

        Ref=Ref.strip()

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos)
        Drill=self.evalNumericParam(Drill)
        OuterRadius=self.evalNumericParam(OuterRadius)
        InnerWidth=self.evalNumericParam(InnerWidth)
        OuterWidth=self.evalNumericParam(OuterWidth)

        if self.anyIsNone(Xpos,Ypos,Drill,OuterRadius,InnerWidth,OuterWidth):
            self.cannotAdd("MOUNTING HOLE")
            return None

        template = template.replace("%REF%", self.getRef(id,Ref))
        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%DRILL%", self.strFloat(Drill))
        template = template.replace("%INNERWIDTH%", self.strFloat(InnerWidth))
        template = template.replace("%OUTERWIDTH%", self.strFloat(OuterWidth))
        template = template.replace("%OUTERRADIUS%", self.strFloat(OuterRadius))

        return template

    #################################################
    # GRAPHIC,Shape,<shape-params>
    #
    # routes the call to the required helper
    #
    #################################################

    def graphic(self,id,params):

        Shape,Remainder=params.split(",",1)
        Shape=Shape.strip().upper()

        if Shape=="LINE":           return self.graphic_line(Remainder)
        elif Shape=="CIRCLE":       return self.graphic_circle(Remainder)
        elif Shape == "ARCANGLE":   return self.graphic_arc_angle(Remainder)
        elif Shape == "PIE":          return self.graphic_pie(Remainder)
        elif Shape == "TEXT":       return self.graphic_text(Remainder)
        elif Shape == "RECT":       return self.graphic_rectangle(Remainder)
        elif Shape == "ROUNDEDRECT": return self.graphic_rounded_rect(Remainder)
        elif Shape == "GRID":       return self.graphic_grid(Remainder)

        self.Warning("Unsupported graphics "+Shape+". Ignored")
        return None

    def graphic_rounded_rect(self,params):
        # uses GRLINE and GRARC
        x,y,width,height,radius,LineWidth,Layer=params.split(",")

        x,y=self.resolveCoords(x,y) # bottom left corenr of the rectangle

        w=self.evalNumericParam(width)
        h=self.evalNumericParam(height)
        r=self.evalNumericParam(radius)
        LineWidth=self.evalNumericParam(LineWidth)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(x,y,w,h,r,LineWidth,Layer):
            self.cannotAdd("GRAPHIC ROUNDEDRECT")
            return None

        # cannot use graphic_rect_helper because of the gaps required for arcs
        # bottom line
        X1=x+self.directionX*r
        X2=x+self.directionX*(w-r)
        Y2=Y1=y
        result=self.graphic_line_helper(X1,Y1,X2,Y2,LineWidth,Layer)
        # top line - just Y changes
        Y2=Y1=y+self.directionY*h
        result = result + "\n" + self.graphic_line_helper(X1,Y1,X2,Y2, LineWidth, Layer)
        # left side top to bottom
        X1=X2=x
        Y1=y+self.directionY*r
        Y2=y+self.directionY*(h-r)
        result = result + self.graphic_line_helper(X1,Y1,X2,Y2, LineWidth, Layer)
        # right hand side - just X changes
        X2=X1=x+self.directionX*w
        result = result + "\n" + self.graphic_line_helper(X1,Y1,X2, Y2, LineWidth, Layer)

        # rounded corners
        #bottom left
        XC=x+self.directionX*r
        YC=y+self.directionY*r
        result = result +  "\n" +self.graphic_arc_helper(XC, YC,r, 180, 270, LineWidth, Layer, False)
        # bottom right - only X and angle changes
        XC=x+self.directionX*(w-r)
        result=result +  "\n"  + self.graphic_arc_helper(XC,YC,r,270,360, LineWidth, Layer, False)
        # top right - only Y changes
        YC=y+self.directionY*(h-r)
        result = result +  "\n" +self.graphic_arc_helper(XC,YC, r,0, 90, LineWidth, Layer, False)
        #top-left - only X changes
        XC = x + self.directionX * r
        result = result +  "\n" +self.graphic_arc_helper(XC,YC ,r, 90, 180, LineWidth, Layer, False)

        return result



    def graphic_arc_angle(self,params):
        # don't create a pie
        Xc, Yc, Radius, startAngle, stopAngle, Width, Layer = params.split(",")

        Xc,Yc=self.resolveCoords(Xc,Yc)
        Radius=self.evalNumericParam(Radius)

        if self.anyIsNone(Xc,Yc,Radius):
            self.cannotAdd("GRAPHIC ARCANGLE")
            return None

        return self.graphic_arc_helper(Xc, Yc, Radius, startAngle, stopAngle, Width, Layer, False)

    def graphic_pie(self,params):
        # tell the helper to draw in the radial lines
        Xc, Yc, Radius, startAngle, stopAngle, Width, Layer = params.split(",")
        Xc,Yc=self.resolveCoords(Xc,Yc)
        Radius=self.evalNumericParam(Radius)

        if self.anyIsNone(Xc,Yc,Radius):
            self.cannotAdd("GRAPHIC PIE")
            return None

        return self.graphic_arc_helper(Xc, Yc, Radius, startAngle, stopAngle, Width, Layer,True)

    # helper sanitises parameters
    # Xc,Yc and Radius are resolved by callers - especially the roundedrect
    def graphic_arc_helper(self, Xc, Yc, Radius, startAngle, stopAngle, Width, Layer,makePie):

        template = self.validateTemplate("GRARC", "gr_arc")
        if template is None: return None

        # oddly, Kicad uses the centre, the start point then the angle (clockwise)

        # evaluate additional params
        startAngle=self.evalNumericParam(startAngle)
        stopAngle=self.evalNumericParam(stopAngle)
        Width=self.evalNumericParam(Width)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(startAngle,stopAngle,Width,Layer):
            self.cannotAdd("GRAPHIC ARCANGLE/PIE")
            return None

        # kicad draws clockwise which means its angles are 360-normal angles
        # start and end also need swapping
        s=startAngle
        startAngle=stopAngle
        stopAngle=s

        stopAngle=360-stopAngle
        startAngle=360-startAngle

        if stopAngle<startAngle: stopAngle=stopAngle+360

        ArcAngle = abs(stopAngle - startAngle) # never changes

        # get co-ords of the start and end points. Kicad uses centre and first point plus angle
        # and draws clockwise so we need to calc start point using stopAngle

        Xstart, Ystart = self.getCircleXY(Xc, Yc, Radius, startAngle)
        Xend, Yend = self.getCircleXY(Xc, Yc, Radius, stopAngle)

        template = template.replace("%XPOS1%", self.strFloat(Xc))
        template = template.replace("%YPOS1%", self.strFloat(Yc))
        template = template.replace("%XPOS2%", self.strFloat(Xstart))
        template = template.replace("%YPOS2%", self.strFloat(Ystart))
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%LAYER%", Layer)
        template = template.replace("%ANGLE%", self.strFloat(ArcAngle))

        if makePie:
            # graphic_line will transform lines

            fmtString=self.fmtFloat+","
            fmtString=fmtString*5+"{}"

            Xstart,Ystart=self.transformXY(Xstart,Ystart)
            Xend, Yend = self.transformXY(Xend, Yend)
            Xc,Yc=self.transformXY(Xc,Yc)

            params=fmtString.format(Xc,Yc,Xstart,Ystart,Width,Layer)
            template=template+self.graphic_line(params)
            params=fmtString.format(Xc,Yc,Xend,Yend,Width,Layer)
            template=template+self.graphic_line(params)

        return "\n"+template

    def graphic_rectangle(self, params):

        X, Y, Width, Height, LineWidth, Layer = params.split(",")

        X, Y = self.resolveCoords(X, Y)
        Width = self.directionX * self.evalNumericParam(Width)
        Height = self.directionY * self.evalNumericParam(Height)
        LineWidth = self.evalNumericParam(LineWidth)
        Layer = self.evalStringParam(Layer)

        if self.anyIsNone(X, Y, Width, Height, LineWidth, Layer):
            self.cannotAdd("GRAPHIC RECT")
            return None

        return self.graphic_rect_helper(X, Y, Width, Height, LineWidth, Layer)

    # graphic_rect_helper
    # called from several places creating rectangular shapes
    def graphic_rect_helper(self, X, Y, Width, Height, LineWidth, Layer):
        # 4 lines - uses graphic_line_helper

        result = self.graphic_line_helper(X, Y, X + Width, Y, LineWidth, Layer)
        result = result + self.graphic_line_helper(X + Width, Y, X + Width, Y + Height, LineWidth, Layer)
        result = result + self.graphic_line_helper(X + Width, Y + Height, X, Y + Height, LineWidth, Layer)
        result = result + self.graphic_line_helper(X, Y + Height, X, Y, LineWidth, Layer)

        return result


    # graphic_text X,Y,Size,Thickness,Layer,text-to-write
    #
    # draws text at the given position. text-to-write MUST not contain
    # double quotes

    def graphic_text(self,params):

        template = self.validateTemplate("GRTEXT", "gr_text")
        if template is None: return None

        # X,Y,Size,Thickness,Layer,the text to display
        # txt is the remainder of the line whatever it contains
        Justify,Xpos,Ypos,Angle,Size,Thickness,Layer,Text=params.split(",",7)

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos)

        Angle=self.evalNumericParam(Angle)
        Size=self.evalNumericParam(Size)
        Thickness=self.evalNumericParam(Thickness)
        Layer=self.evalStringParam(Layer)
        Justify=self.evalStringParam(Justify)

        if self.anyIsNone(Justify,Xpos,Ypos,Angle,Size,Thickness,Layer):
            self.cannotAdd("GRAPHIC TEXT")
            return None

        Text=Text.replace('"','\\"')    # massage embedded quotes
        Justify=Justify.strip().upper()

        if Justify=="LEFT":
            Justify = " (justify left) "
        elif Justify == "RIGHT":
            Justify = " (justify right) "
        # Kicad default is center - no justify statement is included
        elif (Justify=="CENTER") or (Justify=="CENTRE"):
            Justify = ""
        else:
            self.Warning("Unsupported text justification ["+Justify+"] using Centered.")
            Justify="" # default is centered)

        Angle=self.transformAngle(Angle)

        template = template.replace("%JUSTIFY%", Justify)
        template = template.replace("%ANGLE%", self.strFloat(Angle))
        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%SIZE%", self.strFloat(Size))
        template = template.replace("%THICKNESS%", self.strFloat(Thickness))
        template = template.replace("%LAYER%", Layer)
        template = template.replace("%TEXT%", Text)

        return template


    # graphics_circle,X,Y,Radius,Width,Layer
    # create a graphics circle at X,Y of given radius
    #
    def graphic_circle(self,params):

        template = self.validateTemplate("GRCIRCLE", "gr_circle")
        if template is None: return None

        # KiCad requires both X1/Y1 and X2/Y2
        Xpos1, Ypos1, Radius, Width, Layer = params.split(",")

        Xpos1,Ypos1=self.resolveCoords(Xpos1,Ypos1)
        Radius=self.evalNumericParam(Radius)
        Width=self.evalNumericParam(Width)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos1,Ypos1,Radius,Width,Layer):
            self.cannotAdd("GRAPHIC CIRCLE")
            return None

        Xpos2 = Xpos1 + Radius
        Ypos2 = Ypos1

        template = template.replace("%XPOS1%", self.strFloat(Xpos1))
        template = template.replace("%YPOS1%", self.strFloat(Ypos1))
        template = template.replace("%XPOS2%", self.strFloat(Xpos2))
        template = template.replace("%YPOS2%", self.strFloat(Ypos2))
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%LAYER%", Layer)

        return template

    # graphics_line,Xpos1, Ypos1, Xpos2, Ypos2, Width, Layer

    def graphic_line(self,params):

        Xpos1, Ypos1, Xpos2, Ypos2, Width,Layer = params.split(",")

        Xpos1, Ypos1 = self.resolveCoords(Xpos1, Ypos1)
        Xpos2, Ypos2 = self.resolveCoords(Xpos2, Ypos2)
        Width=self.evalNumericParam(Width)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos1,Ypos1,Xpos2,Ypos2,Width,Layer):
            self.cannotAdd("GRAPHIC LINE")
            return None

        return self.graphic_line_helper(Xpos1,Ypos1,Xpos2,Ypos2,Width,Layer)

    # graphic line helpercalled from several places
    # assumes sanitised parameters

    def graphic_line_helper(self,X1,Y1,X2,Y2,Width,Layer):
        assert type(X1) is float, "graphic_liner_helper expected float for X1."
        assert type(Y1) is float, "graphic_liner_helper expected float for Y1."
        assert type(X2) is float, "graphic_liner_helper expected float for X2."
        assert type(Y2) is float, "graphic_liner_helper expected float for Y2."
        assert type(Width) is float, "graphic_liner_helper expected float for width."
        assert type(Layer) is str, "graphic_liner_helper expected a string for Layer."
        #
        template = self.validateTemplate("GRLINE", "gr_line")
        if template is None: return None

        template = template.replace("%XPOS1%", self.strFloat(X1))
        template = template.replace("%YPOS1%", self.strFloat(Y1))
        template = template.replace("%XPOS2%", self.strFloat(X2))
        template = template.replace("%YPOS2%", self.strFloat(Y2))
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%LAYER%", Layer)

        return template

    # graphic_grid
    # uses graphic_line_helper and graphic_rect_helper
    def graphic_grid(self, params):
        Xpos, Ypos, Width, Height, Hgaps, Vgaps, BorderWidth, LineWidth, Layer = params.split(",")

        Xpos, Ypos = self.resolveCoords(Xpos, Ypos)
        Width = self.evalNumericParam(Width)
        Height =self.evalNumericParam(Height)
        Hgaps = int(self.evalNumericParam(Hgaps))
        Vgaps = int(self.evalNumericParam(Vgaps))
        BorderWidth = self.evalNumericParam(BorderWidth)
        LineWidth = self.evalNumericParam(LineWidth)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos, Ypos, Width, Height, Hgaps, Vgaps, BorderWidth, LineWidth, Layer):
            self.cannotAdd("GRAPHIC GRID")
            return None

        # draw the border first

        result = self.graphic_rect_helper(Xpos, Ypos, self.directionX*Width, self.directionY*Height, BorderWidth, Layer)

        # grid is drawn INSIDE the border to prevent the
        # border bloating if the gridlines are very thick

        hGapSize = Width / Hgaps
        vGapSize = Height / Vgaps

        # if lines are thick enough they will fill the rectangle
        # so no point drawing over it in both directions

        drawVertical, drawHorizontal = True, True

        if LineWidth >= 2 * hGapSize: drawVertical = False
        if LineWidth >= 2 * vGapSize: drawHorizontal = False

        if not drawVertical and not drawHorizontal:
            # it doesn't matter which if the result is a filled rectangle
            drawVertical = True

        # now the vertical grid lines
        if drawVertical:
            for x in range(Hgaps - 1):
                X = Xpos + self.directionX*hGapSize * (x + 1)
                result = result + "\n" + self.graphic_line_helper(X, Ypos, X, Ypos + self.directionY*Height, LineWidth, Layer)
        if drawHorizontal:
            # now the horizontal lines
            for y in range(Vgaps - 1):
                Y = Ypos + self.directionY*vGapSize * (y + 1)
                result = result + "\n" + self.graphic_line_helper(Xpos, Y, Xpos + self.directionX*Width, Y, LineWidth, Layer)
        return result

    ###############################################################
    # Zones and Keepouts
    #
    # params: shape,<shape params>
    #
    # used to route calls

    def zone(self,id,params):

        self.ZoneTemplate=id.strip().upper()

        # zone_poly is called by each alternative
        # and checks the template exists

        Shape,Remainder=params.split(",",1)
        Shape=Shape.strip().upper()

        if   Shape=="RECT":         return self.zone_rect(Remainder)
        elif Shape=="POLY":         return self.zone_poly(Remainder)
        elif Shape=="CIRCLE":       return self.zone_circle(Remainder)
        elif Shape=="CROSS":        return self.zone_cross(Remainder)
        elif Shape=="PIE":          return self.zone_pie(Remainder)
        elif Shape=="ROUNDEDRECT":  return self.zone_roundedrect(Remainder)
        elif Shape=="DONUT":        return self.zone_donut(Remainder)
        elif Shape=="HOLLOWRECT":   return self.zone_hollow_rect_centred(Remainder)
        self.Warning("Unknown zone/keepout shape '"+Shape+"'. Zone/keepout ignored.")
        return None

    #####################################
    #
    # zone helpers
    #
    # all use zone_poly which is responsible for adjusting XY offsets
    #
    ######################################

    def zone_rect(self,params):
        X, Y, Width, Height, Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, FillArcSegment, ThermalGap,FillThermalBridge=params.split(",")

        # build a  list of co-ords for corners and pass to zone_poly

        X, Y = self.resolveCoords(X, Y)
        Width=self.evalNumericParam(Width)
        Height=self.evalNumericParam(Height)

        if self.anyIsNone(X,Y,Width,Height):
            self.cannotAdd("ZONE RECT")
            return None

        # compensate for axis direction
        Width=self.directionX*Width
        Height=self.directionY*Height


        coords=[]
        coords.append((X,Y))
        coords.append((X, Y+Height))
        coords.append((X+Width, Y+Height))
        coords.append((X+Width, Y))

        return self.zone_poly_helper(Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, FillArcSegment,ThermalGap, FillThermalBridge,coords)


    def zone_roundedrect(self,params):
        X,Y,Width,Height,Radius,Smooth,Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, FillArcSegment,ThermalGap, FillThermalBridge=params.split(",")

        # build a  list of co-ords for corners and pass to zone_poly

        x, y = self.resolveCoords(X, Y)
        w=self.evalNumericParam(Width)
        h=self.evalNumericParam(Height)
        r=self.evalNumericParam(Radius)
        Smooth=int(self.evalNumericParam(Smooth))

        # remaining params dealt with by zone_poly_helper
        if self.anyIsNone(x,y,w,h,r,Smooth):
            self.cannotAdd("ZONE ROUNDEDRECT")
            return None

        w=self.directionX*w
        h=self.directionY*h

        # for zones we need a poly description
        # we are working anti-clockwise and we MUST follow around the shape

        coords=[]
        coords.append((x + self.directionX*r, y))
        coords.append(( x + w - self.directionX*r, y))

        # adding new coord lists to the growing list is easy
        # corners are all 90 degrees we only need the start

        # bottom right corner
        coords=coords+self.zone_rounded_rect_helper(x+w-self.directionX*r,y+self.directionY*r,r,270,Smooth)

        # right hand side
        coords.append((x+w, y+self.directionY*r))
        coords.append((x+w, y+h-self.directionY*r))

        # top right corner from 0 to 90 degrees
        coords=coords+self.zone_rounded_rect_helper(x+w-self.directionX*r,y+h-self.directionY*r,r,0,Smooth)

        # top side
        coords.append((x + w - self.directionX*r, y + h))
        coords.append((x + self.directionX*r, y + h))

        # top left corner from 90 to 180 degrees
        coords = coords + self.zone_rounded_rect_helper(x + self.directionX*r, y + h - self.directionY*r, r, 90, Smooth)

        # left side top to bottom
        X1, Y1, X2, Y2 = x, y + h - r, x, y + r
        coords.append((x, y + h - self.directionY*r))
        coords.append((x, y + self.directionY*r))

        # bottom left corner from 180 to 270 degrees
        coords = coords + self.zone_rounded_rect_helper(x + self.directionX*r, y + self.directionY*r, r, 180,Smooth)

        return self.zone_poly_helper(Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, FillArcSegment,ThermalGap, FillThermalBridge, coords)

    # returns a coordinate list
    def off_zone_rounded_rect_helper(self,cx,cy,r,stepAngle,startAngle,Smooth):
        coords=[]
        for s in range(Smooth):
            angle = startAngle + s * stepAngle # anti-clockwise
            x, y = self.getCircleXY(cx, cy, r, angle)
            coords.append((x, y))
        return coords

    # returns a coordinate list
    def zone_rounded_rect_helper(self,cx,cy,r,startAngle,Smooth):
        coords=[]
        stepAngle=90.0/Smooth
        for s in range(Smooth):
            angle = startAngle + s * stepAngle # anti-clockwise
            #x, y = self.getCircleXY(cx, cy, r, angle)
            x,y=self.getCircleXY(0.0,0.0,r,angle)
            x=cx+self.directionX*x
            y=cy+self.directionY*y
            coords.append((x, y))
        return coords

    # Kicad draws clockwise which means its angles are 360-normal angles
    # start and end also need swapping
    def kicadCorrect(self,startAngle,stopAngle):
        # swap start and end
        s = startAngle
        startAngle = stopAngle
        stopAngle = s
        #
        stopAngle = 360 - stopAngle
        startAngle = 360 - startAngle

        # make sure pies are draw properly
        if stopAngle < startAngle: stopAngle = stopAngle + 360

        return startAngle,stopAngle



    def zone_donut(self,params):
        # circular donut - possibly with a cutout

        cx,cy,innerRadius,outerRadius,startAngle,stopAngle,Smooth,Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments,ThermalGap, ThermalBridgeWidths=params.split(",")

        #cx,cy=self.evalNumericParam(cx),self.evalNumericParam(cy)
        cx, cy = self.resolveCoords(cx, cy)
        innerR,outerR=self.evalNumericParam(innerRadius),self.evalNumericParam(outerRadius)
        startAngle,stopAngle=self.evalNumericParam(startAngle),self.evalNumericParam(stopAngle)

        Smooth=int(self.evalNumericParam(Smooth))

        if self.anyIsNone(cx,cy,innerR,outerR,startAngle,stopAngle,Smooth):
            self.cannotAdd("ZONE DONUT")
            return None

        # zone_poly_helper resolves the other params

        startAngle,stopAngle=self.kicadCorrect(startAngle,stopAngle)


        stepAngle = abs(stopAngle - startAngle) / Smooth

        # build the coordinate list - must follow in correct order
        coords=[]

        # remember this so we can close the poly at the end to stop leaking
        startX, startY = self.getCircleXY(cx, cy, innerR, startAngle)

        #draw the inner circle anti-clockwise
        angle=startAngle
        stepAngle=(stopAngle-startAngle)/Smooth
        for step in range(Smooth+1):
            X,Y=self.getCircleXY(cx,cy,innerR,angle)
            coords.append((X,Y))
            angle = angle + stepAngle

        # add the outer circle
        # must be plotted in reverse direction to prevent folding
        angle=stopAngle
        for step in range(Smooth+1):
            X,Y=self.getCircleXY(cx, cy, outerR, angle)
            coords.append((X,Y))
            angle=angle-stepAngle

        coords.append((startX, startY)) # close the shape


        return self.zone_poly_helper(Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments,ThermalGap, ThermalBridgeWidths, coords)

    def zone_cross(self,params):
        X, Y, Width, Height, Thickness,Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths = params.split(",")

        # for a cross whose bars are Thickness thick LOL

        x,y=self.evalNumericParam(X),self.evalNumericParam(Y)
        x,y = self.resolveCoords(X, Y)
        w,h=self.evalNumericParam(Width),self.evalNumericParam(Height)
        t=self.evalNumericParam(Thickness)

        if self.anyIsNone( x,y,w,h,t):
            self.cannotAdd("ZONE CROSS")
            return None

        # zone_poly_helper resolves other parameters

        if (t>=w) or (t>=h):
            self.Warning("Cross thickness must be less than width and height of the container rect. Ignored.")
            return None

        w=self.directionX*w
        h=self.directionY*h

        hgap=(w-t)/2
        vgap=(h-t)/2

        # build the coordinate list
        coords=[]
        coords.append((x+hgap,y+vgap))
        coords.append((x+hgap,y))
        coords.append((x+hgap+t,y))
        coords.append((x+hgap+t,y+vgap))
        coords.append((x+w,y+vgap))
        coords.append((x+w,y+vgap+t))
        coords.append((x+hgap+t,y+vgap+t))
        coords.append((x+hgap+t,y+h))
        coords.append((x+hgap,y+h))
        coords.append((x+hgap,y+vgap+t))
        coords.append((x, y + vgap + t))
        coords.append((x, y + vgap))
        # close the shape to prevent leaks
        coords.append((x + hgap, y + vgap))

        return self.zone_poly_helper(Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, ArcSegments,
                                     ThermalGap, ThermalBridgeWidths, coords)


    def zone_hollow_rect_centred(self,params):
        X, Y, outerW,outerH,innerW,innerH,Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths = params.split(",")

        X, Y = self.resolveCoords(X, Y)
        outerW,outerH=self.evalNumericParam(outerW),self.evalNumericParam(outerH)
        innerW,innerH=self.evalNumericParam(innerW),self.evalNumericParam(innerH)

        if self.anyIsNone( X, Y, outerW,outerH,innerW,innerH):
            self.cannotAdd("ZONE HOLLOWRECT")
            return None

        startX,startY=X,Y # for closing the shape

        outerW=self.directionX*outerW
        innerW=self.directionX*innerW
        outerH=self.directionY*outerH
        innerH=self.directionY*innerH

        coords=[]
         # outer coords
        X1,Y1,X2,Y2,X3,Y3,X4,Y4=X,Y,X+outerW,Y,X+outerW,Y+outerH,X,Y+outerH
        coords.append((X1,Y1))
        coords.append((X2,Y2))
        coords.append((X3,Y3))
        coords.append((X4,Y4))
        coords.append((X,Y)) # close the outer rect

        #inner coords
        X=X+(outerW-innerW)/2
        Y=Y+(outerH-innerH)/2
        X1, Y1, X2, Y2, X3, Y3, X4, Y4=X,Y,X+innerW,Y,X+innerW,Y+innerH,X,Y+innerH
        coords.append((X1,Y1))
        coords.append((X2,Y2))
        coords.append((X3,Y3))
        coords.append((X4,Y4))
        coords.append((X,Y))             # close the inner rect
        coords.append((startX, startY))  # link back to outer rect

        return self.zone_poly_helper(Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths,coords)


    def zone_circle(self,params):
        X,Y,Radius,Smooth,Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths=params.split(",")

        # build a  list of co-ords for corners and pass to zone_poly_helper (checks Net and other params)
        X, Y = self.resolveCoords(X, Y)
        Radius=self.evalNumericParam(Radius)
        Smooth=int(self.evalNumericParam(Smooth))
        stepAngle=360/Smooth

        if self.anyIsNone(X,Y,Radius,Smooth):
            self.cannotAdd("ZONE CIRCLE")
            return None

        coordList=[]
        for step in range(Smooth):
            angle=step*stepAngle
            x,y=self.getCircleXY(X, Y, Radius, angle)
            coordList.append((x,y))

        return self.zone_poly_helper(Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths,coordList)

    # zone_pie

    def zone_pie(self,params):
        X,Y,Radius,startAngle,stopAngle,Smooth, Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths=params.split(",")

        # build a  list of co-ords for corners and pass to zone_poly
        Cx=self.evalNumericParam(X)
        Cy=self.evalNumericParam(Y)
        Cx, Cy = self.resolveCoords(X, Y)
        startAngle=self.evalNumericParam(startAngle)
        stopAngle=self.evalNumericParam(stopAngle)
        Smooth=int(self.evalNumericParam(Smooth))
        Radius=self.evalNumericParam(Radius)

        # helper resolves the remainder
        if self.anyIsNone(Cx,Cy,startAngle,stopAngle,Smooth):
            self.cannotAdd("ZONE PIE")
            return None

        # correct for kicad's way of doing circles
        startAngle,stopAngle=self.kicadCorrect(startAngle,stopAngle)


        stepAngle=abs(stopAngle-startAngle)/Smooth

        # pies begin and go back to circle centre!
        # zone_poly_helper adjusts for transformations
        coords=[]
        coords.append((Cx,Cy))   # pies start at the middle
        angle=startAngle
        for s in range(Smooth):
            X,Y=self.getCircleXY(Cx,Cy,Radius,angle)
            coords.append((X,Y))
            angle=angle+stepAngle

        return self.zone_poly_helper(Net, NetName, Layer, Hatch, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidths,coords)

    # zone_poly
    # checks params, bulds an XY point list and hands off to zone_poly_helper

    def zone_poly(self,params):

        # there can be a variable number of XY coords
        Net, NetName, Layer, HatchType, HatchEdge, Clearance, MinThickness, ArcSegments, ThermalGap,ThermalBridgeWidth,Coords = params.split(",")

        # zone_poly_helper resolves all params, coords are tansformed here

        coordList=Coords.split(",")

        # process the XY pairs
        if len(coordList)%2!=0:
            self.Warning("Zone has an odd number of co-ordinates. Zone ignored. Length="+str(len(coordList)))
            return None

        # get the coords and build a pts list
        fmtString="(xy "+self.fmtFloat+ " "+self.fmtFloat+")"

        XYpoints=[]
        for p in range( 0,len(coordList)-1,2):
            X, Y = self.resolveCoords(coordList[p], coordList[p+1])
            XYpoints.append((X,Y))

        return self.zone_poly_helper(Net,NetName,Layer,HatchType,HatchEdge,Clearance,MinThickness,ArcSegments,ThermalGap,ThermalBridgeWidth,XYpoints)



    #
    # zone_poly_helper
    #
    # used by a number of zone shapes
    # parameters

    def zone_poly_helper(self,Net,NetName,Layer,HatchType,HatchEdge,Clearance,MinThickness,ArcSegments,ThermalGap,ThermalBridgeWidth,CoordList):

        # could be ZONE or KEEPOUT being used as the template
        template = self.getTemplate(self.zoneTemplate)
        if template is None: return None

        # these could be variables so we need to evaluate them
        # we do it here to save writing it all out in every
        # zone_xxxx method
        Net=int(self.evalNumericParam(Net))
        NetName=self.evalStringParam(NetName)
        Layer=self.evalStringParam(Layer)
        HatchType=self.evalStringParam(HatchType)
        HatchEdge=self.evalNumericParam(HatchEdge)
        Clearance=self.evalNumericParam(Clearance)
        MinThickness=self.evalNumericParam(MinThickness)
        ArcSegments=int(self.evalNumericParam(ArcSegments))
        ThermalGap=self.evalNumericParam(ThermalGap)
        ThermalBridgeWidth=self.evalNumericParam(ThermalBridgeWidth)


        if self.anyIsNone(Net,NetName,Layer,HatchType,HatchEdge,Clearance,MinThickness,ArcSegments,ThermalGap,ThermalBridgeWidth):
            self.cannotAdd("ZONE")
            return None

        if ArcSegments!=16 and ArcSegments!=32:
            self.Warning("Zone ArcSegments must be 16 or 32 - using 16")
            ArcSegments=16

        template = template.replace("%NET%", str(Net))
        template = template.replace("%NETNAME%", NetName)
        template = template.replace("%LAYER%", Layer)
        template = template.replace("%HATCHTYPE%", HatchType)
        template = template.replace("%HATCHEDGE%", self.strFloat(HatchEdge))
        template = template.replace("%CLEARANCE%", self.strFloat(Clearance))
        template = template.replace("%MINTHICKNESS%", self.strFloat(MinThickness))
        template = template.replace("%ARCSEGMENTS%", self.strInt(ArcSegments))
        template = template.replace("%THERMALGAP%", self.strFloat(ThermalGap))
        template = template.replace("%THERMALBRIDGEWIDTH%", self.strFloat(ThermalBridgeWidth))

        # build the XY points in a string which is a series of coords like this: (xy 1.25 5.76)
        # the coordinate have not yet been transformed so we have to do it
        fmtCoords="(xy "+self.fmtFloat+" "+self.fmtFloat+") "
        XYpoints=""
        Counter=0
        for (x,y) in CoordList:
            XYpoints=XYpoints+fmtCoords.format(x,y)
            Counter=(Counter+1)%5
            if Counter==0:
                XYpoints=XYpoints+"\n"

        template = template.replace("%XYPOINTS%", XYpoints)

        return template


    ##################################################################
    # segment,shape,<shape-params>
    #
    # router to helpers
    # note that segment_line is called to create arc segments
    # segment_line is responsible for adjusting XY offsets
    #
    def segment(self,id,params):

        # all segment_xxx use the same template

        template = self.validateTemplate("SEGMENT", "segment")
        if template is None: return None

        Shape,Remainder=params.split(",",1)
        Shape=Shape.strip().upper()

        if Shape=="LINE":       return self.segment_line(Remainder,template)
        elif Shape=="CIRCLE":   return self.segment_circle(Remainder,template)
        elif Shape=="ARC":      return self.segment_arc(Remainder,template)
        elif Shape=="RECT":     return self.segment_rect(Remainder,template)
        elif Shape=="GRID":     return self.segment_grid(Remainder,template)
        self.Warning("Unsupported segment shape. "+Shape)
        return None

    ################################################
    #
    # segment helpers
    #
    ################################################

    def segment_grid(self,params,template):
        Xpos,Ypos,Width,Height,Hgaps,Vgaps,BorderWidth,LineWidth,Layer,Net=params.split(",")

        Xpos,Ypos=self.resolveCoords(Xpos,Ypos) # transforms Xpos,Ypos

        Width=self.evalNumericParam(Width)
        Height=self.evalNumericParam(Height)
        Hgaps=int(self.evalNumericParam(Hgaps))
        Vgaps=int(self.evalNumericParam(Vgaps))
        BorderWidth=self.evalNumericParam(BorderWidth)
        LineWidth=self.evalNumericParam(LineWidth)
        Net=int(self.evalNumericParam(Net))
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos,Ypos,Width,Height,Hgaps,Vgaps,BorderWidth,LineWidth,Layer,Net):
            self.cannotAdd("SEGMENT ARC")
            return None

        # adjust width and height directions

        Width=self.directionX*Width
        Height=self.directionY*Height

        # draw the border first
        # segment_rect_helper doesn't do any X/Y translations

        result=self.segment_rect_helper(Xpos,Ypos,Width,Height,BorderWidth,Layer,Net,template)

        # grid is drawn INSIDE the border to prevent the
        # border bloating if the gridlines are very thick
        drawVertical=True
        drawHorizontal=True

        hGapSize=Width/Hgaps
        vGapSize=Height/Vgaps

        # if lines are thick enough they will fill the rectangle
        # so no point drawing over it in both directions

        drawVert,drawHoriz=True,True

        if LineWidth>=abs(2*hGapSize): drawVert=False
        if LineWidth>=abs(2*vGapSize): drawHoriz=False

        if not drawVert and not drawHoriz:
            drawVert=True

        # now the vertical grid lines
        if drawVert:
            hGapSize=Width/Hgaps
            for x in range(Hgaps-1):
                X=Xpos+hGapSize*(x+1)
                result=result+"\n"+self.segment_line_helper(X,Ypos,X,Ypos+Height,LineWidth,Layer,Net,template)
        if drawHoriz:
            # now the horizontal lines
            vGapSize=Height/Vgaps
            for y in range(Vgaps-1):
                Y=Ypos+vGapSize*(y+1)
                result=result+"\n"+self.segment_line_helper(Xpos,Y,Xpos+Width,Y,LineWidth,Layer,Net,template)
        return result

    # segment_circle
    # draw a circle composed of track segments
    # this will be editable in pcbnew

    def segment_circle(self,params,template):

        Xpos,Ypos,Radius,NumSegments,Width,Layer,Net=params.split(",")

        NumSegments=int(self.evalNumericParam(NumSegments))
        Radius=self.evalNumericParam(Radius)
        cx,cy=self.resolveCoords(Xpos,Ypos)
        Width=self.evalNumericParam(Width)

        if self.anyIsNone(cx,cy,Radius,NumSegments,Width):
            self.cannotAdd("SEGMENT CIRCLE")
            return None

        # segments are straight tracks between X0,Y0 and X1,Y1
        # we create a circle using very short segments
        # or a spiders web using fewer segments

        X0=cx+Radius
        Y0=cy
        stepAngle=360/NumSegments # convert to radians
        Angle=stepAngle
        result=""

        for seg in range(NumSegments):
            X1,Y1=self.getCircleXY(cx,cy,Radius,Angle)
            result=result+"\n"+self.segment_line_helper(X0, Y0, X1, Y1, Width, Layer, Net,template)
            Angle=Angle+stepAngle
            X0=X1
            Y0=Y1

        return result


    # segment_arc
    #
    # draw an arc composed of segments

    def segment_arc(self, params,template):

        # XY Parameters describe two lines (X1,Y1->X2,Y2) and (X3,Y3->X4,Y4)
        # these are used in order to determine the centre and radius of an arc
        # an arc will be drawn between X2,Y2 and X3,Y3

        CX,CY,Radius,startAngle,stopAngle,NumSegments,Width,Layer,Net=params.split(",")

        CX,CY=self.resolveCoords(CX,CY)
        Radius=self.evalNumericParam(Radius)
        startAngle=self.evalNumericParam(startAngle)
        stopAngle=self.evalNumericParam(stopAngle)
        Width=self.evalNumericParam(Width)
        Net=int(self.evalNumericParam(Net))

        if self.anyIsNone(CX,CY,Radius,startAngle,stopAngle,NumSegments,Width,Layer,Net):
            self.cannotAdd("SEGMENT ARC")
            return None

        # kicad draws clockwise
        startAngle,stopAngle=self.kicadCorrect(startAngle,stopAngle)

        # get co-ords of the start and end points. Kicad uses centre and first point plus angle
        # and draws clockwise so we need to calc start point using stopAngle

        Xstart, Ystart = self.getCircleXY(CX, CY, Radius, startAngle)
        Xend, Yend = self.getCircleXY(CX, CY, Radius, stopAngle)


        NumSegments=int(self.evalNumericParam(NumSegments))
        stepAngle=abs(stopAngle-startAngle)/NumSegments

        X0,Y0=self.getCircleXY(CX,CY,Radius,startAngle)
        Angle=startAngle+stepAngle
        result=""

        for seg in range(NumSegments):
            X1,Y1 = self.getCircleXY(CX,CY, Radius,Angle)
            result = result + "\n"+self.segment_line_helper(X0, Y0, X1, Y1, Width, Layer, Net,template)
            Angle = Angle + stepAngle
            X0 = X1
            Y0 = Y1

        return result

    # segment_line_helper
    # can be called from numerous places
    # expects parameters to be sanitised (e.g. dimensions as float)
    # and transformed

    def segment_line_helper(self,X0,Y0,X1,Y1,Width,Layer,Net,template):

        if self.anyIsNone(X0,Y0,X1,Y1,Width,Layer,Net):
            self.cannotAdd("SEGMENT")
            # do not return None as this is used by a number of callers
            # which may be concatenating values
            return ""

        template = template.replace("%XPOS1%", self.strFloat(X0))
        template = template.replace("%YPOS1%", self.strFloat(Y0))
        template = template.replace("%XPOS2%", self.strFloat(X1))
        template = template.replace("%YPOS2%", self.strFloat(Y1))
        template = template.replace("%LAYER%", Layer)
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%NET%", self.strInt(Net))

        return template

        # segment_line

    def segment_line(self, params, template):

        X0, Y0, X1, Y1, Width, Layer, Net = params.split(",")

        X0,Y0=self.resolveCoords(X0,Y0)
        X1,Y1=self.resolveCoords(X1,Y1)

        Width = self.evalNumericParam(Width)
        Net = self.evalNumericParam(Net)
        Layer = self.evalStringParam(Layer)

        if self.anyIsNone(X0, Y0, X1, Y1, Width, Layer, Net):
            self.cannotAdd("SEGMENT LINE")
            return None

        # no line to draw?
        if (X0 == X1) and (Y0 == Y1): return None

        # cannot use segment_line helper because it will transform
        # saveXYVar values - which we don't want
        #
        template = template.replace("%XPOS1%", self.strFloat(X0))
        template = template.replace("%YPOS1%", self.strFloat(Y0))
        template = template.replace("%XPOS2%", self.strFloat(X1))
        template = template.replace("%YPOS2%", self.strFloat(Y1))

        template = template.replace("%LAYER%", Layer)
        template = template.replace("%WIDTH%", self.strFloat(Width))
        template = template.replace("%NET%", self.strInt(Net))

        return template

    # segment_rect_helper
    # used by GRID,CIRCLE,ARC,LINE and RECT
    def segment_rect_helper(self,X, Y, Width,Height,LineWidth,Layer,Net,template):
        # draw a box outline

        result = self.segment_line_helper(X, Y, X + Width, Y, LineWidth, Layer, Net, template)
        result = result + "\n" + self.segment_line_helper(X, Y+Height, X + Width, Y + Height, LineWidth, Layer, Net,
                                                          template)
        result = result + "\n" + self.segment_line_helper(X + Width, Y, X + Width, Y + Height, LineWidth, Layer, Net,
                                                          template)

        result = result + "\n" + self.segment_line_helper(X, Y + Height, X, Y, LineWidth, Layer, Net, template)

        return result

    # segment_rect
    #
    # creates a rectangular segment
    #
    def segment_rect(self,params,template):
        X, Y, Width,Height,LineWidth,Layer,Net= params.split(",")

        X,Y=self.resolveCoords(X,Y)
        Width=self.evalNumericParam(Width)
        Height=self.evalNumericParam(Height)

        if self.anyIsNone(X,Y,Width,Height):
            self.cannotAdd("SEGMENT RECT")
            return None

        return self.segment_rect_helper(X, Y, Width,Height,LineWidth,Layer,Net,template)

    ##################################################################################################
    #
    # components - this handles ALL user components
    #
    ##################################################################################################

    # XXXXX,Ref, Angle, Xpos, Ypos, Layer
    #
    # all user templates are handled here
    # XXXXX is the user defined Id
    #
    # Use this to define components you want placed on the pcb
    #
    # The components ALL have the same parameters, if not we'll have to extend this here

    def component(self, id, params):

        # components use module templates which all begin with (module
        template=self.validateTemplate(id,"module")
        if template is None: return None
        
        Ref, Angle, Xpos, Ypos, Layer = params.split(",")

        Ref=self.getRef(id.strip(), Ref)
        Xpos,Ypos=self.resolveCoords(Xpos,Ypos)
        Angle=self.evalNumericParam(Angle)
        Layer=self.evalStringParam(Layer)

        if self.anyIsNone(Xpos,Ypos,Angle,Layer):
            self.cannotAdd("MODULE "+id)
            return None

        Angle = self.transformAngle(Angle)

        template = template.replace("%REF%", Ref)
        template = template.replace("%XPOS%", self.strFloat(Xpos))
        template = template.replace("%YPOS%", self.strFloat(Ypos))
        template = template.replace("%ANGLE%", self.strFloat(Angle))
        template = template.replace("%LAYER%", Layer)

        return template
