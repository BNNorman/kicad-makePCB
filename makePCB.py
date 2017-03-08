# makePcb.py
#
# version 1.0.0 Brian Norman March 2017
#
# This is free software with no warranty whatsoever
# You may modify but you may not sell it as your own work.
#
# Uses a position data file to create a kicad_pcb file
# primarily aimed at PCBs with lots of repeating components
# which can easily be calculated
#
# requires KiCadParser.py version 1.0.0

import os
import sys

print("makePCB.py Vsn 1.0.0")

try:
    from KiCadParser import *

except Exception as e:
    print (e.args)
    print("This program requires the parser helper KiCadParser.py.")
    sys.exit(1)



print("\nEnter the name of the position data file without the .pos part. This will also be used as the name of the kicad_pcb output file.")
prompt="Position data file:-"

if sys.version_info>=(3,0):
    #python 3.x
    PosFileName=input(prompt)
else:
    #python 2.x
    PosFileName=raw_input(prompt)

# input/output files
POS_file=None
POS_line=0  # line number of the POS file being processed
PCB_file=None

def closeFilesAndExit():
    global PCB_file,POS_file
    if PCB_file!=None: PCB_file.close()
    if POS_file!=None: POS_file.close()
    sys.exit(0)

# open the .pos file containing the data

def openPositionData(fname):
    global POS_file

    fname=fname+".pos"
    try:
        POS_file=open(fname)
        POS_line=0
        print("Opened position data file",fname)
    except Exception as e:
        print("Unable to open Position data file ",fname," cannot proceed.\n",e.args)
        closeFilesAndExit()

def createPcbFile(fname):
    global PCB_file

    fname=fname+".kicad_pcb"

    try:
        PCB_file=open(fname,"w")
        print("Created kicad_pcb file ",fname)

    except Exception as e:
        print ("Error creating/overwriting '"+fname+".kicad_pcb'. Cannot proceed.", "\n",e.args)
        closeFilesAndExit()

# open the required files

openPositionData(PosFileName)
createPcbFile(PosFileName)

PCB_file.write("(") # all the kicad_pcb files are enclosed in brackets

Parser=KiCadParser();
exceptionCaught=False

try:

    for line in POS_file:
        POS_line=POS_line+1

        # clean up input
        line=line.strip()

        # ignore comments and blank lines
        # ORDER MATTERS !
        if (line=="") or (line[0]=="#"): continue

        # stop?
        # split(",",1) throws a wobbly
        # but partition is happy
        D=line.partition(",")
        if D[0].upper().strip()=="STOP": break


        # None returns just mean there's nothing to write
        # to the output file
        data=Parser.parse(POS_line,D[0],D[2])
        if data is None: continue

        PCB_file.write("\n"+data)

except Exception as e:

    print("ERROR at data file line",POS_line," error=",e.args)
    exc_type, exc_obj, exc_tb = sys.exc_info()
    fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
    print("CAUSED by file ",fname," at line ", exc_tb.tb_lineno)
    print("TRACEBACK",sys.exc_traceback.tb_lineno)
    exceptionCaught=True

finally:
    PCB_file.write(")")  # all the kicad_pcb file contents are enclosed in brackets
    if exceptionCaught:
        print("Please check for any error messages.")
    else:
        print("Finished normally - please check for any warnings.")

    Parser.getStatus()

    closeFilesAndExit() # exits the process




