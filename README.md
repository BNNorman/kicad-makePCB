# kicad-makePCB
python script to generate kicad_pcb files using a data file containing commands to generate tracks and place components.

Can be used to create a new kicad_pcb file from scratch or add to an exisiting kicad_pcb.

##Features:-
*Does not use pcbnew.py nor does it need pcbnew to be running

*Zones/Keepouts can have the following shapes : Poly, Circle, Cross, Donut (open or closed) , Hollow Rectangle, Pie, rectangle, rectangle with rounded corners

*Tracks can be Arc, Circle, Grid or just Line

*Graphics can be Arc, Circle,Line,Pie,Rectabgle,rounded rectangle and text

*Can use lists of data from a separate datafile to place components or tracks etc

*Components can be placed in rectangular or circular arrays (rings)

*Components can be grouped and manipulated together

*Supports global and local variables with simple arithmetic

*The drawing origin can be moved down from top left to bottom left to be more human friendly
