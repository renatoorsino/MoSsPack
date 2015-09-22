(*- utilities -*)

RootDir = Directory[];
SetDirectory[RootDir <> "/external/MathMatrixPack/"];
<<setup.m
SetDirectory[RootDir];


(*- formalisms -*)

<<MoSsPack/formalisms/NewtonEuler.m


(*- modular -*)

<<MoSsPack/modular/MoSs.m
<<MoSsPack/modular/ReferenceMotion.m
<<MoSsPack/modular/LinearizeSystem.m
<<MoSsPack/modular/ParametersEval.m