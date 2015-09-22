ReferenceMotion[xSystem_, xReferenceValues_: {}] :=
	Module[{xOut, xKeys, xVariables},
		xKeys = Part[#,1]& /@ Union @ (Flatten @ {
			(Select[Keys @ xSystem, Part[#, 0] === "q"&]),
			(Select[Keys @ xSystem[#], Part[#, 0] === "q"&])& /@ xSystem["Subsystems Labels"]
			});
		xVariables = Union @@ (Function[xKey, (Union @@ ({
			xSystem["q"[xKey]],
			Union @@ (Function[xSub, xSystem[xSub]["q"[xKey]]] /@ xSystem["Subsystems Labels"])
			} //. Missing[xX__]-> {}
			))] /@ xKeys);
		xOut = Association @ (Flatten @ Outer[(#1-> #2)&, (Superscript[#, \[EmptySmallCircle]])& /@ 
			(xVariables /. SymbolReplacements), {0}]);
		AssociateTo[xOut, (Superscript[First[#], \[EmptySmallCircle]] -> Last[#])& /@ 
			(xReferenceValues /. SymbolReplacements)];
		xOut // Normal
		]