LinearizeSystem[xSystem_, xLinSubsystemsModels_: Association[], xExtraReferenceMotion_: {}, xExtraRules_: {}] :=
	Module[{xIn, xOut, xReferenceMotion, xKeys, xA, xTimer},
		xTimer = AbsoluteTime[];
		xIn = xOut = MoSs @ xSystem;
		(xOut[#] = xLinSubsystemsModels[#])& /@ 
			Intersection[xOut["Subsystems Labels"], Keys[xLinSubsystemsModels]];	
		(xOut[#] = LinearizeSystem[xIn[#], Association[], xExtraReferenceMotion, xExtraRules])& /@
			Complement[xOut["Subsystems Labels"], Keys[xLinSubsystemsModels]];	
		xOut["Reference Motion"] = Union @@ {
			xExtraReferenceMotion,
			(xIn["Reference Motion"] //. Missing[xX__] -> {}),
			Union @@ ((xLinSubsystemsModels[#]["Reference Motion"] //. Missing[xX__] -> {})& /@ 
				Intersection[xOut["Subsystems Labels"], Keys[xLinSubsystemsModels]])
			};
		xReferenceMotion = ReferenceMotion[xIn, xOut["Reference Motion"]];
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:ReferenceMotion:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01],{5,2}],
				xOut["System Label"]]]
			];

		xKeys = First /@ (Select[Keys @ xIn, Part[#,0] === "q#"&]);
		xOut["q#:Def:Order"] = If[KeyExistsQ[xIn,"q#:Def:Order"], 
			xIn["q#:Def:Order"], 
			Max @ ToExpression @ Flatten @ (StringSplit[#, {":", "|"}]& /@  xKeys)
			];
		(xOut["q#"[ToString @ #]]= D[
			xOut["q#"[ToString @  xOut["q#:Def:Order"]]],
			{t,(#-xOut["q#:Def:Order"])}
			])& /@  Complement[Range[0, Max[2, xOut["q:Order"]]], Range[0, xOut["q#:Def:Order"]]];
		xKeys =	Union[ReplaceRepeated[#, {{xA_, xB_} :> (ToString[xA] <> "|" <> ToString[xB])}]& @
			(Select[Flatten[#,1],(Part[#,1]>Part[#,2])&]& @(Outer[List,#,#]))
			]& @ Range[0, Max[2, xOut["q:Order"]]];
		(xOut["q#"[#]]=	D[
			xOut["q#"[Part[#,2]]],
			{t,((ToExpression @ Part[#,1]) - (ToExpression @ Part[#,2]))}
			]& @ StringSplit[#, {":", "|"}]
		)& /@  xKeys;

		xKeys = Part[#, 1]& /@ Union @ (Select[Keys @ xIn, Part[#, 0] === "*q"&]);
		Module[{xRules},
			(xOut["*q"[#]] = RedundantElim @ (Linearize[xIn["*q"[#]] (* //. xIn["_c"] *), 
				xReferenceMotion] //. xExtraRules))& /@ xKeys;
			xRules = (((#-> 0)& /@ Expand @ RedundantElim @ ((Union @@ (xOut["*q"[#]]& /@ xKeys)) 
						//. {xX_[t]-> 0} //. xExtraRules)) /. {({} -> 0) -> {}});
			(xOut["*q"[#]] = RedundantElim @ ((Expand @ xOut["*q"[#]]) //. xRules //. xExtraRules))& /@ xKeys;
			(xOut["*q"[#]] = {})& /@ Complement[ToString /@ Range[0, Max[2, xOut["q:Order"]]], xKeys];		
			xOut["_c"] = Union @@ (((xOut[#]["_c"])& /@ xOut["Subsystems Labels"]) //. Missing[xX__]-> {});
			xOut["_c"] = Union @@ {
				xOut["_c"],
				Union[#, # /. {(xA_ -> xB_) -> (-xA -> -xB)}]& @ xRules					
				};
			xOut["_c"] = Union @@ {
				xOut["_c"],
				((#-> 0)& /@ (RedundantElim @ (
					(Linearize[xIn["_c"] /. {(xX_ -> xY_) -> (xX - xY)}, xReferenceMotion] 
					//.xExtraRules) //.xOut["_c"]
					)))
				};
			(* (xOut["*q"[#]] = RedundantElim @ (xOut["*q"[#]] //. xOut["_c"] //. xExtraRules))& /@ xKeys; *)	
			];	
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:*q:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}], 
				xOut["System Label"]]]
			];

		xKeys = Part[#,1]& /@ Union @ (Select[Keys @ xIn, Part[#,0] === "_q"&]);
		Module[{xFirst, xLast},
			xFirst = Linearize[(First /@ xIn["_q"[#]]), xReferenceMotion] //. xOut["_c"] //. xExtraRules;
			xLast = Linearize[(Last /@ xIn["_q"[#]]), xReferenceMotion] //. xOut["_c"] //. xExtraRules;
			xOut["_q"[#]] = Select[MapThread[(#1 - (#1 //. {xX_[t]-> 0})) -> (#2 - (#2 //. {xX_[t]-> 0}))&, 
				{xFirst, xLast}, 1], (Not @ (First[#] - Last[#] === 0))&];
			xOut["_c"] = Select[Union @@ {
				xOut["_c"],	xOut["_q"[#]],
				Union[#, # /. {(xA_ -> xB_) -> (-xA -> -xB)}]& @ MapThread[#1 -> #2&, 
					{xFirst, xLast} //. {xX_[t] -> 0}, 1]
				}, (Not @ (First[#] - Last[#] === 0))&];
			]& /@ xKeys;

		Module[{xEquations},
			xEquations = RedundantElim @ (xOut["*q"[#]] //. xOut["_c"]);
			xOut["_q"[#]] = If[Or[xEquations === {}, SetComplement[xIn["q"[#]], xOut["q#"[#]]] === {}], 
				(* xOut["_q"[#]] //. Missing[xX__]-> *) {},
				Function[{xX},
					MapThread[(#1-> #2)&, {
						xX,
						Flatten @ (-LinearSolve @@ Reverse @ CoefficientArrays[xEquations, xX])
						}, 1]
					] @ SetComplement[Intersection[xIn["q"[#]], GetVariables @ xEquations], xOut["q#"[#]]] //.xExtraRules
				];
			xOut["_c"] = Complement[Union @@ {xOut["_c"], xOut["_q"[#]]}, {0 -> 0}];
			]& /@ (ToString /@ Range[0, Max[2, xOut["q:Order"]]]);
		If[xOut["Debug Mode"] === "On", 
			Print[StringForm["``:``:_c:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xKeys = (ToString @ xOut["q:Order"]);
		If[KeyExistsQ[xIn, "B"],
			xOut["B"] = SApply[
				Simplify @ (Linearize[#, xReferenceMotion] //. xOut["_c"] //. xExtraRules)&, 
				xIn["B"]
				];
			If[xOut["Debug Mode"] === "On",
				Print[StringForm["``:``:B:OK",
					NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}], 
					xOut["System Label"]]]
				];
			If[And[KeyExistsQ[xIn, "C"], Complement[xIn["C"]["Column Labels"], xIn["q#"[xKeys]]] === {}],
				xOut["C"] = SApply[
					Simplify @ (Linearize[#, xReferenceMotion] //. xOut["_c"] //. xExtraRules)&, 
					xIn["C"]
					],
				xOut["C"] = LSLinearizedOrthogonalComplement[
					xOut["B"],
					xOut["q#"[xKeys]],
					xOut["_c"]
					]
				];
			If[And[KeyExistsQ[xIn, "S"], 
					Complement[xIn["S"]["Column Labels"], xIn["q#"[xKeys]]] === {}],
				xOut["S"] = SApply[
					Simplify @ (Linearize[#, xReferenceMotion] //. xOut["_c"] //. xExtraRules)&, 
					xIn["S"]
					],
				xA = {};
				If[KeyExistsQ[xOut[#], "S"], AppendTo[xA, xOut[#]["S"]]]& /@ xIn["Subsystems Labels"];
				If[xA === {},
					xOut["S"] = xOut["C"],
					If[Not @ (xOut["q+"[xKeys]] === {}),
						AppendTo[xA, SAssemble[1, xOut["q+"[xKeys]]]]
						];
					xOut["S"] = Linearize @ ((SAssemble @@ xA) ~SDot~ xOut["C"])
					];	
				];
			If[xOut["Debug Mode"] === "On",
				Print[StringForm["``:``:S:OK",
					NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
					xOut["System Label"]]]
				];	
			];

		xA = {};					
		If[Not @ (xOut["q+"[xKeys]] === {}),
			If[KeyExistsQ[xIn, "f"],
				AppendTo[xA, SApply[
					(* Collect[ *)Simplify @ (Linearize[#, xReferenceMotion] //. xOut["_c"] //. xExtraRules)(* ,
						Union @@ (xOut["q"[#]]& /@ (ToString /@ Range[xOut["q:Order"], Max[2, xOut["q:Order"]]])), 
						Simplify] *)&,
					SPart[xIn["f"], xOut["q+"[xKeys]]]
					]],
				AppendTo[xA, SPart[0, xOut["q+"[xKeys]]]]
				]
			];
		If[KeyExistsQ[xOut[#], "*f"],
			AppendTo[xA, SApply[
				(# //. xOut["_c"] //. xExtraRules)&, 
				xOut[#]["*f"]]]
			]& /@ xOut["Subsystems Labels"];
		xOut["*f"] = xOut["f"] = SAssemble @@ (RedundantElim @ xA);

		If[And[KeyExistsQ[xOut, "f"], KeyExistsQ[xOut, "C"]],
			xOut["*f"] = SApply[Linearize, STranspose[xOut["C"]] ~SDot~ xOut["f"]];
			If[Or[xOut["Explicit EOM"] === "Yes", xOut["Explicit Linearized EOM"] === "Yes"],			
				(xOut["_f"] = SReplaceFullSimplify[
					Solve[(# == 0)& /@ Flatten @ (Union @@ {SAssemble[xOut["*f"]]["Matrix"], xOut["*q"[#]]}), 
						xOut["q"[#]]],
					xOut["Replacement Rules"]
					])& @ (ToString @ (Max[2, xOut["q:Order"]]));
				If[xOut["Debug Mode"] === "On",
					Print[StringForm["``:``:_f:OK",
						NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
						xOut["System Label"]]]
					];
				];
			]; 
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:*f:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xOut["*f:q"] = Union @ (GetVariables @ xOut["*f"]);
		xOut["System Parameters"] = Union @@ {
			Union @@ (xOut[#]["System Parameters"]&/@xOut["Subsystems Labels"]),
			RedundantElim @ (Quiet @ GetAllVariables[ Join @@ {
				xOut["*f"]["Matrix"],
				Join @@ (xOut["*q"[#]]&/@(ToString/@Range[0,xOut["q:Order"]]))}] //. xX_[t]-> 0)
			};

		If[xOut["Timer"] === "On",
			Print[StringForm["``:``:OK",
				NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],
				xOut["System Label"]]]
			];
		xOut
		];