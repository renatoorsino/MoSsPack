MoSs[xSystem_, xSubSystems_List:{}]:= 
	Module[{xIn, xOut, xRules, xKeys, xA, xTimer},
		xTimer = AbsoluteTime[];
		xIn = xSystem;
		xOut = If[AssociationQ[xIn], xIn, Association[]];
		Quiet @ (
			xOut["System Label"] = xIn /. {
				xX_List /; Length[xX] >= 1 -> xX[[1]],
				xX_Association -> xX["System Label"]
				};
			xOut["Subsystems Labels"] = xIn /. {
				xX_Association /; KeyExistsQ[xX,"Subsystems Labels"] -> xX["Subsystems Labels"],
				xX_ -> {}
				};
			xOut["Description"] = xIn /. {
				xX_List /; And[Length[xX] >= 2,StringQ[xX[[2]]]] -> xX[[2]],
				xX_Association /; And[KeyExistsQ[xX,"Description"], StringQ[xX["Description"]]] -> xX["Description"],
				xX_ -> ""
				};
			xOut["Naming Rules"] = xIn /. {
				xX_List /; Length[xX] >= 3 -> xX[[3]],
				xX_Association /; KeyExistsQ[xX, "Naming Rules"] -> xX["Naming Rules"],
				xX_ -> {}
				};
			xOut["Replacement Rules"] = xIn /. {
				xX_List /; Length[xX] >= 4 -> xX[[4]],
				xX_Association /; KeyExistsQ[xX, "Replacement Rules"] -> xX["Replacement Rules"],
				xX_ -> {}
				};
			);

		Quiet @ (
			xIn = (xSubSystems[[#]]) /. {
				xX_List /; AssociationQ[xX[[1]]] -> xX[[1]]
				};
			xRules["Naming Rules"] = Join[
				(xSubSystems[[#]]) /. {
				xX_List /; And[Length[xX] >= 2, Or[ListQ[xX[[2]]], AssociationQ[xX[[2]]]]] -> Normal @ (xX[[2]]),
				xX_ -> {}
				},
				xOut["Naming Rules"]
				];
			xRules["Replacement Rules"] = Join[
				(xSubSystems[[#]]) /. {
				xX_List /; And[Length[xX] >=  3,Or[ListQ[xX[[3]]],AssociationQ[xX[[3]]]]] -> Normal @ (xX[[3]]),
				xX_ -> {}
				},
				xOut["Replacement Rules"]
				];
			xIn = SRename[xIn, xRules["Naming Rules"], xRules["Replacement Rules"]];
			xOut["Subsystems Labels"] = Union[xOut["Subsystems Labels"], {xIn["System Label"]}];
			xOut[xIn["System Label"]] = xIn;
			xOut["Replacement Rules"] = Union[xOut["Replacement Rules"], xRules["Replacement Rules"]];
			)& /@ Range @ (Length @ xSubSystems);

		xIn = xOut;
		xOut["q:Order"] = If[KeyExistsQ[xIn, "q:Order"], 
			xIn["q:Order"], 
			Max @ (((xIn[#]["q:Order"])& /@ xIn["Subsystems Labels"]) //. Missing[xX__] -> {})
			];	
		(If[xIn[#]["q:Order"] < xOut["q:Order"], 
			xIn[#]["q:Order"] = xOut["q:Order"]]; xOut[#] = MoSs @ xIn[#];
			)& /@ xIn["Subsystems Labels"];
		xOut["Reference Motion"] = Union @@ {
			(xIn["Reference Motion"] //. Missing[xX__] -> {}),
			Union @@ ((xOut[#]["Reference Motion"] //. Missing[xX__] -> {})& /@
				xIn["Subsystems Labels"])
			};
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:Subsystems:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xKeys = Part[#, 1]& /@ Union @ (Flatten @ {
			(Select[Keys @ xIn, Part[#, 0] === "q"&]),
			(Select[Keys @ xIn[#], Part[#, 0] === "q"&])& /@ xIn["Subsystems Labels"]
			});
		Function[{xKey},
			xIn["q+"[xKey]] = Complement[
				xIn["q"[xKey]] //. Missing[xX__] -> {}, 
				Union @@ (Function[{xSub}, xIn[xSub]["q"[xKey]] //. Missing[xX__] -> {}] /@ xIn["Subsystems Labels"])
				];
			] /@ xKeys;
		xKeys = Part[#, 1]& /@ Union @ (Flatten @ {
			Select[Keys @ xIn, And[Part[#, 0] === "q+", Not @ (xIn[#] === {})]&]
			});
		If[xKeys === {},
			(*-TRUE-*)
			(xOut["q+"[ToString @ #]] = {})& /@ Range[0, Max[2, xOut["q:Order"]]],
			(*-FALSE-*)
			(xOut["q+"[#]] = xIn["q+"[#]])& /@ xKeys;
			xOut["q:Def:Order"] = If[KeyExistsQ[xIn,"q:Def:Order"], 
				xIn["q:Def:Order"],
				Max @ ToExpression @ Flatten @ (StringSplit[#, {":", "|"}]& /@ xKeys)
				];
			(xOut["q+"[ToString @ #]] = D[
				xOut["q+"[ToString @  xOut["q:Def:Order"]]],
				{t, (# - xOut["q:Def:Order"])}
				])& /@ Range[xOut["q:Def:Order"] + 1, Max[2, xOut["q:Order"]]];
			];	
		(xOut["q"[#]] = Union[
			xOut["q+"[#]] //. Missing[xX__] -> {}, 
			Union @@ (Function[{xSub}, xOut[xSub]["q"[#]]  //. Missing[xX__] -> {}] /@ xOut["Subsystems Labels"])
			])& /@ (ToString /@ Range[0, Max[2, xOut["q:Order"]]]);	
		xKeys = Union[
			ReplaceRepeated[#, {{xX_,xY_} :> (ToString[xX] <> "|" <> ToString[xY])}]& @
				(Select[Flatten[#, 1], (Part[#, 1] > Part[#, 2])&]& @ (Outer[List, #, #]))
			]& @ Range[0, Max[2, xOut["q:Order"]]];
		(xOut["q"[#]] = D[
			xOut["q"[Part[#, 2]]] //. Missing[xX__] -> {},
			{t, ((ToExpression @ Part[#, 1]) - (ToExpression @ Part[#, 2]))}
			]& @ StringSplit[#, {":", "|"}];
		xOut["q+"[#]] = D[
			xOut["q+"[Part[#, 2]]] //. Missing[xX__] -> {},
			{t, ((ToExpression @ Part[#, 1]) - (ToExpression @ Part[#, 2]))}
			]& @ StringSplit[#, {":", "|"}];	
			)& /@ xKeys;
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:q:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xKeys = Part[#,1]& /@ Union @ (Flatten @ {
			(Select[Keys @ xIn, Part[#, 0] === "*c"&]),
			(Select[Keys @ xIn[#], Part[#, 0] === "*c"&])& /@ xIn["Subsystems Labels"]
			});
		Function[xKey,
			xOut["*c"[xKey]] = (Union @ (Flatten @ ({
				xIn["*c"[xKey]],
				Function[{xSub}, xIn[xSub]["*c"[xKey]]] /@ xIn["Subsystems Labels"]} //. Missing[xX__] -> {})))
			]/@ xKeys;
		(xOut["*c"[#]] = {})& /@ Complement[ToString /@ Range[0, xOut["q:Order"]], xKeys];

		xRules = Union @ (Flatten @
			({(* xIn["_c"], *) Function[{xSub}, xIn[xSub]["_c"]] /@ xIn["Subsystems Labels"]} //. Missing[xX__] -> {})
			);
		(	xOut["_q"[(ToString @ #)<> "|" <> (ToString @ (# - 1))]] = Union @ (Flatten @ ({
				xIn["_q"[(ToString @ #) <> "|" <> (ToString @ (# - 1))]],
				Function[{xSub}, xIn[xSub]["_q"[(ToString @ #)<> "|"<>(ToString @ (#-1))]]] /@ xIn["Subsystems Labels"]
				} //. Missing[xX__] -> {})
				);
			If[Not @ (Complement[
				xOut["q"[(ToString @ #) <> "|" <> (ToString @ (# - 1))]],
				xOut["q"[ToString @ #]], First /@ xRules, 
				First /@ xOut["_q"[(ToString @ #) <> "|" <> (ToString @ (# - 1))]]
				] === {}),
				xOut["_q"[(ToString @ #) <> "|" <> (ToString @ (#-1))]] = Union @@ {
					xOut["_q"[(ToString @ #) <> "|" <> (ToString @ (#-1))]],
					(Simplify @ Flatten @ (Quiet @ Solve[
						(# == 0)& /@ (RedundantElim @((RedundantElim @( Union @@ {
							D[xOut["*c"[ToString @ (#-1)]],t],
							xOut["*c"[ToString @ #]]
							} //. xRules)) //. xRules)),
						Complement[
							xOut["q"[(ToString @ #) <> "|" <> (ToString @ (# - 1))]],
							xOut["q"[ToString @ #]], First/@ xRules,
							First /@ xOut["_q"[(ToString @ #) <> "|" <> (ToString @ (#-1))]]
							]
						])) //. xRules
					}
				];
			xRules = Union @@ {
				xRules,
				xOut["_q"[(ToString @ #) <> "|" <> (ToString @ (# - 1))]]
				};
			)& /@ Range[1, xOut["q:Order"]];
		xOut["_c"] = Union[#, # /. {(xA_ -> xB_) -> (-xA -> -xB)}]& @ 
			(Union[xRules, xIn["_c"] //. Missing[xX__] -> {}]);
		xOut["Replacement Rules"] = Union[#, # /. {(xA_ -> xB_) -> (-xA -> -xB)}]& @ 
			(Union[#, # /. xOut["_c"]]& @ xIn["Replacement Rules"]);
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:_q:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];
		
		xA = {};	
		xKeys = (ToString @ xOut["q:Order"]);	
		If[Not @ (xOut["q+"[xKeys]] === {}),
			If[KeyExistsQ[xIn, "f"],
				AppendTo[xA, SPart[xIn["f"], xOut["q+"[xKeys]]]],
				AppendTo[xA, SPart[0, xOut["q+"[xKeys]]]]
				]
			];
		If[KeyExistsQ[xOut[#], "*f"],
			AppendTo[xA, xOut[#]["*f"]]
			]& /@ xOut["Subsystems Labels"];
		xOut["*f"] = xOut["f"] = SAssemble @@ (RedundantElim @ xA);
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:f:OK",
				NumberForm[Round[AbsoluteTime[]	- xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xKeys = Part[#, 1]& /@ (Select[Keys @ xIn, Or[Part[#, 0] === "*q", Part[#, 0] === "*q+"]&]);
		If[xKeys === {},
			(*-TRUE-*)
			(xOut["*q+"[#]] = {})& /@ (ToString /@ Range[0, Max[2, xOut["q:Order"]]]),
			(*-FALSE-*)	
			xOut["*q:Order"] = If[KeyExistsQ[xIn, "*q:Order"], xIn["*q:Order"], xOut["q:Order"]];				
			(xOut["*q+"[#]] = Complement[
				Union[xIn["*q"[#]] //. Missing[xX__] -> {}, xIn["*q+"[#]] //. Missing[xX__] -> {}],
				Union @@ (Function[{xSub}, xIn[xSub]["*q"[#]] //. Missing[xX__] -> {}] /@ xIn["Subsystems Labels"])
				])& /@ xKeys;
			If[Not @ (xOut["*q?"] === "No"), 
				(*-TRUE-*)
				(xOut["*q+"[#]] = Union[
					xOut["*q+"[#]], 
					RedundantElim @ ((xOut["*c"[#]] //. Missing[xX__] -> {}) //. xOut["_c"])
					])& /@ xKeys;
				(xOut["*q+"[ToString @ #]] = (RedundantElim @ ((Union @@ {
					D[xOut["*q+"[ToString @ (# - 1)]] //. Missing[xX__] -> {}, t],
					xOut["*q+"[ToString @ #]] //. Missing[xX__] -> {}
					}) //. xOut["_c"]))
					)& /@ Range[1, Max[2, xOut["q:Order"]]],
				(*-FALSE-*)
				(xOut["*q+"[ToString @ #]] = ((Union @@ {
					D[xOut["*q+"[ToString @ (# - 1)]] //. Missing[xX__] -> {}, t]
					}) //. xOut["_c"])
					)& /@ Range[xOut["*q:Order"] + 1, 2]
				]
			];
		(xOut["*q"[#]] = Union[
			xOut["*q+"[#]] //. Missing[xX__] -> {},
			Union @@ (Function[{xSub}, xIn[xSub]["*q"[#]] //. Missing[xX__] -> {}] /@ xIn["Subsystems Labels"])
			])& /@ (ToString /@ Range[0, Max[2, xOut["q:Order"]]]);
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:*q:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		xA = {};
		xKeys = (ToString @ xOut["q:Order"]);
		If[KeyExistsQ[xOut, "*q+"[xKeys]],
			If[And[KeyExistsQ[xOut, "q+"[xKeys]], Not @ (xOut["q+"[xKeys]] === {})],
				AppendTo[xA, Jacobi[xOut["*q+"[xKeys]], xOut["q+"[xKeys]]]]
				];
			If[And[KeyExistsQ[xOut[#], "q"[xKeys]], Not @ (xOut[#]["q"[xKeys]] === {})],
				If[KeyExistsQ[xOut[#], "S"],
					AppendTo[xA, Jacobi[xOut["*q+"[xKeys]], xOut[#]["q"[xKeys]]] ~SDot~ xOut[#]["S"]],
					AppendTo[xA, Jacobi[xOut["*q+"[xKeys]], xOut[#]["q"[xKeys]]]]
					]
				]& /@ xIn["Subsystems Labels"];
			xOut["B"] = SAssemble @@ xA
			];
		If[xOut["Debug Mode"] === "On",
			Print[StringForm["``:``:B:OK",
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];

		If[Not @ (xOut["C?"] === "No"),
			If[xOut["B"]["Matrix"] === {},
				xOut["C"] = SAssemble[1, xOut["B"]["Column Labels"]],
				If[KeyExistsQ[xOut, "q#"[xKeys]],
					xOut["C"] = OrthogonalComplement[xOut["B"], xOut["q#"[xKeys]]],
					xOut["C"] = OrthogonalComplement[xOut["B"], ToString @ xOut["System Label"]]
					]
				];							
			If[Not @ (xOut["S?"] === "No"),		
				xA = {};
				If[KeyExistsQ[xOut[#], "S"], AppendTo[xA, xOut[#]["S"]]]& /@ xIn["Subsystems Labels"];
				If[xA === {},
					xOut["S"] = xOut["C"],
					If[Not @ (xOut["q+"[xKeys]] === {}),
						AppendTo[xA, SAssemble[1, xOut["q+"[xKeys]]]]
						];
					xOut["S"] = (SAssemble @@ xA) ~SDot~ xOut["C"]
					];
				];
			If[xOut["Debug Mode"] === "On",
				Print[StringForm["``:``:C:OK",
					NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
					xOut["System Label"]]]
				];
			];

		If[And[KeyExistsQ[xOut, "f"], KeyExistsQ[xOut, "C"]],
			xOut["*f"] = STranspose[xOut["C"]] ~SDot~ xOut["f"];
			If[xOut["Explicit EOM"] === "Yes",
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

		If[xOut["Timer"] === "On",
			Print[StringForm["``:``:OK", 
				NumberForm[Round[AbsoluteTime[] - xTimer, 0.01], {5, 2}],
				xOut["System Label"]]]
			];
		xOut
		]