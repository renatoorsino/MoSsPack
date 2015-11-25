NewtonEuler2D[xLabel_, xCoordinates_: "None", 
	xGravitationalField_: "Default", xExternalActiveTorque_: 0, xExternalActiveForce_List: {0,0}] := 
	Module[{xOut},
		xOut = <|
			"System Label" -> xLabel,
			"Description" -> "Newton-Euler equations of the free 2D rigid body " <> (ToString @ xLabel),
			"q:Order" -> 1
			|>;
		xOut["q"["1"]] = xOut["q#"["1"]] = {
			Subscript[v, xLabel, "x"][t], 
			Subscript[v, xLabel, "y"][t], 
			Subscript[\[Omega], xLabel, "z"][t]
			};

		If[And[
			StringQ @ xCoordinates,
			StringMatchQ[(ToUpperCase @ xCoordinates), ___~~"POSITION"~~___]
			],
			xOut["q"["0"]] = {
				Subscript[p, xLabel, "x"][t],
				Subscript[p, xLabel, "y"][t]
				};
			xOut["*c"["1"]] = {
				Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
				Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t]
				};
			xOut["_q"["1|0"]] = {
				Subscript[p, xLabel, "x"]'[t] -> Subscript[v, xLabel, "x"][t],
				Subscript[p, xLabel, "y"]'[t] -> Subscript[v, xLabel, "y"][t]
				};
			];

		If[And[
			StringQ @ xCoordinates,
			StringMatchQ[(ToUpperCase @ xCoordinates), ___~~"NEWTON-EULER"~~___]
			],
			xOut["q"["0"]] = {
				Subscript[p, xLabel, "x"][t],
				Subscript[p, xLabel, "y"][t],
				Subscript[\[Theta], xLabel][t]
				};				
			xOut["*c"["1"]] = Union @ {
				Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
				Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t],
				Subscript[\[Omega], xLabel, "z"][t]-Subscript[\[Theta], xLabel]'[t]
				};
			xOut["_q"["1|0"]] = {
				Subscript[p, xLabel, "x"]'[t] -> Subscript[v, xLabel, "x"][t],
				Subscript[p, xLabel, "y"]'[t] -> Subscript[v, xLabel, "y"][t],
				Subscript[\[Theta], xLabel]'[t] -> Subscript[\[Omega], xLabel, "z"][t]
				};	
			];

		If[Or[ListQ @ xCoordinates, IntegerQ @ xCoordinates],
			xOut["Nodes"] = <|"#" -> (xCoordinates /. {pX_List :> First @ pX})|>;
			xOut["Nodes"]["O"] = xCoordinates /. {
				pX_List /; And[ListQ[Last @ pX], ListQ[First @ (Last @ pX)]] :> First @ (First @ (Last @ pX)),
				pX_ -> 1
				};
			xOut["Nodes"]["X"] = xCoordinates /. {
				pX_List /; And[ListQ[Last @ pX], ListQ[First @ (Last @ pX)]] :> Last @ (First @ (Last @ pX)),
				pX_ -> 2
				};	
			xOut["Nodes"]["a"] = xCoordinates /. {
				pX_List /; And[ListQ[Last @ pX], ListQ[Last @ (Last @ pX)]] :> First @ (Last @ (Last @ pX)), 
				pX_List /; And[ListQ[Last @ pX], ListQ[First @ (Last @ pX)]] :> (Last @ (Last @ pX)), 
				pX_List /; And[ListQ[Last @ pX]] :> (First @ (Last @ pX)), 
				pX_List :> (Last @ pX), 
				pX_ -> 1/2
				};	
			xOut["Nodes"]["b"] = xCoordinates /. {
				pX_List /; And[ListQ[Last @ pX], ListQ[Last @ (Last @ pX)]] :> Last @ (Last @ (Last @ pX)), 
				pX_List /; And[ListQ[Last @ pX], Not @ ListQ[First @ (Last @ pX)]] :> (Last @ (Last @ pX)), 
				pX_ -> 0
				};
			(xOut["Nodes"][#] = {Subscript[p, xLabel, #, "x"][t], Subscript[p, xLabel, #, "y"][t]}) & /@ (Range @ xOut["Nodes"]["#"]);
			xOut["q"["0"]] = Union @@ (
				{Subscript[p, xLabel, #, "x"][t], Subscript[p, xLabel, #, "y"][t]} & /@ (Range @ xOut["Nodes"]["#"])
				);
			xOut["q"["1"]] = Union @@ {
				xOut["q#"["1"]],
				Union @@ (
					{Subscript[p, xLabel, #, "x"]'[t], Subscript[p, xLabel, #, "y"]'[t]} & /@ (Range @ xOut["Nodes"]["#"])
					)
				};
			xOut["*q"["1"]] =  Union @@ ({
				- Subscript[p, xLabel, #, "x"]'[t] + Subscript[v, xLabel, "x"][t]  
					+ Subscript[\[Omega], xLabel, "z"][t] (
						+ xOut["Nodes"]["b"] (Subscript[p, xLabel, xOut["Nodes"]["X"], "x"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "x"][t])
						+ xOut["Nodes"]["a"] (Subscript[p, xLabel, xOut["Nodes"]["X"], "y"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "y"][t])
						- (Subscript[p, xLabel, #, "y"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "y"][t])
						),
				- Subscript[p, xLabel, #, "y"]'[t] + Subscript[v, xLabel, "y"][t]
					+ Subscript[\[Omega], xLabel, "z"][t] (
						- xOut["Nodes"]["a"] (Subscript[p, xLabel, xOut["Nodes"]["X"], "x"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "x"][t])
						+ xOut["Nodes"]["b"] (Subscript[p, xLabel, xOut["Nodes"]["X"], "y"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "y"][t])
						+ (Subscript[p, xLabel, #, "x"][t] - Subscript[p, xLabel, xOut["Nodes"]["O"], "x"][t])
						)
				} & /@ (Range @ xOut["Nodes"]["#"])
				);
			];	

		Module[{xg},

			xg["Default"] = OverBar[g]{0,-1};
			xg["None"] = {0,0};
			xg["x"] = OverBar[g]{1,0};
			xg["-x"] = OverBar[g]{-1,0};
			xg["y"] = OverBar[g]{0,1};
			xg["-y"] = OverBar[g]{0,-1};
			xg["z"] = OverBar[g]{0,0};
			xg["-z"] = OverBar[g]{0,0};
			xg[xL_List]:= xL;
			xg[xX_]:= OverBar[g]{Sin[xX],-Cos[xX]};

			xOut["*f"] = xOut["f"] = <|
				"Matrix" ->  Join @@ {
					- Subscript[OverBar[m], xLabel] (D[#, t]& /@ {Subscript[v, xLabel, "x"][t], Subscript[v, xLabel, "y"][t]}) 
					+ Subscript[OverBar[m], xLabel] xg[xGravitationalField] 
					+ xExternalActiveForce,
					{- Subscript[OverBar[\[CapitalIota]], xLabel] D[Subscript[\[Omega], xLabel, "z"][t], t]
					+ xExternalActiveTorque}
					},
				"Row Labels" ->  {
					Subscript[v, xLabel, "x"][t],
					Subscript[v, xLabel, "y"][t],
					Subscript[\[Omega], xLabel, "z"][t]
					}
				|>;
			];

		xOut
		]
