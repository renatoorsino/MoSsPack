NewtonEuler[xLabel_, xPositionOrientationDescription_String: "None", 
	xGravitationalField_: "Default", xInertiaSymmetry_: "Central", 
	xExternalActiveTorque_List: {0,0,0}, xExternalActiveForce_List: {0,0,0}] := 
	Module[{xOut},
		xOut = <|
			"System Label" -> xLabel,
			"Description" -> "Newton-Euler equations of the free rigid body " <> (ToString @ xLabel),
			"q:Order" -> 1
			|>;
		xOut["q"["1"]] = xOut["q#"["1"]] = {
			Subscript[v, xLabel, "x"][t], 
			Subscript[v, xLabel, "y"][t], 
			Subscript[v, xLabel, "z"][t],
			Subscript[\[Omega], xLabel, "x"][t],
			Subscript[\[Omega], xLabel, "y"][t],
			Subscript[\[Omega], xLabel, "z"][t]
			};

		If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription), ___~~"POSITION"~~___],
			xOut["q"["0"]] = {
				Subscript[p, xLabel, "x"][t],
				Subscript[p, xLabel, "y"][t],
				Subscript[p, xLabel, "z"][t]
				};
			xOut["*c"["1"]] = {
				Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
				Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t],
				Subscript[v, xLabel, "z"][t]-Subscript[p, xLabel, "z"]'[t]
				};
			xOut["_q"["1|0"]] = {
				Subscript[p, xLabel, "x"]'[t] -> Subscript[v, xLabel, "x"][t],
				Subscript[p, xLabel, "y"]'[t] -> Subscript[v, xLabel, "y"][t],
				Subscript[p, xLabel, "z"]'[t] -> Subscript[v, xLabel, "z"][t]
				};
			];

		If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription), ___~~"QUATERNION"~~___],
			xOut["q"["0"]] = {
				Subscript[p, xLabel, "x"][t],
				Subscript[p, xLabel, "y"][t],
				Subscript[p, xLabel, "z"][t],
				Subscript[q, xLabel, "x"][t],
				Subscript[q, xLabel, "y"][t],
				Subscript[q, xLabel, "z"][t],
				Subscript[q, xLabel, "t"][t]
				};
			xOut[(ToString @ \[ScriptCapitalN]) <> "|" <> (ToString @ xLabel)]  =  QuatToRot @@ {
				Subscript[q, xLabel, "x"][t],
				Subscript[q, xLabel, "y"][t],
				Subscript[q, xLabel, "z"][t],
				Subscript[q, xLabel, "t"][t]
				};
			xOut["_c"] = {
				Subscript[q, xLabel, "t"][t]^2 + Subscript[q, xLabel, "x"][t]^2 + Subscript[q, xLabel, "y"][t]^2 + Subscript[q, xLabel, "z"][t]^2 ->  1,
				1/2 Subscript[q, xLabel, "t"][t]^2 + 1/2 Subscript[q, xLabel, "x"][t]^2 + 1/2 Subscript[q, xLabel, "y"][t]^2 + 1/2 Subscript[q, xLabel, "z"][t]^2 ->  1/2,
				1-(Subscript[q, xLabel, "x"][t]^2 + Subscript[q, xLabel, "y"][t]^2 + Subscript[q, xLabel, "z"][t]^2) ->  Subscript[q, xLabel, "t"][t]^2
				};
			xOut["*c"["0"]] = {
				-1 + Subscript[q, xLabel, "t"][t]^2 + Subscript[q, xLabel, "x"][t]^2 + Subscript[q, xLabel, "y"][t]^2 + Subscript[q, xLabel, "z"][t]^2
				};
			xOut["*c"["1"]] = {
				Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
				Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t],
				Subscript[v, xLabel, "z"][t]-Subscript[p, xLabel, "z"]'[t],
				Subscript[\[Omega], xLabel, "z"][t] + 2 Subscript[q, xLabel, "z"][t] Subscript[q, xLabel, "t"]'[t] + 2 Subscript[q, xLabel, "y"][t] Subscript[q, xLabel, "x"]'[t]-2 Subscript[q, xLabel, "x"][t] Subscript[q, xLabel, "y"]'[t]-2 Subscript[q, xLabel, "t"][t] Subscript[q, xLabel, "z"]'[t],
				Subscript[\[Omega], xLabel, "y"][t] + 2 Subscript[q, xLabel, "y"][t] Subscript[q, xLabel, "t"]'[t]-2 Subscript[q, xLabel, "z"][t] Subscript[q, xLabel, "x"]'[t]-2 Subscript[q, xLabel, "t"][t] Subscript[q, xLabel, "y"]'[t] + 2 Subscript[q, xLabel, "x"][t] Subscript[q, xLabel, "z"]'[t],
				Subscript[\[Omega], xLabel, "x"][t] + 2 Subscript[q, xLabel, "x"][t] Subscript[q, xLabel, "t"]'[t]-2 Subscript[q, xLabel, "t"][t] Subscript[q, xLabel, "x"]'[t] + 2 Subscript[q, xLabel, "z"][t] Subscript[q, xLabel, "y"]'[t]-2 Subscript[q, xLabel, "y"][t] Subscript[q, xLabel, "z"]'[t]
				};
			xOut["_q"["1|0"]] = {
				Subscript[p, xLabel, "x"]'[t] -> Subscript[v, xLabel, "x"][t],
				Subscript[p, xLabel, "y"]'[t] -> Subscript[v, xLabel, "y"][t],
				Subscript[p, xLabel, "z"]'[t] -> Subscript[v, xLabel, "z"][t],
				Subscript[q, xLabel, "t"]'[t] -> 1/2 (-Subscript[q, xLabel, "x"][t] Subscript[\[Omega], xLabel, "x"][t]-Subscript[q, xLabel, "y"][t] Subscript[\[Omega], xLabel, "y"][t]-Subscript[q, xLabel, "z"][t] Subscript[\[Omega], xLabel, "z"][t]),
				Subscript[q, xLabel, "x"]'[t] -> 1/2 (Subscript[q, xLabel, "t"][t] Subscript[\[Omega], xLabel, "x"][t] + Subscript[q, xLabel, "z"][t] Subscript[\[Omega], xLabel, "y"][t]-Subscript[q, xLabel, "y"][t] Subscript[\[Omega], xLabel, "z"][t]),
				Subscript[q, xLabel, "y"]'[t] -> 1/2 (-Subscript[q, xLabel, "z"][t] Subscript[\[Omega], xLabel, "x"][t] + Subscript[q, xLabel, "t"][t] Subscript[\[Omega], xLabel, "y"][t] + Subscript[q, xLabel, "x"][t] Subscript[\[Omega], xLabel, "z"][t]),
				Subscript[q, xLabel, "z"]'[t] -> 1/2 (Subscript[q, xLabel, "y"][t] Subscript[\[Omega], xLabel, "x"][t]-Subscript[q, xLabel, "x"][t] Subscript[\[Omega], xLabel, "y"][t] + Subscript[q, xLabel, "t"][t] Subscript[\[Omega], xLabel, "z"][t])
				};
			];

		If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"EULER ANGLES"~~___] ,
			xOut["q"["0"]] = {
				Subscript[p, xLabel, "x"][t],
				Subscript[p, xLabel, "y"][t],
				Subscript[p, xLabel, "z"][t],
				Subscript[\[Psi], xLabel][t],
				Subscript[\[Phi], xLabel][t],
				Subscript[\[Theta], xLabel][t]
				};
			xOut[(ToString @ \[ScriptCapitalN]) <> "|" <> (ToString @ xLabel)] = 
				(Rotation @@ (Characters @ (First @ StringSplit[xPositionOrientationDescription,{":", "|", " "}])))[Subscript[\[Psi], xLabel][t],Subscript[\[Phi], xLabel][t],Subscript[\[Theta], xLabel][t]];
			If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"REDUNDANT"~~___] ,
				(*-TRUE-*)	
				xOut["q"["1"]] = {
					Subscript[v, xLabel, "x"][t],
					Subscript[v, xLabel, "y"][t],
					Subscript[v, xLabel, "z"][t],
					Subscript[\[Omega], xLabel, "x"][t],
					Subscript[\[Omega], xLabel, "y"][t],
					Subscript[\[Omega], xLabel, "z"][t],
					Subscript[\[Psi], xLabel]'[t],
					Subscript[\[Phi], xLabel]'[t],
					Subscript[\[Theta], xLabel]'[t]
					};
				xOut["q#"["1"]] = {
					Subscript[v, xLabel, "x"][t],
					Subscript[v, xLabel, "y"][t],
					Subscript[v, xLabel, "z"][t],
					Subscript[\[Psi], xLabel]'[t],
					Subscript[\[Phi], xLabel]'[t],
					Subscript[\[Theta], xLabel]'[t]
					};
				xOut["*c"["1"]] = {
					Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
					Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t],
					Subscript[v, xLabel, "z"][t]-Subscript[p, xLabel, "z"]'[t]
					};
				xOut["*q"["1"]] = Union @@ {
					({Subscript[\[Omega], xLabel, "x"][t],Subscript[\[Omega], xLabel, "y"][t],Subscript[\[Omega], xLabel, "z"][t]}
						-(AngularVelocity @ xOut[(ToString @ \[ScriptCapitalN]) <> "|" <> (ToString @ xLabel)]))
					},
				(*-FALSE-*)	
				xOut["*c"["1"]] = Union @@ {
					{Subscript[v, xLabel, "x"][t]-Subscript[p, xLabel, "x"]'[t],
					Subscript[v, xLabel, "y"][t]-Subscript[p, xLabel, "y"]'[t],
					Subscript[v, xLabel, "z"][t]-Subscript[p, xLabel, "z"]'[t]},
					({Subscript[\[Omega], xLabel, "x"][t],Subscript[\[Omega], xLabel, "y"][t],Subscript[\[Omega], xLabel, "z"][t]}
						-(AngularVelocity @ xOut[(ToString @ \[ScriptCapitalN]) <> "|" <> (ToString @ xLabel)]))
					}
				];
			];

		Module[{xI,xg},
			xI["Spherical"] = xI["S"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel]}
				});
			xI["Cylindrical x"] = xI["Cx"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "a"], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "r"], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel, "r"]}
				});
			xI["Cylindrical y"] = xI["Cy"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "r"], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "a"], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel, "r"]}
				});
			xI["Cylindrical z"] = xI["Cz"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "r"], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "r"], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel, "a"]}
				});
			xI["Central"] = xI["xyz"] = xI["C"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "x"], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "y"], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel, "z"]}
				});
			xI["xy Plane"] = xI["xy"] = xI["z"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xx"], Subscript[OverBar[\[CapitalIota]], xLabel, "xy"], 0},
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xy"], Subscript[OverBar[\[CapitalIota]], xLabel, "yy"], 0},
				{0, 0, Subscript[OverBar[\[CapitalIota]], xLabel, "zz"]}
				});
			xI["xz Plane"] = xI["xz"] = xI["y"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xx"], 0, Subscript[OverBar[\[CapitalIota]], xLabel, "xz"]},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "yy"], 0},
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xz"], 0, Subscript[OverBar[\[CapitalIota]], xLabel, "zz"]}
				});
			xI["yz Plane"] = xI["yz"] = xI["x"] = ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xx"], 0, 0},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "yy"], Subscript[OverBar[\[CapitalIota]], xLabel, "yz"]},
				{0, Subscript[OverBar[\[CapitalIota]], xLabel, "yz"], Subscript[OverBar[\[CapitalIota]], xLabel, "zz"]}
				});
			xI[xX_]:= ({
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xx"], Subscript[OverBar[\[CapitalIota]], xLabel, "xy"], Subscript[OverBar[\[CapitalIota]], xLabel, "xz"]},
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xy"], Subscript[OverBar[\[CapitalIota]], xLabel, "yy"], Subscript[OverBar[\[CapitalIota]], xLabel, "yz"]},
				{Subscript[OverBar[\[CapitalIota]], xLabel, "xz"], Subscript[OverBar[\[CapitalIota]], xLabel, "yz"], Subscript[OverBar[\[CapitalIota]], xLabel, "zz"]}
				});

			xg["Default"] = OverBar[g]{Sin[OverBar[\[Xi]]], 0, Cos[OverBar[\[Xi]]]};
			xg["None"] = {0,0,0};
			xg["x"] = OverBar[g]{1,0,0};
			xg["-x"] = OverBar[g]{-1,0,0};
			xg["y"] = OverBar[g]{0,1,0};
			xg["-y"] = OverBar[g]{0,-1,0};
			xg["z"] = OverBar[g]{0,0,1};
			xg["-z"] = OverBar[g]{0,0,-1};
			xg[xL_List]:= xL;
			xg[xX_]:= OverBar[g]{Sin[xX],0,Cos[xX]};

			xOut["*f"] = xOut["f"] = <|
				"Matrix" ->  Join @@ {
					- Subscript[OverBar[m], xLabel] (D[#,t]& /@ 
						{Subscript[v, xLabel, "x"][t], Subscript[v, xLabel, "y"][t], Subscript[v, xLabel, "z"][t]}) 
					+ Subscript[OverBar[m], xLabel]xg[xGravitationalField] 
					+ xExternalActiveForce,
					- xI[xInertiaSymmetry].(D[#,t]& /@ 
						{Subscript[\[Omega], xLabel, "x"][t],Subscript[\[Omega], xLabel, "y"][t],Subscript[\[Omega], xLabel, "z"][t]})
					- {Subscript[\[Omega], xLabel, "x"][t], Subscript[\[Omega], xLabel, "y"][t], Subscript[\[Omega], xLabel, "z"][t]} ~Cross~ 
						(xI[xInertiaSymmetry].{Subscript[\[Omega], xLabel, "x"][t], Subscript[\[Omega], xLabel, "y"][t], Subscript[\[Omega], xLabel, "z"][t]}) 
					+ xExternalActiveTorque
					},
				"Row Labels" ->  {
					Subscript[v, xLabel, "x"][t],
					Subscript[v, xLabel, "y"][t],
					Subscript[v, xLabel, "z"][t],
					Subscript[\[Omega], xLabel, "x"][t],
					Subscript[\[Omega], xLabel, "y"][t],
					Subscript[\[Omega], xLabel, "z"][t]
					}
				|>;
			];

		xOut
		]
