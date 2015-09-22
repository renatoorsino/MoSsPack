ParametersEval[xSystem_Association,xPhysicalParameters_List,xExtraRules_List:{}] :=
	Module[{xAuxiliarParameters,xInvariants,xVariables,xCoeffA,xVarA,xCoeffC,xVarC},
		{xCoeffA,xVarA} = SMatrixCoefficientArrays @ (xSystem["B"]);
		{xCoeffC,xVarC} = SMatrixCoefficientArrays @ (xSystem["C"]);
		xInvariants = Expand /@ RedundantElim @ (Expand /@ (Flatten @ 
			(SAssemble[xCoeffA[1] ~SDot~ xCoeffC[1]]["Matrix"]) //. xExtraRules //. xPhysicalParameters));
		xVariables = Union @ GetAllVariables[xInvariants];
		xAuxiliarParameters = Union @ MapThread[#1-> #2&, {
			xVariables,
			- LeastSquares @@ (Reverse @ CoefficientArrays[xInvariants, xVariables])
			}, 1];
		(
		xInvariants = Expand /@ RedundantElim @ (Chop @ (Expand /@ (Flatten @ 
			(SAssemble[xCoeffA[1] ~SDot~ xCoeffC[#], xCoeffA[#] ~SDot~ xCoeffC[1]]["Matrix"])
			//. xExtraRules //. xPhysicalParameters //. xAuxiliarParameters)));
		xVariables = Union @ GetAllVariables[xInvariants];
		If[Not @ (xInvariants === {}),
			xAuxiliarParameters = Union[
				xAuxiliarParameters,
				MapThread[#1-> #2&, {
					xVariables,
					- LeastSquares @@ (Reverse @ CoefficientArrays[xInvariants, xVariables])
					}, 1]
				]
			];
		)& /@ xVarC;
		Union[xPhysicalParameters,xAuxiliarParameters]
		]