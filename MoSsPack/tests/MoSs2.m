
$PrePrint=#/.{
Csc[xArgument_]:>1/Defer@Sin[xArgument],
Sec[xArgument_]:>1/Defer@Cos[xArgument],
Tan[xArgument_]:>  Defer@Sin[xArgument]/Defer@Cos[xArgument],
Cot[xArgument_]:>  Defer@Cos[xArgument]/Defer@Sin[xArgument]
}&;


Unprotect[Cos,Sin];
Format[Cos[xArgument_]]:=Subscript[c, xArgument]
Format[Sin[xArgument_]]:=Subscript[s, xArgument]
Protect[Cos,Sin];


Format[Subscript[Subscript[xArgument_,xIndexes1__],xIndexes2__]'[t_]]:=Subscript[Subscript[Overscript[xArgument,"."],xIndexes1],xIndexes2][t]
Format[Subscript[Subscript[xArgument_,xIndexes1__],xIndexes2__]''[t_]]:=Subscript[Subscript[Overscript[xArgument,".."],xIndexes1],xIndexes2][t]
Format[Subscript[xArgument_,xIndexes1__]'[t_]]:=Subscript[Overscript[xArgument,"."],xIndexes1][t]
Format[Subscript[xArgument_,xIndexes1__]''[t_]]:= Subscript[Overscript[xArgument,".."],xIndexes1][t]
Format[xArgument_'[t_]]:= Overscript[xArgument,"."][t]
Format[xArgument_''[t_]]:= Overscript[xArgument,".."][t]


SymbolReplacements={
Subscript[Subscript[xBase_, xIndexes__], xIndexes2__]'[t]-> Subscript[Subscript[Overscript[xBase,"."], xIndexes], xIndexes2],
Subscript[Subscript[xBase_, xIndexes__], xIndexes2__]''[t]-> Subscript[Subscript[Overscript[xBase,".."], xIndexes], xIndexes2],
Subscript[xBase_, xIndexes__]'[t]-> Subscript[Overscript[xBase,"."], xIndexes],
Subscript[xBase_, xIndexes__]''[t]-> Subscript[Overscript[xBase,".."], xIndexes],
xVariable_'[t]-> Overscript[xVariable,"."],
xVariable_''[t]->  Overscript[xVariable,".."],
xVariable_[t]-> xVariable
};


RoundOffRules={xNumber_?NumericQ/;Abs[xNumber]<10^-12-> 0,xNumber_?NumericQ/;Abs[xNumber-1]<10^-12-> 1};


SetComplement={xMainSet,xDiffSet}\[Function]Select[xMainSet,Not[MemberQ[xDiffSet,#]]&];


RedundantElim[xX_]:= DeleteDuplicates@(DeleteCases[Simplify@xX,0]);


SSimplify[xA_Association]:=Association@MapThread[#1->#2&,{First/@(Normal@xA),Simplify@(Last/@(Normal@xA))},1]
SSimplify[xX_]:=Simplify[xX]


SReplaceRepeated[xA_Association,xL_List]:=Association@MapThread[#1->#2&,{First/@(Normal@xA),ReplaceRepeated[(Last/@(Normal@xA)),xL]},1]
SReplaceRepeated[xX_,xL_List]:=ReplaceRepeated[xX,xL]


SReplaceFullSimplify[xA_Association,xRules_List]:=
Association@MapThread[#1->#2&,{
First/@(Normal@xA),
FullSimplify[FullSimplify[Expand[(Last/@(Normal@xA))//.xRules]//.xRules]//.xRules]
},1]

SReplaceFullSimplify[xX_,xRules_List]:=
FullSimplify[FullSimplify[Expand[(Flatten @{xX})//.xRules]//.xRules]//.xRules]

SReplaceSimplify[xA_Association,xRules_List]:=
Association@MapThread[#1->#2&,{
First/@(Normal@xA),
Simplify[Simplify[Expand[(Last/@(Normal@xA))//.xRules]//.xRules]//.xRules]
},1]

SReplaceSimplify[xX_,xRules_List]:=
Simplify[Simplify[Expand[(Flatten @{xX})//.xRules]//.xRules]//.xRules]


SRename[xIn_Association,xNamingRules_,xExtraRules_:{}]:=Association@MapThread[
#1-> #2&,
{If[Head[#]===String,StringReplace[#,xNamingRules],#]&/@(First/@Normal @ (xIn)),
Map[SReplaceRepeated[#,xExtraRules]&,Map[SReplaceRepeated[#,xNamingRules]&, Map[SReplaceRepeated[#,xExtraRules]&,(Last/@Normal @ xIn),All],All],All]},
1];


GetVariables[xX_List,xExcept_List:{}]:=Complement[DeleteDuplicates@Cases[xX,xVariable_[t],Infinity],xExcept];

GetVariables[xX_Association,xExcept_List:{}]:=Complement[DeleteDuplicates@Cases[xX["Matrix"],xVariable_[t],Infinity],xExcept];


HeadList={Or,And,Equal,Unequal,Less,LessEqual,Greater,GreaterEqual,Inequality};

GetAllVariables[xNumber_?NumericQ]:=Sequence[]
GetAllVariables[{}]:=Sequence[]
GetAllVariables[xRelationalOperator_]/;MemberQ[HeadList,xRelationalOperator]:=Sequence[]

GetAllVariables[x_List]:=DeleteDuplicates@(Flatten@(Union@(GetAllVariables[#]&/@x)))

GetAllVariables[Derivative[xNumber_Integer][xFunction_][xArgument__]]:=
Module[{xVariable},

If[MemberQ[Attributes[xFunction],NumericFunction]||MemberQ[HeadList,xFunction],

(*-TRUE-*)

xVariable=GetAllVariables[{xArgument}],

(*-FALSE-*)

xVariable=Derivative[xNumber][xFunction][xArgument]
];

xVariable

];

GetAllVariables[xFunction_Symbol[xArgument__]]:=
Module[{xVariable},

If[MemberQ[Attributes[xFunction],NumericFunction]||MemberQ[HeadList,xFunction],

(*-TRUE-*)

xVariable=GetAllVariables[{xArgument}],

(*-FALSE-*)

xVariable=xFunction[xArgument]
];

xVariable

];

GetAllVariables[xOther_]:=xOther


Matrix2Rule[xA_Association]:=
Association@Flatten@MapThread[
(#1-> #2)&,
{Outer[{#1,#2}&,xA["Row Labels"],xA["Column Labels"]],xA["Matrix"]},
2
]


AngleBracket[xA__Association]:=
Module[{xAList,xRowLabels,xColumnLabels,xRList},

xAList=List[xA];

xColumnLabels=Union@(Join@@((#["Column Labels"])&/@xAList));

xRowLabels=Union@(Join@@((#["Row Labels"])&/@xAList));

xRList=Association@((#-> Plus@@DeleteCases[#/.(Matrix2Rule/@xAList),#])&/@
Flatten[Outer[{#1,#2}&,xRowLabels,xColumnLabels],1]);

Association[
"Matrix"-> Outer[{#1,#2}&,xRowLabels,xColumnLabels]/.xRList,
"Row Labels"-> xRowLabels,
"Column Labels"-> xColumnLabels
]
]

AngleBracket[xA_Association,xRowLabels_List]:=
AngleBracket@Association[
"Matrix"-> Part[
xA["Matrix"],
Flatten@(Position[xA["Row Labels"],#]&/@xRowLabels),
All],
"Row Labels"-> xRowLabels,
"Column Labels"-> xA["Column Labels"]
];

AngleBracket[xA_Association,xRowLabel_]:=
If[First@Dimensions@(xA["Column Labels"])==1,
Part[
xA["Matrix"],
First@(Flatten@(Position[xA["Row Labels"],xRowLabel])),
1],
AngleBracket@Association[
"Matrix"-> Part[
xA["Matrix"],
Flatten@(Position[xA["Row Labels"],xRowLabel]),
All],
"Row Labels"-> {xRowLabel},
"Column Labels"-> xA["Column Labels"]
]
];

AngleBracket[xA_Association,xRowLabels_List,xColumnLabels_List]:=
AngleBracket@Association[
"Matrix"-> Part[
xA["Matrix"],
Flatten@(Position[xA["Row Labels"],#]&/@xRowLabels),
Flatten@(Position[xA["Column Labels"],#]&/@xColumnLabels)],
"Row Labels"-> xRowLabels,
"Column Labels"-> xColumnLabels
];

AngleBracket[xA_Association,All,xColumnLabels_List]:=
AngleBracket@Association[
"Matrix"-> Part[
xA["Matrix"],
All,
Flatten@(Position[xA["Column Labels"],#]&/@xColumnLabels)
],
"Row Labels"-> xA["Row Labels"],
"Column Labels"-> xColumnLabels
];

AngleBracket[xA_Association,xRowLabels_List,xColumnLabel_]:=
AngleBracket@Association[
"Matrix"-> {Part[
xA["Matrix"],
Flatten@(Position[xA["Row Labels"],#]&/@xRowLabels),
First@Flatten@(Position[xA["Column Labels"],xColumnLabel])
]}\[Transpose],
"Row Labels"-> xRowLabels,
"Column Labels"-> {xColumnLabel}
];

AngleBracket[xA_Association,All,xColumnLabel_]:=
AngleBracket@Association[
"Matrix"-> {Part[
xA["Matrix"],
All,
First@Flatten@(Position[xA["Column Labels"],xColumnLabel])
]}\[Transpose],
"Row Labels"-> xA["Row Labels"],
"Column Labels"-> {xColumnLabel}
];

AngleBracket[xA_Association,xRowLabel_,xColumnLabels_List]:=
AngleBracket@Association[
"Matrix"-> Part[
xA["Matrix"],
First@Flatten@(Position[xA["Row Labels"],xRowLabel]),
Flatten@(Position[xA["Column Labels"],#]&/@xColumnLabels)],
"Row Labels"-> {xRowLabel},
"Column Labels"-> xColumnLabels
];

AngleBracket[xA_Association,xRowLabel_,xColumnLabel_]:=
Part[
xA["Matrix"],
First@Flatten@(Position[xA["Row Labels"],xRowLabel]),
First@Flatten@(Position[xA["Column Labels"],xColumnLabel])];


SPart=AngleBracket;


SApply[xFunction_,xX_Association]:=
Association[
"Matrix"-> xFunction@(xX["Matrix"]),
"Column Labels"-> xX["Column Labels"],
"Row Labels"-> xX["Row Labels"]
]


CircleDot[xX_Association,xY_Association]:=
Module[{xA,xB},
xA=SAssemble[xX];
xB=SAssemble[xY];
If[xA["Column Labels"]===xB["Row Labels"],
Association[
"Matrix"->(xA["Matrix"].xB["Matrix"]),
"Column Labels"-> xB["Column Labels"],
"Row Labels"-> xA["Row Labels"]
],
"Error"
]]


CircleDot[xX_Association,xY_List]:=(xX["Matrix"].xY)


CircleDot[xX_Association,xY_]:=
Association[
"Matrix"->(SAssemble[xX]["Matrix"])xY,
"Column Labels"-> SAssemble[xX]["Column Labels"],
"Row Labels"-> SAssemble[xX]["Row Labels"]
]

CircleDot[xY_,xX_Association]:=
Association[
"Matrix"->(SAssemble[xX]["Matrix"])xY,
"Column Labels"-> SAssemble[xX]["Column Labels"],
"Row Labels"->SAssemble[xX]["Row Labels"]
]


SuperDagger[xX_Association]:=
Association[
"Matrix"->Transpose@(xX["Matrix"]),
"Column Labels"-> xX["Row Labels"],
"Row Labels"-> xX["Column Labels"]
]


STranspose[xX_Association]:=SuperDagger[xX]


BracketingBar[xX_Association]:=AffineTransform[xX["Matrix"]]

BracketingBar[xX_List/;Dimensions[xX]=={3,3}]:=AffineTransform[xX]

BracketingBar[xX_List/;Dimensions[xX]=={4,4}]:=LinearFractionalTransform[xX]


RowMatrix[xX_List]:=Association[
"Matrix"-> (Transpose@(Join@@(Transpose@Part[#,"Matrix"]&/@xX))),
"Column Labels"-> Join@@(Part[#,"Column Labels"]&/@xX),
"Row Labels"->Part[First@xX,"Row Labels"]
]


ColumnMatrix[xX_List]:=Association[
"Matrix"-> (Join@@(Part[#,"Matrix"]&/@xX)),
"Column Labels"-> Part[First@xX,"Column Labels"],
"Row Labels"->Join@@(Part[#,"Row Labels"]&/@xX)
]


SCoefficientArrays[xA_Association,xVariables_List,xRules_List:{}]:=
Module[{x},
x["Row Labels"]=xA["Row Labels"];
x["Expressions"]=Flatten@(xA["Matrix"]);
x["Coefficient Arrays"]=CoefficientArrays[x["Expressions"]//.xRules,xVariables];
{Association[
"Matrix"-> {Part[#,1]&@(x["Coefficient Arrays"])}\[Transpose],
"Row Labels"->x["Row Labels"],
"Column Labels"-> {""}
],
Association[
"Matrix"->Part[#,2]&@(x["Coefficient Arrays"]),
"Row Labels"->x["Row Labels"],
"Column Labels"-> xVariables
]
}
]


SMatrixCoefficientArrays[xA_Association,xRules_List:{}]:=Module[{xxMatrix,xxVariables,xxRowLabels,xxColumnLabels,xxCoefficientMatrices},
xxMatrix=xA["Matrix"]//.xRules;
xxRowLabels=xA["Row Labels"];
xxColumnLabels=xA["Column Labels"];
xxVariables=Union@GetVariables[xxMatrix];
xxCoefficientMatrices=CoefficientArrays[xxMatrix,xxVariables];
{Association[
Union@@{
{
1->
Association[
"Matrix"->Normal@Part[xxCoefficientMatrices,1],
"Column Labels"->xxColumnLabels,
"Row Labels"->xxRowLabels 
]
},
MapThread[
(#1-> 
Association[
"Matrix"->Normal@Part[xxCoefficientMatrices,2,All,All,#2],
"Column Labels"->xxColumnLabels,
"Row Labels"->xxRowLabels 
])&,
{#,Range@Length@#},
1
]&@xxVariables
}
],
xxVariables
}
]


SLinearSolve[xX_Association,xY_Association]:=
Module[{xA,xB},
xA=SAssemble[xX];
xB=SAssemble[xY];
If[xA["Row Labels"]===xB["Row Labels"],
Association[
"Matrix"->LinearSolve[xA["Matrix"],xB["Matrix"]],
"Column Labels"-> xB["Column Labels"],
"Row Labels"-> xA["Column Labels"]
],
"Error"
]]


LSOCSolver[xJacobian_Association,xRemainder_Association]:=Association[
"Matrix"->- LeastSquares[xJacobian["Matrix"],xRemainder["Matrix"]],
"Row Labels"-> xJacobian["Column Labels"],
"Column Labels"-> xRemainder["Column Labels"]
]


Jacobi[xExpressionsList_,xVariablesList_]:=
Module[{xJacobian},

xJacobian=Association[
"Matrix"-> D[xExpressionsList,{xVariablesList}],
"Column Labels"-> xVariablesList,
"Row Labels"-> Range@@Dimensions@xExpressionsList
]

]


Jacobi[xExpressionsList_,xVariablesList_, xExpressionsLabels_]:=
Module[{xJacobian},

xJacobian=Association[
"Matrix"-> D[xExpressionsList,{xVariablesList}],
"Column Labels"-> xVariablesList,
"Row Labels"-> xExpressionsLabels
]

]


OrthogonalComplement[xJacobian_]:=
Module[{x,xOrthogonalComplement},

 x["Null Space Matrix"]=Transpose@NullSpace[xJacobian["Matrix"]];

x["Independent Variations"]=(* Subscript[OverTilde[q],#][t]&/@*)(Range@(Dimensions[ x["Null Space Matrix"]])[[2]]);

xOrthogonalComplement=Association[
"Matrix"-> x["Null Space Matrix"],
"Column Labels"->x["Independent Variations"],
"Row Labels"->  xJacobian["Column Labels"]
]
]


OrthogonalComplement[xJacobian_,xLabel_String]:=
Module[{x,xOrthogonalComplement},

 x["Null Space Matrix"]=Transpose@NullSpace[xJacobian["Matrix"]];

x["Independent Variations"]=Subscript[OverTilde[q],xLabel,#][t]&/@(Range@(Dimensions[ x["Null Space Matrix"]])[[2]]);

xOrthogonalComplement=Association[
"Matrix"-> x["Null Space Matrix"],
"Column Labels"->x["Independent Variations"],
"Row Labels"->  xJacobian["Column Labels"]
]
]


OrthogonalComplement[xJacobian_,xIndependentVariablesList_List]:=
Module[{x,xOrthogonalComplement},

{x["Number of Constraints"],x["Number of Variables"]}=Dimensions[xJacobian["Matrix"]];

x["Number of Degrees of Freedom"]=x["Number of Variables"]-x["Number of Constraints"];

If[{x["Number of Degrees of Freedom"]}== Dimensions@xIndependentVariablesList,

(*-TRUE-*)

x["Independent Variables Column Indexes"] =Flatten[Position[xJacobian["Column Labels"],#]&/@xIndependentVariablesList,Infinity];

x["Redundant Variables Column Indexes"] =Complement[Range@@Dimensions@xJacobian["Column Labels"],x["Independent Variables Column Indexes"]];

xOrthogonalComplement = Association[
"Matrix"->Array[0&,{x["Number of Variables"],x["Number of Degrees of Freedom"]}],
"Column Labels"-> xIndependentVariablesList,
"Row Labels"-> xJacobian["Column Labels"]
];

xOrthogonalComplement[["Matrix",x["Independent Variables Column Indexes"]]]=IdentityMatrix@x["Number of Degrees of Freedom"];

xOrthogonalComplement[["Matrix",x["Redundant Variables Column Indexes"]]]=LinearSolve@@{xJacobian[["Matrix",All,x["Redundant Variables Column Indexes"]]],-xJacobian[["Matrix",All,x["Independent Variables Column Indexes"]]]};

xOrthogonalComplement,

(*-FALSE-*)

"Error"
]
]


LSOrthogonalComplement[xJacobian_,xIndependentVariablesList_List]:=
Module[{x,xOrthogonalComplement},

{x["Number of Constraints"],x["Number of Variables"]}=Dimensions[xJacobian["Matrix"]];

x["Number of Degrees of Freedom"]=Part[Dimensions@xIndependentVariablesList,1];


x["Independent Variables Column Indexes"] =Flatten[Position[xJacobian["Column Labels"],#]&/@xIndependentVariablesList,Infinity];

x["Redundant Variables Column Indexes"] =Complement[Range@@Dimensions@xJacobian["Column Labels"],x["Independent Variables Column Indexes"]];

xOrthogonalComplement = Association[
"Matrix"->Array[0&,{x["Number of Variables"],x["Number of Degrees of Freedom"]}],
"Column Labels"-> xIndependentVariablesList,
"Row Labels"-> xJacobian["Column Labels"]
];

xOrthogonalComplement[["Matrix",x["Independent Variables Column Indexes"]]]=IdentityMatrix@x["Number of Degrees of Freedom"];

xOrthogonalComplement[["Matrix",x["Redundant Variables Column Indexes"]]]=LeastSquares@@{xJacobian[["Matrix",All,x["Redundant Variables Column Indexes"]]],-xJacobian[["Matrix",All,x["Independent Variables Column Indexes"]]]};

xOrthogonalComplement

]


LSLinearizedOrthogonalComplement[
xLinearizedJacobian_Association,
xIndependentVariables_List,
xCoordinatesReplacements_:{},
xNZero_Rational:1 10^-5,
xTestParameters_List:{}
]:=
Module[{x,xLSOC,xCoordinates,xLinearizedJacobianCoefficients,xNTestParameters,xNA1,xNC1,xNCq,xSC1,xSCq},

{xLinearizedJacobianCoefficients,xCoordinates}=SMatrixCoefficientArrays[xLinearizedJacobian];

xNTestParameters=
Union[
xTestParameters,
(#-> RandomReal[1])&/@(GetAllVariables[(Flatten@(Union@@(Normal@(#["Matrix"])&/@xLinearizedJacobianCoefficients)))//.xTestParameters])
];

xNA1=SReplaceRepeated[xLinearizedJacobianCoefficients[1],xNTestParameters];

xNC1=LSOrthogonalComplement[xNA1,xIndependentVariables];

x["\[Epsilon]"]=1 10^-3;

xNCq=
Association[
(#->SAssemble[
(1/(2x["\[Epsilon]"]))\[CircleDot]SAssemble[
LSOrthogonalComplement[
SAssemble[xNA1,(x["\[Epsilon]"])\[CircleDot]SReplaceRepeated[xLinearizedJacobianCoefficients[#],xNTestParameters]],
xIndependentVariables],
(-1)\[CircleDot]xNC1
],
(-(1/(2x["\[Epsilon]"])))\[CircleDot]SAssemble[
LSOrthogonalComplement[
SAssemble[xNA1,(-x["\[Epsilon]"])\[CircleDot]SReplaceRepeated[xLinearizedJacobianCoefficients[#],xNTestParameters]],
xIndependentVariables],
(-1)\[CircleDot]xNC1
]
]
)&/@xCoordinates
];

xNC1=AppendTo[xNC1,"Matrix"->Round[xNC1["Matrix"],xNZero]];
(xNCq[#]=AppendTo[xNCq[#],"Matrix"->Round[xNCq[#]["Matrix"],xNZero]])&/@xCoordinates;

x["Column Labels"]=xNC1["Column Labels"]//.SymbolReplacements;
x["Row Labels"]=Complement[xNC1["Row Labels"],{}(*xIndependentVariables*)]//.SymbolReplacements;

x["New Parameters"]={};

Function[xRowLabel,
x["Row Number"]=First@(Flatten@Position[x["Row Labels"],xRowLabel]);
x["Parameters Values"]=Flatten@(Join[Part[xNC1["Matrix"],x["Row Number"]],Join@@((Part[xNCq[#]["Matrix"],x["Row Number"]])&/@xCoordinates)]);
x["Parameters Names"]=Flatten@(Join[((Function[{xColumnLabel},Subscript[
\!\(\*OverscriptBox[\(\[CapitalDelta]\), \(_\)]\),1,xRowLabel,xColumnLabel]])/@x["Column Labels"]),Join@@(((Function[{xColumnLabel},Subscript[
\!\(\*OverscriptBox[\(\[CapitalDelta]\), \(_\)]\),#,xRowLabel,xColumnLabel]])/@x["Column Labels"])&/@(xCoordinates//.SymbolReplacements))]);
x["New Parameters:1"]=MapThread[(#2-> #1)&,{x["Parameters Values"],x["Parameters Names"]},1];
x["New Parameters:2"]=
(Flatten@(Normal@DeleteCases[Association[x["New Parameters:1"]],_Integer]));
xNTestParameters=Union[
xNTestParameters,
N[x["New Parameters:2"]]
];
x["New Parameters"]=Union[
x["New Parameters"],
(Reverse/@x["New Parameters:2"]),
(Reverse/@x["New Parameters:2"])/.((xA_->xB_ )->(-xA->-xB ) )];
]/@ x["Row Labels"];

xSC1=Association[xNC1,"Matrix"-> (xNC1["Matrix"]//.x["New Parameters"])];
(xSCq[#]=Association[xNCq[#],"Matrix"-> (xNCq[#]["Matrix"]//.x["New Parameters"])])&/@xCoordinates;

xLSOC=SAssemble[xSC1,Inner[#1\[CircleDot]#2&,xCoordinates,xSCq/@xCoordinates,SPart]];
xLSOC["Test Parameters"]=xNTestParameters;

xLSOC

];


Rotation=Function@Module[{x},

x["AxesList"]=List[##]/.{
"x"-> {1,0,0},"y"-> {0,1,0},"z"-> {0,0,1},
"X"-> {1,0,0},"Y"-> {0,1,0},"Z"-> {0,0,1}
};

Function[(TransformationMatrix@Simplify@(Dot@@(ComplexExpand[MapThread[RotationTransform,{List[##],x["AxesList"]}],TargetFunctions->{Re,Im}])))[[1;;3,1;;3]]]

];


Homogeneous=Function@Module[{x},

x["TransformList"]=List[##]/.{
"Rx"->(RotationTransform[#,{1,0,0}]&),
"Ry"->(RotationTransform[#,{0,1,0}]&),
"Rz"->(RotationTransform[#,{0,0,1}]&),
"R"[xVector_]->(RotationTransform[#,xVector]&),
"Tx"->(TranslationTransform[#{1,0,0}]&),
"Ty"->(TranslationTransform[#{0,1,0}]&),
"Tz"->(TranslationTransform[#{0,0,1}]&),
"T"[xVector_]->(TranslationTransform[# xVector]&)
};

Function[TransformationMatrix@(Simplify@Inner[(#1@#2)&,x["TransformList"],List[##],Dot])]

];


HomogToRot=#[[1;;3,1;;3]]&;
SkewToVec=If[And@@(Flatten@PossibleZeroQ[#+Transpose[#]]), {#[[3,2]],#[[1,3]],#[[2,1]]}]&;
VecToSkew={{0,-#[[3]],#[[2]]},{#[[3]],0,-#[[1]]},{-#[[2]],#[[1]],0}}&;


QuatToRot={
{#1^2-#2^2-#3^2+#4^2,2 #1 #2-2 #3 #4,2 #1 #3+2 #2 #4},
{2 #1 #2+2 #3 #4,-#1^2+#2^2-#3^2+#4^2,2 #2 #3-2 #1 #4},
{2 #1 #3-2 #2 #4,2 #2 #3+2 #1 #4,-#1^2-#2^2+#3^2+#4^2}
}&;


AngularVelocity[xRotationMatrix_List/;Dimensions[xRotationMatrix]=={3,3}]:=
Simplify@(SkewToVec@((Transpose@xRotationMatrix).D[xRotationMatrix,t]))


SetOptions[Plot,BaseStyle->{FontFamily->"Arial",FontSize->16}];
SetOptions[Plot3D,BaseStyle->{FontFamily->"Arial",FontSize->14}];
SetOptions[ParametricPlot,BaseStyle->{FontFamily->"Arial",FontSize->16}];
SetOptions[ParametricPlot3D,BaseStyle->{FontFamily->"Arial",FontSize->14}];
SetOptions[ListPlot,BaseStyle->{FontFamily->"Arial",FontSize->16}];


Style8={{Hue[0.6,1,1],Thickness[0.005]},{Hue[0.3,1,1],Thickness[0.006],Dashed},{Hue[1,1,1],Thickness[0.007],Dotted},{Hue[0.1,1,1],Thickness[0.005]},{Hue[0.9,1,1],Thickness[0.006],Dashed},{Hue[0.5,1,1],Thickness[0.007],Dotted},{Hue[0.2,1,1],Thickness[0.005]},{Hue[0.8,1,1],Thickness[0.006],Dashed}};

SPlot=Module[{st=Style8},TableForm[{Plot[#1,#2,PlotStyle->Style8,PlotRange->Full,Frame->True,FrameLabel->#3,PlotLabel->#4,GridLines->Automatic,ImageSize->1.15 {500,300}],Graphics[{Black,Directive[FontFamily->"Arial",FontSize->16],MapIndexed[Text[#1,{10(First[#2]-1)+6,0}]&,#5],MapIndexed[Join[Last[st=RotateLeft@st],{Line[{{10(First[#2]-1),0},{10(First[#2]-1)+3,0}}]}]&,#5]},ImageSize->1.15 {500,30}]}]]&;


Plot2Axis[
{xF1_,xF2_},
{xVariable_,xVariableMin_,xVariableMax_},
{xRange1_List,xRange2_List},
{xLegend1_,xLegend2_},
xFrameLabel_:{None,None},
xPlotLabel_:""
]:=
Module[{xPlot1,xPlot2,xTicks1,xTicks2},

xPlot1=Plot[
xF1,
{xVariable,xVariableMin,xVariableMax},
PlotRange->xRange1,

PlotStyle->Directive[Hue[0.6,1,1],Thick],

GridLines->Automatic,
Exclusions->Automatic,

AspectRatio->1,

PlotLegends-> Placed[
 LineLegend[{xLegend1},LegendMarkerSize->30,LabelStyle->{GrayLevel[.4],FontFamily->"Arial",FontSize->16}],
Before
]
];

xPlot2=Plot[
xF2,
{xVariable,xVariableMin,xVariableMax},
PlotRange->xRange2,

PlotStyle->Directive[Hue[0.9,1,1],Thick,Dashed],

GridLines->Automatic,

AspectRatio->1,

PlotLegends-> Placed[
 LineLegend[{xLegend2},LegendMarkerSize->30,LabelStyle->{GrayLevel[.4],FontFamily->"Arial",FontSize->16}],
Before
]
];

xTicks1=N@FindDivisions[xRange1,6];xTicks2=Quiet@Transpose@{xTicks1,ToString[NumberForm[#,2],StandardForm]&/@Rescale[xTicks1,xRange1,xRange2]};

Show[
xPlot1,xPlot2/.Graphics[xGraph_,xS___]:>Graphics[GeometricTransformation[xGraph,RescalingTransform[{{0,1},xRange2},{{0,1},xRange1}]],xS],Axes->False,
Frame->True,
FrameLabel->xFrameLabel, 
FrameStyle->{{Style8[[1,1]],Style8[[5,1]]},{Automatic,Automatic}},FrameTicks->{{xTicks1,xTicks2},{Automatic,Automatic}},
PlotLabel-> xPlotLabel
]
]


SMatrixPlot [xA_Association]:=(MatrixPlot[
xA["Matrix"],
FrameTicks->({Transpose[{Range@@Dimensions@xA["Row Labels"],xA["Row Labels"]}],Transpose[{Range@@Dimensions@xA["Column Labels"],xA["Column Labels"]}]}/.SymbolReplacements),
ColorFunction->(RGBColor[(0.00130 (1-#) +0.99985#)(2#-1)^2,(0.35656 (1-#) +0.085864#)(2#-1)^2,(0.56796(1-#))(2#-1)^2,0.13+(2#-1)^2]&),
ColorRules->{xN_/;Not@NumberQ[xN]->RGBColor[0.63521,0.99995,0.19208]}
(*FrameTicksStyle\[Rule]Directive[Orange],FrameStyle\[Rule] Directive[Orange]*)
])


SMatrixForm [xA_Association]:= (MatrixForm[xA["Matrix"],TableHeadings->({xA["Row Labels"],xA["Column Labels"]}/.SymbolReplacements)])
STableForm [xA_Association]:= (TableForm[xA["Matrix"],TableHeadings->({xA["Row Labels"],xA["Column Labels"]}/.SymbolReplacements)])
STableFormC [xA_Association]:= (TableForm[xA["Matrix"],TableHeadings->({xA["Row Labels"],xA["Column Labels"]}/.SymbolReplacements),TableAlignments->Center])
STableFormR[xA_Association]:= (TableForm[xA["Matrix"],TableHeadings->({xA["Row Labels"],xA["Column Labels"]}/.SymbolReplacements),TableAlignments->Right])


CreatePalette[Grid[Partition[PasteButton[Style[#,12],RawBoxes[#],ImageSize->{45,30}]&/@{
	"\[DiamondSuit]","\[NumberSign]","\[Section]","\[Sterling]",
	"\[DoubleStruckQ]","\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\)" ,"\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)","\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)",
	"\!\(\*TemplateBox[{UnderscriptBox[\"\[DoubleStruckQ]\", \"_\"],\"\[EmptySmallCircle]\"},\n\"Superscript\"]\)","\[DoubleStruckD]","\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)","\!\(\*UnderscriptBox[\(\[DoubleStruckD]\), \(_\)]\)",
	"\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)","\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)","\[DoubleStruckCapitalA]","\[DoubleStruckCapitalC]",
	"\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)","[\[DoubleStruckOne]\!\(\*SubscriptBox[\(]\), \(\[Placeholder]\)]\)","|","\[EmptySmallCircle]",
	"\!\(\*OverscriptBox[\(\[SelectionPlaceholder]\), \(\"\<.\>\"\)]\)","\!\(\*OverscriptBox[\(\[SelectionPlaceholder]\), \(\"\<..\>\"\)]\)","\!\(\*OverscriptBox[\(\[SelectionPlaceholder]\), \(_\)]\)","\!\(\*UnderscriptBox[\(\[SelectionPlaceholder]\), \(_\)]\)",
	"\!\(\*OverscriptBox[\(\[SelectionPlaceholder]\), \(~\)]\)","\!\(\*TemplateBox[{\"\[SelectionPlaceholder]\",\"\[Placeholder]\"},\n\"Superscript\"]\)","\!\(\*SubscriptBox[\(\[SelectionPlaceholder]\), \(\[Placeholder]\)]\)","\!\(\*OverscriptBox[\(\[SelectionPlaceholder]\), \(\[Placeholder]\)]\)",
	"(\[SelectionPlaceholder])","{\[SelectionPlaceholder]}","\[LeftDoubleBracket]\[SelectionPlaceholder]\[RightDoubleBracket]","[\[SelectionPlaceholder]]",
	"\[LeftAssociation]\[SelectionPlaceholder]\[RightAssociation]","SAssemble[\[SelectionPlaceholder]]","\"\[SelectionPlaceholder]\"","(*\[SelectionPlaceholder]*)"
	},4],Spacings->{0,0}]];


MoSs[xSystem_,xSubSystems_List:{}]:=
 Module[{xIn, xOut,xRules,xKeys, xA, xTimer},
xTimer=AbsoluteTime[];
xIn=xSystem;
xOut=If[AssociationQ[xIn],xIn, Association[]];
Quiet @(
xOut["System Label"]=xIn/.{
xX_List/;Length[xX]>= 1-> xX[[1]],
xX_Association-> xX["System Label"]
};
xOut["Subsystems Labels"]=xIn/.{
xX_Association/;KeyExistsQ[xX,"Subsystems Labels"]-> xX["Subsystems Labels"],
xX_-> {}
};
xOut["Description"]=xIn/.{
xX_List/;And[Length[xX]>= 2,StringQ[xX[[2]]]]-> xX[[2]],xX_Association/;And[KeyExistsQ[xX,"Description"],StringQ[xX["Description"]]]-> xX["Description"],
xX_-> ""
};
xOut["Replacement Rules"]=xIn/.{
xX_List/;Length[xX]>= 3-> xX[[3]],
xX_Association/;KeyExistsQ[xX,"Replacement Rules"]-> xX["Replacement Rules"],
xX_-> {}
};
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]=xIn/.{
xX_List/;Length[xX]>= 4-> xX[[4]],
xX_Association/;KeyExistsQ[xX,
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]-> xX[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)],
xX_-> {}
};
);


Quiet@(
xIn = (xSubSystems[[#]])/.{
xX_List/;AssociationQ[xX[[1]]]-> xX[[1]]
};
xRules["Replacement Rules"]=Join[
(xSubSystems[[#]])/.{
xX_List/;And[Length[xX]>= 2,Or[ListQ[xX[[2]]],AssociationQ[xX[[2]]]]]-> Normal @ (xX[[2]]),
xX_-> {}
},
xOut["Replacement Rules"]
];
xRules[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]=Join[
(xSubSystems[[#]])/.{
xX_List/;And[Length[xX]>= 3,Or[ListQ[xX[[3]]],AssociationQ[xX[[3]]]]]-> Normal @ (xX[[3]]),
xX_-> {}
},
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]
];
xIn=SRename[xIn,xRules["Replacement Rules"],xRules[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]];
(*Association@MapThread[
#1\[Rule] #2&,
{If[Head[#]===String,StringReplace[#,xRules["Replacement Rules"]],#]&/@(First/@Normal @ (xIn)),
Map[SReplaceRepeated[#,xRules[Underscript[\[DoubleStruckR], _]]]&,Map[SReplaceRepeated[#,xRules["Replacement Rules"]]&, Map[SReplaceRepeated[#,xRules[Underscript[\[DoubleStruckR], _]]]&,(Last/@Normal @ xIn),All],All],All]},
1];*)
xOut["Subsystems Labels"]=Union[xOut["Subsystems Labels"],{xIn["System Label"]}];
xOut[xIn["System Label"]]=xIn;
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]=Union[xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)],xRules[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]];
)&/@ Range @ (Length @ xSubSystems);

xIn=xOut;

xOut["\[DoubleStruckQ]:Order"]=If[KeyExistsQ[xIn,"\[DoubleStruckQ]:Order"], xIn["\[DoubleStruckQ]:Order"], Max @ (((xIn[#]["\[DoubleStruckQ]:Order"])&/@ xIn["Subsystems Labels"])//.Missing[xX__]-> {})];

(
If[xIn[#]["\[DoubleStruckQ]:Order"]< xOut["\[DoubleStruckQ]:Order"], xIn[#]["\[DoubleStruckQ]:Order"]= xOut["\[DoubleStruckQ]:Order"]];
xOut[#]=MoSs[xIn[#]];
)&/@ xIn["Subsystems Labels"];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:Subsystems:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=Part[#,1]& /@ Union@(Flatten@{(Select[Keys @ xIn,Part[#,0]==\[DoubleStruckQ]&])});
If[Not@(xKeys==={}),
xIn["\[DoubleStruckQ]:Def:Order:In"]=If[KeyExistsQ[xIn,"\[DoubleStruckQ]:Def:Order"], xIn["\[DoubleStruckQ]:Def:Order"], Max @ ToExpression @ Flatten @ (StringSplit[#,{":","|"}]& /@  xKeys)];
(xIn[\[DoubleStruckQ][ToString @ #]]=D[xIn[\[DoubleStruckQ][ToString @  xIn["\[DoubleStruckQ]:Def:Order:In"]]],{t,(#-xIn["\[DoubleStruckQ]:Def:Order:In"])}])& /@  
Complement[Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]],Range[0, xIn["\[DoubleStruckQ]:Def:Order:In"]]];
];

xKeys=Part[#,1]& /@ Union@(Flatten@{(Select[Keys @ xIn,Part[#,0]==\[DoubleStruckQ]&]),(Select[Keys @ xIn[#],Part[#,0]==\[DoubleStruckQ]&])&/@ xIn["Subsystems Labels"]});
xOut["\[DoubleStruckQ]:Def:Order"]=If[KeyExistsQ[xIn,"\[DoubleStruckQ]:Def:Order"], xIn["\[DoubleStruckQ]:Def:Order"], Max @ ToExpression @ Flatten @ (StringSplit[#,{":","|"}]& /@  xKeys)];
Function[xKey,
xOut[\[DoubleStruckQ][xKey]]=(Union @ (Flatten@
({xIn[\[DoubleStruckQ][xKey]],Function[xSub,xIn[xSub][\[DoubleStruckQ][xKey]]]/@xIn["Subsystems Labels"]}//.Missing[xX__]-> {})
))
]/@ xKeys;
Function[xKey,
xIn[\[DoubleStruckQ][xKey]]=Complement[xOut[\[DoubleStruckQ][xKey]]//.Missing[xX__]-> {},(Union @ (Flatten@
({Function[xSub,xIn[xSub][\[DoubleStruckQ][xKey]]]/@xIn["Subsystems Labels"]}//.Missing[xX__]-> {})
))]
]/@ xKeys;

(* xOut["\[DoubleStruckQ]:Def:Order"]=If[KeyExistsQ[xIn,"\[DoubleStruckQ]:Def:Order"], xIn["\[DoubleStruckQ]:Def:Order"], Max @ ToExpression @ Flatten @ (StringSplit[#,{":","|"}]& /@  xKeys)];
Print[ xOut["\[DoubleStruckQ]:Def:Order"]];*)

(xOut[\[DoubleStruckQ][ToString @ #]]=D[xOut[\[DoubleStruckQ][ToString @  xOut["\[DoubleStruckQ]:Def:Order"]]],{t,(#-xOut["\[DoubleStruckQ]:Def:Order"])}])& /@  
Complement[Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]],Range[0, xOut["\[DoubleStruckQ]:Def:Order"]]];

xKeys=
Union[ReplaceRepeated[#,{{xX_,xY_}:>( ToString[xX]<>"|"<>ToString[xY])}]& @
(Select[Flatten[#,1],(Part[#,1]>Part[#,2])&]& @(Outer[List,#,#]))
]& @ Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]];
(xOut[\[DoubleStruckQ][#]]=
D[xOut[\[DoubleStruckQ][Part[#,2]]]//.Missing[xX__]-> {},{t,((ToExpression @ Part[#,1])-(ToExpression @ Part[#,2]))}]& @ StringSplit[#,{":","|"}];
)& /@  xKeys;

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckQ]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=Part[#,1]& /@ Union@(Flatten@{(Select[Keys @ xIn,Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)&]),(Select[Keys @ xIn[#],Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)&])&/@ xIn["Subsystems Labels"]});
Function[xKey,
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[xKey]]=(Union @ (Flatten@
({xIn[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[xKey]],Function[xSub,xIn[xSub][
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[xKey]]]/@xIn["Subsystems Labels"]}//.Missing[xX__]-> {})
))
]/@ xKeys;
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[#]]={})& /@Complement[ToString /@ Range[0,xOut["\[DoubleStruckQ]:Order"]], xKeys];

xRules=(Union @ (Flatten@
({xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],Function[xSub,xIn[xSub][
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]]/@xIn["Subsystems Labels"]}//.Missing[xX__]-> {})
));
(xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]]=
(Union @ (Flatten@
({xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]],
Function[xSub,xIn[xSub][
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]]]/@xIn["Subsystems Labels"]}//.Missing[xX__]-> {})
));
If[And[(*Not @ KeyExistsQ[xIn,Underscript[\[DoubleStruckQ], _][(ToString @ #)<> "|"<>(ToString @ (#-1))]],*)
Length[Complement[xOut[\[DoubleStruckQ][(ToString @ #)<> "|"<>(ToString @ (#-1))]],xOut[\[DoubleStruckQ][ToString @ #]],First/@ xRules]]>0],
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]]=
Union @@ {
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]],
(Simplify @ Flatten @ 
(Quiet @ 
Solve[
(#==0)&/@(RedundantElim @((RedundantElim @( Union @@ {D[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[ToString @ (#-1)]],t],xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[ToString @ #]]}//.xRules))//.xRules)),
Complement[Complement[xOut[\[DoubleStruckQ][(ToString @ #)<> "|"<>(ToString @ (#-1))]],xOut[\[DoubleStruckQ][ToString @ #]]],First/@ xRules]
]))//.xRules
}
];
xRules=Union@@{xRules,xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[(ToString @ #)<> "|"<>(ToString @ (#-1))]]};
)& /@ Range[1, xOut["\[DoubleStruckQ]:Def:Order"]];
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Union[xRules,xRules/.{(xA_-> xB_)-> (-xA-> -xB)}];
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]=Union[#,#/.{(xA_-> xB_)-> (-xA-> -xB)}]& @ (Union[#,#/.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]]& @ xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]);

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xA={};
(*If[And[KeyExistsQ[xIn,\[DoubleStruckD]],Not @(xIn[\[DoubleStruckD]]["InputQ"]===False)], AppendTo[xA,xIn[\[DoubleStruckD]]]];*)
If[KeyExistsQ[xIn,\[DoubleStruckF]], AppendTo[xA,xIn[\[DoubleStruckF]]]];
If[KeyExistsQ[xOut[#],
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)],AppendTo[xA,xOut[#][
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]]]&/@xIn["Subsystems Labels"];
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]=xOut[\[DoubleStruckD]]=SAssemble[##]& @@ (RedundantElim @ xA);

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckD]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=Part[#,1]& /@ (Select[Keys @ xIn,Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)&]);

If [Length[xKeys]>0,

xKeys=Part[#,1]& /@Select[Keys @ xIn,Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)&];(*Part[#,1]& /@ Union@(Flatten@{(Select[Keys @ xIn,Part[#,0]\[Equal]Overscript[\[DoubleStruckQ], _]&]),(Select[Keys @ xIn[#],Part[#,0]\[Equal]Overscript[\[DoubleStruckQ], _]&])&/@ xIn["Subsystems Labels"]});*)
 xOut["\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):Def:Order"]=If[KeyExistsQ[xIn,"\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):Def:Order"], xIn["\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):Def:Order"], Max @ ToExpression @ Flatten @ (StringSplit[#,{":","|"}]& /@  xKeys)];
Function[xKey,
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[xKey]]=(xIn[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[xKey]]//.Missing[xX__]-> {});
]/@ xKeys;
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]={})& /@Complement[ToString /@ Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"],xOut["\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):Def:Order"]]], xKeys];

If[Not @ (xOut["\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)?"]==="No"),
xKeys=Part[#,1]& /@ (Select[Keys @ xOut,Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)&]);
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]=(Union @@ ({xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]],xIn[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)[#]]}//.Missing[xX__]-> {})))& /@ xKeys;

(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ #]]=(RedundantElim @(( Union @@ {D[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ (#-1)]],t],xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ #]]})//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]));
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ #]]=Union@(RedundantElim@(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ #]]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]));
)& /@ Range[1,Max[2,xOut["\[DoubleStruckQ]:Order"]]];
,
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @ #]]=D[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[ToString @  (#-1)]],t]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)])& /@(Complement[Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]],Range[0, xOut["\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):Def:Order"]]]);
];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=(ToString @ xOut["\[DoubleStruckQ]:Order"]);
xA={};
If[And[KeyExistsQ[xIn,\[DoubleStruckQ][xKeys]],Length[xIn[\[DoubleStruckQ][xKeys]]]>0],
 AppendTo[xA,Jacobi[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[xKeys]],xIn[\[DoubleStruckQ][xKeys]]]]
];
If[And[KeyExistsQ[xOut[#],\[DoubleStruckQ][xKeys]],Length[xOut[#][\[DoubleStruckQ][xKeys]]]>0],
If[KeyExistsQ[xOut[#],Subscript[\[DoubleStruckCapitalC], \[NumberSign]]],
AppendTo[xA,Jacobi[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[xKeys]],xOut[#][\[DoubleStruckQ][xKeys]]]\[CircleDot]xOut[#][Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]],
AppendTo[xA,Jacobi[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[xKeys]],xOut[#][\[DoubleStruckQ][xKeys]]]]
]
]&/@xIn["Subsystems Labels"];
xOut[\[DoubleStruckCapitalA]]=SAssemble[##]& @@ xA;

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckCapitalA]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

If[Not @ (xOut["\[DoubleStruckCapitalC]?"]==="No"),
If[KeyExistsQ[xOut,Subscript[\[DoubleStruckQ], \[NumberSign]][#]],
xOut[\[DoubleStruckCapitalC]]=OrthogonalComplement[xOut[\[DoubleStruckCapitalA]],xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][#]]],
xOut[\[DoubleStruckCapitalC]]=OrthogonalComplement[xOut[\[DoubleStruckCapitalA]],ToString @ xOut["System Label"]]
] & @ (ToString @ xOut["\[DoubleStruckQ]:Order"]);
xA={};
(*If[KeyExistsQ[xOut[#],\[DoubleStruckCapitalC]],AppendTo[xA,xOut[#][\[DoubleStruckCapitalC]]]]&/@xIn["Subsystems Labels"];*)
If[KeyExistsQ[xOut[#],Subscript[\[DoubleStruckCapitalC], \[NumberSign]]],AppendTo[xA,xOut[#][Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]]]&/@xIn["Subsystems Labels"];
If[xA==={},
xOut[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]=xOut[\[DoubleStruckCapitalC]],
If[Not @ (#==={}),AppendTo[xA,<|"Matrix"-> IdentityMatrix[Length @ #],"Row Labels"->#,"Column Labels"->  #|>]]& @ Complement[xOut[\[DoubleStruckCapitalC]]["Row Labels"](*(xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][ToString @ xOut["\[DoubleStruckQ]:Order"]]])*),Union@@(((xOut[#][Subscript[\[DoubleStruckQ], \[NumberSign]][ToString @ xOut["\[DoubleStruckQ]:Order"]]])&/@xIn["Subsystems Labels"])//.Missing[xX__]-> {})];
xOut[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]=(SAssemble[##]& @@xA)\[CircleDot]xOut[\[DoubleStruckCapitalC]]];
If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckCapitalC]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];
];

If[And[KeyExistsQ[xOut,\[DoubleStruckD]],KeyExistsQ[xOut,\[DoubleStruckCapitalC]],Complement[SAssemble[xOut[\[DoubleStruckD]]]["Row Labels"],SAssemble[xOut[\[DoubleStruckCapitalC]]]["Row Labels"]]==={}],
xKeys=Complement[SAssemble[xOut[\[DoubleStruckCapitalC]]]["Row Labels"],SAssemble[xOut[\[DoubleStruckD]]]["Row Labels"]];
If[Not @ (xKeys ==={}),
xOut[\[DoubleStruckD]]=SAssemble[
xOut[\[DoubleStruckD]],
<|"Matrix"-> ({0}&/@ (Range @ (Length @ xKeys))),"Column Labels"->{""},"Row Labels"->xKeys|>
]];
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]=STranspose[xOut[\[DoubleStruckCapitalC]]]\[CircleDot]xOut[\[DoubleStruckD]];
If[xOut["Explicit EOM"]==="Yes",
(xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckD]\), \(_\)]\)[#]]=SReplaceFullSimplify[
Solve[(#==0)&/@Flatten@(Union@@{SAssemble[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]]["Matrix"],xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]}),xOut[\[DoubleStruckQ][#]]],
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]
])& @ (ToString @ (Max[2,xOut["\[DoubleStruckQ]:Order"]]));
If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*UnderscriptBox[\(\[DoubleStruckD]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];
];
] (*,
xOut[Overscript[\[DoubleStruckD], _]]=xOut[\[DoubleStruckD]]*)
];

(*If[Not @(xOut["Subsystems Labels"]==={}),
xOut[Overscript[\[DoubleStruckD], _]]["InputQ"]=xOut[\[DoubleStruckD]]["InputQ"]=False
];*)

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];
If[xOut["Timer"]==="On",Print[StringForm["``:``:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xOut
]


ReferenceMotion[xSystem_,xReferenceValues_:{}]:=
Module[{xOut,xKeys,xVariables},
xKeys=Part[#,1]& /@ Union@(Flatten@{(Select[Keys @ xSystem,Part[#,0]==\[DoubleStruckQ]&]),(Select[Keys @ xSystem[#],Part[#,0]==\[DoubleStruckQ]&])&/@ xSystem["Subsystems Labels"]});
xVariables=Union @@ (Function[xKey,(Union @@ (
({xSystem[\[DoubleStruckQ][xKey]],Union @@ (Function[xSub,xSystem[xSub][\[DoubleStruckQ][xKey]]]/@xSystem["Subsystems Labels"])}//.Missing[xX__]-> {})))]/@ xKeys);xOut=Association@(Flatten@Outer[(#1-> #2)&,(Superscript[#,\[EmptySmallCircle]])&/@(xVariables/.SymbolReplacements),{0}]);
AssociateTo[xOut,(Superscript[First[#],\[EmptySmallCircle]]-> Last[#])&/@(xReferenceValues/.SymbolReplacements)];
xOut//Normal
]


LinearExpansion[xE_]={

Derivative[2][Subscript[Subscript[xX_,xId__],xId2__]][t]->
Superscript[Subscript[Subscript[Overscript[xX,".."],xId],xId2],\[EmptySmallCircle]]
+xE Derivative[2][Subscript[Subscript[xX,xId],xId2]][t],

Derivative[1][Subscript[Subscript[xX_,xId__],xId2__]][t]->
Superscript[Subscript[Subscript[Overscript[xX,"."],xId],xId2],\[EmptySmallCircle]]
+xE Derivative[1][Subscript[Subscript[xX,xId],xId2]][t],

Subscript[Subscript[xX_,xId__],xId2__][t]->
Superscript[Subscript[Subscript[xX,xId],xId2],\[EmptySmallCircle]]
+xE Subscript[Subscript[xX,xId],xId2][t],

Derivative[2][Subscript[xX_,xId__]][t]->
Superscript[Subscript[Overscript[xX,".."],xId],\[EmptySmallCircle]]
+xE Derivative[2][Subscript[xX,xId]][t],

Derivative[1][Subscript[xX_,xId__]][t]->
Superscript[Subscript[Overscript[xX,"."],xId],\[EmptySmallCircle]]
+xE Derivative[1][Subscript[xX,xId]][t],

Subscript[xX_,xId__][t]->
Superscript[Subscript[xX,xId],\[EmptySmallCircle]]
+xE Subscript[xX,xId][t],

Derivative[2][Subscript[xX_,xId__]][t]->
Superscript[Subscript[Overscript[xX,".."],xId],\[EmptySmallCircle]]
+xE Derivative[2][Subscript[xX,xId]][t],

Derivative[1][Subscript[xX_,xId__]][t]->
Superscript[Subscript[Overscript[xX,"."],xId],\[EmptySmallCircle]]
+xE Derivative[1][Subscript[xX,xId]][t],

Subscript[xX_,xId__][t]->
Superscript[Subscript[xX,xId],\[EmptySmallCircle]]
+xE Subscript[xX,xId][t],

Derivative[2][xX_][t]->
Superscript[Overscript[xX,".."],\[EmptySmallCircle]]
+xE Derivative[2][xX][t],

Derivative[1][xX_][t]->
Superscript[Overscript[xX,"."],\[EmptySmallCircle]]
+xE Derivative[1][xX][t],

xX_[t]->
 Superscript[xX,\[EmptySmallCircle]]
+xE xX[t]

};


Linearize[xA_Association,xReferenceMotion_:{}]:=
Association["Matrix"-> ((Series[((((xA["Matrix"])/.LinearExpansion[xE])/.xReferenceMotion)/.{Superscript[xX_,\[EmptySmallCircle]]-> 0}),{xE,0,1}]//Normal)/.{xE-> 1}),
"Row Labels"-> xA["Row Labels"],
"Column Labels"-> xA["Column Labels"]
];

Linearize[xL_,xReferenceMotion_:{}]:=((Series[(((xL/.LinearExpansion[xE])/.xReferenceMotion)/.{Superscript[xX_,\[EmptySmallCircle]]-> 0}),{xE,0,1}]//Normal)/.{xE-> 1});


LinearizeSystem[xSystem_,xReferenceValues_:{},xLinSubsystemsModels_:Association[],xExtraRules_:{}]:=
Module[{xIn,xOut,xReferenceMotion,xKeys, xA,xTimer},
xTimer=AbsoluteTime[];

xIn=xOut=MoSs @ xSystem;
(xOut[#]=xLinSubsystemsModels[#])&/@ Intersection[xOut["Subsystems Labels"],Keys[xLinSubsystemsModels]];
(xOut[#]=LinearizeSystem[xIn[#],xReferenceValues,xExtraRules])&/@Complement[xOut["Subsystems Labels"],Keys[xLinSubsystemsModels]];
xReferenceMotion=ReferenceMotion[xIn,xReferenceValues];
xOut[Superscript[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\),\[EmptySmallCircle]]]=xReferenceMotion;

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*TemplateBox[{UnderscriptBox[\"\[DoubleStruckQ]\", \"_\"],\"\[EmptySmallCircle]\"},\n\"Superscript\"]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=First/@(Select[Keys @ xIn,Part[#,0]==Subscript[\[DoubleStruckQ], \[NumberSign]]&]);
xOut["\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"]=If[KeyExistsQ[xIn,"\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"], xIn["\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"], Max @ ToExpression @ Flatten @ (StringSplit[#,{":","|"}]& /@  xKeys)];

(xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][ToString @ #]]=D[xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][ToString @  xOut["\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"]]],{t,(#-xOut["\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"])}])& /@  
Complement[Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]],Range[0, xOut["\!\(\*SubscriptBox[\(\[DoubleStruckQ]\), \(\[NumberSign]\)]\):Def:Order"]]];

xKeys=
Union[ReplaceRepeated[#,{{xA_,xB_}:>( ToString[xA]<>"|"<>ToString[xB])}]& @
(Select[Flatten[#,1],(Part[#,1]>Part[#,2])&]& @(Outer[List,#,#]))
]& @ Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]];
(xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][#]]=
D[xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][Part[#,2]]],{t,((ToExpression @ Part[#,1])-(ToExpression @ Part[#,2]))}]& @ StringSplit[#,{":","|"}]
)& /@  xKeys;

xKeys=Part[#,1]& /@ Union@(Select[Keys @ xIn,Part[#,0]==
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)&]);
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]=Linearize[xIn[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]//.xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],xReferenceMotion]//.xExtraRules)&/@ xKeys;
(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]={})& /@Complement[ToString /@ Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]], xKeys];

xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Union@@(((xOut[#][
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)])&/@xOut["Subsystems Labels"])//.Missing[xX__]-> {});

xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Union @@ {
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],
Union[#,#/.{(xA_-> xB_)-> (-xA-> -xB)}]& @(((#-> 0)&/@RedundantElim@((Union @@ (xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]&/@ xKeys))//.{xX_[t]-> 0}//.xExtraRules))/.{({}-> 0)-> {}})
};

xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Union @@ {
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],
((#-> 0)&/@(RedundantElim @((Linearize[xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]/.{(xX_-> xY_)-> xX-xY},xReferenceMotion]//.xExtraRules)//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)])))
};

(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]=xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules)&/@ xKeys;

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xKeys=Part[#,1]& /@ Union@(Select[Keys @ xIn,Part[#,0]==
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)&]);
Module[{xFirst,xLast},
xFirst=Linearize[(First/@xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules;
xLast=Linearize[(Last/@xIn[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules;
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]=MapThread[(#1-(#1//.{xX_[t]-> 0}))->(#2-(#2//.{xX_[t]-> 0}))&,{xFirst,xLast},1];
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Select[
Union @@ {
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]],
Union[#,#/.{(xA_-> xB_)-> (-xA-> -xB)}]& @ MapThread[#1-> #2&,{xFirst,xLast}//.{xX_[t]-> 0},1]
},
(Not@(First[#]-Last[#]===0))&];
]&/@ xKeys;

Module[{xEquations},
xEquations=RedundantElim @(xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]);
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]=If[Or[xEquations==={},SetComplement[xIn[\[DoubleStruckQ][#]],xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][#]]]==={}],{},
Function[{xX},
MapThread[(#1-> #2)&,{xX,(Flatten@(-LinearSolve@@Reverse@CoefficientArrays[xEquations,xX]))},1]
] @SetComplement[Intersection[xIn[\[DoubleStruckQ][#]],GetVariables @ xEquations],xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][#]]]//.xExtraRules];
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]=Complement[Union @@ {xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)],xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]},{0->0}];
]& /@(ToString/@ Range[0,Max[2,xOut["\[DoubleStruckQ]:Order"]]]);

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

If[KeyExistsQ[xIn,\[DoubleStruckCapitalA]],
xOut[\[DoubleStruckCapitalA]]=Association[
"Matrix"-> Simplify@(Linearize[xIn[\[DoubleStruckCapitalA]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules),
"Column Labels"-> xIn[\[DoubleStruckCapitalA]]["Column Labels"],
"Row Labels"-> xIn[\[DoubleStruckCapitalA]]["Row Labels"]
];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckCapitalA]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

If[KeyExistsQ[xIn,\[DoubleStruckCapitalC]],
xOut[\[DoubleStruckCapitalC]]=Association[
"Matrix"-> Simplify@(Linearize[xIn[\[DoubleStruckCapitalC]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules),
"Column Labels"-> xIn[\[DoubleStruckCapitalC]]["Column Labels"],
"Row Labels"-> xIn[\[DoubleStruckCapitalC]]["Row Labels"]
],
xOut[\[DoubleStruckCapitalC]]=LSLinearizedOrthogonalComplement[xOut[\[DoubleStruckCapitalA]],xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][(ToString @xOut["\[DoubleStruckQ]:Order"])]],xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]]
];

If[KeyExistsQ[xIn,Subscript[\[DoubleStruckCapitalC], \[NumberSign]]],
xOut[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]=Association[
"Matrix"-> Simplify@(Linearize[xIn[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules),
"Column Labels"-> xIn[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]["Column Labels"],
"Row Labels"-> xIn[Subscript[\[DoubleStruckCapitalC], \[NumberSign]]]["Row Labels"]
]
];
];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\[DoubleStruckCapitalC]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

xA={};
xKeys=ToString/@Range[xOut["\[DoubleStruckQ]:Order"],(Max[2,xOut["\[DoubleStruckQ]:Order"]])];
If[KeyExistsQ[xIn,\[DoubleStruckF]],
xOut[\[DoubleStruckF]]=Association[
"Matrix"->Collect[
Simplify@(Linearize[xIn[\[DoubleStruckF]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules),
Union@@(xOut[\[DoubleStruckQ][#]]&/@xKeys), Simplify],
"Column Labels"-> xIn[\[DoubleStruckF]]["Column Labels"],
"Row Labels"-> xIn[\[DoubleStruckF]]["Row Labels"]
];
 AppendTo[xA,xOut[\[DoubleStruckF]]];
];
If[KeyExistsQ[xOut[#],
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)],
AppendTo[xA,SApply[(#//.xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]//.xExtraRules)&,xOut[#][
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]]]
]&/@xIn["Subsystems Labels"];
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]=xOut[\[DoubleStruckD]]=SAssemble[##]& @@ (RedundantElim @ xA);

If[And[KeyExistsQ[xOut,\[DoubleStruckD]],KeyExistsQ[xOut,\[DoubleStruckCapitalC]],Complement[SAssemble[xOut[\[DoubleStruckD]]]["Row Labels"],SAssemble[xOut[\[DoubleStruckCapitalC]]]["Row Labels"]]==={}],
xKeys=Complement[SAssemble[xOut[\[DoubleStruckCapitalC]]]["Row Labels"],SAssemble[xOut[\[DoubleStruckD]]]["Row Labels"]];
If[Not @ (xKeys ==={}),
xOut[\[DoubleStruckD]]=SAssemble[
xOut[\[DoubleStruckD]],
<|"Matrix"-> ({0}&/@ (Range @ (Length @ xKeys))),"Column Labels"->{""},"Row Labels"->xKeys|>
]];
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]=Linearize @ (STranspose[xOut[\[DoubleStruckCapitalC]]]\[CircleDot]xOut[\[DoubleStruckD]]);
If[xOut["Explicit Linearized EOM"]==="Yes",
(xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckD]\), \(_\)]\)[#]]=SReplaceFullSimplify[
Solve[(#==0)&/@Flatten@(Union@@{SAssemble[xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]]["Matrix"],xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]}),xOut[\[DoubleStruckQ][#]]],
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckR]\), \(_\)]\)]
])& @ (ToString @ (Max[2,xOut["\[DoubleStruckQ]:Order"]]));
If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*UnderscriptBox[\(\[DoubleStruckD]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];
];
];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\):OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

(*xOut[\[DoubleStruckD]]=Association[
"Matrix"\[Rule]Collect[
Simplify@(Linearize[xIn[\[DoubleStruckD]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[Underscript[\[DoubleStruckC], _]]//.xExtraRules),
Union@@(xOut[\[DoubleStruckQ][#]]&/@xKeys), Simplify],
"Column Labels"\[Rule] xIn[\[DoubleStruckD]]["Column Labels"],
"Row Labels"\[Rule] xIn[\[DoubleStruckD]]["Row Labels"]
];
xOut[Overscript[\[DoubleStruckD], _]]=Association[
"Matrix"\[Rule]Collect[
Simplify@(Linearize[xIn[Overscript[\[DoubleStruckD], _]]["Matrix"](*//.xIn[Underscript[\[DoubleStruckC], _]]*),xReferenceMotion]//.xOut[Underscript[\[DoubleStruckC], _]]//.xExtraRules),
Union@@(xOut[\[DoubleStruckQ][#]]&/@xKeys), Simplify],
"Column Labels"\[Rule] xIn[Overscript[\[DoubleStruckD], _]]["Column Labels"],
"Row Labels"\[Rule] xIn[Overscript[\[DoubleStruckD], _]]["Row Labels"]
];
If[And[KeyExistsQ[xIn,\[DoubleStruckCapitalA]],Not @ KeyExistsQ[xIn,\[DoubleStruckCapitalC]]],
xOut[Overscript[\[DoubleStruckD], _]]=Linearize@(STranspose[xOut[\[DoubleStruckCapitalC]]]\[CircleDot]xOut[\[DoubleStruckD]])
];

If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:Overscript[\[DoubleStruckD], _]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];

If[xOut["Explicit Linearized EOM"]==="Yes",
(xOut[Underscript[\[DoubleStruckD], _][#]]=SReplaceFullSimplify[
Solve[(#\[Equal]0)&/@Flatten@(Union@@{SAssemble[xOut[Overscript[\[DoubleStruckD], _]]]["Matrix"]}),xOut[Subscript[\[DoubleStruckQ], \[NumberSign]][#]]],
xOut[Underscript[\[DoubleStruckR], _]]
])& @ (ToString @ (Max[2,xOut["\[DoubleStruckQ]:Order"]]));
If[xOut["Debug Mode"]==="On",Print[StringForm["``:``:Underscript[\[DoubleStruckD], _]:OK",NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}],xOut["System Label"]]]];
];*)

xOut["\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\):\[DoubleStruckQ]"]=Union @ (GetVariables @ xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]);
xOut["System Parameters"]=Union @@{
Union @@ (xOut[#]["System Parameters"]&/@xOut["Subsystems Labels"]),
RedundantElim @(Quiet @ GetAllVariables[Join@@{xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]["Matrix"],Join @@ (xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)[#]]&/@(ToString/@Range[0,xOut["\[DoubleStruckQ]:Order"]]))}]//.xX_[t]-> 0)};

If[xOut["Timer"]==="On",Print[StringForm["``:``:OK",(NumberForm[Round[AbsoluteTime[]-xTimer,0.01],{5,2}]),xOut["System Label"]]]];

xOut
];


ParametersEval[xSystem_Association,xPhysicalParameters_List,xExtraRules_List:{}]:=
Module[{xAuxiliarParameters,xInvariants,xVariables,xCoeffA,xVarA,xCoeffC,xVarC},

{xCoeffA,xVarA}=SMatrixCoefficientArrays@(xSystem[\[DoubleStruckCapitalA]]);
{xCoeffC,xVarC}=SMatrixCoefficientArrays@(xSystem[\[DoubleStruckCapitalC]]);

xInvariants=Expand/@RedundantElim@(Expand/@(Flatten@(SAssemble[xCoeffA[1]\[CircleDot]xCoeffC[1]]["Matrix"])//.xExtraRules//.xPhysicalParameters));
xVariables=Union@GetAllVariables[xInvariants];
xAuxiliarParameters=Union@
MapThread[#1-> #2&,{xVariables,-LeastSquares@@(Reverse@CoefficientArrays[xInvariants,xVariables])},1];

(
xInvariants=Expand/@RedundantElim@(Chop@(Expand/@(Flatten@(SAssemble[xCoeffA[1]\[CircleDot]xCoeffC[#],xCoeffA[#]\[CircleDot]xCoeffC[1]]["Matrix"])//.xExtraRules//.xPhysicalParameters//.xAuxiliarParameters)));
xVariables=Union@GetAllVariables[xInvariants];
If[Not[xInvariants==={}],
xAuxiliarParameters=Union[
xAuxiliarParameters,
MapThread[#1-> #2&,{xVariables,-LeastSquares@@(Reverse@CoefficientArrays[xInvariants,xVariables])},1]
]
];
)&/@xVarC;

Union[xPhysicalParameters,xAuxiliarParameters]
];


NewtonEuler[
xLabel_,
xPositionOrientationDescription_String:"None",
xGravitationalField_:"Default",
xInertiaSymmetry_:"Central",
xExternalActiveTorque_List:{0,0,0},
xExternalActiveForce_List:{0,0,0}
]:=
Module[{xOut},
xOut=<|
"System Label"-> xLabel,
"Description"-> ToString @ StringForm["Newton-Euler equations of the free rigid body ``",xLabel],
"\[DoubleStruckQ]:Order"-> 1
|>;

xOut[\[DoubleStruckQ]["1"]]=xOut[Subscript[\[DoubleStruckQ], \[NumberSign]]["1"]]={
Subscript[v, xLabel,"x"][t],Subscript[v, xLabel,"y"][t],Subscript[v, xLabel,"z"][t],
Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]
};


If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"POSITION"~~___],
xOut[\[DoubleStruckQ]["0"]]={
Subscript[p, xLabel,"x"][t],Subscript[p, xLabel,"y"][t],Subscript[p, xLabel,"z"][t]
};
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)["1"]]={
Subscript[v, xLabel,"x"][t]-Subscript[p, xLabel,"x"]'[t],
Subscript[v, xLabel,"y"][t]-Subscript[p, xLabel,"y"]'[t],
Subscript[v, xLabel,"z"][t]-Subscript[p, xLabel,"z"]'[t]
};
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)["1|0"]]={
Subscript[p, xLabel,"x"]'[t]->Subscript[v, xLabel,"x"][t],
Subscript[p, xLabel,"y"]'[t]->Subscript[v, xLabel,"y"][t],
Subscript[p, xLabel,"z"]'[t]->Subscript[v, xLabel,"z"][t]
};
];

If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"QUATERNION"~~___],
xOut[\[DoubleStruckQ]["0"]]={
Subscript[p, xLabel,"x"][t],Subscript[p, xLabel,"y"][t],Subscript[p, xLabel,"z"][t],
Subscript[q, xLabel,"x"][t],Subscript[q, xLabel,"y"][t],Subscript[q, xLabel,"z"][t],Subscript[q, xLabel,"t"][t]
};
xOut[ToString @ StringForm["[\[DoubleStruckOne]\!\(\*SubscriptBox[\(]\), \(\[ScriptCapitalN] | ``\)]\)",xLabel]]=QuatToRot@@{
Subscript[q, xLabel,"x"][t],Subscript[q, xLabel,"y"][t],Subscript[q, xLabel,"z"][t],Subscript[q, xLabel,"t"][t]
};
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckC]\), \(_\)]\)]={
Subscript[q, xLabel,"t"][t]^2+Subscript[q, xLabel,"x"][t]^2+Subscript[q, xLabel,"y"][t]^2+Subscript[q, xLabel,"z"][t]^2-> 1,
1/2 Subscript[q, xLabel,"t"][t]^2+1/2 Subscript[q, xLabel,"x"][t]^2+1/2 Subscript[q, xLabel,"y"][t]^2+1/2 Subscript[q, xLabel,"z"][t]^2-> 1/2,
1-(Subscript[q, xLabel,"x"][t]^2+Subscript[q, xLabel,"y"][t]^2+Subscript[q, xLabel,"z"][t]^2)-> Subscript[q, xLabel,"t"][t]^2
};
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)["0"]]={
-1+Subscript[q, xLabel,"t"][t]^2+Subscript[q, xLabel,"x"][t]^2+Subscript[q, xLabel,"y"][t]^2+Subscript[q, xLabel,"z"][t]^2
};
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)["1"]]={
Subscript[v, xLabel,"x"][t]-Subscript[p, xLabel,"x"]'[t],
Subscript[v, xLabel,"y"][t]-Subscript[p, xLabel,"y"]'[t],
Subscript[v, xLabel,"z"][t]-Subscript[p, xLabel,"z"]'[t],
Subscript[\[Omega], xLabel,"z"][t]+2 Subscript[q, xLabel,"z"][t] Subscript[q, xLabel,"t"]'[t]+2 Subscript[q, xLabel,"y"][t] Subscript[q, xLabel,"x"]'[t]-2 Subscript[q, xLabel,"x"][t] Subscript[q, xLabel,"y"]'[t]-2 Subscript[q, xLabel,"t"][t] Subscript[q, xLabel,"z"]'[t],
Subscript[\[Omega], xLabel,"y"][t]+2 Subscript[q, xLabel,"y"][t] Subscript[q, xLabel,"t"]'[t]-2 Subscript[q, xLabel,"z"][t] Subscript[q, xLabel,"x"]'[t]-2 Subscript[q, xLabel,"t"][t] Subscript[q, xLabel,"y"]'[t]+2 Subscript[q, xLabel,"x"][t] Subscript[q, xLabel,"z"]'[t],
Subscript[\[Omega], xLabel,"x"][t]+2 Subscript[q, xLabel,"x"][t] Subscript[q, xLabel,"t"]'[t]-2 Subscript[q, xLabel,"t"][t] Subscript[q, xLabel,"x"]'[t]+2 Subscript[q, xLabel,"z"][t] Subscript[q, xLabel,"y"]'[t]-2 Subscript[q, xLabel,"y"][t] Subscript[q, xLabel,"z"]'[t]
};
xOut[
\!\(\*UnderscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)["1|0"]]={
Subscript[p, xLabel,"x"]'[t]->Subscript[v, xLabel,"x"][t],
Subscript[p, xLabel,"y"]'[t]->Subscript[v, xLabel,"y"][t],
Subscript[p, xLabel,"z"]'[t]->Subscript[v, xLabel,"z"][t],Subscript[q, xLabel,"t"]'[t]->1/2 (-Subscript[q, xLabel,"x"][t] Subscript[\[Omega], xLabel,"x"][t]-Subscript[q, xLabel,"y"][t] Subscript[\[Omega], xLabel,"y"][t]-Subscript[q, xLabel,"z"][t] Subscript[\[Omega], xLabel,"z"][t]),Subscript[q, xLabel,"x"]'[t]->1/2 (Subscript[q, xLabel,"t"][t] Subscript[\[Omega], xLabel,"x"][t]+Subscript[q, xLabel,"z"][t] Subscript[\[Omega], xLabel,"y"][t]-Subscript[q, xLabel,"y"][t] Subscript[\[Omega], xLabel,"z"][t]),Subscript[q, xLabel,"y"]'[t]->1/2 (-Subscript[q, xLabel,"z"][t] Subscript[\[Omega], xLabel,"x"][t]+Subscript[q, xLabel,"t"][t] Subscript[\[Omega], xLabel,"y"][t]+Subscript[q, xLabel,"x"][t] Subscript[\[Omega], xLabel,"z"][t]),Subscript[q, xLabel,"z"]'[t]->1/2 (Subscript[q, xLabel,"y"][t] Subscript[\[Omega], xLabel,"x"][t]-Subscript[q, xLabel,"x"][t] Subscript[\[Omega], xLabel,"y"][t]+Subscript[q, xLabel,"t"][t] Subscript[\[Omega], xLabel,"z"][t])
};
];

If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"EULER ANGLES"~~___] ,
xOut[\[DoubleStruckQ]["0"]]={
Subscript[p, xLabel,"x"][t],Subscript[p, xLabel,"y"][t],Subscript[p, xLabel,"z"][t],
Subscript[\[Psi], xLabel][t],Subscript[\[Phi], xLabel][t],Subscript[\[Theta], xLabel][t]
};
xOut[ToString @ StringForm["[\[DoubleStruckOne]\!\(\*SubscriptBox[\(]\), \(\[ScriptCapitalN] | ``\)]\)",xLabel]]=(Rotation @@ (Characters @ (First @ StringSplit[xPositionOrientationDescription,{":","|"," "}])))[Subscript[\[Psi], xLabel][t],Subscript[\[Phi], xLabel][t],Subscript[\[Theta], xLabel][t]];
If[StringMatchQ[(ToUpperCase @ xPositionOrientationDescription),___~~"REDUNDANT"~~___] ,
xOut[\[DoubleStruckQ]["1"]]={
Subscript[v, xLabel,"x"][t],Subscript[v, xLabel,"y"][t],Subscript[v, xLabel,"z"][t],
Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t],
Subscript[\[Psi], xLabel]'[t],Subscript[\[Phi], xLabel]'[t],Subscript[\[Theta], xLabel]'[t]
};
xOut[Subscript[\[DoubleStruckQ], \[NumberSign]]["1"]]={
Subscript[v, xLabel,"x"][t],Subscript[v, xLabel,"y"][t],Subscript[v, xLabel,"z"][t],
Subscript[\[Psi], xLabel]'[t],Subscript[\[Phi], xLabel]'[t],Subscript[\[Theta], xLabel]'[t]
};
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)["1"]]=
{Subscript[v, xLabel,"x"][t]-Subscript[p, xLabel,"x"]'[t],
Subscript[v, xLabel,"y"][t]-Subscript[p, xLabel,"y"]'[t],
Subscript[v, xLabel,"z"][t]-Subscript[p, xLabel,"z"]'[t]};
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckQ]\), \(_\)]\)["1"]]=Union @@ {
({Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]}-(AngularVelocity @ xOut[ToString @ StringForm["[\[DoubleStruckOne]\!\(\*SubscriptBox[\(]\), \(\[ScriptCapitalN] | ``\)]\)",xLabel]]))
}
,
xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckC]\), \(_\)]\)["1"]]=Union @@ {
{Subscript[v, xLabel,"x"][t]-Subscript[p, xLabel,"x"]'[t],
Subscript[v, xLabel,"y"][t]-Subscript[p, xLabel,"y"]'[t],
Subscript[v, xLabel,"z"][t]-Subscript[p, xLabel,"z"]'[t]},
({Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]}-(AngularVelocity @ xOut[ToString @ StringForm["[\[DoubleStruckOne]\!\(\*SubscriptBox[\(]\), \(\[ScriptCapitalN] | ``\)]\)",xLabel]]))
}
];
];

Module[{xI,xg},
xI["Spherical"]=xI["S"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel]}
});
xI["Cylindrical x"]=xI["Cx"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"a"], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"]}
});
xI["Cylindrical y"]=xI["Cy"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"a"], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"]}
});
xI["Cylindrical z"]=xI["Cz"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"r"], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"a"]}
});
xI["Central"]=xI["xyz"]=xI["C"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"x"], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"y"], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"z"]}
});
xI["xy Plane"]=xI["xy"]=xI["z"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xx"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xy"], 0},
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xy"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yy"], 0},
 {0, 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"zz"]}
});
xI["xz Plane"]=xI["xz"]=xI["y"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xx"], 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xz"]},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yy"], 0},
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xz"], 0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"zz"]}
});
xI["yz Plane"]=xI["yz"]=xI["x"]=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xx"], 0, 0},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yy"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yz"]},
 {0, Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yz"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"zz"]}
});
xI[xX_]:=({
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xx"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xy"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xz"]},
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xy"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yy"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yz"]},
 {Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"xz"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"yz"], Subscript[
  \!\(\*OverscriptBox[\(\[CapitalIota]\), \(_\)]\), xLabel,"zz"]}
});

xg["Default"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){Sin[
\!\(\*OverscriptBox[\(\[Xi]\), \(_\)]\)],0,Cos[
\!\(\*OverscriptBox[\(\[Xi]\), \(_\)]\)]};
xg["None"]={0,0,0};
xg["x"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){1,0,0};
xg["-x"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){-1,0,0};
xg["y"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){0,1,0};
xg["-y"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){0,-1,0};
xg["z"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){0,0,1};
xg["-z"]=
\!\(\*OverscriptBox[\(g\), \(_\)]\){0,0,-1};
xg[xL_List]:=xL;
xg[xX_]:=
\!\(\*OverscriptBox[\(g\), \(_\)]\){Sin[xX],0,Cos[xX]};

xOut[
\!\(\*OverscriptBox[\(\[DoubleStruckD]\), \(_\)]\)]=xOut[\[DoubleStruckD]]=xOut[\[DoubleStruckF]]=<|
"Matrix"-> Transpose@{Join@@{
-Subscript[
\!\(\*OverscriptBox[\(m\), \(_\)]\), xLabel](D[#,t]&/@{Subscript[v, xLabel,"x"][t],Subscript[v, xLabel,"y"][t],Subscript[v, xLabel,"z"][t]})+Subscript[
\!\(\*OverscriptBox[\(m\), \(_\)]\), xLabel]xg[xGravitationalField]+xExternalActiveForce,
-xI[xInertiaSymmetry].(D[#,t]&/@{Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]})-
{Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]}\[Cross](xI[xInertiaSymmetry].{Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]})+xExternalActiveTorque
}},
"Row Labels"-> {
Subscript[v, xLabel,"x"][t],Subscript[v, xLabel,"y"][t],Subscript[v, xLabel,"z"][t],
Subscript[\[Omega], xLabel,"x"][t],Subscript[\[Omega], xLabel,"y"][t],Subscript[\[Omega], xLabel,"z"][t]
},
"Column Labels"-> {""}
|>;
];

xOut
]
