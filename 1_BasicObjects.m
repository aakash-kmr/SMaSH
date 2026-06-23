(* ::Package:: *)

(* ::Chapter::Closed:: *)
(*Massive LG Index*)


MakeBoxes[MsIndex[J_,i_],StandardForm|TraditionalForm]:=TemplateBox[{StyleBox[ToBoxes[J],FontColor->Red],StyleBox[ToBoxes[i],FontColor->Red]},"littlegroupindex",DisplayFunction->(RowBox[{#1,"\[NegativeVeryThinSpace]",#2}]&),InterpretationFunction->(RowBox[{"MsIndex","[",#1,",",#2,"]"}]&)]
MsI=MsIndex;


(* ::Chapter::Closed:: *)
(*Tilde Legs*)


TL=TildeLeg;
TL[TL[expr_]]:=expr;
MakeBoxes[TildeLeg[expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[expr]},"TildeSpinor",DisplayFunction->(OverscriptBox[#1,"~"]&),InterpretationFunction->(RowBox[{"TildeLeg","[",#1,"]"}]&)];


(* ::Chapter::Closed:: *)
(*SH Spinors and Scalars*)


(* ::Section::Closed:: *)
(*SHA*)


(* ::Subsection::Closed:: *)
(*Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHA[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]&&IfP[LGI]&&MsQ[Part]:=TemplateBox[{ ToBoxes[Part],ToBoxes[LGI],ToBoxes[ SL2CI]},"RightAngle",
	DisplayFunction->(SuperscriptBox[RowBox[{"\[LeftBracketingBar]",SuperscriptBox[#1,#2],"\[RightAngleBracket]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHA[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]&&IfN[LGI]&&MsQ[Part]:=TemplateBox[{ ToBoxes[Part],ToBoxes[-LGI],ToBoxes[ SL2CI]},"RightAngle",
	DisplayFunction->(SuperscriptBox[RowBox[{"\[LeftBracketingBar]",SubscriptBox[#1,#2],"\[RightAngleBracket]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHA[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]&&IfP[LGI]&&MsQ[Part]:=TemplateBox[{ToBoxes[Part],ToBoxes[LGI],ToBoxes[- SL2CI]},"LeftAngle",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[",#2,"]",",","-",#3,"]"}]&)
];

MakeBoxes[SHA[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]&&IfN[LGI]&&MsQ[Part]:=TemplateBox[{ToBoxes[Part],ToBoxes[-LGI],ToBoxes[- SL2CI]},"LeftAngle",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[","-",#2,"]",",","-",#3,"]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHA[Part_, SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]:=TemplateBox[{ ToBoxes[Part],ToBoxes[SL2CI]},"RightAngle",
	DisplayFunction->(SuperscriptBox[RowBox[{"\[LeftBracketingBar]",#1,"\[RightAngleBracket]"}],OverscriptBox[#2,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,",",#2,"]"}]&)
];

MakeBoxes[SHA[Part_, SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]:=TemplateBox[{ToBoxes[Part],ToBoxes[-SL2CI]},"LeftAngle",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]"}],OverscriptBox[#2,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,",","-",#2,"]"}]&)
];


(* ::Section::Closed:: *)
(*SHB*)


(* ::Subsection::Closed:: *)
(*Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHB[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]&&IfP[LGI]&&MsQ[Part]:=TemplateBox[{ ToBoxes[Part],ToBoxes[LGI],ToBoxes[SL2CI]},"LeftBox",
	DisplayFunction->(SuperscriptBox[RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHB[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]&&IfN[LGI]&&MsQ[Part]:=TemplateBox[{ ToBoxes[Part],ToBoxes[-LGI],ToBoxes[SL2CI]},"LeftBox",
	DisplayFunction->(SuperscriptBox[RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHB[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]&&IfP[LGI]&&MsQ[Part]:=TemplateBox[{ToBoxes[Part],ToBoxes[LGI],ToBoxes[- SL2CI]},"RightBox",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftBracketingBar]",SuperscriptBox[#1,#2],"]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[",#2,"]",",","-",#3,"]"}]&)
];

MakeBoxes[SHB[Part_[LGI_], SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]&&IfN[LGI]&&MsQ[Part]:=TemplateBox[{ToBoxes[Part],ToBoxes[-LGI],ToBoxes[- SL2CI]},"RightBox",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftBracketingBar]",SubscriptBox[#1,#2],"]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[","-",#2,"]",",","-",#3,"]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHB[Part_, SL2CI_ ],StandardForm|TraditionalForm]/;IfN[SL2CI]:=TemplateBox[{ ToBoxes[Part],ToBoxes[ -SL2CI]},"RightBox",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftBracketingBar]",#1,"]"}],#2]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,",","-",#2,"]"}]&)
];

MakeBoxes[SHB[Part_, SL2CI_ ],StandardForm|TraditionalForm]/;IfP[SL2CI]:=TemplateBox[{ToBoxes[Part],ToBoxes[ SL2CI]},"LeftBox",
	DisplayFunction->(SuperscriptBox[RowBox[{"[",#1,"\[RightBracketingBar]"}],#2]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,",",#2,"]"}]&)
];


(* ::Section::Closed:: *)
(*SHAA*)


(* ::Subsection::Closed:: *)
(*Massive-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAA[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfP[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"[",#4,"]","]"}]&)
];
MakeBoxes[SHAA[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfN[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[-LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
];
MakeBoxes[SHAA[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfP[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"[",#4,"]","]"}]&)
];
MakeBoxes[SHAA[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfN[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[-LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
];



(* ::Subsection::Closed:: *)
(*Massive-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAA[Part1_[LGI1_],Part2_],StandardForm|TraditionalForm]/;IfP[LGI1]&&MsQ[Part1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHAA[Part1_[LGI1_],Part2_],StandardForm|TraditionalForm]/;IfN[LGI1]&&MsQ[Part1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
];



(* ::Subsection::Closed:: *)
(*Massless-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAA[Part1_,Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI2]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,",",SuperscriptBox[#2,#3],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,",",#2,"[",#3,"]","]"}]&)
];

MakeBoxes[SHAA[Part1_,Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI2]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[-LGI2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,",",SubscriptBox[#2,#3],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,",",#2,"[","-",#3,"]","]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAA[Part1_,Part2_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,",",#2,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,",",#2,"]"}]&)
];


(* ::Section::Closed:: *)
(*SHBB*)


(* ::Subsection::Closed:: *)
(*Massive-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBB[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfP[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"[",#4,"]","]"}]&)
];
MakeBoxes[SHBB[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfN[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[-LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
];
MakeBoxes[SHBB[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfP[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"[",#4,"]","]"}]&)
];
MakeBoxes[SHBB[Part1_[LGI1_],Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfN[LGI2]&&MsQ[Part1]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[-LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBB[Part1_,Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfP[LGI2]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",#1,",",SuperscriptBox[#2,#3],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,",",#2,"[",#3,"]","]"}]&)
];

MakeBoxes[SHBB[Part1_,Part2_[LGI2_]],StandardForm|TraditionalForm]/;IfN[LGI2]&&MsQ[Part2]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[-LGI2]},"BBScalar",
DisplayFunction->(RowBox[{"[",#1,",",SubscriptBox[#2,#3],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,",",#2,"[","-",#3,"]","]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massive-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBB[Part1_[LGI1_],Part2_],StandardForm|TraditionalForm]/;IfP[LGI1]&&MsQ[Part1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",#3,"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"]"}]&)
];

MakeBoxes[SHBB[Part1_[LGI1_],Part2_],StandardForm|TraditionalForm]/;IfN[LGI1]&&MsQ[Part1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",#3,"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBB[Part1_,Part2_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2]},"BBScalar",
DisplayFunction->(RowBox[{"[",#1,",",#2,"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,",",#2,"]"}]&)
];


(* ::Section::Closed:: *)
(*SHAB*)


(* ::Subsection::Closed:: *)
(*Massive-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfP[LGI3]&&MsQ[Part1]&&MsQ[Part3]:=
TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
];

MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfP[LGI1]&&IfN[LGI3]&&MsQ[Part1]&&MsQ[Part3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
];

MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfP[LGI3]&&MsQ[Part1]&&MsQ[Part3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
];

MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfN[LGI1]&&IfN[LGI3]&&MsQ[Part1]&&MsQ[Part3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAB[Part1_,Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfP[LGI3]&&MsQ[Part3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,",",#2,",",#3,"[",#4,"]","]"}]&)
];

MakeBoxes[SHAB[Part1_,Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;IfN[LGI3]&&MsQ[Part3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,",",#2,",",#3,"[","-",#4,"]","]"}]&)
];



(* ::Subsection::Closed:: *)
(*Massive-Massless*)


MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_],StandardForm|TraditionalForm]/;MsQ[Part1]&&IfP[LGI1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"]"}]&)
];

MakeBoxes[SHAB[Part1_[LGI1_],Part2_,Part3_],StandardForm|TraditionalForm]/;MsQ[Part1]&&IfN[LGI1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHAB[Part1_,Part2_,Part3_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",#3,"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,",",#2,",",#3,"]"}]&)
];


(* ::Section::Closed:: *)
(*SHBA*)


(* ::Subsection:: *)
(*Massive-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part1]&&MsQ[Part3]&&IfP[LGI1]&&IfP[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
];

MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part1]&&MsQ[Part3]&&IfP[LGI1]&&IfN[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
];

MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part1]&&MsQ[Part3]&&IfN[LGI1]&&IfP[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
];

MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part1]&&MsQ[Part3]&&IfN[LGI1]&&IfN[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
];


(* ::Subsection:: *)
(*Massless-Massive*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBA[Part1_,Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part3]&&IfP[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,",",#2,",",#3,"[",#4,"]","]"}]&)
];

MakeBoxes[SHBA[Part1_,Part2_,Part3_[LGI3_]],StandardForm|TraditionalForm]/;MsQ[Part3]&&IfN[LGI3]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3],ToBoxes[-LGI3]},"BAScalar",
DisplayFunction->(RowBox[{"[",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,",",#2,",",#3,"[","-",#4,"]","]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massive-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_],StandardForm|TraditionalForm]/;MsQ[Part1]&&IfP[LGI1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[LGI1],ToBoxes[Part2],ToBoxes[Part3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"]"}]&)
];

MakeBoxes[SHBA[Part1_[LGI1_],Part2_,Part3_],StandardForm|TraditionalForm]/;MsQ[Part1]&&IfN[LGI1]:=TemplateBox[{ToBoxes[Part1],ToBoxes[-LGI1],ToBoxes[Part2],ToBoxes[Part3]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"]"}]&)
];


(* ::Subsection::Closed:: *)
(*Massless-Massless*)


(* ::Input::Initialization:: *)
MakeBoxes[SHBA[Part1_,Part2_,Part3_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[Part1],ToBoxes[Part2],ToBoxes[Part3]},"BAScalar",
DisplayFunction->(RowBox[{"[",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,",",#2,",",#3,"]"}]&)
];


(* ::Chapter::Closed:: *)
(*Metric Bilinears*)


(* ::Section::Closed:: *)
(*Met *)


(* ::Input::Initialization:: *)
Met[\[Alpha]_, \[Beta]_] :=
    If[Or[(And[IfP[\[Alpha]], IfP[\[Beta]]]), (And[IfN[\[Alpha]], IfN[\[Beta]]])],
        \[Epsilon][\[Alpha], \[Beta]]
        ,
        \[Delta][\[Alpha], \[Beta]]
    ]

Metd[\[Alpha]_, \[Beta]_] :=
    If[Or[(And[IfP[\[Alpha]], IfP[\[Beta]]]), (And[IfN[\[Alpha]], IfN[\[Beta]]])],
        \[Epsilon]d[\[Alpha], \[Beta]]
        ,
        \[Delta]d[\[Alpha], \[Beta]]
    ]

Metlg[\[Alpha]_, \[Beta]_] :=
    If[Or[(And[IfP[\[Alpha]], IfP[\[Beta]]]), (And[IfN[\[Alpha]], IfN[\[Beta]]])],
        \[Epsilon]lg[\[Alpha], \[Beta]]
        ,
        \[Delta]lg[\[Alpha], \[Beta]]
    ]


(* ::Section::Closed:: *)
(*SU2L*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Epsilon][A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfP[B]:=TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2L",DisplayFunction->(SuperscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]","[",#1,",",#2,"]"}]&)
];

MakeBoxes[\[Epsilon][A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfN[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[-B]},"\[Epsilon]SU2L",DisplayFunction->(SubscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]","[","-",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta][A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfN[B]:=TemplateBox[{ToBoxes[A],ToBoxes[-B]},"\[Epsilon]SU2L",DisplayFunction->(SubscriptBox[SuperscriptBox["\[Delta]",#1],#2]&),InterpretationFunction->(RowBox[{"\[Delta]","[",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta][A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfP[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[B]},"\[Epsilon]SU2L",DisplayFunction->(SuperscriptBox[SubscriptBox["\[Delta]",#1],#2]&),InterpretationFunction->(RowBox[{"\[Delta]","[","-",#1,",",#2,"]"}]&)
];

\[Epsilon]::neg="Need both indices of \[Epsilon] either up or down";
\[Delta]::neg="Need one of the indices of \[Delta] up and other down";

MakeBoxes[\[Epsilon][A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfN[B])||(IfN[A]&&IfP[B]):=(Message[\[Epsilon]::neg];
TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2L",DisplayFunction->(RowBox[{"\[Epsilon]","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Epsilon]","[",#1,",",#2,"]"}]&)
]);

MakeBoxes[\[Delta][A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfP[B])||(IfN[A]&&IfN[B]):=(Message[\[Delta]::neg];TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2L",DisplayFunction->(RowBox[{"\[Delta]","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Delta]","[",#1,",",#2,"]"}]&)
]);


(* ::Section::Closed:: *)
(*SU2R*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Epsilon]d[A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfP[B]:=TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2R",DisplayFunction->(SuperscriptBox["\[Epsilon]d",RowBox[{OverscriptBox[#1,"."],OverscriptBox[#2,"."]}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]d","[",#1,",",#2,"]"}]&)
];

MakeBoxes[\[Epsilon]d[A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfN[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[-B]},"\[Epsilon]SU2R",DisplayFunction->(SubscriptBox["\[Epsilon]d",RowBox[{OverscriptBox[#1,"."],OverscriptBox[#2,"."]}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]d","[","-",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta]d[A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfN[B]:=TemplateBox[{ToBoxes[A],ToBoxes[-B]},"\[Epsilon]SU2R",DisplayFunction->(SubscriptBox[SuperscriptBox["\[Delta]d",OverscriptBox[#1,"."]],OverscriptBox[#2,"."]]&),InterpretationFunction->(RowBox[{"\[Delta]d","[",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta]d[A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfP[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[B]},"\[Epsilon]SU2R",DisplayFunction->(SuperscriptBox[SubscriptBox["\[Delta]d",OverscriptBox[#1,"."]],OverscriptBox[#2,"."]]&),InterpretationFunction->(RowBox[{"\[Delta]d","[","-",#1,",",#2,"]"}]&)
];

\[Epsilon]d::neg="Need both indices of \[Epsilon]d either up or down";
\[Delta]d::neg="Need one of the indices of \[Delta]d up and other down";

MakeBoxes[\[Epsilon]d[A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfN[B])||(IfN[A]&&IfP[B]):=(Message[\[Epsilon]d::neg];
TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2R",DisplayFunction->(RowBox[{"\[Epsilon]d","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Epsilon]d","[",#1,",",#2,"]"}]&)
]);

MakeBoxes[\[Delta]d[A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfP[B])||(IfN[A]&&IfN[B]):=(Message[\[Delta]d::neg];TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2R",DisplayFunction->(RowBox[{"\[Delta]d","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Delta]d","[",#1,",",#2,"]"}]&)
]);


(* ::Section::Closed:: *)
(*SU2 Little Group*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Epsilon]lg[A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfP[B]:=TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2LG",DisplayFunction->(SuperscriptBox["\[Epsilon]lg",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]lg","[",#1,",",#2,"]"}]&)
];

MakeBoxes[\[Epsilon]lg[A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfN[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[-B]},"\[Epsilon]SU2LG",DisplayFunction->(SubscriptBox["\[Epsilon]lg",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Epsilon]lg","[","-",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta]lg[A_,B_],StandardForm|TraditionalForm]/;IfP[A]&&IfN[B]:=TemplateBox[{ToBoxes[A],ToBoxes[-B]},"\[Epsilon]SU2LG",DisplayFunction->(SubscriptBox[SuperscriptBox["\[Delta]lg",#1],#2]&),InterpretationFunction->(RowBox[{"\[Delta]lg","[",#1,",","-",#2,"]"}]&)
];

MakeBoxes[\[Delta]lg[A_,B_],StandardForm|TraditionalForm]/;IfN[A]&&IfP[B]:=TemplateBox[{ToBoxes[-A],ToBoxes[B]},"\[Epsilon]SU2LG",DisplayFunction->(SuperscriptBox[SubscriptBox["\[Delta]lg",#1],#2]&),InterpretationFunction->(RowBox[{"\[Delta]lg","[","-",#1,",",#2,"]"}]&)
];

\[Epsilon]lg::neg="Need both indices of \[Epsilon]lg either up or down";
\[Delta]lg::neg="Need one of the indices of \[Delta]lg up and other down";

MakeBoxes[\[Epsilon]lg[A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfN[B])||(IfN[A]&&IfP[B]):=(Message[\[Epsilon]lg::neg];
TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2LG",DisplayFunction->(RowBox[{"\[Epsilon]lg","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Epsilon]lg","[",#1,",",#2,"]"}]&)
]);

MakeBoxes[\[Delta]lg[A_,B_],form_:StandardForm|TraditionalForm]/;(IfP[A]&&IfP[B])||(IfN[A]&&IfN[B]):=(Message[\[Delta]lg::neg];TemplateBox[{ToBoxes[A],ToBoxes[B]},"\[Epsilon]SU2LG",DisplayFunction->(RowBox[{"\[Delta]lg","[",#1,",",#2,"]"}]&),InterpretationFunction->(RowBox[{"\[Delta]lg","[",#1,",",#2,"]"}]&)
]);


(* ::Subsection:: *)
(*\[CapitalSigma]*)


(* ::Input::Initialization:: *)
MakeBoxes[\[CapitalSigma][i_][I_?IfP,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[J]},"Pauli3",DisplayFunction->(SuperscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalSigma]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalSigma]","[",#1,"]","[",#2,",",#3,"]"}]&)];

MakeBoxes[\[CapitalSigma][i_][I_?IfN,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[RowBox[{"(",SubscriptBox["\[CapitalSigma]",#1],")"}],RowBox[{#2,#3}]]&),InterpretationFunction->(RowBox[{"\[CapitalSigma]","[",#1,"]","[","-",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalSigma][i_][I_?IfP,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalSigma]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalSigma]","[",#1,"]","[",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalSigma][i_][I_?IfN,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalSigma]",#1],")"}],#3],#2]&),InterpretationFunction->(RowBox[{"\[CapitalSigma]","[",#1,"]","[","-",#2,",",#3,"]"}]&)];


(* ::Subsection:: *)
(*\[CapitalOmega]*)


(* ::Input::Initialization:: *)
MakeBoxes[\[CapitalOmega][i_][I_?IfP,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[J]},"Pauli3",DisplayFunction->(SuperscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalOmega]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalOmega]","[",#1,"]","[",#2,",",#3,"]"}]&)];

MakeBoxes[\[CapitalOmega][i_][I_?IfN,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[RowBox[{"(",SubscriptBox["\[CapitalOmega]",#1],")"}],RowBox[{#2,#3}]]&),InterpretationFunction->(RowBox[{"\[CapitalOmega]","[",#1,"]","[","-",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalOmega][i_][I_?IfP,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalOmega]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalOmega]","[",#1,"]","[",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalOmega][i_][I_?IfN,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalOmega]",#1],")"}],#3],#2]&),InterpretationFunction->(RowBox[{"\[CapitalOmega]","[",#1,"]","[","-",#2,",",#3,"]"}]&)];


(* ::Subsection:: *)
(*\[CapitalDelta]*)


(* ::Input::Initialization:: *)
MakeBoxes[\[CapitalDelta][i_][I_?IfP,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[J]},"Pauli3",DisplayFunction->(SuperscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalDelta]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalDelta]","[",#1,"]","[",#2,",",#3,"]"}]&)];

MakeBoxes[\[CapitalDelta][i_][I_?IfN,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[RowBox[{"(",SubscriptBox["\[CapitalDelta]",#1],")"}],RowBox[{#2,#3}]]&),InterpretationFunction->(RowBox[{"\[CapitalDelta]","[",#1,"]","[","-",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalDelta][i_][I_?IfP,J_?IfN],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[I],ToBoxes[-J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalDelta]",#1],")"}],#2],#3]&),InterpretationFunction->(RowBox[{"\[CapitalDelta]","[",#1,"]","[",#2,",","-",#3,"]"}]&)];

MakeBoxes[\[CapitalDelta][i_][I_?IfN,J_?IfP],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[-I],ToBoxes[J]},"Pauli3",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[CapitalDelta]",#1],")"}],#3],#2]&),InterpretationFunction->(RowBox[{"\[CapitalDelta]","[",#1,"]","[","-",#2,",",#3,"]"}]&)];


(* ::Section::Closed:: *)
(*Lorentz Metric*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Eta][\[Mu]_,\[Nu]_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfP[\[Nu]]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[\[Nu]]},"\[Sigma]matrix",
DisplayFunction->(SuperscriptBox["\[Eta]",RowBox[{#1,#2}]]&),
InterpretationFunction->(RowBox[{"\[Eta]","[",#1,",",#2,"]"}]&)
];
MakeBoxes[\[Eta][\[Mu]_,\[Nu]_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfN[\[Nu]]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[-\[Nu]]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox[SuperscriptBox["\[Eta]",#1],#2]&),
InterpretationFunction->(RowBox[{"\[Eta]","[",#1,",","-",#2,"]"}]&)
];
MakeBoxes[\[Eta][\[Mu]_,\[Nu]_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfP[\[Nu]]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[\[Nu]]},"\[Sigma]matrix",
DisplayFunction->(SuperscriptBox[SubscriptBox["\[Eta]",#1],#2]&),
InterpretationFunction->(RowBox[{"\[Eta]","[","-",#1,",",#2,"]"}]&)
];
MakeBoxes[\[Eta][\[Mu]_,\[Nu]_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfN[\[Nu]]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[-\[Nu]]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox["\[Eta]",RowBox[{#1,#2}]]&),
InterpretationFunction->(RowBox[{"\[Eta]","[","-",#1,",","-",#2,"]"}]&)
];


(* ::Section::Closed:: *)
(*4D Levi-Cevita*)


MakeBoxes[epsilon\[Eta][\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfP[\[Nu]]&&IfP[\[Rho]]&&IfP[\[Sigma]]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[\[Nu]],ToBoxes[\[Rho]],ToBoxes[\[Sigma]]},"\[Sigma]matrix",
DisplayFunction->(SuperscriptBox["\[Epsilon]\[Eta]",RowBox[{#1,#2,#3,#4}]]&),
InterpretationFunction->(RowBox[{"epsilon\[Eta]","[",#1,",",#2,",",#3,",",#4,"]"}]&)
];

MakeBoxes[epsilon\[Eta][\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfN[\[Nu]]&&IfN[\[Rho]]&&IfN[\[Sigma]]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[-\[Nu]],ToBoxes[-\[Rho]],ToBoxes[-\[Sigma]]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox["\[Epsilon]\[Eta]",RowBox[{#1,#2,#3,#4}]]&),
InterpretationFunction->(RowBox[{"epsilon\[Eta]","[","-",#1,",","-",#2,",","-",#3,",","-",#4,"]"}]&)
];


(* ::Chapter::Closed:: *)
(*Clifford Algebra*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfP[A]&&IfP[B]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[A],ToBoxes[B]},"\[Sigma]matrix",DisplayFunction->(SuperscriptBox[RowBox[{"(",SuperscriptBox[OverscriptBox["\[Sigma]","\[LongDash]"],#1],")"}],RowBox[{OverscriptBox[#3,"."],#2}]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[",#1,"]","[",#2,",",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfN[A]&&IfN[B]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[-A],ToBoxes[-B]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox[RowBox[{"(",SuperscriptBox["\[Sigma]",#1],")"}],RowBox[{#2,OverscriptBox[#3,"."]}]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[",#1,"]","[","-",#2,",","-",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfP[A]&&IfP[B]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[A],ToBoxes[B]},"\[Sigma]matrix",DisplayFunction->(SuperscriptBox[RowBox[{"(",SubscriptBox[OverscriptBox["\[Sigma]","\[LongDash]"],#1],")"}],RowBox[{OverscriptBox[#3,"."],#2}]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[","-",#1,"]","[",#2,",",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfN[A]&&IfN[B]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[-A],ToBoxes[-B]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox[RowBox[{"(",SubscriptBox["\[Sigma]",#1],")"}],RowBox[{#2,OverscriptBox[#3,"."]}]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[","-",#1,"]","[","-",#2,",","-",#3,"]"}]&)
];


(* ::Input::Initialization:: *)
MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfP[A]&&IfN[B]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[A],ToBoxes[-B]},"\[Sigma]matrix",DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SuperscriptBox["\[Sigma]",#1],")"}],#2],OverscriptBox[#3,"."]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[",#1,"]","[",#2,",","-",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfP[\[Mu]]&&IfN[A]&&IfP[B]:=TemplateBox[{ToBoxes[\[Mu]],ToBoxes[-A],ToBoxes[B]},"\[Sigma]matrix",DisplayFunction->(SuperscriptBox[SubscriptBox[RowBox[{"(",SuperscriptBox["\[Sigma]",#1],")"}],#2],OverscriptBox[#3,"."]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[",#1,"]","[","-",#2,",",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfP[A]&&IfN[B]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[A],ToBoxes[-B]},"\[Sigma]matrix",
DisplayFunction->(SubscriptBox[SuperscriptBox[RowBox[{"(",SubscriptBox["\[Sigma]",#1],")"}],#2],OverscriptBox[#3,"."]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[","-",#1,"]","[",#2,",","-",#3,"]"}]&)
];

MakeBoxes[\[Sigma]mat[\[Mu]_][A_,B_],StandardForm|TraditionalForm]/;IfN[\[Mu]]&&IfN[A]&&IfP[B]:=TemplateBox[{ToBoxes[-\[Mu]],ToBoxes[-A],ToBoxes[B]},"\[Sigma]matrix",
DisplayFunction->(SuperscriptBox[SubscriptBox[RowBox[{"(",SubscriptBox["\[Sigma]",#1],")"}],#2],OverscriptBox[#3,"."]]&),InterpretationFunction->(RowBox[{"\[Sigma]mat","[","-",#1,"]","[","-",#2,",",#3,"]"}]&)
];


(* ::Chapter::Closed:: *)
(*Differentiate*)


(* ::Input::Initialization:: *)
MakeBoxes[Differentiate[X_][expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[X],ToBoxes[expr]},"DifferentialOperator",DisplayFunction->(FractionBox[RowBox[{"\[PartialD]",#2}],RowBox[{"\[PartialD]",#1}]]&),InterpretationFunction->(RowBox[{"Differentiate","[",#1,"]","[",#2,"]"}]&)]


(* ::Chapter::Closed:: *)
(*Minkowski Product*)


(* ::Input::Initialization:: *)
MakeBoxes[SP[X_[\[Mu]_]Y_[\[Nu]_]],StandardForm|TraditionalForm]/;\[Mu]+\[Nu]==0:=TemplateBox[{ToBoxes[X],ToBoxes[Y]},"MinkowskiProduct",DisplayFunction->(RowBox[{"(",#1,"\[CenterDot]",#2,")"}]&),InterpretationFunction->(RowBox[{"SP","[",#1,"[","\[Mu]","]",#2,"[","-\[Mu]","]","]"}]&)];

MakeBoxes[SP[X_[a1_]Y_[a2_,a3_]Z_[a4_]],StandardForm|TraditionalForm]/;a1+a2==0&&a3+a4==0:=TemplateBox[{ToBoxes[X],ToBoxes[Y],ToBoxes[Z]},"MinkowskiProduct",DisplayFunction->(RowBox[{"(",#1,"\[CenterDot]",#2,"\[CenterDot]",#3,")"}]&),InterpretationFunction->(RowBox[{"SP","[",#1,"[","\[Mu]","]",#2,"[","-\[Mu]",",","-\[Nu]","]",#3,"[","\[Nu]","]","]"}]&)]


(* ::Chapter::Closed:: *)
(*Mass, Momenta, Energy, and Angles*)


m[TL[i_]]:=m[i];
\[CapitalEpsilon][TL[i_]]:=\[CapitalEpsilon][i];
Modp[TL[i_]]:=Modp[i];
p[TL[i_]][\[Mu]_]:=p[i][\[Mu]];
\[Theta][TL[i_]]:=\[Theta][i];
\[Phi][TL[i_]]:=\[Phi][i];


(* ::Input::Initialization:: *)
MakeBoxes[m[i_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i]},"Mass",DisplayFunction->(SubscriptBox["m",#1]&),InterpretationFunction->(RowBox[{"m","[",#1,"]"}]&)];

MakeBoxes[Modp[i_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i]},"Mom",DisplayFunction->(RowBox[{"\[VerticalSeparator]",SubscriptBox["p",#1],"\[VerticalSeparator]"}]&),InterpretationFunction->(RowBox[{"Modp","[",#1,"]"}]&)];


MakeBoxes[p[i_][\[Mu]_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[\[Mu]]},"Mom",DisplayFunction->(SubscriptBox[RowBox[{"(",SubscriptBox["p",#1],")"}],#2]&),InterpretationFunction->(RowBox[{"p","[",#1,"]","[",#2,"]"}]&)];

MakeBoxes[\[CapitalEpsilon][i_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i]},"Energy",DisplayFunction->(SubscriptBox["\[CapitalEpsilon]",#1]&),InterpretationFunction->(RowBox[{"\[CapitalEpsilon]","[",#1,"]"}]&)];

MakeBoxes[\[Theta][i_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i]},"PolarAngle",DisplayFunction->(SubscriptBox["\[Theta]",#1]&),InterpretationFunction->(RowBox[{"\[Theta]","[",#1,"]"}]&)];

MakeBoxes[\[Phi][i_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i]},"AzimuthalAngle",DisplayFunction->(SubscriptBox["\[Phi]",#1]&),InterpretationFunction->(RowBox[{"\[Phi]","[",#1,"]"}]&)];


(* ::Chapter::Closed:: *)
(*C,P,T*)


MakeBoxes[HC[expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[expr]},"HermitianConjugate",
DisplayFunction->(SuperscriptBox[#1,"\[Dagger]"]&), InterpretationFunction->(RowBox[{"HC","[",#1,"]"}]&)];


(* ::Input::Initialization:: *)
MakeBoxes[Conjugate[expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[expr]},"Conjugate",DisplayFunction->(SuperscriptBox[#1,"*"]&),InterpretationFunction->(RowBox[{"Conjugate","[",#1,"]"}]&)]


(* ::Input::Initialization:: *)
MakeBoxes[Parity[expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[expr]},"Parity",DisplayFunction->(SuperscriptBox[#1,"\[ScriptCapitalP]"]&),InterpretationFunction->(RowBox[{"Parity","[",#1,"]"}]&)];
MakeBoxes[TimeReversal[expr_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[expr]},"TimeReversal",DisplayFunction->(SuperscriptBox[#1,"\[ScriptCapitalT]"]&),InterpretationFunction->(RowBox[{"TimeReversal","[",#1,"]"}]&)];


(* ::Chapter::Closed:: *)
(*Coupling*)


(* ::Input::Initialization:: *)
MakeBoxes[Coupling[g_,i_],StandardForm|TraditionalForm]:=TemplateBox[{StyleBox[ToBoxes[g],FontSlant->Italic],ToBoxes[i]},"CouplingConstant",DisplayFunction->(SubscriptBox[#1,#2]&),InterpretationFunction->(RowBox[{"Coupling","[",#1,",",#2,"]"}]&)];


(* ::Chapter::Closed:: *)
(*Mandelstam*)


(* ::Input::Initialization:: *)
MakeBoxes[sm[i_,j_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[j]},"Mandelstam",DisplayFunction->(SubscriptBox["\[ScriptS]",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"sm","[",#1,",",#2,"]"}]&)]


(* ::Input::Initialization:: *)
MakeBoxes[SM[i___],StandardForm|TraditionalForm]:=TemplateBox[Map[ToBoxes,{i}],"Mandelstams",DisplayFunction->(SubscriptBox["\[ScriptCapitalS]",RowBox[{##}]]&),InterpretationFunction->(RowBox[{"SM","[",RowBox@Riffle[{##},","],"]"}]&)]


(* ::Chapter:: *)
(*Input Form Aliases*)


(* ::Input::Initialization:: *)
$SMaSHShortcuts={
"ep"->MakeBoxes[\[Epsilon][\[Placeholder],\[SelectionPlaceholder]]],"epd"->MakeBoxes[\[Epsilon]d[\[Placeholder],\[SelectionPlaceholder]]],"eplg"->MakeBoxes[\[Epsilon]lg[\[Placeholder],\[SelectionPlaceholder]]],
"dl"->MakeBoxes[\[Delta][\[Placeholder],-\[SelectionPlaceholder]]],"dld"->MakeBoxes[\[Delta]d[\[Placeholder],-\[SelectionPlaceholder]]],"dlg"->MakeBoxes[\[Delta]lg[\[Placeholder],-\[SelectionPlaceholder]]],"\[Eta]"-> MakeBoxes[\[Eta][\[Placeholder],\[Placeholder]]],
"<"->MakeBoxes[SHA[\[Placeholder],-\[SelectionPlaceholder]]],">"->MakeBoxes[SHA[\[Placeholder],\[SelectionPlaceholder]]],"["->MakeBoxes[SHB[\[Placeholder],\[SelectionPlaceholder]]],"]"->MakeBoxes[SHB[\[Placeholder],-\[SelectionPlaceholder]]],
"[]"->MakeBoxes[SHBB[\[Placeholder],\[SelectionPlaceholder]]],"<>"->MakeBoxes[SHAA[\[Placeholder],\[SelectionPlaceholder]]],
"<]"->MakeBoxes[SHAB[\[Placeholder],\[SelectionPlaceholder],\[SelectionPlaceholder]]],"[>"->MakeBoxes[SHBA[\[Placeholder],\[SelectionPlaceholder],\[SelectionPlaceholder]]],
"\[Sigma]"->MakeBoxes[\[Sigma]mat[\[SelectionPlaceholder]][\[SelectionPlaceholder],\[SelectionPlaceholder]]],"gc"->MakeBoxes[Coupling[\[SelectionPlaceholder],\[SelectionPlaceholder]]],
"ms"->MakeBoxes[m[\[SelectionPlaceholder]]],"\[Theta]"->MakeBoxes[\[Theta][\[SelectionPlaceholder]]],"\[Phi]"->MakeBoxes[\[Phi][\[SelectionPlaceholder]]],"En"->MakeBoxes[\[CapitalEpsilon][\[SelectionPlaceholder]]],"p"->MakeBoxes[p[\[SelectionPlaceholder]][\[SelectionPlaceholder]]],
"mp"->MakeBoxes[Modp[\[SelectionPlaceholder]]],"sp"->MakeBoxes[SP[\[SelectionPlaceholder][\[SelectionPlaceholder]] \[SelectionPlaceholder][\[SelectionPlaceholder]]]],"sm"->MakeBoxes[sm[\[SelectionPlaceholder],\[SelectionPlaceholder]]],
"hc"->MakeBoxes[HC[\[SelectionPlaceholder]]],"cc"->MakeBoxes[Conjugate[\[SelectionPlaceholder]]],"pt"->MakeBoxes[Parity[\[SelectionPlaceholder]]],"tr"->MakeBoxes[TimeReversal[\[SelectionPlaceholder]]],"msi"->TemplateBox[{StyleBox[ToBoxes[\[SelectionPlaceholder]],FontColor->Red],StyleBox[ToBoxes[\[SelectionPlaceholder]],FontColor->Red]},"littlegroupindex",DisplayFunction->(RowBox[{#1,"\[NegativeVeryThinSpace]",#2}]&),InterpretationFunction->(RowBox[{"MsIndex","[",#1,",",#2,"]"}]&)],
"diff"-> TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"DifferentialOperator",DisplayFunction->(FractionBox[RowBox[{"\[PartialD]",#2}],RowBox[{"\[PartialD]",#1}]]&),InterpretationFunction->(RowBox[{"Differentiate","[",#1,"]","[",#2,"]"}]&)],

">'"->TemplateBox[{ ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[ \[Placeholder]]},"RightAngle",
	DisplayFunction->(SuperscriptBox[RowBox[{"\[LeftBracketingBar]",SuperscriptBox[#1,#2],"\[RightAngleBracket]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[",#2,"]",",",#3,"]"}]&)],
"<'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[ \[Placeholder]]},"LeftAngle",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[",#2,"]",",","-",#3,"]"}]&)],
">,"->TemplateBox[{ ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[ \[Placeholder]]},"RightAngle",
	DisplayFunction->(SuperscriptBox[RowBox[{"\[LeftBracketingBar]",SubscriptBox[#1,#2],"\[RightAngleBracket]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[","-",#2,"]",",",#3,"]"}]&)],
"<,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[ \[Placeholder]]},"LeftAngle",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]"}],OverscriptBox[#3,"."]]&),
	InterpretationFunction->(RowBox[{"SHA","[",#1,"[","-",#2,"]",",","-",#3,"]"}]&)],

"['"->TemplateBox[{ ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"LeftBox",
	DisplayFunction->(SuperscriptBox[RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[",#2,"]",",",#3,"]"}]&)],
"[,"->TemplateBox[{ ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"LeftBox",
	DisplayFunction->(SuperscriptBox[RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[","-",#2,"]",",",#3,"]"}]&)],
"]'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"RightBox",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftBracketingBar]",SuperscriptBox[#1,#2],"]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[",#2,"]",",","-",#3,"]"}]&)],
"],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"RightBox",
	DisplayFunction->(SubscriptBox[RowBox[{"\[LeftBracketingBar]",SubscriptBox[#1,#2],"]"}],#3]&),
	InterpretationFunction->(RowBox[{"SHB","[",#1,"[","-",#2,"]",",","-",#3,"]"}]&)],

"<'>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"[",#4,"]","]"}]&)],
"<'>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"[","-",#4,"]","]"}]&)],
"<,>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"[",#4,"]","]"}]&)],
"<,>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"[","-",#4,"]","]"}]&)],


"<'>"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],",",#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[",#2,"]",",",#3,"]"}]&)
],
"<,>"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],",",#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
],
"<>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,",",SuperscriptBox[#2,#3],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,",",#2,"[",#3,"]","]"}]&)
],
"<>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"AAScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,",",SubscriptBox[#2,#3],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHAA","[",#1,",",#2,"[","-",#3,"]","]"}]&)
],

"[']'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"[",#4,"]","]"}]&)
],
"['],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
],
"[,]'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"[",#4,"]","]"}]&)
],
"[,],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"[","-",#4,"]","]"}]&)
],

"[']"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],",",#3,"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[",#2,"]",",",#3,"]"}]&)
],
"[,]"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],",",#3,"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,"[","-",#2,"]",",",#3,"]"}]&)
],
"[]'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",#1,",",SuperscriptBox[#2,#3],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,",",#2,"[",#3,"]","]"}]&)
],
"[],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BBScalar",
DisplayFunction->(RowBox[{"[",#1,",",SubscriptBox[#2,#3],"]"}]&),
InterpretationFunction->(RowBox[{"SHBB","[",#1,",",#2,"[","-",#3,"]","]"}]&)
],

"<']'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
],
"<'],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
],
"<,]'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
],
"<,],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
],
"<']"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[",#2,"]",",",#3,",",#4,"]"}]&)
],
"<,]"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,"[","-",#2,"]",",",#3,",",#4,"]"}]&)
],
"<]'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SuperscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,",",#2,",",#3,"[",#4,"]","]"}]&)
],
"<],"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"ABScalar",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SubscriptBox[#3,#4],"]"}]&),
InterpretationFunction->(RowBox[{"SHAB","[",#1,",",#2,",",#3,"[","-",#4,"]","]"}]&)
],

"['>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
],
"['>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
],
"[,>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SuperscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"[",#5,"]","]"}]&)
],
"[,>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",SubscriptBox[#4,#5],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"[","-",#5,"]","]"}]&)
],

"['>"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SuperscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[",#2,"]",",",#3,",",#4,"]"}]&)
],
"[,>"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",SubscriptBox[#1,#2],"\[RightBracketingBar]",#3,"\[LeftBracketingBar]",#4,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,"[","-",#2,"]",",",#3,",",#4,"]"}]&)
],
"[>'"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SuperscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,",",#2,",",#3,"[",#4,"]","]"}]&)
],
"[>,"->TemplateBox[{ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]],ToBoxes[\[Placeholder]]},"BAScalar",
DisplayFunction->(RowBox[{"[",#1,"\[RightBracketingBar]",#2,"\[LeftBracketingBar]",SubscriptBox[#3,#4],"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"SHBA","[",#1,",",#2,",",#3,"[","-",#4,"]","]"}]&)
]
};


(* ::Input::Initialization:: *)
RunInputAliasis[]:=Module[{},
CurrentValue[$FrontEndSession,InputAliases]=Append[CurrentValue[$FrontEndSession,InputAliases],$SMaSHShortcuts];]

RunInputAliasis[];


(* ::Chapter::Closed:: *)
(*Ignore*)


Print["Loaded: BasicObjects"]
