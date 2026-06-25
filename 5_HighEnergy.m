(* ::Package:: *)

(* ::Section::Closed:: *)
(*Format*)


(* ::Input::Initialization:: *)
MakeBoxes[\[Lambda][i_,sgn_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[sgn]},"SU2LRBasisSpinors",DisplayFunction->(SubscriptBox["\[Lambda]",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Lambda]","[",#1,",",#2,"]"}]&)];
MakeBoxes[\[Chi][i_,sgn_],StandardForm|TraditionalForm]:=TemplateBox[{ToBoxes[i],ToBoxes[sgn]},"SU2LRBasisSpinors",DisplayFunction->(SubscriptBox["\[Chi]",RowBox[{#1,#2}]]&),InterpretationFunction->(RowBox[{"\[Chi]","[",#1,",",#2,"]"}]&)];


(* ::Section::Closed:: *)
(*Subscript[SU2, L] and Subscript[SU2, R]*)


(* ::Input::Initialization:: *)
SU2LBasis[i_]:={SHB[\[Chi][i,p],\[Alpha]_?IfN]:>{angc[i],angs[i]}, SHB[\[Chi][i,m],\[Alpha]_?IfN]:>{angsC[i],-angc[i]},SHB[\[Chi][i,p],\[Alpha]_?IfP]:>{angs[i],-angc[i]},SHB[\[Chi][i,m],\[Alpha]_?IfP]:>{-angc[i],-angsC[i]}};

SU2RBasis[i_]:={SHA[\[Chi][i,p],\[Alpha]_?IfP]:>{-angc[i],-angs[i]}, SHA[\[Chi][i,m],\[Alpha]_?IfP]:>{-angsC[i],angc[i]},SHA[\[Chi][i,p],\[Alpha]_?IfN]:>{angs[i],-angc[i]},SHA[\[Chi][i,m],\[Alpha]_?IfN]:>{-angc[i],-angsC[i]}};

ExpandSU2Basis[i_][expr_]:=expr//.SU2LBasis[i]//.SU2RBasis[i]//.SU2LGBasis;


(* ::Input::Initialization:: *)
SU2LInnerProduct[legs_:AllMassiveLegs[]][expr_]:=
expr//.{
SHB[\[Lambda][i_,p],\[Alpha]_?IfP]SHB[\[Lambda][i_,m],\[Beta]_?IfN]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> +m[i],
SHB[\[Lambda][i_,m],\[Alpha]_?IfP]SHB[\[Lambda][i_,p],\[Beta]_?IfN]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> -m[i],
SHB[\[Lambda][i_,p],\[Alpha]_?IfN]SHB[\[Lambda][i_,p],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> 0,
SHB[\[Lambda][i_,m],\[Alpha]_?IfN]SHB[\[Lambda][i_,m],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> 0,
SHBB[\[Lambda][i_,p],\[Lambda][i_,m]]/;MemberQ[legs,i]:>+m[i],
SHBB[\[Lambda][i_,m],\[Lambda][i_,p]]/;MemberQ[legs,i]:>-m[i] 
};

SU2RInnerProduct[legs_:AllMassiveLegs[]][expr_]:=
expr//.{
SHA[\[Lambda][i_,p],\[Alpha]_?IfN]SHA[\[Lambda][i_,m],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> +m[i],
SHA[\[Lambda][i_,m],\[Alpha]_?IfN]SHA[\[Lambda][i_,p],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> -m[i],
SHA[\[Lambda][i_,p],\[Alpha]_?IfN]SHA[\[Lambda][i_,p],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> 0,
SHA[\[Lambda][i_,m],\[Alpha]_?IfN]SHA[\[Lambda][i_,m],\[Beta]_?IfP]/;\[Alpha]+\[Beta]==0&&MemberQ[legs,i]:> 0,
SHAA[\[Lambda][i_,p],\[Lambda][i_,m]]/;MemberQ[legs,i]:>+m[i],
SHAA[\[Lambda][i_,m],\[Lambda][i_,p]]/;MemberQ[legs,i]:>-m[i]
};

SU2LRInnerProduct[i_][expr_]:=expr//SU2LInnerProduct[i]//SU2RInnerProduct[i]


(* ::Section:: *)
(*Subscript[SU(2), LG] basis*)


SU2LGBasis:={\[Zeta]m[I_?IfN]:> {0,1},\[Zeta]p[I_?IfN]:> {-1,0},\[Zeta]m[I_?IfP]:> {1,0},\[Zeta]p[I_?IfP]:> {0,1}};

SU2LGBasisComponent[expr_]:=expr//.{\[Zeta]m[I_?IfN]/;MemberQ[{1,2,-1,-2},I]:> {0,1}[[Abs[I]]],\[Zeta]p[I_?IfN]/;MemberQ[{1,2,-1,-2},I]:> {-1,0}[[Abs[I]]],\[Zeta]m[I_?IfP]/;MemberQ[{1,2,-1,-2},I]:> {1,0}[[Abs[I]]],\[Zeta]p[I_?IfP]/;MemberQ[{1,2,-1,-2},I]:> {0,1}[[Abs[I]]]};

SU2LGInnerProduct[expr_]:=expr//.{
\[Zeta]p[I_]\[Zeta]p[J_]/;I+J==0:>0,
\[Zeta]m[I_]\[Zeta]m[J_]/;I+J==0:>0 ,
\[Zeta]p[I_?IfP]\[Zeta]m[J_?IfN]/;I+J==0:>1,
\[Zeta]m[I_?IfP]\[Zeta]p[J_?IfN]/;I+J==0:>-1 ,
\[Zeta]p[I_?IfP]\[Zeta]m[J_?IfP]-\[Zeta]m[I_?IfP]\[Zeta]p[J_?IfP]:> -\[Epsilon]lg[I,J],
\[Zeta]p[I_?IfN]\[Zeta]m[J_?IfN]-\[Zeta]m[I_?IfN]\[Zeta]p[J_?IfN]:> \[Epsilon]lg[I,J],
\[Zeta]p[I_?IfP]\[Zeta]m[J_?IfN]-\[Zeta]m[I_?IfP]\[Zeta]p[J_?IfN]:> \[Delta]lg[I,J],
\[Zeta]p[I_?IfN]\[Zeta]m[J_?IfP]-\[Zeta]m[I_?IfN]\[Zeta]p[J_?IfP]:> -\[Delta]lg[I,J]};


(* ::Section:: *)
(*Decompose to SU2 Basis*)


ToDimensionfullBasis[legs_:AllMassiveLegs[]][expr_]:=expr//.{
	SHB[leg_[J_],\[Alpha]_]/;MemberQ[legs,leg]:> SHB[\[Lambda][leg,p], \[Alpha]]\[Zeta]m[  J]+SHB[\[Lambda][leg,m], \[Alpha]]\[Zeta]p[ J],
	SHA[leg_[J_],\[Alpha]_]/;MemberQ[legs,leg]:> SHA[\[Lambda][leg,m], \[Alpha]]\[Zeta]p[  J]+SHA[\[Lambda][leg,p], \[Alpha]]\[Zeta]m[ J],
	HP@SHBB[i1___,leg_[J_],i2___]/;MemberQ[legs,leg]:> SHBB[i1,\[Lambda][leg,p], i2]\[Zeta]m[  J]+SHBB[i1,\[Lambda][leg,m], i2]\[Zeta]p[ J],
	HP@SHAA[i1___,leg_[J_],i2___]/;MemberQ[legs,leg]:> SHAA[i1,\[Lambda][leg,m], i2]\[Zeta]p[  J]+SHAA[i1,\[Lambda][leg,p], i2]\[Zeta]m[ J],
	SHAB[i1_,leg_,i2_]/;MemberQ[legs,leg]:> SHAA[i1,\[Lambda][leg,p]]SHBB[i2,\[Lambda][leg,m]]+SHAA[i1,\[Lambda][leg,m]]SHBB[i2,\[Lambda][leg,p]],
	SHBA[i1_,leg_,i2_]/;MemberQ[legs,leg]:> SHBB[i1,\[Lambda][leg,p]]SHAA[i2,\[Lambda][leg,m]]+SHBB[i1,\[Lambda][leg,m]]SHAA[i2,\[Lambda][leg,p]],
SHAB[leg_[J_],i1_,i2_]/;MemberQ[legs,leg]:> SHAB[\[Lambda][leg,m],i1,i2]\[Zeta]p[J]+SHAB[\[Lambda][leg,p],i1,i2]\[Zeta]m[J],
SHAB[i1_,i2_,leg_[J_]]/;MemberQ[legs,leg]:> SHAB[i1,i2,\[Lambda][leg,m]]\[Zeta]p[J]+SHAB[i1,i2,\[Lambda][leg,p]]\[Zeta]m[J],
SHBA[leg_[J_],i1_,i2_]/;MemberQ[legs,leg]:> SHAB[\[Lambda][leg,p],i1,i2]\[Zeta]m[J]+SHAB[\[Lambda][leg,m],i1,i2]\[Zeta]p[J],
SHBA[i1_,i2_,leg_[J_]]/;MemberQ[legs,leg]:> SHBA[i1,i2,\[Lambda][leg,m]]\[Zeta]p[J]+SHBA[i1,i2,\[Lambda][leg,p]]\[Zeta]m[J]
}//SU2LGBasisComponent;


DimFulltoDimLessBasis[legs_:AllMassiveLegs[]][expr_]:=expr//.{
SHB[\[Lambda][i_,p], \[Alpha]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]]SHB[\[Chi][i,p], \[Alpha]],
SHB[\[Lambda][i_,m], \[Alpha]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]]SHB[\[Chi][i,m], \[Alpha]],
SHA[\[Lambda][i_,p], \[Alpha]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]]SHA[\[Chi][i,p], \[Alpha]],
SHA[\[Lambda][i_,m], \[Alpha]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]]SHA[\[Chi][i,m], \[Alpha]],
HP@SHAA[\[Mu]___,\[Lambda][i_,p],\[Nu]___]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHAA[\[Mu],\[Chi][i,p],\[Nu]],
HP@SHAA[\[Mu]___,\[Lambda][i_,m],\[Nu]___]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHAA[\[Mu],\[Chi][i,m],\[Nu]],
HP@SHBB[\[Mu]___,\[Lambda][i_,p],\[Nu]___]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHBB[\[Mu],\[Chi][i,p],\[Nu]],
HP@SHBB[\[Mu]___,\[Lambda][i_,m],\[Nu]___]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHBB[\[Mu],\[Chi][i,m],\[Nu]],
SHAB[\[Lambda][i_,p],\[Mu]_,\[Nu]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHAB[\[Chi][i,p],\[Mu],\[Nu]],
SHAB[\[Lambda][i_,m],\[Mu]_,\[Nu]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHAB[\[Chi][i,m],\[Mu],\[Nu]],
SHAB[\[Mu]_,\[Nu]_,\[Lambda][i_,p]]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHAB[\[Mu],\[Nu],\[Chi][i,p]],
SHAB[\[Mu]_,\[Nu]_,\[Lambda][i_,m]]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHAB[\[Mu],\[Nu],\[Chi][i,m]],
SHAB[\[Mu]_,\[Lambda][i_,p_],\[Nu]_]/;MemberQ[legs,i]:> m[i]SHAB[\[Mu],\[Chi][i,p],\[Nu]],
SHBA[\[Lambda][i_,p],\[Mu]_,\[Nu]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHBA[\[Chi][i,p],\[Mu],\[Nu]],
SHBA[\[Lambda][i_,m],\[Mu]_,\[Nu]_]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHBA[\[Chi][i,m],\[Mu],\[Nu]],
SHBA[\[Mu]_,\[Nu]_,\[Lambda][i_,p]]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]+Modp[i]] SHBA[\[Mu],\[Nu],\[Chi][i,p]],
SHBA[\[Mu]_,\[Nu]_,\[Lambda][i_,m]]/;MemberQ[legs,i]:> Sqrt[\[CapitalEpsilon][i]-Modp[i]] SHBA[\[Mu],\[Nu],\[Chi][i,m]],
SHBA[\[Mu]_,\[Lambda][i_,p_],\[Nu]_]/;MemberQ[legs,i]:> m[i]SHBA[\[Mu],\[Chi][i,p],\[Nu]]
};


(* ::Input::Initialization:: *)
ToDimensionlessBasis[legs_:AllMassiveLegs[]][expr_]:=expr//ToDimensionfullBasis[legs]//DimFulltoDimLessBasis[legs];


(* ::Section:: *)
(*High Energy Limit*)


HighEnergyLimit[rules_List][expr_]:=Module[{sublegs,expr1,expr2,Mslegs},
sublegs=rules;
Mslegs=Keys[rules];
expr1=SU2LGBasisComponent[ToDimensionfullBasis[Mslegs][expr]];
expr2=(expr1)//.{\[CapitalEpsilon][i_]-Modp[i_]/;MemberQ[Mslegs,i]:>m[i]^2/(2\[CapitalEpsilon][i//.sublegs]),
\[CapitalEpsilon][i_]+Modp[i_]/;MemberQ[Mslegs,i]:>2 \[CapitalEpsilon][i//.sublegs]};
expr2//.{
SHA[\[Lambda][i_,p],\[Alpha]_]/;MemberQ[Mslegs,i]:> SHA[i//.sublegs,\[Alpha]],
SHB[\[Lambda][i_,m],\[Alpha]_]/;MemberQ[Mslegs,i]:> SHB[i//.sublegs,\[Alpha]],
SHAA[\[Mu]___,\[Lambda][i_,p],\[Rho]___]/;MemberQ[Mslegs,i]:> SHAA[\[Mu],i//.sublegs,\[Rho]],
SHBB[\[Mu]___,\[Lambda][i_,m],\[Rho]___]/;MemberQ[Mslegs,i]:> SHBB[\[Mu],i//.sublegs,\[Rho]],
SHAB[\[Lambda][i_,p],\[Mu]_,\[Rho]_]/;MemberQ[Mslegs,i]:> SHAB[i//.sublegs,\[Mu],\[Rho]],
SHAB[\[Mu]_,\[Rho]_,\[Lambda][i_,m]]/;MemberQ[Mslegs,i]:> SHAB[\[Mu],\[Rho],i//.sublegs],
SHAB[\[Mu]_,i_,\[Nu]_]/;MemberQ[Mslegs,i]:> SHAA[\[Mu],i//.sublegs]SHBB[\[Nu],i//.sublegs]+SHAA[\[Mu],\[Lambda][i//.sublegs,m]]SHBB[\[Nu],\[Lambda][i//.sublegs,p]],
SHBA[\[Lambda][i_,m],\[Mu]_,\[Rho]_]/;MemberQ[Mslegs,i]:> SHBA[i//.sublegs,\[Mu],\[Rho]],
SHBA[\[Mu]_,\[Rho]_,\[Lambda][i_,p]]/;MemberQ[Mslegs,i]:> SHBA[\[Mu],\[Rho],i//.sublegs],
SHBA[\[Mu]_,i_,\[Nu]_]/;MemberQ[Mslegs,i]:> SHAA[\[Nu],i//.sublegs]SHBB[\[Mu],i//.sublegs]+SHAA[\[Nu],\[Lambda][i//.sublegs,m]]SHBB[\[Mu],\[Lambda][i//.sublegs,p]]
}//.{\[Theta][i_]/;MemberQ[Mslegs,i]:>\[Theta][i//.sublegs],\[Phi][i_]/;MemberQ[Mslegs,i]:>\[Phi][i//.sublegs], p[i_][a_]/;MemberQ[Mslegs,i]:> p[i//.sublegs][a],Modp[i_]/;MemberQ[Mslegs,i]:> Modp[i//.sublegs]} ];


(* ::Section:: *)
(*ToMassless*)


(* ::Input::Initialization:: *)
ToMassless[list_List][expr_]:=Composition[Sequence@@Map[ToMassless[#]&,list]][expr];
ToMassless[i_->{\[Lambda]1_,\[Lambda]2_}][expr_]/;MsQ[i]:=Module[{expr1,expr2},
DeclareLegs[][{\[Lambda]1,\[Lambda]2}];
expr1=expr//ToDimensionfullBasis[{i}]//SU2LGBasisComponent//SU2LRInnerProduct[{i}]//HighEnergyLimit[{i->\[Lambda]1}];
expr2=expr1//.{X_[\[Mu]___,\[Lambda][i,m_],\[Nu]___]:> X[\[Mu],\[Lambda]2,\[Nu]]}//PutMasslessLGScalarFor[_,\[Lambda]1,_]//PutMasslessLGScalarFor[_,\[Lambda]2,_]
]


(* ::Section:: *)
(*Ignore*)


Print["Loaded: HighEnergyLimit"]
