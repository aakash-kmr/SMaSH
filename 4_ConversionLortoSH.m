(* ::Package:: *)

(* ::Section:: *)
(*Change Metric and Clifford algebra conventions*)


(* ::Input::Initialization:: *)
MetricConvention:=+1;
CliffordConvention:=-1;


Conventions:={MetricConvention,CliffordConvention};


ChangeConventions[metricconvention_:MetricConvention][cliffordconvention_:MetricConvention]/;metricconvention*cliffordconvention==+1:=Module[{},
Convention::neg="Convention product should be -1 to be consistent with the current choices of Levi-Civita bilinears.";
Message[Convention::neg]
]


(* ::Input::Initialization:: *)
ChangeConventions[metricconvention_:MetricConvention][cliffordconvention_:CliffordConvention]/;metricconvention*cliffordconvention==-1:=Module[{},If[metricconvention===MetricConvention,MetricConvention=MetricConvention,MetricConvention=metricconvention];If[cliffordconvention===CliffordConvention,CliffordConvention=CliffordConvention,CliffordConvention=cliffordconvention];
Conventions:={MetricConvention,CliffordConvention};
];


(* ::Section:: *)
(*Lorentz to SH Converter New*)


PickPosition[X_,a_]:=ToExpression[StringTake[ToString[X],a],StandardForm];

ExpandScalar[expr_]:=expr//.{SP[X_]:> SP[Expand[X ]]}


(* ::Input::Initialization:: *)
ToSP[expr_]:=expr//.{B3_[\[Mu]_,\[Nu]_]/;MemberQ[AllMasslessFieldStrengths[],B3]&&Not[OrderedQ[{\[Mu],\[Nu]}]]:>-B3[Sequence@@Sort[{\[Mu],\[Nu]}]]}//.{
X_[\[Mu]_]Y_[\[Nu]_]/;\[Mu]+\[Nu]==0:> SP[X[\[Mu]]Y[-\[Mu]]],
X_[a1_]Y_[a2_,a3_]Z_[a4_]/;a1+a2==0&&a3+a4==0:> SP[X[a1]Y[a2,a3]Z[a4]],
SP[z___]:> SP[z]
}
SP[-x_]:=-SP[x];


(* ::Input::Initialization:: *)
RunLortoSHConversionRules[]:=Module[{},
ConvertMettoSHRules:={
\[Eta][\[Mu]_,\[Nu]_]:> -2 \[Epsilon][-Lidx[{\[Alpha],MI[\[Eta],\[Mu]]}],-Lidx[{\[Alpha],MI[\[Eta],\[Nu]]}]]\[Epsilon]d[-Ridx[{\[Alpha],MI[\[Eta],\[Mu]]}],-Ridx[{\[Alpha],MI[\[Eta],\[Nu]]}]] \[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[\[Eta],\[Mu]]}],Ridx[{\[Alpha],MI[\[Eta],\[Mu]]}]]/2 \[Sigma]mat[\[Nu]][Lidx[{\[Alpha],MI[\[Eta],\[Nu]]}],Ridx[{\[Alpha],MI[\[Eta],\[Nu]]}]]/2,				epsilon\[Eta][\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_]:>- iota 4( \[Epsilon][-Lidx[{\[Alpha],MI[e\[Eta],\[Mu]]}],-Lidx[{\[Alpha],MI[e\[Eta],\[Rho]]}]]\[Epsilon][-Lidx[{\[Alpha],MI[e\[Eta],\[Nu]]}],-Lidx[{\[Alpha],MI[e\[Eta],\[Sigma]]}]]\[Epsilon]d[-Ridx[{\[Alpha],MI[e\[Eta],\[Mu]]}],-Ridx[{\[Alpha],MI[e\[Eta],\[Sigma]]}]]\[Epsilon]d[-Ridx[{\[Alpha],MI[e\[Eta],\[Nu]]}],-Ridx[{\[Alpha],MI[e\[Eta],\[Rho]]}]]-\[Epsilon][-Lidx[{\[Alpha],MI[e\[Eta],\[Mu]]}],-Lidx[{\[Alpha],MI[e\[Eta],\[Sigma]]}]]\[Epsilon][-Lidx[{\[Alpha],MI[e\[Eta],\[Nu]]}],-Lidx[{\[Alpha],MI[e\[Eta],\[Rho]]}]]\[Epsilon]d[-Ridx[{\[Alpha],MI[e\[Eta],\[Mu]]}],-Ridx[{\[Alpha],MI[e\[Eta],\[Rho]]}]]\[Epsilon]d[-Ridx[{\[Alpha],MI[e\[Eta],\[Nu]]}],-Ridx[{\[Alpha],MI[e\[Eta],\[Sigma]]}]]) \[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[e\[Eta],\[Mu]]}],Ridx[{\[Alpha],MI[e\[Eta],\[Mu]]}]]/2 \[Sigma]mat[\[Nu]][Lidx[{\[Alpha],MI[e\[Eta],\[Nu]]}],Ridx[{\[Alpha],MI[e\[Eta],\[Nu]]}]]/2 \[Sigma]mat[\[Rho]][Lidx[{\[Alpha],MI[e\[Eta],\[Rho]]}],Ridx[{\[Alpha],MI[e\[Eta],\[Rho]]}]]/2 \[Sigma]mat[\[Sigma]][Lidx[{\[Alpha],MI[e\[Eta],\[Sigma]]}],Ridx[{\[Alpha],MI[e\[Eta],\[Sigma]]}]]/2
}//.iota:> I;

ConvertMomtoSHRules[Legs_:AllLegs[],MomHeads_:AllMomenta[]]:={X_[\[Mu]_]/;MemberQ[MomHeads,X]:>  MetricConvention(-(1/2)\[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[X,\[Mu]]}],Ridx[{\[Alpha],MI[X,\[Mu]]}]]Mom[Legs[[Sequence@@First@Flatten@Position[MomHeads,X]]],-Lidx[{\[Alpha], MI[X,\[Mu]]}],-Ridx[{\[Alpha], MI[X,\[Mu]]}]])
};
ConvertMsPoltoSHRules[legs_:AllMassiveLegs[],polheads_:AllMassivePolarizations[]]:={
X_[\[Mu]_]/;MemberQ[polheads,X]:> MetricConvention( -(1/2)\[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[X,\[Mu]]}],Ridx[{\[Beta],MI[X,\[Mu]]}]]MsPol[legs[[Sequence@@First@Flatten@Position[polheads,X]]],-Lidx[{\[Alpha], MI[X,\[Mu]]}],-Ridx[{\[Beta],MI[X,\[Mu]]}],MsIndex[J, MIL[{legs[[Sequence@@First@Flatten@Position[polheads,X]]],1}]],MsIndex[J,MIL[{ legs[[Sequence@@First@Flatten@Position[polheads,X]]],2}]]])
};

ConvertMlPoltoSHRules[legs_:AllMasslessLegs[],polheads_:AllMasslessPolarizations[],hel_:AllMasslessHelicities[],refs_:AllMasslessReferenceSpinors[]]:={
X_[\[Mu]_]/;MemberQ[polheads,X]:> MetricConvention( -(1/2)\[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[X,\[Mu]]}],Ridx[{\[Alpha],MI[X,\[Mu]]}]]MlPol[legs[[Sequence@@First@Flatten@Position[polheads,X]]],-Lidx[{\[Alpha], MI[X,\[Mu]]}],-Ridx[{\[Alpha], MI[X,\[Mu]]}],hel[[Sequence@@First@Flatten@Position[polheads,X]]],refs[[Sequence@@First@Flatten@Position[polheads,X]]]])
};

ConvertMlFStoSHRules[legs_:AllMasslessLegs[],fsheads_:AllMasslessFieldStrengths[],hel_:AllMasslessHelicities[]]:={
B3_[\[Mu]_,\[Nu]_]/;MemberQ[fsheads,B3]:>				KroneckerDelta[hel[[Sequence@@First@Flatten@Position[fsheads,B3]]],1] (Sqrt[2]/4 SHB[legs[[Sequence@@First@Flatten@Position[fsheads,B3]]],-Lidx[{\[Alpha],MI[B3,\[Mu]]}]] SHB[legs[[Sequence@@First@Flatten@Position[fsheads,B3]]],-Lidx[{\[Alpha],MI[B3,\[Nu]]}]] \[Epsilon]d[-Ridx[{\[Alpha],MI[B3,\[Mu]]}],-Ridx[{\[Alpha],MI[B3,\[Nu]]}]]\[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[B3,\[Mu]]}],Ridx[{\[Alpha],MI[B3,\[Mu]]}]]\[Sigma]mat[\[Nu]][Lidx[{\[Alpha],MI[B3,\[Nu]]}],Ridx[{\[Alpha],MI[B3,\[Nu]]}]])+KroneckerDelta[hel[[Sequence@@First@Flatten@Position[fsheads,B3]]],-1]( Sqrt[2]/4 SHA[legs[[Sequence@@First@Flatten@Position[fsheads,B3]]],-Ridx[{\[Alpha],MI[B3,\[Mu]]}]] SHA[legs[[Sequence@@First@Flatten@Position[fsheads,B3]]],-Ridx[{\[Alpha],MI[B3,\[Nu]]}]] \[Epsilon][-Lidx[{\[Alpha],MI[B3,\[Mu]]}],-Lidx[{\[Alpha],MI[B3,\[Nu]]}]]\[Sigma]mat[\[Mu]][Lidx[{\[Alpha],MI[B3,\[Mu]]}],Ridx[{\[Alpha],MI[B3,\[Mu]]}]]\[Sigma]mat[\[Nu]][Lidx[{\[Alpha],MI[B3,\[Nu]]}],Ridx[{\[Alpha],MI[B3,\[Nu]]}]])
};

];

RunLortoSHConversionRules[];


(* ::Input::Initialization:: *)
ConvertMettoSH[expr_]:=Module[{},RunLortoSHConversionRules[];expr//.ConvertMettoSHRules//CanonicalizeIndices];
ConvertMomtoSH[h___][expr_]:=Module[{},RunLortoSHConversionRules[];expr//.ConvertMomtoSHRules[h]//CanonicalizeIndices];
ConvertMsPoltoSH[h___][expr_]:=Module[{},RunLortoSHConversionRules[];expr//.ConvertMsPoltoSHRules[h]//CanonicalizeIndices];
ConvertMlPoltoSH[h___][expr_]:=Module[{},RunLortoSHConversionRules[];expr//.ConvertMlPoltoSHRules[h]//CanonicalizeIndices];
ConvertMlFStoSH[h___][expr_]:=Module[{},RunLortoSHConversionRules[];expr//.ConvertMlFStoSHRules[h]//CanonicalizeIndices];


(* ::Input::Initialization:: *)
RunConvertLortoSHRules[]:=Module[{},ConvertLortoSHRules[mslegs_:AllMassiveLegs[],msmomheads_:AllMassiveMomenta[],mspolheads_:AllMassivePolarizations[]][mllegs_:AllMasslessLegs[],mlmomheads_:AllMasslessMomenta[],mlpolheads_:AllMasslessPolarizations[],fsheads_:AllMasslessFieldStrengths[],hel_:AllMasslessHelicities[],mlrefs_:AllMasslessReferenceSpinors[]]:=Join[ConvertMettoSHRules,ConvertMomtoSHRules[Join[mslegs,mllegs],Join[msmomheads,mlmomheads]],ConvertMsPoltoSHRules[mslegs,mspolheads],ConvertMlPoltoSHRules[mllegs,mlpolheads,hel,mlrefs],ConvertMlFStoSHRules[mllegs,fsheads,hel]]];
RunConvertLortoSHRules[];
ConvertLortoSH[h1___][h2___][expr_]:=Module[{expr1},RunConvertLortoSHRules[]; 
expr1=expr//ToSP;
expr1//.ConvertLortoSHRules[h1][h2]//ExpandScalar//CanonicalizeIndices//\[Sigma]matRule//SimplifyPolynomial//PutLGScalar//ApplyRule[SP[Z_]:> Z]];


(* ::Title:: *)
(*Ignore*)


Print["Loaded: ConversionLortoSH"]
