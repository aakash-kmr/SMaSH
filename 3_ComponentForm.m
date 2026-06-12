(* ::Package:: *)

(* ::Chapter:: *)
(*SH Component Form*)


(* ::Section:: *)
(*Assumptions*)


(* ::Input::Initialization:: *)
ComponentAssumptions[]:=Module[{},Flatten[
Join[Map[{(m[#]\[Element]Positive),
List@@(\[CapitalEpsilon][#]\[Element]PositiveReals),
List@@(Modp[#]\[Element]PositiveReals),
\[CapitalEpsilon][#]==-p[#][0],
p[#][0]\[Element] Reals,
p[#][1]\[Element] Reals,
p[#][2]\[Element] Reals,
p[#][3]\[Element] Reals, 
\[Theta][#]\[Element] Reals,0<=\[Theta][#]<=\[Pi],
\[Phi][#]\[Element] Reals,0<=\[Phi][#]<2\[Pi],
 \[CapitalEpsilon][#]==Sqrt[m[#]^2+Modp[#]^2]
}&,AllMassiveLegs[]],
Map[{
List@@(\[CapitalEpsilon][#]\[Element]PositiveReals),
List@@(Modp[#]\[Element]PositiveReals),
\[CapitalEpsilon][#]==Modp[#],
\[CapitalEpsilon][#]==-p[#][0],
p[#][0]\[Element] Reals,
p[#][1]\[Element] Reals,
p[#][2]\[Element] Reals,
p[#][3]\[Element] Reals, 
\[Theta][#]\[Element] Reals,0<=\[Theta][#]<=\[Pi],
\[Phi][#]\[Element] Reals,0<=\[Phi][#]<2\[Pi]}&,AllMasslessLegs[]]]]];


(* ::Input::Initialization:: *)
SetComponentFormAssumption[]:=AddAssumptions[ComponentAssumptions[]];
UnsetComponentFormAssumption[]:=RemoveAssumptions[ComponentAssumptions[]];


(* ::Input::Initialization:: *)
ComponentAssumptions[mllegs_]:=Module[{},Flatten[
Map[{m[#]==0,
List@@(\[CapitalEpsilon][#]\[Element]PositiveReals),
List@@(Modp[#]\[Element]PositiveReals),
\[CapitalEpsilon][#]==Modp[#],
p[#][0]\[Element] Reals,
p[#][1]\[Element] Reals,
p[#][2]\[Element] Reals,
p[#][3]\[Element] Reals, 
\[Theta][#]\[Element] Reals,0<=\[Theta][#]<=\[Pi],
\[Phi][#]\[Element] Reals,0<=\[Phi][#]<2\[Pi]}&,mllegs]]];


(* ::Input::Initialization:: *)
SetComponentFormAssumption[mllegs_]:=AddAssumptions[ComponentAssumptions[mllegs]];
UnsetComponentFormAssumption[mllegs_]:=RemoveAssumptions[ComponentAssumptions[mllegs]];


(* ::Section:: *)
(*Utilities*)


(* ::Input::Initialization:: *)
(*Spherical c and s. *)
angc[i_]:=Cos[\[Theta][i]/2];
angs[i_]:=Exp[I \[Phi][i]]Sin[\[Theta][i]/2];
angsC[i_]:=Exp[-I \[Phi][i]]Sin[\[Theta][i]/2]; (*C : Conjugate of angs*)

(*Cartesian c and s. *)
angcc[i_]:=Sqrt[Modp[i]+p[i][3]]/(Sqrt[2] Sqrt[Modp[i]]);
angsc[i_]:=Sqrt[p[i][1]+I p[i][2]]/Sqrt[p[i][1]-I p[i][2]] Sqrt[Modp[i]-p[i][3]]/(Sqrt[2] Sqrt[Modp[i]]);
angsCc[i_]:=Sqrt[p[i][1]-I p[i][2]]/Sqrt[p[i][1]+I p[i][2]] Sqrt[Modp[i]-p[i][3]]/(Sqrt[2] Sqrt[Modp[i]]);(*C : Conjugate of angsc*)



SphericalCoordinates[expr_]:=expr//.{
Sqrt[Modp[i_]+p[i_][3]]:>Sqrt[2 Modp[i]] Cos[\[Theta][i]/2],
Sqrt[Modp[i_]-p[i_][3]]:>Sqrt[2 Modp[i]] Sin[\[Theta][i]/2],
Sqrt[p[i_][1]+I p[i_][2]]/Sqrt[p[i_][1]-I p[i_][2]]:> Exp[I \[Phi][i]],
Sqrt[p[i_][1]-I p[i_][2]]/Sqrt[p[i_][1]+I p[i_][2]]:> Exp[-I \[Phi][i]],
Sqrt[p[i_][1]^2+p[i_][2]^2+p[i_][3]^2]:> Modp[i]
}//.
Thread[{p[i_][0],p[i_][1],p[i_][2],p[i_][3]}:> {-\[CapitalEpsilon][i],Modp[i] Sin[\[Theta][i]]Cos[\[Phi][i]],Modp[i] Sin[\[Theta][i]]Sin[\[Phi][i]],Modp[i] Cos[\[Theta][i]]}];


CartesianCoordinates[expr_]:=expr//.{
\[CapitalEpsilon][i_]:> -p[i][0],
p[i_][a_]:> p[i][a],
\[Theta][i_]:> ArcCos[p[i][3]/Modp[i]],
\[Phi][i_]:> ArcTan[p[i][2],p[i][1]],
Modp[i_]:> Sqrt[p[i][1]^2+p[i][2]^2+p[i][3]^2]
};


(*Momentum vector Subscript[P, \[Mu]]*)
pVecLower[i_]:={p[i][0],p[i][1],p[i][2],p[i][3]};

(*Momentum vector P^\[Mu]*)
pVecUpper[i_]:={-p[i][0],p[i][1],p[i][2],p[i][3]};


(*pMatLower and pMatUpper are the most general momentum matrices.*)
pMatUpper[i_]:={{p[i][0]-p[i][3],-p[i][1]+I p[i][2]},{-p[i][1]-I p[i][2],p[i][0]+p[i][3]}} ;(*Upper p^{\[Alpha]\[Beta]}*)
pMatLower[i_]:={{p[i][0]+p[i][3],p[i][1]-I*p[i][2]},{p[i][1]+I*p[i][2],p[i][0]-p[i][3]}} ; (*Lower p_\[Alpha]\[Beta]*)


(* ::Input::Initialization:: *)
PutOnShellComponent[expr_]:=expr//.{
Sqrt[-Modp[i_]+\[CapitalEpsilon][i_]] :>m[i]/Sqrt[Modp[i]+\[CapitalEpsilon][i]],
Modp[i_]^2+m[i_]^2:> \[CapitalEpsilon][i]^2,
-\[CapitalEpsilon][i_]^2+Modp[i_]^2:> -m[i]^2,
\[CapitalEpsilon][i_]^2-m[i_]^2:> Modp[i]^2,
\[CapitalEpsilon][i_]^2-Modp[i_]^2:> m[i]^2,
-\[CapitalEpsilon][i_]^2+m[i_]^2:> -Modp[i]^2,
m[i_?MlQ]:> 0,
Modp[i_?MlQ]:> \[CapitalEpsilon][i]
};

PutMasslessCondition[masslesslegs_List:AllMasslessLegs[]][expr_]:=expr//.{m[i_]/;MemberQ[masslesslegs,i]:> 0,Modp[i_]/;MemberQ[masslesslegs,i]:> \[CapitalEpsilon][i]};

SimplifyComponentForm[expr_]:=expr//RepeatedRule[PutOnShellComponent[FullSimplify[PowerContract[FullSimplify[PowerExpand[#]]]]]&]


(* ::Section::Closed:: *)
(*Metrics*)


(*Lorentz Metric*)
\[Eta]Mat=DiagonalMatrix[{-1,1,1,1}];


(* ::Input::Initialization:: *)
(*SU2's Metric*)
\[Epsilon]Mat=I PauliMatrix[2];
\[Epsilon]dMat = I PauliMatrix[2];
\[Epsilon]lgMat = I PauliMatrix[2];

\[Delta]Mat= IdentityMatrix[2];
\[Delta]dMat =  IdentityMatrix[2];
\[Delta]lgMat =  IdentityMatrix[2];

\[Epsilon]MatUpper=I PauliMatrix[2];
\[Epsilon]dMatUpper = I PauliMatrix[2];
\[Epsilon]lgMatUpper = I PauliMatrix[2];

\[Epsilon]MatLower=-I PauliMatrix[2];
\[Epsilon]dMatLower= -I PauliMatrix[2];
\[Epsilon]lgMatLower=- I PauliMatrix[2];


(* ::Input::Initialization:: *)
(*\[Sigma]bar always has spinor indices in superscript. \[Sigma] always has spinor indices in the subscript.*)
\[Sigma]VecUpper={IdentityMatrix[2],PauliMatrix[1],PauliMatrix[2],PauliMatrix[3]};(*Subscript[(\[Sigma]^\[Mu]), \[Alpha]\[Beta]] *)
\[Sigma]VecLower={-IdentityMatrix[2],PauliMatrix[1],PauliMatrix[2],PauliMatrix[3]};(*Subscript[Subscript[\[Sigma], \[Mu]], \[Alpha]\[Beta]]*)
\[Sigma]barVecUpper={IdentityMatrix[2],-PauliMatrix[1],-PauliMatrix[2],-PauliMatrix[3]}; (* \[Sigma]b^\[Mu]^\[Beta]\[Alpha]*)
\[Sigma]barVecLower={-IdentityMatrix[2],-PauliMatrix[1],-PauliMatrix[2],-PauliMatrix[3]}; (* Subscript[\[Sigma]b, \[Mu]]^\[Beta]\[Alpha]*)


ApplySHOnShell[expr_]:=(expr//PowerContract)//.{Sqrt[\[CapitalEpsilon][i_]^2-Modp[i_]^2]:>m[i]}


(* ::Section::Closed:: *)
(*Massive*)


(* ::Input::Initialization:: *)
r[B][i_?MsQ[1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angcc[i],angsc[i]}];
r[B][i_?MsQ[2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{angsCc[i],-angcc[i]}];
r[B][i_?MsQ[-1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{-angsCc[i],angcc[i]}];
r[B][i_?MsQ[-2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angcc[i],angsc[i]}];


(* ::Input::Initialization::Bold:: *)
l[B][i_?MsQ[1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angsc[i],-angcc[i]}];
l[B][i_?MsQ[2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{-angcc[i],-angsCc[i]}];
l[B][i_?MsQ[-1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{angcc[i],angsCc[i]}];
l[B][i_?MsQ[-2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angsc[i],-angcc[i]}];


(* ::Input::Initialization::Bold:: *)
l[A][i_?MsQ[1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{angsc[i],-angcc[i]}];
l[A][i_?MsQ[2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{-angcc[i],-angsCc[i]}];
l[A][i_?MsQ[-1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angcc[i],angsCc[i]}];
l[A][i_?MsQ[-2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{angsc[i],-angcc[i]}];


(* ::Input::Initialization::Bold:: *)
r[A][i_?MsQ[1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{-angcc[i],-angsc[i]}];
r[A][i_?MsQ[2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{-angsCc[i],angcc[i]}];
r[A][i_?MsQ[-1]]:=Flatten[Sqrt[\[CapitalEpsilon][i]-Modp[i]]{angsCc[i],-angcc[i]}];
r[A][i_?MsQ[-2]]:=Flatten[Sqrt[\[CapitalEpsilon][i]+Modp[i]]{-angcc[i],-angsc[i]}];


(* ::Input::Initialization:: *)
(*Subscript[\[Zeta], \[Alpha]\[Beta]]*)(*Little group indices are symmetrized.*)
\[Zeta]Lower[i_?MsQ,J_,L_]:=(  (TensorProduct[r[B][i[J]] ,l[A][i[L]]]+TensorProduct[r[B][i[L]] ,l[A][i[J]]])/ m[i](1/Sqrt[2] KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],1]+  KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],2]+1/Sqrt[2] KroneckerDelta[Abs[J],2]KroneckerDelta[Abs[L],2]))//.{m[i]->Sqrt[ \[CapitalEpsilon][i]^2-Modp[i]^2]};

(*\[Zeta]^\[Beta]\[Alpha]*)
\[Zeta]Upper[i_?MsQ,J_,L_]:=(  (TensorProduct[r[A][i[J]] ,l[B][i[L]]]+TensorProduct[r[A][i[L]] ,l[B][i[J]]])/ m[i] (1/Sqrt[2] KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],1]+  KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],2]+1/Sqrt[2] KroneckerDelta[Abs[J],2]KroneckerDelta[Abs[L],2])
)//.{m[i]->Sqrt[ \[CapitalEpsilon][i]^2-Modp[i]^2]};


(* ::Section::Closed:: *)
(*Massless*)


(* ::Input::Initialization:: *)
r[B][i_]/;!MsQ[i]:=Sqrt[2 \[CapitalEpsilon][i]] {angsCc[i],- angcc[i]};
l[B][i_]/;!MsQ[i]:= Sqrt[2 \[CapitalEpsilon][i]]{-angcc[i],-angsCc[i]};
r[A][i_]/;!MsQ[i]:=Sqrt[2 \[CapitalEpsilon][i]] {-angcc[i],-angsc[i]};
l[A][i_]/;!MsQ[i]:=Sqrt[2 \[CapitalEpsilon][i]]{angsc[i],-angcc[i]};


(* ::Input::Initialization:: *)
(*Subscript[\[CurlyEpsilon], \[Alpha]\[Beta]]*)
\[CurlyEpsilon]Lower[i_][ri_,+1]/;!MsQ[i]:=(Sqrt[2]TensorProduct[ r[B][i] ,l[A][ri]]/(l[A][i] . r[A][ri]));
\[CurlyEpsilon]Lower[i_][ri_,-1]/;!MsQ[i]:=(Sqrt[2]TensorProduct[ r[B][ri] ,l[A][i]]/(l[B][ri] . r[B][i]));

(*\[CurlyEpsilon]^\[Beta]\[Alpha]*)
\[CurlyEpsilon]Upper[i_][ri_,+1]/;!MsQ[i]:=(Sqrt[2]TensorProduct [r[A][ri],l[B][i]]/(l[A][i] . r[A][ri]));
\[CurlyEpsilon]Upper[i_][ri_,-1]/;!MsQ[i]:=(Sqrt[2] TensorProduct[r[A][i],l[B][ri]]/(l[B][ri] . r[B][i]));


(* ::Section::Closed:: *)
(*Component Form*)


(* ::Input::Initialization:: *)
ComponentForm[expr_]:=With[{eprN=expr//ExpandAll//ContractMetric//PutSL2CScalar//PutLGScalar},
eprN//. {
X_[\[Mu]___,i_[a_],\[Nu]___]Y_[\[Mu]___,i_[b_],\[Nu]___]/;a+b==0&&Not[IntegerQ[a]]:> With[{sign=SignOf[b]},Sum[X[\[Mu],i[-sign J],\[Nu]]Y[\[Mu],i[sign J],\[Nu]],{J,1,2}]],
	SHBB[i_[a_],j_[b_]]/;a+b==0&&Not[IntegerQ[a]]:>With[{sign=SignOf[b]},Sum[l[B][i[-sign J]] . r[B][j[sign J]],{J,1,2}]],
	SHAA[i_[a_],j_[b_]]/;a+b==0&&Not[IntegerQ[a]]:>With[{sign=SignOf[b]},Sum[l[A][i[-sign J]] . r[A][j[sign J]],{J,1,2}]],SHAA[i_,j_]:>l[A][i] . r[A][j],
	SHBB[i_,j_]:>l[B][i] . r[B][j],
	SHAB[i_[a_],j_,k_[b_]]/;a+b==0&&Not[IntegerQ[a]]:>With[{sign=SignOf[b]},Sum[l[B][k[sign J]] . (pMatLower[j]) . r[A][i[-sign J]],{J,1,2}]],
	SHBA[i_[a_],j_,k_[b_]]/;a+b==0&&Not[IntegerQ[a]]:>With[{sign=SignOf[b]},Sum[l[B][i[- sign J]] . (pMatLower[j]) . r[A][k[sign J]],{J,1,2}]],SHAB[i_,j_,k_]:>l[B][k] . (pMatLower[j]) . r[A][i],
	SHBA[i_,j_,k_]:>l[B][i] . (pMatLower[j]) . r[A][k],
	SHA[i_,\[Alpha]_]:>If[IfP[\[Alpha]],r[A][i],l[A][i]],
	SHB[i_,\[Alpha]_]:> If[IfP[\[Alpha]],l[B][i],r[B][i]],
	\[Epsilon][\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfP[\[Alpha]]&&IfP[\[Beta]]:> \[Epsilon]MatUpper[[\[Alpha]]][[\[Beta]]],\[Epsilon][\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfN[\[Alpha]]&&IfN[\[Beta]]:> \[Epsilon]MatLower[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Delta][\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]:> \[Delta]Mat[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Epsilon]d[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfP[\[Alpha]]&&IfP[\[Beta]]:> \[Epsilon]dMatUpper[[\[Alpha]]][[\[Beta]]],\[Epsilon]d[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfN[\[Alpha]]&&IfN[\[Beta]]:> \[Epsilon]dMatLower[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Delta]d[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]:> \[Delta]dMat[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Epsilon]lg[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfP[\[Alpha]]&&IfP[\[Beta]]:> \[Epsilon]lgMatUpper[[\[Alpha]]][[\[Beta]]],\[Epsilon]lg[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfN[\[Alpha]]&&IfN[\[Beta]]:> \[Epsilon]lgMatLower[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Delta]lg[\[Alpha]_,\[Beta]_]/;IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]:> \[Delta]lgMat[[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]/;IntegerQ[\[Mu]]&&IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfP[\[Mu]]&&IfN[\[Alpha]]&&IfN[\[Beta]]:> \[Sigma]VecUpper[[\[Mu]+1]][[Abs[\[Alpha]]]][[Abs[\[Beta]]]],\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]/;IntegerQ[\[Mu]]&&IntegerQ[\[Alpha]]&&IntegerQ[\[Beta]]&&IfP[\[Mu]]&&IfP[\[Alpha]]&&IfP[\[Beta]]:>\[Sigma]barVecUpper[[\[Mu]+1]][[\[Alpha]]][[\[Beta]]]
}];


(* ::Section::Closed:: *)
(*Compton COM Frame*)


(* ::Input::Initialization:: *)
COMrules[i_]/;i==1:=Thread[{p[i][0],p[i][1],p[i][2],p[i][3],\[CapitalEpsilon][i],Modp[i],\[Theta][i],\[Phi][i]}->{\[CapitalEpsilon][1],0,0,-\[CapitalEpsilon][3],\[CapitalEpsilon][1],\[CapitalEpsilon][3], \[Pi],0 }];
COMrules[i_]/;i==3:= Thread[{p[i][0],p[i][1],p[i][2],p[i][3],\[CapitalEpsilon][i],Modp[i],\[Theta][i],\[Phi][i]}->{\[CapitalEpsilon][3],0,0,\[CapitalEpsilon][3],\[CapitalEpsilon][3],\[CapitalEpsilon][3],0,0}];
COMrules[i_]/;i==2:=Thread[{p[i][0],p[i][1],p[i][2],p[i][3],\[CapitalEpsilon][i],Modp[i],\[Theta][i],\[Phi][i]}->{-\[CapitalEpsilon][1],\[CapitalEpsilon][3]Sin[\[Theta]],0,\[CapitalEpsilon][3]Cos[\[Theta]],-\[CapitalEpsilon][1], \[CapitalEpsilon][3],\[Theta],0 }];
COMrules[i_]/;i==4:= Thread[{p[i][0],p[i][1],p[i][2],p[i][3],\[CapitalEpsilon][i],Modp[i],\[Theta][i],\[Phi][i]}->{-\[CapitalEpsilon][3],-\[CapitalEpsilon][3]Sin[\[Theta]],0,-\[CapitalEpsilon][3]Cos[\[Theta]],-\[CapitalEpsilon][3],\[CapitalEpsilon][3],\[Pi]-\[Theta],\[Pi]}];
ComptonCOMFrame[expr_]:=(expr)//.Flatten[Table[COMrules[i],{i,1,4}]]


(* ::Chapter::Closed:: *)
(*Lorentz COM Conversion*)


(* ::Section:: *)
(*Definitions*)


(* ::Input::Initialization:: *)
Suf[x_, y_]:=ToExpression[ToString[x]<>ToString[y]];
Vector[r0_, r1_, r2_, r3_]:= {{r0}, {r1}, {r2}, {r3}};
\[Eta]Mat = DiagonalMatrix[{-1, 1, 1, 1}];
SP2[v1_List, v2_List]:=( Transpose[v1] . \[Eta]Mat . v2)[[1]][[1]];
SP[OrderlessPatternSequence[v1_, v2_]]:= Scalar[v1[a]v2[-a]];


(* ::Input::Initialization:: *)
\[Zeta]1[1]= (-1/Sqrt[2])Vector[0, 1, I, 0];
\[Zeta]1[0] = (1/m)Vector[p, 0,0, \[CapitalEpsilon]]; 
\[Zeta]1[-1] = (1/Sqrt[2])Vector[0, 1, -I, 0];

\[Zeta]2[1] = (-1/Sqrt[2])Vector[0, -1, I, 0];
\[Zeta]2[0] = (1/m)Vector[p, 0,0,- \[CapitalEpsilon]];
 \[Zeta]2[-1] = (1/Sqrt[2])Vector[0, -1, -I, 0];

\[CurlyEpsilon]3[1]= (1/Sqrt[2])Vector[0 , 1,-I  Cos[\[Theta]],  I Sin[\[Theta]]]; 
\[CurlyEpsilon]3[-1]= (1/Sqrt[2])Vector[0, 1,I  Cos[\[Theta]],- I Sin[\[Theta]]]; 
\[CurlyEpsilon]4[1]= (1/Sqrt[2])Vector[0 , 1,  I Cos[\[Theta]],- I  Sin[\[Theta]]]; 
\[CurlyEpsilon]4[-1]= (1/Sqrt[2])Vector[0, 1,- I Cos[\[Theta]], I Sin[\[Theta]]];

k1[0] = Vector[\[CapitalEpsilon], 0, 0, p];
k2[0]= Vector[\[CapitalEpsilon], 0, 0,- p];
k3[0]= Vector[-\[CapitalEpsilon], 0, -\[CapitalEpsilon] Sin[\[Theta]], -\[CapitalEpsilon] Cos[\[Theta]]];
k4[0]= Vector[-\[CapitalEpsilon], 0, \[CapitalEpsilon] Sin[\[Theta]], \[CapitalEpsilon] Cos[\[Theta]]];


(* ::Input::Initialization:: *)
BasisBlocks = Join[
{SP[\[Zeta]1, \[Zeta]2], SP[\[CurlyEpsilon]3, \[Zeta]1], SP[\[CurlyEpsilon]4, \[Zeta]1], SP[\[CurlyEpsilon]3, \[Zeta]2], SP[\[CurlyEpsilon]4, \[Zeta]2], SP[\[CurlyEpsilon]3, \[CurlyEpsilon]4]}, Flatten[Table[SP[Suf[k, j], Suf[\[Zeta], i]], {i, 1, 4}, {j,Join[Range[1,i-1], Range[i+1, 4]]}]]]/.{\[Zeta]3->\[CurlyEpsilon]3, \[Zeta]4->\[CurlyEpsilon]4};

BasisBlocksCOM[h__] :=Join[
{SP2[\[Zeta]1[{h}[[1]]], \[Zeta]2[{h}[[2]]]], SP2[\[CurlyEpsilon]3[{h}[[3]]], \[Zeta]1[{h}[[1]]]], SP2[\[CurlyEpsilon]4[{h}[[4]]], \[Zeta]1[{h}[[1]]]], SP2[\[CurlyEpsilon]3[{h}[[3]]], \[Zeta]2[{h}[[2]]]], SP2[\[CurlyEpsilon]4[{h}[[4]]], \[Zeta]2[{h}[[2]]]], SP2[\[CurlyEpsilon]3[{h}[[3]]], \[CurlyEpsilon]4[{h}[[4]]]]}, Flatten[Table[SP2[Suf[\[Zeta], i][{h}[[i]]],Suf[k, j][0]], {i, 1, 4}, {j,Join[Range[1,i-1], Range[i+1, 4]]}]]]/.{\[Zeta]3->\[CurlyEpsilon]3,\[Zeta]4->\[CurlyEpsilon]4}/.{m->Sqrt[\[CapitalEpsilon]^2-p^2]}//FullSimplify;

BasisBlocksSHCOM[h1_, h2_, h3_, h4_] := Map[FullSimplify[ComptonCOMFrame[ComponentForm[Convert[#, h3, h4, 4, 3]/.Join[Thread[{bf[J1], bf[L1]}->{{2,2}, {1,2}, {1,1}}[[h1+2]]], Thread[{bf[J2], bf[L2]}->{{2,2}, {1,2}, {1,1}}[[h2+2]]]]]]]&, BasisBlocks ]/.{m[1]->m, m[2]->m}/.{m->Sqrt[\[CapitalEpsilon]^2-p^2]}//FullSimplify;


(* ::Input::Initialization:: *)
LorentzCOMrule[h__][expr_]:=expr//.Thread[BasisBlocks-> BasisBlocksCOM[h]]


(* ::Chapter:: *)
(*Numerics*)


(* ::Section:: *)
(*Mass conditions and Lorentz Boost*)


(* ::Input::Initialization:: *)
(*MassConditions[expr_]:=Module[{MassEqualities,Equalities,AllMasses,exprList},AllMasses=DeleteDuplicates@Map[m,AllLegs[]];
Equalities[e_,pat_]:=Module[{stripped},stripped=e/. pat->0;
!FreeQ[e,pat]&&FreeQ[stripped,s_Symbol/;Context[s]=!="System`",{0,Infinity},Heads->True]];
(*Safely convert to list whether it is an And,List,or a single Equation*)
exprList=If[MatchQ[Head[expr],And|List],List@@expr,{expr}];
MassEqualities=Cases[exprList,e_/;Equalities[e,m[_]]]];*)


MassConditions[expr_]:=Cases[expr,a_/;!FreeQ[a,m[_]]];


(* ::Input::Initialization:: *)
CheckOnShell[E_]:=With[{masses=MassNumerics[E][[;;,1]],massNumerics=MassNumerics[E][[;;,2]],momenta=MomentaNumerics[E][[;;,1]],momentaNumerics=MomentaNumerics[E][[;;,2]]},onshellconds=Chop[Map[momentaNumerics[[#]] . \[Eta]Mat . momentaNumerics[[#]]+ massNumerics[[#]]^2&,Range[Length[massNumerics]]],10^-6]//Chop;And@@Thread[onshellconds==0]
]


(* ::Input::Initialization:: *)
(*Boosts p along q*)

LabBoost[Q_,p_]:=Module[{M,E0,Pvec,p0,pvec,gamma,beta,nDir,p0New,pvecNew},E0=Q[[1]];
Pvec=Rest[Q];
M=Sqrt[E0^2-Pvec . Pvec];
If[Norm[Pvec]==0,Return[p]];
p0=p[[1]];
pvec=Rest[p];
gamma=E0/M;
beta=Norm[Pvec]/E0;
nDir=Pvec/Norm[Pvec];
p0New=gamma*(p0+beta*Dot[pvec,nDir]);
pvecNew=pvec+((gamma-1)*Dot[pvec,nDir]+gamma*beta*p0)*nDir;
Join[{p0New},pvecNew]];


(* ::Input::Initialization:: *)
(*1. Lorentz Boost Utility*)(*Boosts a 4-momentum p into a frame moving with velocity v*)LorentzBoost[p_,v_]:=Module[{gamma,vSq,vDotp,p0,pVec},p0=p[[1]];
pVec=p[[2;;4]];
vSq=v . v;
If[vSq==0,Return[p]];
gamma=1/Sqrt[1-vSq];
vDotp=v . pVec;
Join[{gamma (p0-vDotp)},pVec+v (gamma^2/(gamma+1) vDotp-gamma p0)]]



(* ::Section::Closed:: *)
(*Rambo*)


(* ::Input::Initialization:: *)
RAMBO[0,sqrts_,numEffMassesNeg_,iterations_:20,allseeds_:Table[Automatic,{10000}]]:=Module[{},{}];


(* ::Input::Initialization:: *)
RAMBO[1,sqrts_,masses_List,iterations_:20,allseeds_:Table[Automatic,{10000}]]:=Module[{rawQ,totalQ,beta,boostedQ,scaledQ,xi,xiNext,f,fPrime,pFinal,p3Mag2},
(*Sanity check for kinematic threshold*)
If[Total[masses]>sqrts,Print["Error: Total mass exceeds available CM energy."];
Return[$Failed]];
pFinal=With[{
u1=(SeedRandom[allseeds[[1]]];RandomReal[]),u2=(SeedRandom[allseeds[[2]]];RandomReal[])},With[{costh=2 u1-1,phi=2 Pi u2,e=sqrts},{e,Sqrt[e^2-masses[[1]]^2] Sqrt[1-costh^2] Cos[phi],Sqrt[e^2-masses[[1]]^2] Sqrt[1-costh^2] Sin[phi],Sqrt[e^2-masses[[1]]^2] costh}]]

];

RAMBO[n_,sqrts_,masses_List,iterations_:20,allseeds_:Table[Automatic,{10000}]]/;n>1:=Module[{rawQ,totalQ,beta,boostedQ,scaledQ,xi,xiNext,f,fPrime,pFinal,p3Mag2},
(* check for kinematic threshold*)
If[Total[masses]>sqrts,Print["Error: Total mass exceeds available CM energy."];
Return[$Failed]];
(*Step 1:Generate n random momenta*)rawQ=Table[With[{u1=(SeedRandom[allseeds[[3i$-2]]];RandomReal[]),u2=(SeedRandom[allseeds[[3i$-1]]];RandomReal[]),u3=(SeedRandom[allseeds[[3i$]]];RandomReal[])},With[{costh=2 u1-1,phi=2 Pi u2,e=-Log[u3]},{e,e Sqrt[1-costh^2] Cos[phi],e Sqrt[1-costh^2] Sin[phi],e costh}]],{i$,1,n}];
(*Step 2:Calculate their sum and boost them to their own CM frame*)totalQ=Total[rawQ];
beta=totalQ[[2;;4]]/totalQ[[1]];
boostedQ=Map[LorentzBoost[#,beta]&,rawQ];
(*Step 3:Scale to desired COM energy (assuming massless)*)
scaledQ=boostedQ*(sqrts/Sqrt[totalQ[[1]]^2-totalQ[[2;;4]] . totalQ[[2;;4]]]);
(*Step 4:Apply mass corrections (skip if all particles are massless)*)
If[Total[masses]==0,Return[scaledQ]];
(*Extract spatial momentum squared for the Newton-Raphson solver*)
p3Mag2=Map[#[[2;;4]] . #[[2;;4]]&,scaledQ];
(*Newton-Raphson iteration to find the scale factor xi*)
xi=Sqrt[1-(Total[masses]/sqrts)^2];(*initial guess*)
Catch[Do[f=Total[Sqrt[masses^2+xi^2 p3Mag2]]-sqrts;
fPrime=Total[(xi p3Mag2)/Sqrt[masses^2+xi^2 p3Mag2]];
xiNext=xi-f/fPrime;
If[Abs[xiNext-xi]<10^-10,Throw[xi=xiNext]];
xi=xiNext,{iterations} (*Max iterations*)]];
(*Step 5:Construct the final on-shell,momentum-conserving 4-vectors*)pFinal=Table[Join[{Sqrt[masses[[k]]^2+xi^2 p3Mag2[[k]]]},xi scaledQ[[k,2;;4]]],{k,1,n}];
If[n==1,pFinal[[1]],pFinal]]


(* ::Section:: *)
(*generate numerics*)


(* ::Subsection::Closed:: *)
(*1->n*)


GenerateNumerics1n[label_,n_,sqrts_,Legs_,kVars_,{keys_,values_},{incomingks_,outgoingks_},{inks_,outks_},massConstraints1_,COM_,iterations_,allseeds_]:=Module[{incomingkcoeff,outgoingkscoeff,coefficients,mvars,incomingm,outgoingms,incomingkvec,numericMasses,Finalincomingk,Finaloutgoingks,z,effMasses,effMassesConstraint,massConstraints,allConstraints,objective,optRes,effnumericmasses,unitdirection,pFinal,incomingkz,outgoingkzs,kmag,partitionz,parentTarget
},(*1. Parse the arbitrary kinematic expression*)
incomingkcoeff=Coefficient[keys,incomingks];
outgoingkscoeff=Coefficient[values,outgoingks];
coefficients=Join[incomingkcoeff,outgoingkscoeff];
mvars=Map[m,Legs];
massConstraints=Cases[massConstraints1//.Thread[AllMomenta[]->AllLegs[]],dummya_/;!FreeQ[dummya,m[dummyx_]/;MemberQ[Legs,dummyx]]];

(*Generate initial spatial vector*)incomingkvec=With[{u1=(SeedRandom[allseeds[[1]]];RandomReal[]),u2=(SeedRandom[allseeds[[2]]];RandomReal[])},With[{costh=2 u1-1,phi=2 Pi u2},kmag=(SeedRandom[allseeds[[3]]];RandomReal[{0,sqrts}]);
kmag {Sqrt[1-costh^2] Cos[phi],Sqrt[1-costh^2] Sin[phi],costh}]];

(*Check if parent is massless*)
If[TrueQ[Simplify[mvars[[1]]==0,Assumptions->And@@massConstraints]],
(*Massless decay branch*)
If[!AllTrue[mvars[[2;;]],TrueQ[Simplify[#==0,Assumptions->And@@massConstraints]]&],(Print[Style["A massless particle can only decay to massless particles. Assuming all particles are massless.",Bold]])];
numericMasses=Table[0,{n}];
Finalincomingk=Join[{kmag},incomingkvec];
z=If[n>=2,Sort@(SeedRandom[allseeds[[4]]];RandomReal[{0,1},n-2]),{0}];
partitionz=Differences[Join[{0},z,{1}]];
Finaloutgoingks=Map[partitionz[[#]]*Finalincomingk&,Range[1,n-1]];,

If[!TrueQ[Simplify[mvars[[1]]==0,Assumptions->And@@massConstraints]],
Print[Style["Massive decay",Bold] ];
(*Massive Decay Branch*)
parentTarget=(SeedRandom[allseeds[[5]]];RandomReal[{sqrts/10,sqrts}]);
effMasses=Map[Abs[coefficients[[#]]]*mvars[[#]]&,Range[1,n]];
effMassesConstraint={Total[effMasses[[2;;]]]<=effMasses[[1]]<=sqrts};
allConstraints=Join[massConstraints,Thread[mvars>=0],effMassesConstraint]//.Thread[AllMomenta[]->AllLegs[]];
objective=(mvars[[1]]-parentTarget)^2+Total[MapIndexed[(#1-(SeedRandom[allseeds[[5+First[#2]]]];RandomReal[{0,sqrts/10}]))^2&,mvars[[2;;]]]];
optRes=NMinimize[{objective,allConstraints},mvars];
numericMasses=mvars/. optRes[[2]];If[n==2,Print[" 1 -> 1 is a trivial scattering. The masses must be same."];numericMasses[[2]]=Abs[coefficients[[1]]]/Abs[coefficients[[2]]] numericMasses[[1]],numericMasses];
effnumericmasses=Map[Abs[coefficients[[#]]] numericMasses[[#]]&,Range[1,n]]//Chop;
incomingkz={effnumericmasses[[1]],0,0,0};
outgoingkzs=If[n==2,{incomingkz},RAMBO[n-1,effnumericmasses[[1]],effnumericmasses[[2;;]],iterations,allseeds[[6;;5+3 n]]]];

If[!COM,unitdirection=Join[{Sqrt[kmag^2+effnumericmasses[[1]]^2]},incomingkvec];
Finalincomingk=LabBoost[unitdirection,incomingkz];
Finaloutgoingks=Map[LabBoost[unitdirection,outgoingkzs[[#]]]&,Range[1,n-1]];,Finalincomingk=Chop[incomingkz];
Finaloutgoingks=Chop[outgoingkzs];]]

];


(*Scaling the momenta back*)
pFinal=Table[0,{n}];
pFinal[[1]]=Finalincomingk/coefficients[[1]];
Do[pFinal[[i+1]]=Finaloutgoingks[[i]]/coefficients[[i+1]],{i,n-1}];
MassNumerics[label]=Thread[mvars->Chop[numericMasses]];
MomentaNumerics[label]=Thread[kVars->Chop[pFinal]];
(*Print["Mass numerics generated : ",MassNumerics[label]];
Print["Momenta numerics generated : ",TableForm[MomentaNumerics[label]]];*)
{TableForm[MassNumerics[label]],TableForm[MomentaNumerics[label]]}

]


(* ::Subsection::Closed:: *)
(*n->m (n != 1)*)


(* ::Input::Initialization:: *)
GenerateNumericsn1[label_,n_,sqrts_,Legs_,kVars_,{keys_,values_},{incomingks_,outgoingks_},{inks_,outks_},massConstraints1_,COM_,iterations_,allseeds_]:=Module[{incomingkscoeff,outgoingkscoeff,coefficients,mvars,incomingms,outgoingms,ineffMasses,outeffMasses,ineffMassesConstraint,outeffMassesConstraint,massConstraints,allConstraints,thresholdConstraint,objective,optRes,numericMasses,incomingkvec,kmag,Finaloutgoingks0,Finaloutgoingks,z,partitionz,Finalincomingks0,Finalincomingks,ineffnumMasses,outeffnumMasses,pFinal},
(*1. Parse the arbitrary kinematic expression*)
incomingkscoeff=Coefficient[keys,incomingks];
outgoingkscoeff=Coefficient[values,outgoingks];
coefficients=Join[incomingkscoeff,outgoingkscoeff];
mvars=Map[m,Legs];incomingms=mvars[[1;;inks]];outgoingms=mvars[[inks+1;;]];

massConstraints=Cases[massConstraints1//.Thread[AllMomenta[]->AllLegs[]],dummya_/;!FreeQ[dummya,m[dummyx_]/;MemberQ[Legs,dummyx]]];
(*2. Mass constraints*)
If[!(outks==1&&TrueQ[Simplify[mvars[[n]]==0,Assumptions->And@@massConstraints]]),
ineffMasses=Map[Abs[incomingkscoeff[[#]]]*incomingms[[#]]&,Range[1,inks]];
outeffMasses=Map[Abs[outgoingkscoeff[[#]]]*outgoingms[[#]]&,Range[1,n-inks]];
ineffMassesConstraint=0<=Total[ineffMasses]<=sqrts;
outeffMassesConstraint=0<=Total[outeffMasses]<=sqrts;
thresholdConstraint=If[outks==1,Total[mvars[[inks+1;;]]]-Total[mvars[[1;;inks]]]>=10^(-MantissaExponent[sqrts][[2]]+2),True];allConstraints=Join[massConstraints,Thread[mvars>=0],{ineffMassesConstraint,outeffMassesConstraint,thresholdConstraint}]//.Thread[AllMomenta[]->AllLegs[]];
objective=Total[MapIndexed[(m[#1]-(SeedRandom[allseeds[[First[#2]]]];RandomReal[{sqrts/10000,sqrts/10}]))^2&,Legs]];
(*3. solve for numeric values of mass*)
optRes=NMinimize[{objective,allConstraints},mvars];
numericMasses=mvars/. optRes[[2]];];


(*4. Generate initial spatial vector*)incomingkvec=With[{u1=(SeedRandom[allseeds[[n+1]]];RandomReal[]),u2=(SeedRandom[allseeds[[n+2]]];RandomReal[])},With[{costh=2 u1-1,phi=2 Pi u2},kmag=(SeedRandom[allseeds[[n+3]]];RandomReal[{0,sqrts}]);
kmag {Sqrt[1-costh^2] Cos[phi],Sqrt[1-costh^2] Sin[phi],costh}]];

(*5. We divide the code for outks==1 and outks != 1*)
If[outks==1,

If[AllTrue[{mvars[[n]]},TrueQ[Simplify[#==0,Assumptions->And@@massConstraints]]&],
Print[Style["Fusion to a massless particle is possible only if all the incoming momenta are massless and collinear. Assuming all particles are massless.",Bold]];
numericMasses=Table[0,{n}];
Finaloutgoingks0={Join[{kmag},incomingkvec]};
z=If[n>=2,Sort@(SeedRandom[allseeds[[n+4]]];RandomReal[{0,1},n-2]),{0}];
partitionz=Differences[Join[{0},z,{1}]];
Finalincomingks0=Map[partitionz[[#]]*Finaloutgoingks0[[1]]&,Range[1,n-1]];,


ineffnumMasses=Map[Abs[incomingkscoeff[[#]]]*numericMasses[[#]]&,Range[1,inks]];
Finalincomingks0=RAMBO[inks,numericMasses[[n]],numericMasses[[1;;inks]],iterations,allseeds[[n+5;;n+4+3 inks]]];
Finaloutgoingks0={{numericMasses[[n]],0,0,0}};
],


ineffnumMasses=Map[Abs[incomingkscoeff[[#]]]*numericMasses[[#]]&,Range[1,inks]];
outeffnumMasses=Map[Abs[outgoingkscoeff[[#]]]*numericMasses[[inks+#]]&,Range[1,outks]];
Finalincomingks0=RAMBO[inks,sqrts,ineffnumMasses,iterations,allseeds[[n+5+3inks;;n+4+6inks]]];
Finaloutgoingks0=RAMBO[outks,sqrts,outeffnumMasses,iterations,allseeds[[n+5+6 inks;; n+4+ 6 inks+ 3 outks ]]];
];

(* If boost is true or false*)
If[!COM,unitdirection=Join[{Sqrt[kmag^2+(SeedRandom[allseeds[[n+14]]];RandomReal[{0,sqrts}])^2]},incomingkvec];
Finalincomingks=Map[LabBoost[unitdirection,Finalincomingks0[[#]]]&,Range[1,inks]];
Finaloutgoingks=Map[LabBoost[unitdirection,Finaloutgoingks0[[#]]]&,Range[1,outks]];,Finalincomingks=Chop[Finalincomingks0];
Finaloutgoingks=Chop[Finaloutgoingks0];];

pFinal=Table[0,{i,n}];
Do[pFinal[[i]]=1/coefficients[[i]] Finalincomingks[[i]],{i,inks}];
Do[pFinal[[i+inks]]=1/coefficients[[i+inks]] Finaloutgoingks[[i]],{i,outks}];

MassNumerics[label]=Thread[mvars->numericMasses];
MomentaNumerics[label]=Thread[kVars->pFinal];

{TableForm[MassNumerics[label]],TableForm[MomentaNumerics[label]]}
]


(* ::Subsection:: *)
(*GenerateNumerics*)


(* ::Input::Initialization:: *)
Options[GenerateNumerics]={MassConstraints->Automatic, Seed-> Automatic,Energy-> 100, Iterations->20,COM-> False};


(* ::Input::Initialization:: *)
GenerateNumerics[label_:0,kinematicExpr_,OptionsPattern[]]:=Module[{n,sqrts,keys,values,incomingks,outgoingks,kVars,inks,outks,Legs,defaultassumps,finalnumerics,massConstraints1,iterations,seed(*,allseeds*)},
massConstraints1=Replace[OptionValue[MassConstraints],Automatic:>MassConditions[$Assumptions]];
ClearNumerics[label];
sqrts=OptionValue[Energy];
iterations=OptionValue[Iterations];
keys=Keys[kinematicExpr];values=Values[kinematicExpr];incomingks=Variables[keys];outgoingks=Variables[values];
kVars=Join[incomingks,outgoingks];
inks=Length[incomingks];outks=Length[outgoingks];n=inks+outks;
Legs=kVars//.Thread[AllMomenta[]->AllLegs[]];
seed=OptionValue[Seed];
allseeds=If[seed===Automatic, Table[Automatic,{10n}],Map[ToString[StringJoin[ToString[seed],ToString[#]]]&, Range[1,10n]]];

finalnumerics=If[inks==1,GenerateNumerics1n[label,n,sqrts,Legs,kVars,{keys,values},{incomingks,outgoingks},{inks,outks},massConstraints1,OptionValue[COM],iterations,allseeds],GenerateNumericsn1[label,n,sqrts,Legs,kVars,{keys,values},{incomingks,outgoingks},{inks,outks},massConstraints1,OptionValue[COM],iterations,allseeds]];

ComponentNumerics[label]=Flatten@Join[MassNumerics[label], Map[Thread[pVecLower[Leg[#]]->\[Eta]Mat . Lookup[MomentaNumerics[label],#] ]& ,kVars]];

NumericLabels=DeleteDuplicates@Join[NumericLabels,{label}];

finalnumerics
]


(* ::Input::Initialization:: *)
NumericLabels={};


(* ::Input::Initialization:: *)
Options[PutNumerics]={$Kinematics-> "Real"};
Options[MassNumerics]={$Kinematics-> "Real"};
Options[MomentaNumerics]={$Kinematics-> "Real"};
Options[ComponentNumerics]={$Kinematics-> "Real"};


(* ::Input::Initialization:: *)
PutNumerics[numlabel_:0,$Kinematics-> "Real"]:=PutNumerics[numlabel]
ComponentNumerics[numlabel_:0,$Kinematics-> "Real"]:=ComponentNumerics[numlabel]
MomentaNumerics[numlabel_:0,$Kinematics-> "Real"]:=MomentaNumerics[numlabel]
MassNumerics[numlabel_:0,$Kinematics-> "Real"]:=MassNumerics[numlabel]


(* ::Input::Initialization:: *)
PutNumerics[numlabel_:0,OptionsPattern[]][expr_]:=Module[{$kinematics,expr1,expr2,assumps,vars,dummyvars,subvars,subnums,expr3,$dummy$},
$kinematics=OptionValue[$Kinematics];
expr1=expr//.MomentaNumerics[numlabel,$Kinematics->$kinematics]//.MassNumerics[numlabel,$Kinematics->$kinematics]//ComponentForm//CartesianCoordinates;vars=ComponentNumerics[numlabel,$Kinematics->$kinematics][[;;,1]];
dummyvars=LIndex[$dummy$,Length[vars]];
subvars=Thread[vars-> dummyvars];
assumps=Thread[dummyvars\[Element]Reals];
expr2=expr1//.subvars;
subnums=ComponentNumerics[numlabel,$Kinematics->$kinematics]//.subvars;
expr3=Limit[expr2,subnums,Direction->"FromBelow"]
]//Chop;


(* ::Input::Initialization:: *)
PutNumerics[labels_List][expr_]:=Module[{expr1,expr2,assumps,vars,dummyvars,subvars,subnums,expr3,$dummy$,MassMomentaNumerics,Componentnumerics},
MassMomentaNumerics=Flatten@Map[Join[MomentaNumerics[#,$Kinematics->$kinematics],MassNumerics[#,$Kinematics->$kinematics]]&,labels];
Componentnumerics=Flatten@Map[ComponentNumerics[#,$Kinematics->$kinematics]&,labels];
expr1=expr//.MassMomentaNumerics//ComponentForm//CartesianCoordinates;vars=Flatten@Componentnumerics[[;;,1]];
dummyvars=LIndex[$dummy$,Length[vars]];
subvars=Thread[vars-> dummyvars];
assumps=Thread[dummyvars\[Element]Reals];
expr2=expr1//.subvars;
subnums=Componentnumerics//.subvars;
expr3=Limit[expr2,subnums,Direction->"FromBelow"]
]//Chop;


(* ::Input::Initialization:: *)
ClearNumerics[label_List:NumericLabels]:=Module[{},Map[ClearNumerics,label];];
ClearNumerics[label_]/;MemberQ[NumericLabels,label]:=Module[{},ComponentNumerics[label]=.;NumericLabels=DeleteElements[NumericLabels,{label}]];


(* ::Section:: *)
(*Complexify Numerics*)


(* ::Input::Initialization:: *)
Options[GenerateLightLikeOrthogonalMomenta]={$Helicity->+1};


(* ::Input::Initialization:: *)
GenerateLightLikeOrthogonalMomenta[q_,label_,k_,OptionsPattern[]]:=Module[{threeseeds,knumerics,sp1,sp2,soln,mom,momNumerics,kvec,kEnergy,qVecbasis,qvecRe,qvecIm,$hel,finalq},
If[!MemberQ[NumericLabels,label],Error::labelerror=StringJoin["Kinematics not generated for label : ", ToString[label]]; Message[Error::labelerror];Return[$Failed]];

(*declaring the leg q*)
DeclareMasslessLegs[{q}];AddAssumptions[{\[CapitalEpsilon][q]==0,p[q][0]==0}];
mom=Momenta[q];
(*parsing the massless mom k*)
knumerics=k//.MomentaNumerics[label];
kvec=knumerics[[2;;4]];
kEnergy=knumerics[[1]];

qVecbasis=If[kvec[[1]]^2+kvec[[2]]^2>10^-8,{0,0,1},{1,0,0}];
(*Here we construct two vectors which are orthogonal to each other and to the kvec*)
qvecRe= Cross[kvec,qVecbasis];(*this will form the real part of the q*)
qvecIm=Cross[kvec,qvecRe];(*this will form the imaginary part of the q*)

(*Here we scale the components of q back to the scale of energies*)
qvecRe=kEnergy qvecRe/Norm[qvecRe];
qvecIm=kEnergy qvecIm/Norm[qvecIm];
(*Constructing the final momenta based on the helicity option*)
$hel=OptionValue[$Helicity];
finalq=Join[{0},qvecRe+If[$hel==1, +1,-1] I qvecIm];

finalq
];


(* ::Input::Initialization:: *)
Options[ComplexifyNumerics]={$Helicity-> +1,Seed->Automatic};


(* ::Input::Initialization:: *)
ComplexifyNumerics[q_,label_,MomentumConservation_,OptionsPattern[]]:=Module[{n,legs,masses,momq,allks,keys,values,klist,knumerics,momcons,coeffs,zs,newks,allzs,seed,partzs,ReplacepItonI,ReplacenItopI,helchoice},

If[!MemberQ[NumericLabels,label],Error::labelerror=StringJoin["Kinematics not generated for label : ", ToString[label]]; Message[Error::labelerror];Return[$Failed]];

values=Values[MomentumConservation];keys=Keys[MomentumConservation];
klist=Variables@{values,keys};
legs=klist//.Thread[AllMomenta[]-> AllLegs[]];
masses=Map[m,legs];
knumerics=klist//.MomentaNumerics[label];
n=Length[klist];
momcons=keys-values;
coeffs=Coefficient[momcons,klist];
helchoice=OptionValue[$Helicity];

seed=OptionValue[Seed];
zs=Sort@(SeedRandom[seed];RandomComplex[{0.1+0.1 I, 0.9+0.9 I},n-1]);
partzs=Differences[Join[{1},zs,{1}]];
allzs[q]=Map[Coupling[ToExpression[StringJoin["z",ToString[q]]],#]&,legs];

BCFWParameters[label]=Thread[allzs[q]->Map[1/coeffs[[#]] partzs[[#]]&,Range[1,n]]];



momq=GenerateLightLikeOrthogonalMomenta[q,label,klist[[1]],$Helicity-> helchoice];
newks=Map[knumerics[[#]]+1/coeffs[[#]] partzs[[#]]momq&,Range[1,n]];



MomentaNumerics[label,$Kinematics->"Complex"]=DeleteDuplicates@Join[Thread[klist-> newks],{Momenta[q]->momq}];
MassNumerics[label,$Kinematics->"Complex"]=DeleteDuplicates@Join[MassNumerics[label],{m[q]->0}];

allks=Join[klist,{Momenta[q]}];
ComponentNumerics[label,$Kinematics->"Complex"]=Sort@Flatten@Join[MassNumerics[label,$Kinematics->"Complex"], Map[Thread[pVecLower[Leg[#]]->\[Eta]Mat . Lookup[MomentaNumerics[label,$Kinematics->"Complex"],#] ]& ,allks]];

{MassNumerics[label,$Kinematics->"Complex"]//TableForm,MomentaNumerics[label,$Kinematics->"Complex"]//TableForm}
];


(* ::Chapter::Closed:: *)
(*Old Numerics*)


(* ::Subsection::Closed:: *)
(*n=1*)


(* ::Input::Initialization:: *)
(*GenerateNumerics[1,sqrts_,kinematicExpr_:momconsRule,massConstraints_List:MassConditions[$Assumptions],iterations_:20]:=Module[{assumptions$,kVars,mvars,Legs,coefficients,posCoeffs,negCoeffs,effMasses,posKinConstraint,negKinConstraint,allConstraints,objective,optRes,numericMasses,numEffMasses,qMom,qMomAdjusted,allpositiveQ,pFinal},
n=1;
(*1. Parse the arbitrary kinematic expression*)
assumptions$=And@@massConstraints;
kVars=Sort[Variables[kinematicExpr]];
mvars=Sort[DeleteDuplicates@Cases[massConstraints,m[_],Infinity]];
Legs=mvars//.m[i_]:>i;
(*2. Extract arbitrary coefficients for every particle index*)
coefficients=Coefficient[kinematicExpr,kVars];
(*Numeric Masses*)
(*numericMasses=With[{random=RandomReal[{0,sqrts/10}]},{random,random}If[Simplify[mvars[[1]]==0,Assumptions->massConstraints],0,1]];
*)
AllConstraints=Cases[massConstraints,m[_]==x_|___==x_==___,Infinity];
objective=With[{random=RandomReal[{0,sqrts/10}]},Total[Map[(m[#]-random)^2&,Legs]]];
optRes=NMinimize[{objective,AllConstraints},mvars];
numericMasses=mvars/. optRes[[2]];
(*Full Mass Numerics*)
numEffMasses=Table[numericMasses[[i]],{i,n}];
MassNumerics[sqrts]=Thread[mvars->numEffMasses];
(*4. Run RAMBO Run using numeric masses*)
qMom={0};
qMom[[1]]=RAMBO[1,sqrts,{numEffMasses[[1]]},iterations];
 pFinal=Table[0,{n}];
pFinal={qMom[[1]]};

MomentaNumerics[sqrts]=Thread[kVars->pFinal];
(*Print the momenta*)
Print["Mass numerics generated : ",MassNumerics[sqrts]];
Print["Momenta numerics generated : ",MomentaNumerics[sqrts]];

]*)


(* ::Subsection::Closed:: *)
(*n=2*)


(* ::Input::Initialization:: *)
(*GenerateNumerics[2,sqrts_,kinematicExpr_:momconsRule,massConstraints_List:MassConditions[$Assumptions],iterations_:20]:=Module[{keys,values,incomingk,outgoingk,n,kVars,mvars,Legs,incomingkcoeff,outgoingkcoeff,coefficients,assumptions$,AllConstraints,objective,optRes,numericMasses,numEffMasses,qMom,allpositiveQ,pFinal},
n=2;
(*1. Parse the arbitrary kinematic expression*)
keys=Keys[kinematicExpr];values=Values[kinematicExpr];
incomingk=Variables[keys];outgoingk=Variables[values];
kVars=Join[incomingk,outgoingk];
incomingkcoeff=Coefficient[keys,incomingk];outgoingkcoeff=Coefficient[values,outgoingk];coefficients=Join[incomingkcoeff,outgoingkcoeff];
If[Length[kVars]!=2, Print["Number of momenta is not same as total number of particles."];Return[$Failed]];
Legs=kVars//.Thread[AllMomenta[]-> AllLegs[]];
mvars=Map[m,Legs];
(*2. Make all mass assumptions for NMinimize*)
assumptions$=Select[massConstraints,!FreeQ[#,Alternatives@@mvars]&];
AllConstraints=Join[assumptions$,{mvars[[1]]==mvars[[2]]},Thread[mvars>=0]];
objective=With[{random=RandomReal[{0,sqrts/10}]},Total[Map[(m[#]-random)^2&,Legs]]];
optRes=NMinimize[{objective,AllConstraints},mvars];
numericMasses=mvars/. optRes[[2]];
(*Full Mass Numerics*)
numEffMasses=Table[1/Abs[coefficients[[i]]]*numericMasses[[i]],{i,2}];
MassNumerics[sqrts]=Thread[mvars->numEffMasses];
(*4. Run RAMBO Run using numeric masses*)
qMom={0,0};
qMom[[1]]=RAMBO[1,sqrts,{numEffMasses[[1]]},iterations];
(*---Sign Flip for all incoming or all outgoing convention---*)
(*Transform back to the momenta with correct coefficients:k_i=q_i/ |c_i| and distributing the energies to positive and negative momenta, keeping their randomness as it is.*) pFinal=Table[0,{n}];
allpositiveQ=Or[And@@Thread[coefficients>0],And@@Thread[coefficients<0]];

pFinal=If[Or[incomingkcoeff[[1]]>0&&outgoingkcoeff[[1]]<0,incomingkcoeff[[1]]<0&&outgoingkcoeff[[1]]>0],
{1/Abs[coefficients[[1]]] qMom[[1]],-(1/Abs[coefficients[[2]]])qMom[[1]]},{1/Abs[coefficients[[1]]] qMom[[1]],1/Abs[coefficients[[2]]] qMom[[1]]}];

MomentaNumerics[sqrts]=Thread[kVars->pFinal];
(*Print the momenta*)
Print["Mass numerics generated : ",MassNumerics[sqrts]];
Print["Momenta numerics generated : ",MomentaNumerics[sqrts]];

]*)


(* ::Subsection::Closed:: *)
(*n=3 (Kallen Function)*)


(* ::Input::Initialization:: *)
(*KallenFunction[{a_,b_,c_}]:=(a+b-c)^2-4a b*)


(* ::Input::Initialization:: *)
(*KallenConstraint[{m1_,m2_,m3_}]:={KallenFunction[{m1^2,m2^2,m3^2}]>=0}*)


(* ::Input::Initialization:: *)
(*KallenQ[m1_,m2_,m3_]:=Or[KallenFunction[{m1^2,m2^2,m3^2}]<0, And[m1==0, KallenFunction[{m1^2,m2^2,m3^2}]!=0]]*)


(* ::Input::Initialization:: *)
(*AllowedThreePoints[{m1_,m2_,m3_}]:=Module[{},
If[KallenQ[m1,m2,m3],False,True]
];*)


(* ::Input::Initialization:: *)
(*GenerateNumerics[3,sqrts_,kinematicExpr_,massConstraints_List]:=Module[{keys,values,incomingk,outgoingks,incomingkcoeff,outgoingkscoeff,coefficients,kVars,mvars,incomingm,outgoingms,Legs,effMasses,effMassesConstraint,kallenconstraint,allConstraints,objective,optRes,numericMasses,effnumericmasses,incomingkvec,kmag,z,outgoingk1,outgoingk2,Kallen,outgoingk1kz,outgoingk1Energy,outgoingk2Energy,outgoingk1z,outgoingk2z,Finalincomingk, Finaloutgoingk1,Finaloutgoingk2,pFinal},
(*1. Parse the arbitrary kinematic expression*)
keys=Keys[kinematicExpr];
values=Values[kinematicExpr];
incomingk=Variables[keys];incomingkcoeff=Coefficient[keys,incomingk];
outgoingks=Variables[values];outgoingkscoeff=Coefficient[values,outgoingks];
kVars=Join[incomingk,outgoingks];coefficients=Join[incomingkcoeff,outgoingkscoeff];
mvars=Sort[DeleteDuplicates@Cases[massConstraints,m[_],Infinity]];


incomingm=m[incomingk//.Reverse/@Normal[MasslessMomentaThread]//.Reverse/@Normal[MassiveMomentaThread]//First];
outgoingms=DeleteElements[mvars,{incomingm}];
Legs=mvars//.m[i_]:>i;

effMasses=Map[Abs[coefficients[[#]]]*mvars[[#]]&,{1,2,3}];
effMassesConstraint={effMasses[[1]]<=sqrts,Total[effMasses[[2;;]]]<=sqrts};
kallenconstraint=KallenConstraint[mvars];
allConstraints=Join[massConstraints,Thread[mvars>=0],effMassesConstraint,kallenconstraint];
objective=Total[Map[(m[#]-RandomReal[{0,sqrts/10}])^2&,Legs]];
optRes=NMinimize[{objective,allConstraints},mvars];
numericMasses=mvars/. optRes[[2]];
effnumericmasses=Map[Abs[coefficients[[#]]]numericMasses[[#]]&,{1,2,3}]//Chop;
MassNumerics[sqrts]=Thread[mvars->Chop[numericMasses]];

incomingkvec=With[{u1=RandomReal[],u2=RandomReal[]},With[{costh=2 u1-1,phi=2 Pi u2},kmag=RandomReal[{0,sqrts}];kmag{ Sqrt[1-costh^2] Cos[phi], Sqrt[1-costh^2] Sin[phi], costh}]];

If[effnumericmasses[[1]]==0, 
If[Chop[effnumericmasses[[2;;]]]=={0,0},((*A massless particle can only decay to two massless particles.*)
Finalincomingk=Join[{kmag},incomingkvec];
z=RandomReal[{0.1,0.9}];
Finaloutgoingk1=z*Finalincomingk;
Finaloutgoingk2=(1-z)*Finalincomingk;),Print["A massless particle can only decay to two massless particles."];Return[$Failed]],
((*A massive particle can decay into two massless/massive or massless-massive particles. We first find the momenta of outgoing along z direction and then boost them in arbitrary direction.*)
Finalincomingk=Join[{Sqrt[kmag^2+effnumericmasses[[1]]^2]},incomingkvec];

Kallen=With[{kallen=KallenFunction[effnumericmasses*effnumericmasses]},If[kallen<0,0,kallen]];
outgoingk1kz=Sqrt[Kallen]/(2*effnumericmasses[[1]]);
outgoingk1Energy=(effnumericmasses[[1]]^2+effnumericmasses[[2]]^2-effnumericmasses[[3]]^2)/(2 effnumericmasses[[1]]);
outgoingk2Energy=(effnumericmasses[[1]]^2+effnumericmasses[[3]]^2-effnumericmasses[[2]]^2)/(2 effnumericmasses[[1]]);
(*Rest frame decay strictly on the Z-axis*)
outgoingk1z={outgoingk1Energy,0,0,outgoingk1kz};
outgoingk2z={outgoingk2Energy,0,0,-outgoingk1kz};
(*Boost outgoing legs from the z-axis rest frame into the arbitrary moving frame*)Finaloutgoingk1=LabBoost[Finalincomingk,outgoingk1z];
Finaloutgoingk2=LabBoost[Finalincomingk,outgoingk2z];)];
(*Scaling the momenta back*)
pFinal={0,0,0};
pFinal[[1]]=Finalincomingk/coefficients[[1]];
pFinal[[2]]=Finaloutgoingk1/coefficients[[2]];
pFinal[[3]]=Finaloutgoingk2/coefficients[[3]];

MomentaNumerics[sqrts]=Thread[kVars->pFinal];
Print["Mass numerics generated : ",MassNumerics[sqrts]];
Print["Momenta numerics generated : ",MomentaNumerics[sqrts]];

]*)


(* ::Subsection::Closed:: *)
(*n=4*)


(* ::Input::Initialization:: *)
(*GenerateNumerics[n_,sqrts_,kinematicExpr_:momconsRule,massConstraints_List:MassConditions[$Assumptions],iterations_:20]/;n>=4:=Module[{(*keys,values,incomingka,outgoingks,kVars,mVars,incomingms,outgoingms,incomingkscoeff,outgoingkscoeff,coefficients,Legs,ineffMasses,outeffMasses,ineffMassesConstraint,outeffMassesConstraint,allConstraints,objective,optRes,numericMasses,effnumMasses,ineffnumMasses,outeffnumMasses,inRambo,outRambo,pFinal*)},
(*1. Parse the arbitrary kinematic expression*)
keys=Keys[kinematicExpr];
values=Values[kinematicExpr];
incomingks=Variables[keys];incomingkscoeff=Coefficient[keys,incomingks];
outgoingks=Variables[values];outgoingkscoeff=Coefficient[values,outgoingks];
kVars=Join[incomingks,outgoingks];coefficients=Join[incomingkscoeff,outgoingkscoeff];
mvars=Sort[DeleteDuplicates@Cases[massConstraints,m[_],Infinity]];

incomingms=Map[m[#//.Reverse/@Normal[MasslessMomentaThread]//.Reverse/@Normal[MassiveMomentaThread]]&,incomingks];
outgoingms=DeleteElements[mvars,incomingms];
Legs=mvars//.m[i_]:>i;
inks=Length[incomingks];
(*Mass constraints*)
ineffMasses=Map[Abs[incomingkscoeff[[#]]]*incomingms[[#]]&,{1,inks}];
outeffMasses=Map[Abs[outgoingkscoeff[[#]]]*outgoingms[[#]]&,{1,n-inks}];
ineffMassesConstraint=0<=Total[ineffMasses]<=sqrts;
outeffMassesConstraint=0<=Total[outeffMasses]<=sqrts;
allConstraints=Join[massConstraints,Thread[mvars>=0],{ineffMassesConstraint,outeffMassesConstraint}];

(*4. Solve for Masses using Randomized Least-Squares*)objective=Total[Map[(m[#]-RandomReal[{sqrts/1000,sqrts/10}])^2&,Legs]];
optRes=NMinimize[{objective,allConstraints},mvars];
numericMasses=mvars/. optRes[[2]];
effnumMasses=Map[Abs[coefficients[[#]]]*numericMasses[[#]]&,Range[1,n]];
MassNumerics[sqrts]=Thread[mvars->(*effnumMasses*)numericMasses];
Print["Mass numerics generated : ",MassNumerics[sqrts]];

(*5. Split-RAMBO Engine Generation*)
ineffnumMasses=Map[Abs[incomingkscoeff[[#]]]*numericMasses[[#]]&,Range[1,inks]];
outeffnumMasses=Map[Abs[outgoingkscoeff[[#]]]*numericMasses[[inks+#]]&,Range[1,n-inks]];
inRambo=RAMBO[inks,sqrts,ineffnumMasses];outRambo=RAMBO[n-inks,sqrts,outeffnumMasses];

pFinal=Table[0,{i,n}];
Do[pFinal[[i]]=1/coefficients[[i]] inRambo[[i]],{i,inks}];
Do[pFinal[[i+inks]]=1/coefficients[[i+inks]] outRambo[[i]],{i,n-inks}];

MomentaNumerics[sqrts]=Thread[kVars->pFinal];Print["Momenta numerics generated : ",MomentaNumerics[sqrts]];
]*)


(* ::Title:: *)
(*Ignore*)


Print["Loaded: ComponentForm"]
