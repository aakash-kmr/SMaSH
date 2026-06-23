(* ::Package:: *)

(* ::Chapter::Closed:: *)
(*Xfactor*)


(* ::Input::Initialization:: *)
Xfactor[Mlleg_,Msleg_]:=Xfactor[Mlleg,Msleg,Helicity[Mlleg]]

Xfactor[Mlleg_,Msleg_,+1]:=With[{ref=ReferenceSpinor[Mlleg]},SHAB[ref,Msleg,Mlleg]/(m[Msleg]SHAA[Mlleg,ref])]

Xfactor[Mlleg_,Msleg_,-1]:=With[{ref=ReferenceSpinor[Mlleg]},-(SHAB[Mlleg,Msleg,ref]/(m[Msleg]SHBB[Mlleg,ref]))]


(* ::Chapter::Closed:: *)
(*Classification of Three Point Interactions *)


(* ::Section::Closed:: *)
(*Three Massless Amplitude*)


(* ::Input::Initialization:: *)
ThreeMasslessAmplitude[leglist_List:{1,2,3},helList_:{1,1,1}]/;Total[helList]>=0&&IntegerQ[Total[helList]]:= SHBB[leglist[[1]],leglist[[2]]]^(helList[[1]]+helList[[2]]-helList[[3]]) SHBB[leglist[[2]],leglist[[3]]]^(helList[[2]]+helList[[3]]-helList[[1]]) SHBB[leglist[[3]],leglist[[1]]]^(helList[[3]]+helList[[1]]-helList[[2]]);

ThreeMasslessAmplitude[leglist_List:{1,2,3},helList_:{1,1,1}]/;Total[helList]<0&&IntegerQ[Total[helList]]:= SHAA[leglist[[1]],leglist[[2]]]^(-helList[[1]]-helList[[2]]+helList[[3]]) SHAA[leglist[[2]],leglist[[3]]]^(-helList[[2]]-helList[[3]]+helList[[1]]) SHAA[leglist[[3]],leglist[[1]]]^(-helList[[3]]-helList[[1]]+helList[[2]]);

ThreeMasslessAmplitude[leglist_List:{1,2,3},helList_:{1,1,1}]/;!IntegerQ[Total[helList]]:= 0



(* ::Section::Closed:: *)
(*Two-Massless One-Massive Amplitude*)


TwoMasslessOneMassiveAmplitude[leg_List:{1,2,3},hel_:{1,1,1}]/;Or[
And[hel[[1]]==hel[[2]],OddQ[hel[[3]]]],!(Abs[hel[[1]]-hel[[2]]]<=hel[[3]]),!IntegerQ[Abs[hel[[1]]]+Abs[hel[[2]]]+Abs[hel[[3]]]]]:= 0;

TwoMasslessOneMassiveAmplitude[leg_List:{1,2,3},hel_:{1,1,1}]/;Or[
And[hel[[1]]==hel[[2]],EvenQ[hel[[3]]]],(Abs[hel[[1]]-hel[[2]]]<=hel[[3]])]&&IntegerQ[Abs[hel[[1]]]+Abs[hel[[2]]]+Abs[hel[[3]]]]&&hel[[1]]+hel[[2]]+hel[[3]]>=0:= (
1/m[leg[[3]]]^(3 hel[[3]]+hel[[2]]+hel[[1]]) SHBB[leg[[1]],leg[[2]]]^(hel[[1]]+hel[[2]]+hel[[3]]) 
(SHAA[leg[[1]],leg[[3]][MsIndex[J,3]]])^(hel[[3]]+hel[[2]]-hel[[1]]) (SHAA[leg[[2]],leg[[3]][MsIndex[J,3]]])^(hel[[3]]-hel[[2]]+hel[[1]]));

TwoMasslessOneMassiveAmplitude[leg_List:{1,2,3},hel_:{1,1,1}]/;Or[And[hel[[1]]==hel[[2]],EvenQ[hel[[3]]]],(Abs[hel[[1]]-hel[[2]]]<=hel[[3]])]&&IntegerQ[Abs[hel[[1]]]+Abs[hel[[2]]]+Abs[hel[[3]]]]&&hel[[1]]+hel[[2]]+hel[[3]]<0:= (
1/m[leg[[3]]]^(2 hel[[3]]+Abs[hel[[3]]+hel[[2]]+hel[[1]]]) SHAA[leg[[1]],leg[[2]]]^Abs[(hel[[1]]+hel[[2]]+hel[[3]])] 
(SHAA[leg[[1]],leg[[3]][MsIndex[J,3]]])^(hel[[3]]+hel[[2]]-hel[[1]]) (SHAA[leg[[2]],leg[[3]][MsIndex[J,3]]])^(hel[[3]]-hel[[2]]+hel[[1]]));


(* ::Section::Closed:: *)
(*Two-Massive One-Massless  Amplitude*)


TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]>=Spin[[2]]&&0<=Spin[[3]]<=Spin[[1]]+Spin[[2]]:= 
(1/(m[leg[[1]]]m[leg[[2]]]))^(Spin[[1]]+Spin[[2]]) Map[Coupling[g,#-1]SHBB[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^# SHBB[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(Spin[[1]]+Spin[[2]]+Spin[[3]]-#) SHAA[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(2Spin[[1]]-#) SHAA[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(Spin[[2]]-Spin[[1]]-Spin[[3]]+#)&,Range[Spin[[1]]-Spin[[2]]+Spin[[3]], Min[Spin[[1]]+Spin[[2]]+Spin[[3]],2 Spin[[1]]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]>=Spin[[2]]&&-Spin[[1]]-Spin[[2]]<=Spin[[3]]<=0:= 
(1/(m[leg[[1]]]m[leg[[2]]]))^(Spin[[1]]+Spin[[2]]) Map[Coupling[g,#+1]SHBB[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^# SHBB[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(Spin[[1]]+Spin[[2]]+Spin[[3]]-#) SHAA[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(2Spin[[1]]-#) SHAA[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(Spin[[2]]-Spin[[1]]-Spin[[3]]+#)&,Range[Max[0,Spin[[1]]-Spin[[2]]+Spin[[3]]], Spin[[1]]+Spin[[2]]+Spin[[3]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]<=Spin[[2]]&&0<=Spin[[3]]<=Spin[[1]]+Spin[[1]]:= 
(1/(m[leg[[1]]]m[leg[[2]]]))^(Spin[[1]]+Spin[[2]]) Map[Coupling[g,#-1]SHBB[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^# SHBB[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(Spin[[2]]+Spin[[1]]+Spin[[3]]-#) SHAA[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(2Spin[[2]]-#) SHAA[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(Spin[[1]]-Spin[[2]]-Spin[[3]]+#)&,Range[Spin[[2]]-Spin[[1]]+Spin[[3]], Min[Spin[[1]]+Spin[[2]]+Spin[[3]],2 Spin[[2]]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]<=Spin[[2]]&&-Spin[[1]]-Spin[[2]]<=Spin[[3]]<=0:= 
(1/(m[leg[[1]]]m[leg[[2]]]))^(Spin[[1]]+Spin[[2]]) Map[Coupling[g,#+1]SHBB[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^# SHBB[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(Spin[[2]]+Spin[[1]]+Spin[[3]]-#) SHAA[leg[[2]][MsIndex[J,leg[[2]]]],leg[[3]]]^(2Spin[[2]]-#) SHAA[leg[[1]][MsIndex[J,leg[[1]]]],leg[[3]]]^(Spin[[1]]-Spin[[2]]-Spin[[3]]+#)&,Range[Max[0,Spin[[2]]-Spin[[1]]+Spin[[3]]], Spin[[1]]+Spin[[2]]+Spin[[3]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]>=Spin[[2]]&&Or[Spin[[3]]>Spin[[1]]+Spin[[2]],h<-Spin[[1]]-Spin[[2]]]:=0;
TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_:{1,1,1}]/;Not[Simplify[m[leg[[1]]]==m[leg[[2]]]]]&&Spin[[1]]<=Spin[[2]]&&Or[Spin[[3]]>Spin[[1]]+Spin[[1]],h<-Spin[[1]]-Spin[[2]]]:=0;


(* ::Input::Initialization:: *)
TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_List:{1,1,1}]/;Simplify[m[leg[[1]]]==m[leg[[2]]]]&&Abs[Spin[[3]]]>0&&Spin[[1]]>=Spin[[2]]:= Module[{leg1,leg2,leg3,m1,m2,s1,s2,s3},
leg1=leg[[1]][MsIndex[J,leg[[1]]]];leg2=leg[[2]][MsIndex[J,leg[[2]]]];leg3=leg[[3]];
m1=m[leg[[1]]];m2=m[leg[[2]]];s1=Spin[[1]];s2=Spin[[2]];s3=Spin[[3]];
(1/(m1^2))^( Spin[[1]]) PutLGScalar[(Xfactor[leg3,leg[[1]],s3/Abs[s3]])^Abs[s3]]Map[Coupling[g,#+1]SHAB[leg1,leg3,leg1]^(Spin[[1]]-Spin[[2]]) SHAA[leg1,leg2]^(#) SHBB[leg1,leg2]^(2s2-#) &,Range[0, 2Spin[[2]]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_List:{1,1,1}]/;Simplify[m[leg[[1]]]==m[leg[[2]]]]&&Abs[Spin[[3]]]>0&&Spin[[1]]<=Spin[[2]]:= Module[{leg1,leg2,leg3,m1,m2,s1,s2,s3},
leg1=leg[[1]][MsIndex[J,leg[[1]]]];leg2=leg[[2]][MsIndex[J,leg[[2]]]];leg3=leg[[3]];
m1=m[leg[[1]]];m2=m[leg[[2]]];s1=Spin[[1]];s2=Spin[[2]];s3=Spin[[3]];
(1/(m1^2))^(Spin[[2]]) PutLGScalar[(Xfactor[leg3,leg[[1]],s3/Abs[s3]])^Abs[s3]]Map[Coupling[g,#+1]SHAB[leg2,leg3,leg2]^(Spin[[2]]-Spin[[1]]) SHAA[leg1,leg2]^(#) SHBB[leg1,leg2]^(2s1-#) &,Range[0, 2Spin[[1]]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_List:{1,1,1}]/;Simplify[m[leg[[1]]]==m[leg[[2]]]]&&Abs[Spin[[3]]]==0&&Spin[[1]]>=Spin[[2]]:= Module[{leg1,leg2,leg3,m1,m2,s1,s2,s3},
leg1=leg[[1]][MsIndex[J,leg[[1]]]];leg2=leg[[2]][MsIndex[J,leg[[2]]]];leg3=leg[[3]];
m1=m[leg[[1]]];m2=m[leg[[2]]];s1=Spin[[1]];s2=Spin[[2]];s3=Spin[[3]];
(1/(m1^2))^(Spin[[1]]) Map[Coupling[g,#+1]SHAB[leg1,leg3,leg1]^(Spin[[1]]-Spin[[2]]) SHAA[leg1,leg2]^(#) SHBB[leg1,leg2]^(2s2-#) &,Range[0, 2Spin[[2]]]]];

TwoMassiveOneMasslessAmplitude[leg_List:{1,2,3},Spin_List:{1,1,1}]/;Simplify[m[leg[[1]]]==m[leg[[2]]]]&&Abs[Spin[[3]]]==0&&Spin[[1]]<=Spin[[2]]:= Module[{leg1,leg2,leg3,m1,m2,s1,s2,s3},
leg1=leg[[1]][MsIndex[J,leg[[1]]]];leg2=leg[[2]][MsIndex[J,leg[[2]]]];leg3=leg[[3]];
m1=m[leg[[1]]];m2=m[leg[[2]]];s1=Spin[[1]];s2=Spin[[2]];s3=Spin[[3]];
(1/(m1^2))^(Spin[[2]]) Map[Coupling[g,#+1]SHAB[leg2,leg3,leg2]^(Spin[[2]]-Spin[[1]]) SHAA[leg1,leg2]^(#) SHBB[leg1,leg2]^(2s1-#) &,Range[0, 2Spin[[1]]]]];


(* ::Chapter::Closed:: *)
(*Higher spin Propagator*)


(* ::Section::Closed:: *)
(*Projectors*)


\[CapitalTheta][p_:k1,m_:m[1],\[Xi]_:\[Xi],LIndx_List:{\[Alpha], \[Alpha]},RIndx_List:{ \[Beta], \[Beta]}]:=-2 \[Epsilon][LIndx[[1]],RIndx[[1]]]\[Epsilon]d[LIndx[[2]],RIndx[[2]]] +(\[Xi]-1)(DressMom[p, LIndx[[1]],LIndx[[2]]]DressMom[p,RIndx[[1]],RIndx[[2]]])/(Simplify[PutLGScalar@SimplifyPolynomial[-1/2 DressMom[p,a,b]DressMom[p,-a,-b]]+\[Xi] m^2]);


UG\[CapitalTheta][p_:k1,m_:m[1],LIndx_List:{\[Alpha], \[Alpha]},RIndx_List:{ \[Beta], \[Beta]}]:=-2 \[Epsilon][LIndx[[1]],RIndx[[1]]]\[Epsilon]d[LIndx[[2]],RIndx[[2]]] +(DressMom[p, LIndx[[1]],LIndx[[2]]]DressMom[p,RIndx[[1]],RIndx[[2]]])/(Simplify[ m^2]);


FG\[CapitalTheta][p_:k1,m_:m[1],LIndx_List:{\[Alpha], \[Alpha]},RIndx_List:{ \[Beta], \[Beta]}]:=-2 \[Epsilon][LIndx[[1]],RIndx[[1]]]\[Epsilon]d[LIndx[[2]],RIndx[[2]]];


(* ::Section::Closed:: *)
(*Propagators*)


(* ::Input::Initialization:: *)
PropCoeff[j1_,r_,d_]:= (-1/2)^r (j1! (2j1+d-2r-5)!!)/(r!(j1-2r)!(2j1+d-5)!!)//FullSimplify;
Options[Projector]={LeftSymm->False,RightSymm->False,\[Xi]->\[Xi]};
Projector[j_Integer:1, p_:k1,m_:m[1], prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:= 
	Module[{A, Term, DimM, PreProjector, perms,list\[Alpha],list\[Alpha]d,list\[Beta],list\[Beta]d,projec1,projec2,\[Xi]1,LeftSymm1,RightSymm1},
\[Xi]1=OptionValue[\[Xi]];LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
		A[j1_,r_,d_]:= PropCoeff[j1, r, d];
		DimM = 4;
		list\[Alpha] =  LIndex[prefixesL[[1]],j];
		list\[Alpha]d = LIndex[prefixesL[[2]],j];
		list\[Beta] = LIndex[prefixesR[[1]],j];
		list\[Beta]d = LIndex[prefixesR[[2]],j];
		PreProjector[plist\[Alpha]_,plist\[Alpha]d_,plist\[Beta]_,plist\[Beta]d_]:= If[j==0, 1,Total@ Map[A[j, #, DimM]
						Times@@Map[\[CapitalTheta][p, m,\[Xi]1,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]},{ plist\[Alpha][[#+1]], plist\[Alpha]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[\[CapitalTheta][p, m,\[Xi]1, {plist\[Beta][[#]], plist\[Beta]d[[#]]},{ plist\[Beta][[#+1]], plist\[Beta]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[\[CapitalTheta][p, m,\[Xi]1,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]}, {plist\[Beta][[#]], plist\[Beta]d[[#]]}]&, Range[ 2#+1, j]]&,
				   Range[ 0,Floor[j/2]]]];	   
		
		perms=Permutations[Range[j]];
projec1=If[LeftSymm1,Symmetrized[list\[Alpha]d]@Symmetrized[list\[Alpha]]@PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d],PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d]];
projec2=If[RightSymm1,Symmetrized[list\[Beta]d]@Symmetrized[list\[Beta]]@projec1,projec1];
projec2
	];


Options[Propagator]={LeftSymm->False,RightSymm->False,\[Xi]->\[Xi]};
Propagator[j_Integer:1, p_:k1, m_:m[1],prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:=Module[{dummya,dummyb,\[Xi]1,LeftSymm1,RightSymm1},\[Xi]1=OptionValue[\[Xi]];LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
((-I)/(PutLGScalar@SimplifyPolynomial[-((DressMom[p,dummya,dummyb]DressMom[p,-dummya,-dummyb])/2)]+m^2+I \[CurlyEpsilon]))Projector[j, p, m,prefixesL,prefixesR,LeftSymm->LeftSymm1,RightSymm->RightSymm1,\[Xi]->\[Xi]1]];


(* ::Input::Initialization:: *)
Options[UGProjector]={LeftSymm->False,RightSymm->False};
UGProjector[j_Integer:1, p_:k1,m_:m[1], prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:= 
	Module[{A, Term, DimM, PreProjector, perms,list\[Alpha],list\[Alpha]d,list\[Beta],list\[Beta]d,projec1,projec2,LeftSymm1,RightSymm1},
LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
		A[j1_,r_,d_]:= PropCoeff[j1, r, d];
		DimM = 4;
		list\[Alpha] =  LIndex[prefixesL[[1]],j];
		list\[Alpha]d = LIndex[prefixesL[[2]],j];
		list\[Beta] = LIndex[prefixesR[[1]],j];
		list\[Beta]d = LIndex[prefixesR[[2]],j];
		PreProjector[plist\[Alpha]_,plist\[Alpha]d_,plist\[Beta]_,plist\[Beta]d_]:= If[j==0, 1,Total@ Map[A[j, #, DimM]
						Times@@Map[UG\[CapitalTheta][p, m,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]},{ plist\[Alpha][[#+1]], plist\[Alpha]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[UG\[CapitalTheta][p, m, {plist\[Beta][[#]], plist\[Beta]d[[#]]},{ plist\[Beta][[#+1]], plist\[Beta]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[UG\[CapitalTheta][p, m,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]}, {plist\[Beta][[#]], plist\[Beta]d[[#]]}]&, Range[ 2#+1, j]]&,
				   Range[ 0,Floor[j/2]]]];	   
		
		perms=Permutations[Range[j]];
projec1=If[LeftSymm1,Symmetrized[list\[Alpha]d]@Symmetrized[list\[Alpha]]@PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d],PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d]];
projec2=If[RightSymm1,Symmetrized[list\[Beta]d]@Symmetrized[list\[Beta]]@projec1,projec1];
projec2
	];



Options[UGPropagator]={LeftSymm->False,RightSymm->False};
UGPropagator[j_Integer:1, p_:k1, m_:m[1],  prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:=Module[{dummya,dummyb,\[Xi]1,LeftSymm1,RightSymm1},
LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
((-I)/(PutLGScalar@SimplifyPolynomial[-((DressMom[p,dummya,dummyb]DressMom[p,-dummya,-dummyb])/2)]+m^2+I \[CurlyEpsilon]))UGProjector[j, p, m,prefixesL,prefixesR,LeftSymm ->LeftSymm1,RightSymm->RightSymm1]];


(* ::Input::Initialization:: *)
Options[FGProjector]={LeftSymm->False,RightSymm->False};
FGProjector[j_Integer:1, p_:k1,m_:m[1], prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:= 
	Module[{A, Term, DimM, PreProjector, perms,list\[Alpha],list\[Alpha]d,list\[Beta],list\[Beta]d,projec1,projec2,LeftSymm1,RightSymm1},
LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
		A[j1_,r_,d_]:= PropCoeff[j1, r, d];
		DimM = 4;
		list\[Alpha] =  LIndex[prefixesL[[1]],j];
		list\[Alpha]d = LIndex[prefixesL[[2]],j];
		list\[Beta] = LIndex[prefixesR[[1]],j];
		list\[Beta]d = LIndex[prefixesR[[2]],j];
		PreProjector[plist\[Alpha]_,plist\[Alpha]d_,plist\[Beta]_,plist\[Beta]d_]:= If[j==0, 1,Total@ Map[A[j, #, DimM]
						Times@@Map[FG\[CapitalTheta][p, m,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]},{ plist\[Alpha][[#+1]], plist\[Alpha]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[FG\[CapitalTheta][p, m, {plist\[Beta][[#]], plist\[Beta]d[[#]]},{ plist\[Beta][[#+1]], plist\[Beta]d[[#+1]]}]&, Range[ 1, 2#, 2]]
						Times@@Map[FG\[CapitalTheta][p, m,{ plist\[Alpha][[#]], plist\[Alpha]d[[#]]}, {plist\[Beta][[#]], plist\[Beta]d[[#]]}]&, Range[ 2#+1, j]]&,
				   Range[ 0,Floor[j/2]]]];	   
		
		perms=Permutations[Range[j]];
projec1=If[LeftSymm1,Symmetrized[list\[Alpha]d]@Symmetrized[list\[Alpha]]@PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d],PreProjector[list\[Alpha], list\[Alpha]d, list\[Beta], list\[Beta]d]];
projec2=If[RightSymm1,Symmetrized[list\[Beta]d]@Symmetrized[list\[Beta]]@projec1,projec1];
projec2
	];



Options[FGPropagator]={LeftSymm->False,RightSymm->False};
FGPropagator[j_Integer:1, p_:k1, m_:m[1],  prefixesL_List:{\[Alpha], \[Alpha]},prefixesR_List:{ \[Beta], \[Beta]},OptionsPattern[]]:=Module[{dummya,dummyb,\[Xi]1,LeftSymm1,RightSymm1},
LeftSymm1=OptionValue[LeftSymm];RightSymm1=OptionValue[RightSymm];
((-I)/(PutLGScalar@SimplifyPolynomial[-((DressMom[p,dummya,dummyb]DressMom[p,-dummya,-dummyb])/2)]+m^2+I \[CurlyEpsilon]))FGProjector[j, p, m,prefixesL,prefixesR,LeftSymm->LeftSymm1,RightSymm ->RightSymm1 ]];


(* ::Chapter::Closed:: *)
(*Mandelstam variables*)


(* ::Section::Closed:: *)
(*SM*)


(* ::Input::Initialization:: *)
SM/:SM[i___]:=Map[sm[Sequence@@#]&,Tuples[{i},{2}]]//Total


(* ::Section::Closed:: *)
(*sm*)


(* ::Input::Initialization:: *)
sm/:sm[a_,b_]/;!OrderedQ[{a,b}]:=sm[b,a];
sm/:sm[i___,-a_,b___]:=-sm[i,a,b];
sm/:sm[i___,a_?Negative,b___]:=-sm[i,-a,b];
sm/:sm[\[Mu]___,i_,\[Nu]___]/;MemberQ[AllMomenta[],i]:=sm[\[Mu],Leg[i],\[Nu]];
sm/:sm[a_,a_]/;(Head[a]=!=Plus&&Head[a]=!=Times):=-m[a]^2;
sm/:sm[i___,a_Plus,j___]:=Total@Map[sm[i,#,j]&,List@@a];
sm/:sm[a___,x_Times,b___]/;!FreeQ[{x},Alternatives@@AllMomenta[]]:= With[{removefactor=Select[DeleteDuplicates@AllMomenta[],!FreeQ[x,#]&][[1]]},x/removefactor sm[a,removefactor,b]];


SM/:SM[i___]:=Map[sm[Sequence@@#]&,Tuples[{i},{2}]]//Total;


(* ::Input::Initialization:: *)
SHToMandelstam[expr_]:=expr//.Join[{
SHAB[i_,j_,i_]/;!MsQ[i]:> 2 sm[i,j],
SHAB[i_[a_],j_,i_[b_]]/;MsQ[i]&&a+b==0&&!IntegerQ[a]:>2 SignOf[b]sm[i,j]},
MakeRulesForExponents[{HF@SHAB[i_,j_,k_],SHAB[i,j,k]},{HF@SHAB[k_,j_,i_],SHAB[k,j,i]},HF[4 sm[i,j]sm[k,j]],HF[Not[MsQ[j]]&&Not[MsQ[k]]&&Not[MsQ[i]]]],
MakeRulesForExponents[{HF@SHAB[i_,j_,k_],SHAB[i,j,k]},{HF@SHAB[k_,j_,i_],SHAB[k,j,i]},HF[4 sm[i,j]sm[k,j] +2 m[j]^2 sm[i,k]],HF[MsQ[j]&&Not[MsQ[k]]&&Not[MsQ[i]]]]
]//.MandelstamRules;

LorToMandelstam[expr_]:=expr//.{
k1_[\[Mu]_]k2_[\[Nu]_]/;\[Mu]+\[Nu]==0:> sm[k1,k2]
}//.SP[j_]:> j//.MandelstamRules;

ToMandelstam[expr_]:=expr//RepeatedRule[PutLGScalar[Together[SplitMassless[LorToMandelstam[SHToMandelstam[#]]]]]&]

MandelstamtoSH[expr_]:=expr//.{
HP@sm[i_,j_]/;!MsQ[i]:> 1/2 SHAB[i,j,i],
HP@sm[i_,j_]/;!MsQ[j]:>1/2  SHAB[j,i,j],
HP@sm[i_,j_]/;MsQ[i]:>1/2 SHAB[i[-MIL[{\[ScriptCapitalI],GI[1]}]],j,i[MIL[{\[ScriptCapitalI],GI[0]}]]]
};
MandelstamtoLor[expr_]:=expr//.{
HP@sm[i_,j_]:> SP[i[\[Mu]]j[-\[Mu]]//.Thread[AllLegs[]->AllMomenta[]]]
};


(* ::Chapter::Closed:: *)
(*Declare Momentum conservation*)


(* ::Input::Initialization:: *)
ToEqns[expr_]:=expr//.{(a_->b_):> (a==b)};
SimplifyRules[r_]:=DeleteDuplicatesBy[Reverse@DeleteCases[r,x_->x_],First]//Reverse;


(* ::Input::Initialization:: *)
Options[DeclareMomentumConservation]={$Mandelstams-> Automatic};


(* ::Input::Initialization:: *)
DeclareMomentumConservation[momsum_,OptionsPattern[]]/;(Simplify[momsum-Total[Thread[Coefficient[momsum,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]]])===0:=Module[{assumptions,allks,Legs,allkscoeffs,allkwithcoeffs,allkwithabscoeffs,baremomsum,momconsList,decomposesm,indepsms,$tsm,MandelstamRules0},
assumptions=List@@$Assumptions;
$Assumptions={};

allks=DeleteDuplicates@Cases[momsum,a_/;MemberQ[AllMomenta[],a],Infinity];
Legs=Map[m,allks];
allkscoeffs=Coefficient[momsum,allks];
allkwithcoeffs=allks*allkscoeffs;
allkwithabscoeffs=allks*Map[Abs, allkscoeffs];
baremomsum=Total[allks];
momconsRule[]={allks[[1]]->1/allkscoeffs[[1]] Total[-allkwithcoeffs[[2;;]]]};
AllMandelstam[]=(Map[sm[Sequence@@#]&,Subsets[DeleteDuplicates@allks,{2}]]);

indepsms=OptionValue[$Mandelstams];

decomposesm[$i_,allks_]:=(AllMandelstam[]//.HP@sm[i_,j_]:> $tsm[Momenta[i],Momenta[j]]//.allks[[$i]]->Total[-DeleteElements[allks,{allks[[$i]]}]]//.$tsm->sm);

MandelstamRules0=If[indepsms===Automatic,SimplifyRules@Flatten@Solve@ToEqns@Flatten@Map[Thread[AllMandelstam[]->decomposesm[#,allks]]&,Range[Length[allks]]],
SimplifyRules@Flatten@Solve[ToEqns@Flatten@Map[Thread[AllMandelstam[]->decomposesm[#,allks]]&,Range[Length[allks]]],Complement[AllMandelstam[],indepsms]]
];

MandelstamRules1=MandelstamRules0//.{HP@sm[i_,j_]:>$tsm[Momenta[i],Momenta[j]],m[i_]:> Sqrt[-$tsm[Momenta[i],Momenta[i]]]}/.Thread[allks->allkwithcoeffs]//.$tsm:> sm//.(x___ HP@sm[\[Mu]___]-> y___):> (sm[\[Mu]]-> 1/x y);

AddAssumptions[assumptions];

MandelstamRules=MandelstamRules1//Simplify;

AllIndepedentMandelstam[]=DeleteDuplicates@Cases[MandelstamRules[[;;,2]],HP@sm[___],All];

AllIndepedentMandelstam[]
];

DeclareMomentumConservation[momsum_,OptionsPattern[]]:=Module[{},
Error::FoundUndefMom=StringJoin["Found Undefined Momenta : ",ToString[(momsum-Total[Thread[Coefficient[momsum,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]])] ];
Message[Error::FoundUndefMom]];


(* ::Input::Initialization:: *)
ClearMomentumConservation[]:=Module[{},momconsRule[]={};AllMandelstam[]={};AllIndepedentMandelstam[]={};MandelstamRules={};]


(* ::Chapter::Closed:: *)
(*Standardize Expression*)


StandardizeExpression[rule_List:momconsRule[]][expr_]:=expr//ReplaceMomenta[rule];


(* ::Chapter::Closed:: *)
(*Pure Gauge Transformations*)


(* ::Input::Initialization:: *)
PureGaugeTransformation[leg_][expr_List]:=Map[PureGaugeTransformation[leg],expr];
PureGaugeTransformation[leg_][expr_]:=Module[{expr1,expr2,expr2Nums,expr2Denoms,expr2Nums1,FinalExpr,ref,newref},
ref=ReferenceSpinor[leg];
newref=MIL[{ref,leg}];
expr1=ToList[Expand[expr]];
expr2=(expr1-(expr1//ReplaceSpinors[X_[ref,\[Alpha]_]:> X[newref,\[Alpha]]]));
expr2Nums=Map[Numerator[Together[#]]&,expr2];expr2Denoms=Map[Denominator[Together[#]]&,expr2];
expr2Nums1=expr2Nums//NoLGScalar//SimplifyGT[ref,newref];
FinalExpr=Thread[expr2Nums1*1/expr2Denoms]//Total;
FinalExpr
]


(* ::Input::Initialization:: *)
SimplifyGT[r_,rr_][expr_]:=Module[{expr1},
expr1=NoLGScalar[expr];
expr1//.{
X_[$a___,r]X_[$a1___,rr]:>If[OrderedQ[{$a,$a1}]===OrderedQ[{r,rr}],PutCanonicalOrder[SplitSchouten[{BaseHead@$a,r},{BaseHead@$a1,rr}][X[$a,r]X[$a1,rr]]],X[$a,r]X[$a1,rr]],
X_[$a___,r]X_[rr,$a1___]:>If[OrderedQ[{$a,$a1}]===OrderedQ[{r,rr}],PutCanonicalOrder[SplitSchouten[{BaseHead@$a,r},{rr,BaseHead@$a1}][X[$a,r]X[rr,$a1]]],X[$a,r]X[rr,$a1]],
X_[r,$a___]X_[$a1___,rr]:>If[OrderedQ[{$a,$a1}]===OrderedQ[{r,rr}],PutCanonicalOrder[SplitSchouten[{r,BaseHead@$a},{BaseHead@$a1,rr}][X[r,$a]X[$a1,rr]]],X[r,$a]X[$a1,rr]],
X_[r,$a___]X_[rr,$a1___]:>If[OrderedQ[{$a,$a1}]===OrderedQ[{r,rr}],PutCanonicalOrder[SplitSchouten[{r,BaseHead@$a},{rr,BaseHead@$a1}][X[r,$a]X[rr,$a1]]],X[r,$a]X[rr,$a1]]}//PutCanonicalOrder//Expand//PutMassiveLGScalar]


(* ::Input::Initialization:: *)
GIQ[leg_][expr_]:=(StandardizeExpression[momconsRule[]]@Simplify[SHToMandelstam[PureGaugeTransformation[leg][expr]]]===0)


(* ::Chapter::Closed:: *)
(*Find Contact Term*)


(* ::Input::Initialization:: *)
FindContactTerm[leg_][expr_]:=Module[{expr1,ref,newref,expr1Nums,expr1Denoms,expr2},
ref=ReferenceSpinor[leg];
newref=MIL[{ref,leg}];
expr1=PutCanonicalOrder[ToList[Expand[expr]]];
expr1Nums=SplitMassless[Map[Numerator[Together[#]]&,expr1]];expr1Denoms=Map[Denominator[Together[#]]&,expr1];
expr2=expr1Nums//.MakeRulesForExponents[{HF@X_[ref,newref],HF@X[ref,newref]},{HF@X_[\[Mu]___,leg],HF@X[\[Mu],leg]},HF@SplitSchouten[{ref,newref},{BaseHead@\[Mu],leg}][X[ref,newref]X[\[Mu],leg]]]//.MakeRulesForExponents[{HF@X_[ref,newref],HF@X[ref,newref]},{HF@X_[leg,\[Mu]___],HF@X[leg,\[Mu]]},HF@SplitSchouten[{ref,newref},{leg,BaseHead@\[Mu]}][X[ref,newref]X[leg,\[Mu]]]];
Total@(Thread[expr2*1/expr1Denoms]//Expand//ApplyRule[{X_[\[Mu]___,newref,\[Nu]___]/;Or[!(\[Mu]===leg),!(\[Nu]===leg)]:> 0}])
]


(* ::Chapter::Closed:: *)
(*Manifest GI*)


(* ::Input::Initialization:: *)
ManifestGI[rule_][expr_List]:=Map[ManifestGI[rule],expr]


(* ::Input::Initialization:: *)
ManifestGI[tobasis_][expr_]:= Module[{expr1,expr1Num,expr1Den,cases,casescoeffs},
expr1=expr//ToBasis[tobasis]//ToMandelstam;
expr1Num=expr1//Numerator;expr1Den=expr1//Denominator//PutLGScalar;
cases=Cases[expr1Num,X_[a___,tobasis[[1]],b___]|X_[a___,tobasis[[1]],b___],All]//DeleteDuplicates;
casescoeffs=Map[Coefficient[expr1Num,#]&,cases]//PutCanonicalIndices//PutLGScalar//ToMandelstam//FullSimplify//StandardizeExpression[];
If[casescoeffs=={},expr1,Thread[casescoeffs*cases/expr1Den]//Total]
];


(* ::Title:: *)
(*Ignore*)


Print["Loaded: Amplitudes"]
