(* ::Package:: *)

(* ::Title:: *)
(*Dirac spinor \[CapitalPsi] and \[ScriptCapitalB], \[ScriptCapitalC], \[Beta], Subscript[\[Gamma], 5] matrices*)


(* ::Input::Initialization:: *)
\[ScriptCapitalB][\[Alpha]_,\[Beta]_]:={{0,\[Epsilon]d[-\[Alpha],-\[Beta]]},{\[Epsilon][\[Alpha],\[Beta]],0}}
Inv\[ScriptCapitalB][\[Alpha]_,\[Beta]_]:={{0,\[Epsilon][-\[Alpha],-\[Beta]]},{\[Epsilon]d[\[Alpha],\[Beta]],0}}


(* ::Input::Initialization:: *)
\[ScriptCapitalC][\[Alpha]_,\[Beta]_]:={{-\[Epsilon][\[Alpha],\[Beta]],0},{0,-\[Epsilon]d[-\[Alpha],-\[Beta]]}}


(* ::Input::Initialization:: *)
\[Beta][\[Alpha]_,\[Beta]_]:={{0,\[Delta]d[\[Alpha],-\[Beta]]},{\[Delta][-\[Alpha],\[Beta]],0}}


(* ::Input::Initialization:: *)
\[Gamma][\[Mu]_][\[Alpha]_,\[Beta]_]:={{0,\[Sigma]mat[\[Mu]][-\[Alpha],-\[Beta]]},{\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]],0}};


(* ::Input::Initialization:: *)
\[Gamma]5[\[Alpha]_,\[Beta]_]:={{-\[Delta][-\[Alpha],\[Beta]],0},{0,\[Delta]d[\[Alpha],-\[Beta]]}}


(* ::Input::Initialization:: *)
Dirac\[CapitalPsi][i_[J_],\[Alpha]_]/;MsQ[i]:={SHB[i[J],-\[Alpha]],SHA[i[J],\[Alpha]]};
Dirac\[CapitalPsi][i_,\[Alpha]_]/;!MsQ[i]:={SHB[i,-\[Alpha]],SHA[i,\[Alpha]]};
\[CapitalPsi]=Dirac\[CapitalPsi];


(* ::Title::Closed:: *)
(*Complex Conjugate*)


(* ::Subsection::Closed:: *)
(*Distribution Formulas*)


(*Unprotect[HC];
HC=HermitianConjugate;
Protect[HC];

HermitianConjugate[x_+ y_] := HermitianConjugate[x]+HermitianConjugate[y];
HermitianConjugate[x_ y_] := HermitianConjugate[x] HermitianConjugate[y];
HermitianConjugate[x_/y_]:= HermitianConjugate[x]/HermitianConjugate[y];
HermitianConjugate[x_^n_] := HermitianConjugate[x]^HermitianConjugate[n];

HermitianConjugate[x_?MatrixQ]:= Transpose[Map[HermitianConjugate,x]];
HermitianConjugate[x_List] /;!MatrixQ[x]:= Map[HermitianConjugate,x];
HermitianConjugate[x_]/;Simplify[Element[x,Integers]] := x;
HermitianConjugate[x_]/;Simplify[Element[x,Rationals]] := x;
HermitianConjugate[x_]/;Simplify[Element[x,Reals]] := x;
HermitianConjugate[x_]/;Simplify[Element[x,Complexes]] := Conjugate[x];
HermitianConjugate[HermitianConjugate[x_]]:= x;*)


ComplexConjugate=Conjugate;


(* ::Subsection::Closed:: *)
(*Metric*)


(* ::Input::Initialization:: *)
\[Epsilon]/:Conjugate@\[Epsilon][\[Alpha]_,\[Beta]_]:= \[Epsilon]d[\[Alpha],\[Beta]];
\[Epsilon]d/:Conjugate@\[Epsilon]d[\[Alpha]_,\[Beta]_]:=\[Epsilon][\[Alpha],\[Beta]];
\[Delta]/:Conjugate@\[Delta][\[Alpha]_,\[Beta]_]:= \[Delta]d[\[Alpha],\[Beta]];
\[Delta]d/:Conjugate@\[Delta]d[\[Alpha]_,\[Beta]_]:=\[Delta][\[Alpha],\[Beta]];
\[Epsilon]lg/:Conjugate@\[Epsilon]lg[J_,K_]:=-\[Epsilon]lg[-J,-K];
\[Delta]lg/:Conjugate@\[Delta]lg[J_,K_]:=\[Delta]lg[-J,-K];

\[Sigma]mat/:Conjugate@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]:=\[Sigma]mat[\[Mu]][\[Beta],\[Alpha]];

\[Eta]/:Conjugate@\[Eta][\[Mu]___]:=\[Eta][\[Mu]];


(* ::Subsection::Closed:: *)
(*SHA and SHB*)


(* ::Input::Initialization:: *)
SHA/:Conjugate@SHA[x_,\[Alpha]_]/;And[
!MsQ[x],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]
]:=SHB[TL[x],\[Alpha]];

SHA/:Conjugate@SHA[x_[a_],\[Alpha]_]/;MsQ[x]:=-SignOf[a]SHB[TL[x][-a],\[Alpha]];


(* ::Input::Initialization:: *)
SHB/:Conjugate@SHB[x_,\[Alpha]_]/;And[
!MsQ[x],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]
]:=SHA[TL[x],\[Alpha]];
SHB/:Conjugate@SHB[x_[a_],\[Alpha]_]/;MsQ[x]:=SignOf[a]SHA[TL[x][-a],\[Alpha]];


(* ::Subsection::Closed:: *)
(*SHAA and SHBB*)


(* ::Input::Initialization:: *)
SHAA/:Conjugate@SHAA[x_,y_]/;And[
!MsQ[x],!MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SHBB[TL[y],TL[x]];
SHAA/:Conjugate@SHAA[x_[a_],y_]/;And[
MsQ[x],!MsQ[y],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=-SignOf[a]SHBB[TL[y],TL[x][-a]];
SHAA/:Conjugate@SHAA[x_,y_[a_]]/;And[
!MsQ[x],MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]]:=-SignOf[a]SHBB[TL[y][-a],TL[x]];
SHAA/:Conjugate@SHAA[x_[a_],y_[b_]]/;And[
MsQ[x],MsQ[y]]:=SignOf[a]SignOf[b]SHBB[TL[y][-b],TL[x][-a]];


(* ::Input::Initialization:: *)
SHBB/:Conjugate@SHBB[x_,y_]/;And[
!MsQ[x],!MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SHAA[TL[y],TL[x]];
SHBB/:Conjugate@SHBB[x_[a_],y_]/;And[
MsQ[x],!MsQ[y],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SignOf[a]SHAA[TL[y],TL[x][-a]];
SHBB/:Conjugate@SHBB[x_,y_[a_]]/;And[
!MsQ[x],MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]]:=SignOf[a]SHAA[TL[y][-a],TL[x]];
SHBB/:Conjugate@SHBB[x_[a_],y_[b_]]/;And[
MsQ[x],MsQ[y]]:=SignOf[a]SignOf[b]SHAA[TL[y][-b],TL[x][-a]];


(* ::Subsection::Closed:: *)
(*SHAB and SHBA*)


(* ::Input::Initialization:: *)
SHAB/:Conjugate@SHAB[x_,i_,y_]/;And[
!MsQ[x],!MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SHAB[TL[y],TL[i],TL[x]];
SHAB/:Conjugate@SHAB[x_[a_],i_,y_]/;And[
MsQ[x],!MsQ[y],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=-SignOf[a]SHAB[TL[y],TL[i],TL[x][-a]];
SHAB/:Conjugate@SHAB[x_,i_,y_[a_]]/;And[
!MsQ[x],MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]]:=SignOf[a]SHAB[TL[y][-a],TL[i],TL[x]];
SHAB/:Conjugate@SHAB[x_[a_],i_,y_[b_]]/;And[
MsQ[x],MsQ[y]]:=-SignOf[a]SignOf[b]SHAB[TL[y][-b],TL[i],TL[x][-a]];


(* ::Input::Initialization:: *)
SHBA/:Conjugate@SHBA[x_,i_,y_]/;And[
!MsQ[x],!MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SHBA[TL[y],TL[i],TL[x]];
SHBA/:Conjugate@SHBA[x_[a_],i_,y_]/;And[
MsQ[x],!MsQ[y],
Or[RAQ[y],MatchQ[y,_[___]]&&!MsQ[Head[y]]]]:=SignOf[a]SHBA[TL[y],TL[i],TL[x][-a]];
SHBA/:Conjugate@SHBA[x_,i_,y_[a_]]/;And[
!MsQ[x],MsQ[y],
Or[RAQ[x],MatchQ[x,_[___]]&&!MsQ[Head[x]]]]:=-SignOf[a]SHBA[TL[y][-a],TL[i],TL[x]];
SHBA/:Conjugate@SHBA[x_[a_],i_,y_[b_]]/;And[
MsQ[x],MsQ[y]]:=-SignOf[a]SignOf[b]SHBA[TL[y][-b],TL[i],TL[x][-a]];


(* ::Title::Closed:: *)
(*Charge Conjugation*)


(* ::Subsection::Closed:: *)
(*Distribution rules*)


Unprotect[CC];
CC=ChargeConjugate;
Protect[CC];

ChargeConjugate[x_+ y_] := ChargeConjugate[x]+ChargeConjugate[y];
ChargeConjugate[x_ y_] := ChargeConjugate[x] ChargeConjugate[y];
ChargeConjugate[x_/y_]:= ChargeConjugate[x]/ChargeConjugate[y];
ChargeConjugate[x_^n_] := ChargeConjugate[x]^ChargeConjugate[n];
ChargeConjugate[x_List]:= Map[ChargeConjugate,x];
ChargeConjugate[ChargeConjugate[x_]]:= x;

ChargeConjugate[x_]/;NumericQ[x] := x;
ChargeConjugate[x_]/;Simplify[Element[x,Reals]] := x;


(* ::Subsection::Closed:: *)
(*Metric*)


(* ::Input::Initialization:: *)
\[Epsilon]/:ChargeConjugate[\[Epsilon][\[Alpha]_,\[Beta]_]]:=\[Epsilon][\[Alpha],\[Beta]];
\[Epsilon]d/:ChargeConjugate[\[Epsilon]d[\[Alpha]_,\[Beta]_]]:=\[Epsilon]d[\[Alpha],\[Beta]];
\[Epsilon]lg/:ChargeConjugate[\[Epsilon]lg[\[Alpha]_,\[Beta]_]]:=\[Epsilon]lg[\[Alpha],\[Beta]];
\[Delta]/:ChargeConjugate[\[Delta][\[Alpha]_,\[Beta]_]]:=\[Delta][\[Alpha],\[Beta]];
\[Delta]d/:ChargeConjugate[\[Delta]d[\[Alpha]_,\[Beta]_]]:=\[Delta]d[\[Alpha],\[Beta]];
\[Delta]lg/:ChargeConjugate[\[Delta]lg[\[Alpha]_,\[Beta]_]]:=\[Delta]lg[\[Alpha],\[Beta]];

\[Sigma]mat/:ChargeConjugate@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]:=\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]];

\[Eta]/:ChargeConjugate@\[Eta][\[Mu]___]:=\[Eta][\[Mu]];


(* ::Subsection::Closed:: *)
(*SHA and SHB*)


(* ::Input::Initialization:: *)
SHA/:ChargeConjugate@SHA[x_,\[Alpha]_]/;!MsQ[x]:=SHA[TL[x],\[Alpha]];
SHA/:ChargeConjugate@SHA[x_[a_],\[Alpha]_]/;MsQ[x]:=SHA[TL[x][a],\[Alpha]];


(* ::Input::Initialization:: *)
SHB/:ChargeConjugate@SHB[x_,\[Alpha]_]/;!MsQ[x]:=SHB[TL[x],\[Alpha]];
SHB/:ChargeConjugate@SHB[x_[a_],\[Alpha]_]/;MsQ[x]:=SHB[TL[x][a],\[Alpha]];


(* ::Subsection::Closed:: *)
(*SHAA and SHBB*)


(* ::Input::Initialization:: *)
SHAA/:ChargeConjugate@SHAA[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=SHAA[TL[x],TL[y]];
SHAA/:ChargeConjugate@SHAA[x_[a_],y_]/;And[MsQ[x],!MsQ[y]]:=SHAA[TL[x][a],TL[y]];
SHAA/:ChargeConjugate@SHAA[x_,y_[a_]]/;And[!MsQ[x],MsQ[y]]:=SHAA[TL[x],TL[y][a]];
SHAA/:ChargeConjugate@SHAA[x_[a_],y_[b_]]/;And[MsQ[x],MsQ[y]]:=SHAA[TL[x][a],TL[y][b]];


(* ::Input::Initialization:: *)
SHBB/:ChargeConjugate@SHBB[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=SHBB[TL[x],TL[y]];
SHBB/:ChargeConjugate@SHBB[x_[a_],y_]/;And[MsQ[x],!MsQ[y]]:=SHBB[TL[x][a],TL[y]];
SHBB/:ChargeConjugate@SHBB[x_,y_[a_]]/;And[!MsQ[x],MsQ[y]]:=SHBB[TL[x],TL[y][a]];
SHBB/:ChargeConjugate@SHBB[x_[a_],y_[b_]]/;And[MsQ[x],MsQ[y]]:=SHBB[TL[x][a],TL[y][b]];


(* ::Subsection::Closed:: *)
(*SHAB and SHBA*)


(* ::Input::Initialization:: *)
SHAB/:ChargeConjugate@SHAB[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=SHAB[TL[x],TL[i],TL[y]];
SHAB/:ChargeConjugate@SHAB[x_[a_],i_,y_]/;And[MsQ[x],!MsQ[y]]:=SHAB[TL[x][a],TL[i],TL[y]];
SHAB/:ChargeConjugate@SHAB[x_,i_,y_[a_]]/;And[!MsQ[x],MsQ[y]]:=SHAB[TL[x],TL[i],TL[y][a]];
SHAB/:ChargeConjugate@SHAB[x_[a_],i_,y_[b_]]/;And[MsQ[x],MsQ[y]]:=SHAB[TL[x][a],TL[i],TL[y][b]];


(* ::Input::Initialization:: *)
SHBA/:ChargeConjugate@SHBA[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=SHBA[TL[x],TL[i],TL[y]];
SHBA/:ChargeConjugate@SHBA[x_[a_],i_,y_]/;And[MsQ[x],!MsQ[y]]:=SHBA[TL[x][a],TL[i],TL[y]];
SHBA/:ChargeConjugate@SHBA[x_,i_,y_[a_]]/;And[!MsQ[x],MsQ[y]]:=SHBA[TL[x],TL[i],TL[y][a]];
SHBA/:ChargeConjugate@SHBA[x_[a_],i_,y_[b_]]/;And[MsQ[x],MsQ[y]]:=SHBA[TL[x][a],TL[i],TL[y][b]];


(* ::Title:: *)
(*Parity*)


(* ::Subsection::Closed:: *)
(*Distribution rules*)


Unprotect[PC];
PC=Parity;
Protect[PC];

Parity[x_+ y_] := Parity[x]+Parity[y];
Parity[x_ y_] := Parity[x] Parity[y];
Parity[x_/y_]:= Parity[x]/Parity[y];
Parity[x_^n_] := Parity[x]^Parity[n];
Parity[x_List]:= Map[Parity,x];
Parity[Parity[x_]]:= x;

Parity[x_]/;NumericQ[x] := x;
Parity[x_]/;Simplify[Element[x,Reals]] := x;


(* ::Subsection:: *)
(*Intrinsic Parity*)


(* ::Input::Initialization:: *)
\[CapitalSigma][i_][1,1]:=+1;
\[CapitalSigma][i_][2,2]:=-1;
\[CapitalSigma][i_][1,2]:=0;
\[CapitalSigma][i_][2,1]:=0;


(* ::Input::Initialization:: *)
\[CapitalSigma][i_][-1,-1]:=-1;
\[CapitalSigma][i_][-2,-2]:=+1;
\[CapitalSigma][i_][-1,-2]:=0;
\[CapitalSigma][i_][-2,-1]:=0;


(* ::Input::Initialization:: *)
\[CapitalSigma][i_][1,-1]:=0;
\[CapitalSigma][i_][2,-2]:=0;
\[CapitalSigma][i_][1,-2]:=+1;
\[CapitalSigma][i_][2,-1]:=+1;


(* ::Input::Initialization:: *)
\[CapitalSigma][i_][-1,1]:=0;
\[CapitalSigma][i_][-2,2]:=0;
\[CapitalSigma][i_][-1,2]:=+1;
\[CapitalSigma][i_][-2,1]:=+1;


(* ::Input::Initialization:: *)
(*\[CapitalSigma][i_][OPS[1,a_?IfP]]:=\[Delta]lg[a,-1]
\[CapitalSigma][i_][OPS[2,a_?IfP]]:=-\[Delta]lg[a,-2]*)


(* ::Input::Initialization:: *)
(*\[CapitalSigma][i_][OPS[-1,a_?IfN]]:=-\[Delta]lg[a,1]
\[CapitalSigma][i_][OPS[-2,a_?IfN]]:=\[Delta]lg[a,2]*)


(* ::Input::Initialization:: *)
(*\[CapitalSigma][i_][OPS[1,a_?IfN]]:=\[Delta]lg[a,2]
\[CapitalSigma][i_][OPS[2,a_?IfN]]:=\[Delta]lg[a,1]*)


(* ::Input::Initialization:: *)
(*\[CapitalSigma][i_][OPS[-1,a_?IfP]]:=\[Delta]lg[a,-2]
\[CapitalSigma][i_][OPS[-2,a_?IfP]]:=\[Delta]lg[a,-1]*)


\[CapitalSigma]/:\[CapitalSigma][i_][a_,b_]/;!OrderedQ[{SignOf[a]a,SignOf[b]b}]:=\[CapitalSigma][i][Sequence@@Sort[{a,b}]]


(* ::Input::Initialization:: *)
Ang\[Kappa]P[i_[J_,K_],\[Alpha]_]:=+I \[CapitalSigma][i][J,K] SignOf[\[Alpha]]SignOf[J];
Ang\[Kappa]P[i_,\[Alpha]_]:=+I SignOf[\[Alpha]];


(* ::Input::Initialization:: *)
Box\[Kappa]P[i_[J_,K_],\[Alpha]_]:=-I \[CapitalSigma][i][J,K] SignOf[\[Alpha]]SignOf[J];
Box\[Kappa]P[i_,\[Alpha]_]:=-I SignOf[\[Alpha]];


(* ::Subsection::Closed:: *)
(*Metric*)


(* ::Input::Initialization:: *)
\[Epsilon]/:Parity[\[Epsilon][\[Alpha]_,\[Beta]_]]:=-\[Epsilon]d[-\[Alpha],-\[Beta]];
\[Epsilon]d/:Parity[\[Epsilon]d[\[Alpha]_,\[Beta]_]]:=-\[Epsilon][-\[Alpha],-\[Beta]];
\[Epsilon]lg/:Parity[\[Epsilon]lg[\[Alpha]_,\[Beta]_]]:=\[Epsilon]lg[\[Alpha],\[Beta]];
\[Delta]/:Parity[\[Delta][\[Alpha]_,\[Beta]_]]:=\[Delta]d[-\[Alpha],-\[Beta]];
\[Delta]d/:Parity[\[Delta]d[\[Alpha]_,\[Beta]_]]:=\[Delta][-\[Alpha],-\[Beta]];
\[Delta]lg/:Parity[\[Delta]lg[\[Alpha]_,\[Beta]_]]:=\[Delta]lg[\[Alpha],\[Beta]];

\[Sigma]mat/:Parity@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]:=\[Sigma]mat[\[Mu]][-\[Beta],-\[Alpha]];

\[Eta]/:Parity@\[Eta][\[Mu]___]:=\[Eta][\[Mu]];


(* ::Subsection::Closed:: *)
(*SHA and SHB*)


(* ::Input::Initialization:: *)
SHA/:Parity@SHA[x_,\[Alpha]_]/;!MsQ[x]:=Ang\[Kappa]P[x,\[Alpha]]SHB[x,-\[Alpha]];

SHA/:Parity@SHA[x_[a_],\[Alpha]_]/;MsQ[x]&&IntegerQ[a]:=Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy],\[Alpha]]SHB[x[SignOf[a]dummy],-\[Alpha]],{dummy,1,2}];
SHA/:Parity@SHA[x_[a_],\[Alpha]_]/;MsQ[x]&&!IntegerQ[a]:=Ang\[Kappa]P[x[a,-GI1[a]],\[Alpha]]SHB[x[GI0[a]],-\[Alpha]];


(* ::Input::Initialization:: *)
SHB/:Parity@SHB[x_,\[Alpha]_]/;!MsQ[x]:=Box\[Kappa]P[x,\[Alpha]]SHA[x,-\[Alpha]];
SHB/:Parity@SHB[x_[a_],\[Alpha]_]/;MsQ[x]&&IntegerQ[a]:=Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy],\[Alpha]]SHA[x[SignOf[a]dummy],-\[Alpha]],{dummy,1,2}];
SHB/:Parity@SHB[x_[a_],\[Alpha]_]/;MsQ[x]&&!IntegerQ[a]:=Box\[Kappa]P[x[a,-GI1[a]],\[Alpha]]SHA[x[GI0[a]],-\[Alpha]];


(* ::Subsection::Closed:: *)
(*SHAA and SHBB*)


(* ::Input::Initialization:: *)
GI0[a_]:=MIL[{a,GI[0]}];
GI1[a_]:=MIL[{a,GI[1]}];
Protect[GI0];
Protect[GI1];


(* ::Input::Initialization:: *)
SHAA/:Parity@SHAA[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=Ang\[Kappa]P[y,1]Ang\[Kappa]P[x,-1]SHBB[x,y];

SHAA/:Parity@SHAA[x_[a_],y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=Ang\[Kappa]P[y,1]Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy],-1]SHBB[x[SignOf[a]dummy],y],{dummy,1,2}];

SHAA/:Parity@SHAA[x_[a_],y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=Ang\[Kappa]P[y,1]Ang\[Kappa]P[x[a,-GI1[a]],-1]SHBB[x[GI0[a]],y];

SHAA/:Parity@HP@SHAA[x_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=Ang\[Kappa]P[x,-1]Sum[Ang\[Kappa]P[y[a,-SignOf[a]dummy],1]SHBB[x,y[SignOf[a]dummy]],{dummy,1,2}];

SHAA/:Parity@HP@SHAA[x_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=Ang\[Kappa]P[y[a,-GI1[a]],1]Ang\[Kappa]P[x,-1]SHBB[x,y[GI0[a]]];

SHAA/:Parity@SHAA[x_[a_],y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy1],-1]SHBB[x[SignOf[a]dummy1],y[GI1[b]]]Ang\[Kappa]P[y[b,-GI0[b]],1],{dummy1,1,2}];

SHAA/:Parity@SHAA[x_[a_],y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]P[x[a,-GI1[a]],-1]SHBB[x[GI0[a]],y[SignOf[b]dummy2]]Ang\[Kappa]P[y[b,-SignOf[b]dummy2],1],{dummy2,1,2}];

SHAA/:Parity@SHAA[x_[a_],y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy1],-1]SHBB[x[SignOf[a]dummy1],y[SignOf[b]dummy2]]Ang\[Kappa]P[y[b,-SignOf[b]dummy2],1],{dummy1,1,2},{dummy2,1,2}];

SHAA/:Parity@SHAA[x_[a_],y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Ang\[Kappa]P[x[a,-GI1[a]],-1]SHBB[x[GI0[a]],y[GI1[b]]]Ang\[Kappa]P[y[b,-GI0[b]],1];


(* ::Input::Initialization:: *)
SHBB/:Parity@SHBB[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=Box\[Kappa]P[y,-1]Box\[Kappa]P[x,1]SHAA[x,y];

SHBB/:Parity@SHBB[x_[a_],y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=Box\[Kappa]P[y,-1]Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy],1]SHAA[x[SignOf[a]dummy],y],{dummy,1,2}];

SHBB/:Parity@SHBB[x_[a_],y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=Box\[Kappa]P[y,-1]Box\[Kappa]P[x[a,-GI1[a]],1]SHAA[x[GI0[a]],y];

SHBB/:Parity@HP@SHBB[x_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=Box\[Kappa]P[x,1]Sum[Box\[Kappa]P[y[a,-SignOf[a]dummy],-1]SHAA[x,y[SignOf[a]dummy]],{dummy,1,2}];

SHBB/:Parity@HP@SHBB[x_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=Box\[Kappa]P[y[a,-GI1[a]],-1]Box\[Kappa]P[x,1]SHAA[x,y[GI0[a]]];

SHBB/:Parity@SHBB[x_[a_],y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy1],1]SHAA[x[SignOf[a]dummy1],y[GI1[b]]]Box\[Kappa]P[y[b,-GI0[b]],-1],{dummy1,1,2}];

SHBB/:Parity@SHBB[x_[a_],y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]P[x[a,-GI1[a]],1]SHAA[x[GI0[a]],y[SignOf[b]dummy2]]Box\[Kappa]P[y[b,-SignOf[b]dummy2],-1],{dummy2,1,2}];

SHBB/:Parity@SHBB[x_[a_],y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy1],1]SHAA[x[SignOf[a]dummy1],y[SignOf[b]dummy2]]Box\[Kappa]P[y[b,-SignOf[b]dummy2],-1],{dummy1,1,2},{dummy2,1,2}];

SHBB/:Parity@SHBB[x_[a_],y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Box\[Kappa]P[x[a,-GI1[a]],1]SHAA[x[GI0[a]],y[GI1[b]]]Box\[Kappa]P[y[b,-GI0[b]],-1];


(* ::Subsection::Closed:: *)
(*SHAB and SHBA*)


(* ::Input::Initialization:: *)
SHAB/:Parity@SHAB[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Ang\[Kappa]P[x,-1] Box\[Kappa]P[y,1] SHAB[y,i,x];

SHAB/:Parity@SHAB[x_[a_],i_,y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Sum[ Ang\[Kappa]P[x[a,-SignOf[a]dummy],-1] Box\[Kappa]P[y,1]SHAB[y,i,x[SignOf[a]dummy]],{dummy,1,2}];
SHAB/:Parity@SHAB[x_[a_],i_,y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Ang\[Kappa]P[x[a,-GI1[a]],-1] Box\[Kappa]P[y,1]SHAB[y,i,x[GI0[a]]];

SHAB/:Parity@SHAB[x_,i_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[MsQ[i]] Sum[ Box\[Kappa]P[y[a,-SignOf[a]dummy],1] Ang\[Kappa]P[x,-1]SHAB[y[SignOf[a]dummy],i,x],{dummy,1,2}];
SHAB/:Parity@SHAB[x_,i_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[MsQ[i]] Box\[Kappa]P[y[a,-GI1[a]],1] Ang\[Kappa]P[x,-1]SHAB[y[GI0[a]],i,x];

SHAB/:Parity@SHAB[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy],-1] SHAB[y[GI1[b]],i,x[SignOf[a]dummy]]Box\[Kappa]P[y[b,-GI0[b]],1],{dummy,1,2}];
SHAB/:Parity@SHAB[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Box\[Kappa]P[y[b,-SignOf[b]dummy],1] SHAB[y[SignOf[a]dummy],i,x[GI1[a]]]Ang\[Kappa]P[y[b,-GI0[b]],-1],{dummy,1,2}];
SHAB/:Parity@SHAB[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Ang\[Kappa]P[x[a,-SignOf[a]dummy1],-1] SHAB[y[SignOf[b]dummy2],i,x[SignOf[a]dummy1]]Box\[Kappa]P[y[b,-SignOf[b]dummy2],1],{dummy1,1,2},{dummy2,1,2}];
SHAB/:Parity@SHAB[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Ang\[Kappa]P[x[a,-MIL[{a,GI[2]}]],-1] SHAB[y[MIL[{b,GI[1]}]],i,x[MIL[{a,GI[-1]}]]]Box\[Kappa]P[y[b,-MIL[{b,GI[1]}]],1];


(* ::Input::Initialization:: *)
SHBA/:Parity@SHBA[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Box\[Kappa]P[x,1] Ang\[Kappa]P[y,-1] SHBA[y,i,x];

SHBA/:Parity@SHBA[x_[a_],i_,y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Sum[ Box\[Kappa]P[x[a,-SignOf[a]dummy],1] Ang\[Kappa]P[y,-1]SHBA[y,i,x[SignOf[a]dummy]],{dummy,1,2}];
SHBA/:Parity@SHBA[x_[a_],i_,y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[MsQ[i]] Box\[Kappa]P[x[a,-GI1[a]],1] Ang\[Kappa]P[y,-1]SHBA[y,i,x[GI0[a]]];

SHBA/:Parity@SHBA[x_,i_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[MsQ[i]] Sum[ Ang\[Kappa]P[y[a,-SignOf[a]dummy],-1] Box\[Kappa]P[x,1]SHBA[y[SignOf[a]dummy],i,x],{dummy,1,2}];
SHBA/:Parity@SHBA[x_,i_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[MsQ[i]] Ang\[Kappa]P[y[a,-GI1[a]],-1] Box\[Kappa]P[x,1]SHBA[y[GI0[a]],i,x];

SHBA/:Parity@SHBA[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy],1] SHBA[y[GI1[b]],i,x[SignOf[a]dummy]]Ang\[Kappa]P[y[b,-GI0[b]],-1],{dummy,1,2}];
SHBA/:Parity@SHBA[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Ang\[Kappa]P[y[b,-SignOf[b]dummy],-1] SHBA[y[SignOf[a]dummy],i,x[GI1[a]]]Box\[Kappa]P[y[b,-GI0[b]],1],{dummy,1,2}];
SHBA/:Parity@SHBA[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Sum[Box\[Kappa]P[x[a,-SignOf[a]dummy1],1] SHBA[y[SignOf[b]dummy2],i,x[SignOf[a]dummy1]]Ang\[Kappa]P[y[b,-SignOf[b]dummy2],-1],{dummy1,1,2},{dummy2,1,2}];
SHBA/:Parity@SHBA[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[MsQ[i]] Box\[Kappa]P[x[a,-MIL[{a,GI[2]}]],1] SHBA[y[MIL[{b,GI[1]}]],i,x[MIL[{a,GI[-1]}]]]Ang\[Kappa]P[y[b,-MIL[{b,GI[1]}]],-1];


(* ::Title::Closed:: *)
(*Time Reversal*)


(* ::Subsection::Closed:: *)
(*Distribution rules*)


Unprotect[TR];
TR=TimeReversal;
Protect[TR];

TimeReversal[x_+ y_] := TimeReversal[x]+TimeReversal[y];
TimeReversal[x_ y_] := TimeReversal[x] TimeReversal[y];
TimeReversal[x_/y_]:= TimeReversal[x]/TimeReversal[y];
TimeReversal[x_^n_] := TimeReversal[x]^TimeReversal[n];
TimeReversal[x_List]:= Map[TimeReversal,x];
TimeReversal[TimeReversal[x_]]:= x;

TimeReversal[x_]/;NumericQ[x] := Conjugate[x];
TimeReversal[x_]/;Simplify[Element[x,Reals]] := x;


(* ::Subsection::Closed:: *)
(*Intrinsic parity*)


(* ::Input::Initialization:: *)
\[CapitalOmega][i_][1,-1]:=+1;
\[CapitalOmega][i_][2,-2]:=-1;
\[CapitalOmega][i_][1,-2]:=0;
\[CapitalOmega][i_][2,-1]:=0;


(* ::Input::Initialization:: *)
\[CapitalOmega][i_][-1,1]:=+1;
\[CapitalOmega][i_][-2,2]:=-1;
\[CapitalOmega][i_][-1,2]:=0;
\[CapitalOmega][i_][-2,1]:=0;


(* ::Input::Initialization:: *)
\[CapitalOmega][i_][1,2]:=-1;
\[CapitalOmega][i_][2,1]:=-1;
\[CapitalOmega][i_][1,1]:=0;
\[CapitalOmega][i_][2,2]:=0;


(* ::Input::Initialization:: *)
\[CapitalOmega][i_][-1,-2]:=+1;
\[CapitalOmega][i_][-2,-1]:=+1;
\[CapitalOmega][i_][-1,-1]:=0;
\[CapitalOmega][i_][-2,-2]:=0;


(* ::Input::Initialization:: *)
(*\[CapitalOmega][i_][OPS[1,a_?IfP]]:=-\[Delta]lg[a,-2]
\[CapitalOmega][i_][OPS[2,a_?IfP]]:=-\[Delta]lg[a,-1]*)


(* ::Input::Initialization:: *)
(*\[CapitalOmega][i_][OPS[-1,a_?IfN]]:=+\[Delta]lg[a,2]
\[CapitalOmega][i_][OPS[-2,a_?IfN]]:=+\[Delta]lg[a,1]*)


(* ::Input::Initialization:: *)
(*\[CapitalOmega][i_][OPS[1,a_?IfN]]:=\[Delta]lg[a,1]
\[CapitalOmega][i_][OPS[2,a_?IfN]]:=-\[Delta]lg[a,2]*)


(* ::Input::Initialization:: *)
(*\[CapitalOmega][i_][OPS[-1,a_?IfP]]:=\[Delta]lg[a,-1]
\[CapitalOmega][i_][OPS[-2,a_?IfP]]:=-\[Delta]lg[a,-2]*)


\[CapitalOmega]/:\[CapitalOmega][i_][a_,b_]/;!OrderedQ[{SignOf[a]a,SignOf[b]b}]:=\[CapitalOmega][i][Sequence@@Sort[{a,b}]]


(* ::Subsection::Closed:: *)
(*Metric*)


(* ::Input::Initialization:: *)
\[Epsilon]/:TimeReversal[\[Epsilon][\[Alpha]_,\[Beta]_]]:=-\[Epsilon][-\[Alpha],-\[Beta]];
\[Epsilon]d/:TimeReversal[\[Epsilon]d[\[Alpha]_,\[Beta]_]]:=-\[Epsilon]d[-\[Alpha],-\[Beta]];
\[Epsilon]lg/:TimeReversal[\[Epsilon]lg[\[Alpha]_,\[Beta]_]]:=\[Epsilon]lg[\[Alpha],\[Beta]];
\[Delta]/:TimeReversal[\[Delta][\[Alpha]_,\[Beta]_]]:=\[Delta][-\[Alpha],-\[Beta]];
\[Delta]d/:TimeReversal[\[Delta]d[\[Alpha]_,\[Beta]_]]:=\[Delta]d[-\[Alpha],-\[Beta]];
\[Delta]lg/:TimeReversal[\[Delta]lg[\[Alpha]_,\[Beta]_]]:=\[Delta]lg[\[Alpha],\[Beta]];

\[Sigma]mat/:TimeReversal@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]:=\[Sigma]mat[\[Mu]][-\[Alpha],-\[Beta]];

\[Eta]/:TimeReversal@\[Eta][\[Mu]___]:=\[Eta][\[Mu]];


(* ::Input::Initialization:: *)
Ang\[Kappa]T[i_[J_,K_],\[Alpha]_]:=-I \[CapitalOmega][i][J,K] (+SignOf[\[Alpha]])(SignOf[J]);
Ang\[Kappa]T[i_,\[Alpha]_]:=-I SignOf[\[Alpha]];


(* ::Input::Initialization:: *)
Box\[Kappa]T[i_[J_,K_],\[Alpha]_]:=-I \[CapitalOmega][i][J,K] (+SignOf[\[Alpha]])(SignOf[J]);
Box\[Kappa]T[i_,\[Alpha]_]:=+I SignOf[\[Alpha]];


(* ::Subsection::Closed:: *)
(*SHA and SHB*)


(* ::Input::Initialization:: *)
SHA/:TimeReversal@SHA[x_,\[Alpha]_]/;!MsQ[x]:=Ang\[Kappa]T[x,\[Alpha]]SHA[x,-\[Alpha]];

SHA/:TimeReversal@SHA[x_[a_],\[Alpha]_]/;MsQ[x]&&IntegerQ[a]:=Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy],\[Alpha]]SHA[x[SignOf[a]dummy],-\[Alpha]],{dummy,1,2}];
SHA/:TimeReversal@SHA[x_[a_],\[Alpha]_]/;MsQ[x]&&!IntegerQ[a]:=Ang\[Kappa]T[x[a,-GI1[a]],\[Alpha]]SHA[x[GI0[a]],-\[Alpha]];


(* ::Input::Initialization:: *)
SHB/:TimeReversal@SHB[x_,\[Alpha]_]/;!MsQ[x]:=Box\[Kappa]T[x,\[Alpha]]SHB[x,-\[Alpha]];
SHB/:TimeReversal@SHB[x_[a_],\[Alpha]_]/;MsQ[x]&&IntegerQ[a]:=Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy],\[Alpha]]SHB[x[SignOf[a]dummy],-\[Alpha]],{dummy,1,2}];
SHB/:TimeReversal@SHB[x_[a_],\[Alpha]_]/;MsQ[x]&&!IntegerQ[a]:=Box\[Kappa]T[x[a,-GI1[a]],\[Alpha]]SHB[x[GI0[a]],-\[Alpha]];


(* ::Subsection::Closed:: *)
(*SHAA and SHBB*)


(* ::Input::Initialization:: *)
SHAA/:TimeReversal@SHAA[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=Ang\[Kappa]T[y,1]Ang\[Kappa]T[x,-1]SHAA[y,x];

SHAA/:TimeReversal@SHAA[x_[a_],y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=Ang\[Kappa]T[y,1]Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy],-1]SHAA[y,x[SignOf[a]dummy]],{dummy,1,2}];

SHAA/:TimeReversal@SHAA[x_[a_],y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=Ang\[Kappa]T[y,1]Ang\[Kappa]T[x[a,-GI1[a]],-1]SHAA[y,x[GI0[a]]];

SHAA/:TimeReversal@HP@SHAA[x_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=Ang\[Kappa]T[x,-1]Sum[Ang\[Kappa]T[y[a,-SignOf[a]dummy],1]SHAA[y[SignOf[a]dummy],x],{dummy,1,2}];

SHAA/:TimeReversal@HP@SHAA[x_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=Ang\[Kappa]T[y[a,-GI1[a]],1]Ang\[Kappa]T[x,-1]SHAA[y[GI0[a]],x];

SHAA/:TimeReversal@SHAA[x_[a_],y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy1],-1]SHAA[y[GI1[b]],x[SignOf[a]dummy1]]Ang\[Kappa]T[y[b,-GI0[b]],1],{dummy1,1,2}];

SHAA/:TimeReversal@SHAA[x_[a_],y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]T[x[a,-GI1[a]],-1]SHAA[y[SignOf[b]dummy2],x[GI0[a]]]Ang\[Kappa]T[y[b,-SignOf[b]dummy2],1],{dummy2,1,2}];

SHAA/:TimeReversal@SHAA[x_[a_],y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy1],-1]SHAA[y[SignOf[b]dummy2],x[SignOf[a]dummy1]]Ang\[Kappa]T[y[b,-SignOf[b]dummy2],1],{dummy1,1,2},{dummy2,1,2}];

SHAA/:TimeReversal@SHAA[x_[a_],y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Ang\[Kappa]T[y[b,-GI1[b]],1]SHAA[y[GI0[b]],x[GI1[a]]]Ang\[Kappa]T[x[a,-GI0[a]],-1];


(* ::Input::Initialization:: *)
SHBB/:TimeReversal@SHBB[x_,y_]/;And[!MsQ[x],!MsQ[y]]:=Box\[Kappa]T[y,-1]Box\[Kappa]T[x,1]SHBB[y,x];

SHBB/:TimeReversal@SHBB[x_[a_],y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=Box\[Kappa]T[y,-1]Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy],1]SHBB[y,x[SignOf[a]dummy]],{dummy,1,2}];

SHBB/:TimeReversal@SHBB[x_[a_],y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=Box\[Kappa]T[y,-1]Box\[Kappa]T[x[a,-GI1[a]],1]SHBB[y,x[GI0[a]]];

SHBB/:TimeReversal@HP@SHBB[x_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=Box\[Kappa]T[x,1]Sum[Box\[Kappa]T[y[a,-SignOf[a]dummy],-1]SHBB[y[SignOf[a]dummy],x],{dummy,1,2}];

SHBB/:TimeReversal@HP@SHBB[x_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=Box\[Kappa]T[y[a,-GI1[a]],-1]Box\[Kappa]T[x,1]SHBB[y[GI0[a]],x];

SHBB/:TimeReversal@SHBB[x_[a_],y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy1],1]SHBB[y[GI1[b]],x[SignOf[a]dummy1]]Box\[Kappa]T[y[b,-GI0[b]],-1],{dummy1,1,2}];

SHBB/:TimeReversal@SHBB[x_[a_],y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]T[x[a,-GI1[a]],1]SHBB[y[SignOf[b]dummy2],x[GI0[a]]]Box\[Kappa]T[y[b,-SignOf[b]dummy2],-1],{dummy2,1,2}];

SHBB/:TimeReversal@SHBB[x_[a_],y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:=Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy1],1]SHBB[y[SignOf[b]dummy2],x[SignOf[a]dummy1]]Box\[Kappa]T[y[b,-SignOf[b]dummy2],-1],{dummy1,1,2},{dummy2,1,2}];

SHBB/:TimeReversal@SHBB[x_[a_],y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:=Box\[Kappa]T[y[b,-GI1[b]],-1]SHBB[y[GI0[b]],x[GI1[a]]]Box\[Kappa]T[x[a,-GI0[a]],1];


(* ::Subsection::Closed:: *)
(*SHAB and SHBA*)


(* ::Input::Initialization:: *)
SHAB/:TimeReversal@SHAB[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]]Ang\[Kappa]T[x,-1] Box\[Kappa]T[y,1] SHAB[x,i,y];

SHAB/:TimeReversal@SHAB[x_[a_],i_,y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]]Sum[ Ang\[Kappa]T[x[a,-SignOf[a]dummy],-1] Box\[Kappa]T[y,1]SHAB[x[SignOf[a]dummy],i,y],{dummy,1,2}];
SHAB/:TimeReversal@SHAB[x_[a_],i_,y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]] Ang\[Kappa]T[x[a,-GI1[a]],-1] Box\[Kappa]T[y,1]SHAB[x[GI0[a]],i,y];

SHAB/:TimeReversal@SHAB[x_,i_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[!MsQ[i]]Sum[ Box\[Kappa]T[y[a,-SignOf[a]dummy],1] Ang\[Kappa]T[x,-1]SHAB[x,i,y[SignOf[a]dummy]],{dummy,1,2}];
SHAB/:TimeReversal@SHAB[x_,i_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[!MsQ[i]] Box\[Kappa]T[y[a,-GI1[a]],1] Ang\[Kappa]T[x,-1]SHAB[x,i,y[GI0[a]]];

SHAB/:TimeReversal@SHAB[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy],-1] SHAB[x[SignOf[a]dummy],i,y[GI1[b]]]Box\[Kappa]T[y[b,-GI0[b]],1],{dummy,1,2}];
SHAB/:TimeReversal@SHAB[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Box\[Kappa]T[y[b,-SignOf[b]dummy],1] SHAB[x[GI1[a]],i,y[SignOf[a]dummy]]Ang\[Kappa]T[y[b,-GI0[b]],-1],{dummy,1,2}];
SHAB/:TimeReversal@SHAB[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Ang\[Kappa]T[x[a,-SignOf[a]dummy1],-1] SHAB[x[SignOf[a]dummy1],i,y[SignOf[b]dummy2]]Box\[Kappa]T[y[b,-SignOf[b]dummy2],1],{dummy1,1,2},{dummy2,1,2}];
SHAB/:TimeReversal@SHAB[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Ang\[Kappa]T[x[a,-GI1[a]],-1] SHAB[x[GI0[a]],i,y[GI1[b]]]Box\[Kappa]T[y[b,-GI0[b]],1];


(* ::Input::Initialization:: *)
SHBA/:TimeReversal@SHBA[x_,i_,y_]/;And[!MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]]Box\[Kappa]T[x,1] Ang\[Kappa]T[y,-1] SHBA[x,i,y];

SHBA/:TimeReversal@SHBA[x_[a_],i_,y_]/;And[IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]]Sum[ Box\[Kappa]T[x[a,-SignOf[a]dummy],1] Ang\[Kappa]T[y,-1]SHBA[x[SignOf[a]dummy],i,y],{dummy,1,2}];
SHBA/:TimeReversal@SHBA[x_[a_],i_,y_]/;And[!IntegerQ[a],MsQ[x],!MsQ[y]]:=(-1)^Boole[!MsQ[i]] Box\[Kappa]T[x[a,-GI1[a]],1] Ang\[Kappa]T[y,-1]SHBA[x[GI0[a]],i,y];

SHBA/:TimeReversal@SHBA[x_,i_,y_[a_]]/;And[IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[!MsQ[i]]Sum[ Ang\[Kappa]T[y[-a,-SignOf[a]dummy],-1] Box\[Kappa]T[x,1]SHBA[x,i,y[SignOf[a]dummy]],{dummy,1,2}];
SHBA/:TimeReversal@SHBA[x_,i_,y_[a_]]/;And[!IntegerQ[a],!MsQ[x],MsQ[y]]:=(-1)^Boole[!MsQ[i]] Ang\[Kappa]T[y[a,-GI1[a]],-1] Box\[Kappa]T[x,1]SHBA[x,i,y[GI0[a]]];

SHBA/:TimeReversal@SHBA[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy],1] SHBA[x[SignOf[a]dummy],i,y[GI1[b]]]Ang\[Kappa]T[y[b,-GI0[b]],-1],{dummy,1,2}];
SHBA/:TimeReversal@SHBA[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Ang\[Kappa]T[y[b,-SignOf[b]dummy],-1] SHBA[x[GI1[a]],i,y[SignOf[a]dummy]]Box\[Kappa]T[y[b,-GI0[b]],1],{dummy,1,2}];
SHBA/:TimeReversal@SHBA[x_[a_],i_,y_[b_]]/;And[IntegerQ[a],IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Sum[Box\[Kappa]T[x[a,-SignOf[a]dummy1],1] SHBA[x[SignOf[a]dummy1],i,y[SignOf[b]dummy2]]Ang\[Kappa]T[y[b,-SignOf[b]dummy2],-1],{dummy1,1,2},{dummy2,1,2}];
SHBA/:TimeReversal@SHBA[x_[a_],i_,y_[b_]]/;And[!IntegerQ[a],!IntegerQ[b],MsQ[x],MsQ[y]]:= (-1)^Boole[!MsQ[i]]Box\[Kappa]T[x[a,-GI1[a]],1] SHBA[x[GI0[a]],i,y[GI1[b]]]Ang\[Kappa]T[y[b,-GI0[b]],-1];


(* ::Title::Closed:: *)
(*CPT*)


(* ::Subsection::Closed:: *)
(*Intrinsic Parity*)


(* ::Input::Initialization:: *)
\[CapitalDelta][i_][1,1]:=+1;
\[CapitalDelta][i_][2,2]:=+1;
\[CapitalDelta][i_][1,2]:=0;
\[CapitalDelta][i_][2,1]:=0;


(* ::Input::Initialization:: *)
\[CapitalDelta][i_][-1,-1]:=+1;
\[CapitalDelta][i_][-2,-2]:=+1;
\[CapitalDelta][i_][-1,-2]:=0;
\[CapitalDelta][i_][-2,-1]:=0;


(* ::Input::Initialization:: *)
\[CapitalDelta][i_][1,-1]:=0;
\[CapitalDelta][i_][2,-2]:=0;
\[CapitalDelta][i_][1,-2]:=+1;
\[CapitalDelta][i_][2,-1]:=-1;


(* ::Input::Initialization:: *)
\[CapitalDelta][i_][-1,1]:=0;
\[CapitalDelta][i_][-2,2]:=0;
\[CapitalDelta][i_][-1,2]:=-1;
\[CapitalDelta][i_][-2,1]:=+1;


(* ::Input::Initialization:: *)
ChargeConjugate[\[CapitalSigma][a_][b___]]:=\[CapitalSigma][a][b];
Parity[\[CapitalSigma][a_][b___]]:=\[CapitalSigma][a][b];
TimeReversal[\[CapitalSigma][a_][b___]]:=\[CapitalSigma][a][b];
ChargeConjugate[\[CapitalOmega][a_][b___]]:=\[CapitalOmega][a][b];
Parity[\[CapitalOmega][a_][b___]]:=\[CapitalOmega][a][b];
TimeReversal[\[CapitalOmega][a_][b___]]:=\[CapitalOmega][a][b]


(* ::Subsection::Closed:: *)
(*CPT*)


CPT[expr_]:=expr//TimeReversal//Parity//ChargeConjugate;


(* ::Title:: *)
(*Ignore*)


Print["Loaded: CPT"]
