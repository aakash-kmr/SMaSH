(* ::Package:: *)

(* ::Section::Closed:: *)
(*Default Canonical*)


(* ::Input::Initialization:: *)
\[Epsilon][A_,A_]:=0;
\[Epsilon]d[A_,A_]:=0;
\[Epsilon]lg[A_,A_]:=0;


\[Delta]d/:\[Delta]d[1,-1]:= 1;
\[Delta]d/:\[Delta]d[2,-2]:= 1;
\[Delta]d/:\[Delta]d[-1,1]:= 1;
\[Delta]d/:\[Delta]d[-2,2]:= 1;
\[Delta]d/:\[Delta]d[1,-2]:= 0;
\[Delta]d/:\[Delta]d[-1,2]:= 0;
\[Delta]d/:\[Delta]d[2,-1]:= 0;
\[Delta]d/:\[Delta]d[-2,1]:= 0;
\[Epsilon]d/:\[Epsilon]d[1,2]:=1;
\[Epsilon]d/:\[Epsilon]d[2,1]:=-1;
\[Epsilon]d/:\[Epsilon]d[-1,-2]:=-1;
\[Epsilon]d/:\[Epsilon]d[-2,-1]:=1;


\[Delta]/:\[Delta][1,-1]:= 1;
\[Delta]/:\[Delta][2,-2]:= 1;
\[Delta]/:\[Delta][-1,1]:= 1;
\[Delta]/:\[Delta][-2,2]:= 1;
\[Delta]/:\[Delta][1,-2]:= 0;
\[Delta]/:\[Delta][-1,2]:= 0;
\[Delta]/:\[Delta][2,-1]:= 0;
\[Delta]/:\[Delta][-2,1]:= 0;
\[Epsilon]/:\[Epsilon][1,2]:=1;
\[Epsilon]/:\[Epsilon][2,1]:=-1;
\[Epsilon]/:\[Epsilon][-1,-2]:=-1;
\[Epsilon]/:\[Epsilon][-2,-1]:=1;


\[Delta]lg/:\[Delta]lg[1,-1]:= 1;
\[Delta]lg/:\[Delta]lg[2,-2]:= 1;
\[Delta]lg/:\[Delta]lg[-1,1]:= 1;
\[Delta]lg/:\[Delta]lg[-2,2]:= 1;
\[Delta]lg/:\[Delta]lg[1,-2]:= 0;
\[Delta]lg/:\[Delta]lg[-1,2]:= 0;
\[Delta]lg/:\[Delta]lg[2,-1]:= 0;
\[Delta]lg/:\[Delta]lg[-2,1]:= 0;
\[Epsilon]lg/:\[Epsilon]lg[1,2]:=1;
\[Epsilon]lg/:\[Epsilon]lg[2,1]:=-1;
\[Epsilon]lg/:\[Epsilon]lg[-1,-2]:=-1;
\[Epsilon]lg/:\[Epsilon]lg[-2,-1]:=1;


SHAA[A_,A_]:=0;
SHBB[A_,A_]:=0;
SHAB[i_,i_,k_]:=0;
SHAB[i_,j_,j_]:=0;
SHBA[i_,i_,k_]:=0;
SHBA[i_,j_,j_]:=0;


(* ::Input::Initialization:: *)
SHA[-a_,\[Alpha]_]:=-SHA[a,\[Alpha]]
SHA[a_?Negative,\[Alpha]_]:=-SHA[-a,\[Alpha]]


(* ::Input::Initialization:: *)
SHB[-a_,\[Alpha]_]:=SHB[a,\[Alpha]]
SHB[a_?Negative,\[Alpha]_]:=SHB[-a,\[Alpha]]


(* ::Input::Initialization:: *)
SHAA[a1___,-a_,a2___]:=-SHAA[a1,a,a2]
SHAA[a1___,a_?Negative,a2___]:=-SHAA[a1,-a,a2]


(* ::Input::Initialization:: *)
SHBB[a1___,-a_,a2___]:=SHBB[a1,a,a2]
SHBB[a1___,a_?Negative,a2___]:=SHBB[a1,-a,a2]


(* ::Input::Initialization:: *)
SHAB[-a1_,a_,a2_]:=-SHAB[a1,a,a2]
SHAB[a1_?Negative,a_,a2_]:=-SHAB[-a1,a,a2]
SHAB[a1_,-a_,a2_]:=-SHAB[a1,a,a2]
SHAB[a1_,a_?Negative,a2_]:=-SHAB[a1,-a,a2]
SHAB[a1_,a_,-a2_]:=SHAB[a1,a,a2]
SHAB[a1_,a_,a2_?Negative]:=SHAB[a1,a,-a2]


(* ::Input::Initialization:: *)
SHBA[-a1_,a_,a2_]:=SHBA[a1,a,a2]
SHBA[a1_?Negative,a_,a2_]:=SHBA[-a1,a,a2]
SHBA[a1_,-a_,a2_]:=-SHBA[a1,a,a2]
SHBA[a1_,a_?Negative,a2_]:=-SHBA[a1,-a,a2]
SHBA[a1_,a_,-a2_]:=-SHBA[a1,a,a2]
SHBA[a1_,a_,a2_?Negative]:=-SHBA[a1,a,-a2]


(* ::Input::Initialization:: *)
SHAB/:SHAB[i_,TL[a_],b_]:=SHAB[i,a,b]
SHBA/:SHBA[i_,TL[a_],b_]:=SHBA[i,a,b]


(* ::Section::Closed:: *)
(*CanonicalOrder*)


(* ::Input::Initialization:: *)
(*Function to make a canonical choice of ordering based on lexicographic order for both legs massless or massive. In case of one massless-one massive, {massive,massless} ordering is chosen.*)
CanonicalOrderFunction[x_,y_]:= If [MatchQ[x, _[_]], If[MatchQ[y, _[_]], OrderedQ[{x,y}], True], If[MatchQ[y, _[_]], False, OrderedQ[{x,y}]]];

(* Function which checks the ordering based on CanonicalOrderFunction.*)

CanonicalOrderedQ[x_]:= OrderedQ[x,CanonicalOrderFunction];


(* ::Input::Initialization:: *)
(*Put Canonical Ordering*)
CanonicalOrderRules:={
\[Epsilon][A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:>-\[Epsilon][B,A ],
\[Epsilon]d[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:>-\[Epsilon]d[B,A ],
\[Epsilon]lg[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:>-\[Epsilon]lg[B,A ],
\[Delta][A_,B_]/;IfN[A]:>\[Delta][B,A],
\[Delta]d[A_,B_]/;IfN[A]:>\[Delta]d[B,A],
\[Delta]lg[A_,B_]/;IfN[A]:>\[Delta]lg[B,A],
SHAA[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:>-SHAA[B,A ],
SHBB[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:>-SHBB[B,A ],

X_[a___,i_?MsQ[K_],b___]*Y_[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]&&MemberQ[{SHB,SHBB},Y]:>-X[a,i[-K],b]*Y[c,j[-L],d],

X_[a___,i_?MsQ[K_],b___]*SHAB[c_,d_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]:>-X[a,i[-K],b]*SHAB[c,d,j[-L]],
SHAB[i_?MsQ[K_],a_,b_]*Y_[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHB,SHBB},Y]:>-SHAB[i[-K],a,b]*Y[c,j[-L],d],

X_[a___,i_?MsQ[K_],b___]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0&&MemberQ[{SHB,SHBB},X]:>-X[a,i[-K],b]*SHBA[c,d,j[-L]],
SHBA[i_?MsQ[K_],a_,b_]*Y_[c___,j_?MsQ[L_],d___]/;SignOf[L]==1&&K+L==0&&MemberQ[{SHA,SHAA},Y]:>-SHBA[i[-K],a,b]*Y[c,j[-L],d],

SHAB[i_?MsQ[K_],a_,b_]*SHAB[c_,d_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:>-SHAB[i[-K],a,b]*SHAB[c,d,j[-L]],
SHAB[a_,b_,i_?MsQ[K_]]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:>-SHAB[a,b,i[-K]]*SHBA[c,d,j[-L]],
SHAB[i_?MsQ[K_],a_,b_]*SHBA[j_?MsQ[L_],c_,d_]/;SignOf[K]==1&&K+L==0:>-SHAB[i[-K],a,b]*SHBA[j[-L],c,d],
SHBA[i_?MsQ[K_],a_,b_]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:>-SHBA[i[-K],a,b]*SHBA[c,d,j[-L]],

SHAB[i_?MsQ[K_],a_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:> -SHAB[i[-K],a,j[-L]],
SHBA[i_?MsQ[K_],a_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:> -SHBA[i[-K],a,j[-L]],

X_[a___,i_?MsQ[K_],b___]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]:>-X[a,i[-K],b]*\[CapitalSigma]1[i][c,-L,d],
X_[a___,i_?MsQ[K_],b___]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==-1&&K+L==0&&MemberQ[{SHB,SHBB},X]:>-X[a,i[-K],b]*\[CapitalSigma]1[i][c,-L,d],
SHAB[i_?MsQ[K_],a_,b_]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==1&&K+L==0:>-SHAB[i[-K],a,b]*\[CapitalSigma]1[i][c,-L,d],
SHAB[a_,b_,i_?MsQ[K_]]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==-1&&K+L==0:>-SHAB[a,b,i[-K]]*\[CapitalSigma]1[i][c,-L,d],
SHBA[i_?MsQ[K_],a_,b_]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==-1&&K+L==0:>-SHBA[i[-K],a,b]*\[CapitalSigma]1[i][c,-L,d],
SHBA[a_,b_,i_?MsQ[K_]]*\[CapitalSigma]1_[i_][c___,L_,d___]/;MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&SignOf[K]==1&&K+L==0:>-SHBA[a,b,i[-K]]*\[CapitalSigma]1[i][c,-L,d]
};

PutCanonicalOrder[expr_]:=expr//.CanonicalOrderRules;


(* ::Input::Initialization:: *)
SetDefaultOrdering[]:=Module[{},
Unprotect[\[CapitalSigma],\[CapitalOmega],\[CapitalDelta],SHA,SHB,SHAA,SHBB,SHAB,SHBA,\[Epsilon],\[Epsilon]d,\[Epsilon]lg,\[Sigma]mat,GI,GI0,GI1,MI,pMatLower,pMatUpper,\[Sigma]VecLower,\[Sigma]VecUpper,\[Sigma]barVecLower,\[Sigma]barVecUpper,\[Eta],Met,Metd,Metlg];
	\[Epsilon]/:\[Epsilon][A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:=-\[Epsilon][B,A ];
	\[Epsilon]d/:\[Epsilon]d[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:=-\[Epsilon]d[B,A ];
	\[Epsilon]lg/:\[Epsilon]lg[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:=-\[Epsilon]lg[B,A ];
	\[Delta]/:\[Delta][A_,B_]/;IfN[A]:=\[Delta][B,A];
	\[Delta]d/:\[Delta]d[A_,B_]/;IfN[A]:=\[Delta]d[B,A];
	\[Delta]lg/:\[Delta]lg[A_,B_]/;IfN[A]:=\[Delta]lg[B,A];
	SHAA/:SHAA[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:=-SHAA[B,A ];
	SHBB/:SHBB[A_,B_]/;Not[CanonicalOrderedQ[{A,B}]]:=-SHBB[B,A ];
	(*Define the rule on the Multiplication operator*)
	SHAA/:SHAA[a___,i_?MsQ[K_],b___]*Y_[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHB,SHBB},Y]:=-SHAA[a,i[-K],b]*Y[c,j[-L],d];
	SHA/:SHA[a___,i_?MsQ[K_],b___]*Y_[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHB,SHBB},Y]:=-SHA[a,i[-K],b]*Y[c,j[-L],d];
	SHBB/:X_[a___,i_?MsQ[K_],b___]*SHBB[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHB,SHBB},Y]:=-X[a,i[-K],b]*SHBB[c,j[-L],d];
	SHB/:X_[a___,i_?MsQ[K_],b___]*SHB[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHB,SHBB},Y]:=-X[a,i[-K],b]*SHB[c,j[-L],d];
	
	SHA/:SHA[a___,i_?MsQ[K_],b___]*SHAB[c_,d_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:=-SHA[a,i[-K],b]*SHAB[c,d,j[-L]];
	SHAA/:SHAA[a___,i_?MsQ[K_],b___]*SHAB[c_,d_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:=-SHAA[a,i[-K],b]*SHAB[c,d,j[-L]];
	SHB/:SHAB[i_?MsQ[K_],a_,b_]*SHB[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*SHB[c,j[-L],d];
	SHBB/:SHAB[i_?MsQ[K_],a_,b_]*SHBB[c___,j_?MsQ[L_],d___]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*SHBB[c,j[-L],d];
	
	SHB/:SHB[a___,i_?MsQ[K_],b___]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:=-SHB[a,i[-K],b]*SHBA[c,d,j[-L]];
	SHBB/:SHBB[a___,i_?MsQ[K_],b___]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:=-SHBB[a,i[-K],b]*SHBA[c,d,j[-L]];
	
	SHA/:SHBA[i_?MsQ[K_],a_,b_]*SHA[c___,j_?MsQ[L_],d___]/;SignOf[L]==1&&K+L==0:=-SHBA[i[-K],a,b]*Y[c,j[-L],d];
	SHAA/:SHBA[i_?MsQ[K_],a_,b_]*SHAA[c___,j_?MsQ[L_],d___]/;SignOf[L]==1&&K+L==0:=-SHBA[i[-K],a,b]*Y[c,j[-L],d];
	
	SHAB/:SHAB[i_?MsQ[K_],a_,b_]*SHAB[c_,d_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*SHAB[c,d,j[-L]];
	SHAB/:SHAB[a_,b_,i_?MsQ[K_]]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:=-SHAB[a,b,i[-K]]*SHBA[c,d,j[-L]];
	SHAB/:SHAB[i_?MsQ[K_],a_,b_]*SHBA[j_?MsQ[L_],c_,d_]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*SHBA[j[-L],c,d];
	SHBA/:SHBA[i_?MsQ[K_],a_,b_]*SHBA[c_,d_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:=-SHBA[i[-K],a,b]*SHBA[c,d,j[-L]];
	
	SHAB/:SHAB[i_?MsQ[K_],a_,j_?MsQ[L_]]/;SignOf[K]==1&&K+L==0:= -SHAB[i[-K],a,j[-L]];
	SHBA/:SHBA[i_?MsQ[K_],a_,j_?MsQ[L_]]/;SignOf[L]==1&&K+L==0:= -SHBA[i[-K],a,j[-L]];

\[CapitalSigma]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]:=-X[a,i[-K],b]*\[CapitalSigma][i][c,-L,d];
\[CapitalSigma]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0&&MemberQ[{SHB,SHBB},X]:=-X[a,i[-K],b]*\[CapitalSigma][i][c,-L,d];
\[CapitalSigma]/:SHAB[i_?MsQ[K_],a_,b_]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*\[CapitalSigma][i][c,-L,d];
\[CapitalSigma]/:SHAB[a_,b_,i_?MsQ[K_]]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHAB[a,b,i[-K]]*\[CapitalSigma][i][c,-L,d];
\[CapitalSigma]/:SHBA[i_?MsQ[K_],a_,b_]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHBA[i[-K],a,b]*\[CapitalSigma][i][c,-L,d];
\[CapitalSigma]/:SHBA[a_,b_,i_?MsQ[K_]]*\[CapitalSigma][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHBA[a,b,i[-K]]*\[CapitalSigma][i][c,-L,d];

\[CapitalOmega]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]:=-X[a,i[-K],b]*\[CapitalOmega][i][c,-L,d];
\[CapitalOmega]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0&&MemberQ[{SHB,SHBB},X]:=-X[a,i[-K],b]*\[CapitalOmega][i][c,-L,d];
\[CapitalOmega]/:SHAB[i_?MsQ[K_],a_,b_]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*\[CapitalOmega][i][c,-L,d];
\[CapitalOmega]/:SHAB[a_,b_,i_?MsQ[K_]]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHAB[a,b,i[-K]]*\[CapitalOmega][i][c,-L,d];
\[CapitalOmega]/:SHBA[i_?MsQ[K_],a_,b_]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHBA[i[-K],a,b]*\[CapitalOmega][i][c,-L,d];
\[CapitalOmega]/:SHBA[a_,b_,i_?MsQ[K_]]*\[CapitalOmega][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHBA[a,b,i[-K]]*\[CapitalOmega][i][c,-L,d];

\[CapitalDelta]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0&&MemberQ[{SHA,SHAA},X]:=-X[a,i[-K],b]*\[CapitalDelta][i][c,-L,d];
\[CapitalDelta]/:X_[a___,i_?MsQ[K_],b___]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0&&MemberQ[{SHB,SHBB},X]:=-X[a,i[-K],b]*\[CapitalDelta][i][c,-L,d];
\[CapitalDelta]/:SHAB[i_?MsQ[K_],a_,b_]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHAB[i[-K],a,b]*\[CapitalDelta][i][c,-L,d];
\[CapitalDelta]/:SHAB[a_,b_,i_?MsQ[K_]]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHAB[a,b,i[-K]]*\[CapitalDelta][i][c,-L,d];
\[CapitalDelta]/:SHBA[i_?MsQ[K_],a_,b_]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==-1&&K+L==0:=-SHBA[i[-K],a,b]*\[CapitalDelta][i][c,-L,d];
\[CapitalDelta]/:SHBA[a_,b_,i_?MsQ[K_]]*\[CapitalDelta][i_][c___,L_,d___]/;SignOf[K]==1&&K+L==0:=-SHBA[a,b,i[-K]]*\[CapitalDelta][i][c,-L,d];

Protect[\[CapitalSigma],\[CapitalOmega],\[CapitalDelta],SHA,SHB,SHAA,SHBB,SHAB,SHBA,\[Epsilon],\[Epsilon]d,\[Epsilon]lg,\[Sigma]mat,GI,GI0,GI1,MI,pMatLower,pMatUpper,\[Sigma]VecLower,\[Sigma]VecUpper,\[Sigma]barVecLower,\[Sigma]barVecUpper,\[Eta],Met,Metd,Metlg];
];


(* ::Section::Closed:: *)
(*Contract Metric*)


(* ::Input::Initialization:: *)
MetricRules:=Join[SU2LMetricRules,SU2RMetricRules,SU2LGMetricRules,LorMetricRules];


ContractBilinears[expr_]:=expr//.MetricRules//PutCanonicalOrder;


ContractMetric=ContractBilinears;


(* ::Subsection:: *)
(*Subscript[SU(2), L] Metric Product Rules*)


(* ::Input::Initialization:: *)
SU2LMetricRules:=Join[
MakeRulesForExponents[{HF@HP@\[Epsilon][A_,B_],HF@ \[Epsilon][A,B]},{HF@HP@\[Epsilon][C_,D_],HF@ \[Epsilon][C,D]}, HF[-\[Delta][A,C]\[Delta][B,D ]+\[Delta][A,D]\[Delta][B,C ]],HF[And[IfN[A],IfN[B],IfP[C],IfP[D]]]],
MakeRulesForExponents[{HF@HP@\[Epsilon][A_,B_],HF@ \[Epsilon][A,B]},{HF@\[Delta][OPS[C_,D_]],HF@\[Delta][OPS[C,D]]}, HF@ \[Epsilon][A,D],HF[B+C==0&&!IntegerQ[C]]],
MakeRulesForExponents[{HF@HP@\[Epsilon][A_,B_],HF@ \[Epsilon][A,B]},{HF@\[Delta][OPS[C_,D_]],HF@\[Delta][OPS[C,D]]},HF@ \[Epsilon][D,B],HF[A+C==0&&!IntegerQ[C]]],
MakeRulesForExponents[{HF@\[Delta][OPS[A_,B_]],HF@\[Delta][OPS[A,B]]},{HF@\[Delta][OPS[C_,D_]],HF@\[Delta][C,D]},HF@ \[Delta][D,B],HF[A+C==0&&!IntegerQ[C]]],
{\[Delta][A_, B_]/;(A+B)==0 &&!IntegerQ[SignOf[A]A]:>2 },(*The repeated indices are summed over*)

MakeRulesForExponents[{HF@SHB[j_, B_],HF@SHB[j, B]},{HF@ HP@\[Epsilon][A_, C_] ,HF@ \[Epsilon][A, C] },HF@ SHB[j, A],HF[(B + C == 0)&&!IntegerQ[C]]],
MakeRulesForExponents[{HF@SHB[j_, B_],HF@SHB[j, B]},{HF@ \[Delta][A_, C_] ,HF@\[Delta][A, C] },HF@ SHB[j, A],HF[(B + C == 0)  &&!IntegerQ[C]]],
MakeRulesForExponents[{HF@SHB[j_, B_],HF@SHB[j, B]},{ HF@ HP@\[Epsilon][A_, C_], HF@ \[Epsilon][A, C]} ,  HF[-SHB[j, C]],HF[(B + A == 0) &&!IntegerQ[A]]],
MakeRulesForExponents[{HF@SHB[j_, B_],HF@SHB[j, B]},{ HF@\[Delta][OPS[A_, C_]], HF@\[Delta][A, C]} ,  HF[SHB[j, C]],HF[(B + A == 0)&&!IntegerQ[A]]],

MakeRulesForExponents[{HF@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@HP@\[Epsilon][\[Gamma]_,\[Delta]_],HF@ \[Epsilon][\[Gamma],\[Delta]]}, HF@ \[Sigma]mat[\[Mu]][\[Gamma],\[Beta]],HF[\[Delta]+\[Alpha]==0&&!IntegerQ[\[Alpha]]]],
MakeRulesForExponents[{HF@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@HP@\[Epsilon][\[Delta]1_,\[Gamma]_],HF@ \[Epsilon][\[Delta]1,\[Gamma]]},HF[ - \[Sigma]mat[\[Mu]][\[Gamma],\[Beta]]],HF[\[Delta]1+\[Alpha]==0&&!IntegerQ[\[Alpha]]]],
MakeRulesForExponents[{HF@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@\[Delta][OPS[\[Delta]1_,\[Gamma]_]],HF@\[Delta][\[Delta]1,\[Gamma]]},  HF@ \[Sigma]mat[\[Mu]][\[Gamma],\[Beta]],HF[\[Delta]1+\[Alpha]==0&&!IntegerQ[\[Alpha]]]],
MakeRulesForExponents[{HF@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@\[Delta][OPS[\[Gamma]_,\[Delta]1_]],HF@\[Delta][\[Gamma],\[Delta]1]}, HF@  \[Sigma]mat[\[Mu]][\[Gamma],\[Beta]],HF[\[Delta]1+\[Alpha]==0&&!IntegerQ[\[Alpha]]]]
];

ContractLBilinear[expr_]:=expr//.SU2LMetricRules//Expand;
ContractSU2LMetric=ContractLBilinear;


(* ::Subsection:: *)
(*Subscript[SU(2), R] Metric Product Rules*)


(* ::Input::Initialization:: *)
SU2RMetricRules:=Join[
MakeRulesForExponents[{HF@HP@\[Epsilon]d[A_,B_],HF@ \[Epsilon]d[A,B]},{HF@HP@\[Epsilon]d[C_,D_],HF@ \[Epsilon]d[C,D]}, HF[-\[Delta]d[A,C]\[Delta]d[B,D ]+\[Delta]d[A,D]\[Delta]d[B,C ]],HF@And[IfN[A],IfN[B],IfP[C],IfP[D]]],
MakeRulesForExponents[{HF@HP@\[Epsilon]d[A_,B_],HF@ \[Epsilon]d[A,B]},{HF@\[Delta]d[OPS[C_,D_]],HF@\[Delta]d[OPS[C,D]]}, HF@ \[Epsilon]d[A,D],HF[B+C==0&&!IntegerQ[B]]],
MakeRulesForExponents[{HF@HP@\[Epsilon]d[A_,B_],HF@ \[Epsilon]d[A,B]},{HF@\[Delta]d[OPS[C_,D_]],HF@\[Delta]d[OPS[C,D]]}, HF@\[Epsilon]d[D,B],HF[A+C==0&&!IntegerQ[A]]],
MakeRulesForExponents[{HF@\[Delta]d[OPS[A_,B_]],HF@\[Delta]d[OPS[A,B]]},{HF@\[Delta]d[OPS[C_,D_]],HF@\[Delta]d[OPS[C,D]]},HF@\[Delta]d[D,B],HF[A+C==0&&!IntegerQ[B]]],
{\[Delta]d[A_, B_]/;(A+B)==0&&!IntegerQ[SignOf[A]A] :>2},(*The repeated indices are summed over*)
MakeRulesForExponents[{HF@HP@SHA[j_, B_],HF@SHA[j, B]},{HF@ HP@\[Epsilon]d[A_, C_],HF@ \[Epsilon]d[A, C]},  HF@SHA[j, A],HF[ (B + C == 0)&&!IntegerQ[B] ]],
MakeRulesForExponents[{HF@HP@SHA[j_, B_],HF@SHA[j, B]},{HF@ \[Delta]d[OPS[A_, C_]],HF@ \[Delta]d[A, C]},  HF@SHA[j, A],HF[ (B + C == 0) &&!IntegerQ[B]]],
MakeRulesForExponents[{HF@HP@SHA[j_, B_],HF@SHA[j, B]},{HF@ HP@\[Epsilon]d[A_, C_],HF@ \[Epsilon]d[A, C]},  HF[-SHA[j, C]],HF[ (B + A == 0)&&!IntegerQ[B] ]],
MakeRulesForExponents[{HF@HP@SHA[j_, B_],HF@SHA[j, B]},{HF@\[Delta]d[OPS[A_, C_]],HF@ \[Delta]d[A, C]}, HF@SHA[j, C],HF[ (B + A == 0)&&!IntegerQ[B] ]],

MakeRulesForExponents[{HF@HP@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@HP@\[Epsilon]d[\[Gamma]_,\[Delta]_],HF@ \[Epsilon]d[\[Gamma],\[Delta]]},  HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Gamma]],HF[\[Delta]+\[Beta]==0&&!IntegerQ[\[Delta]]]],
MakeRulesForExponents[{HF@HP@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@HP@\[Epsilon]d[\[Delta]_,\[Gamma]_],HF@ \[Epsilon]d[\[Delta],\[Gamma]]}, HF[- \[Sigma]mat[\[Mu]][\[Alpha],\[Gamma]]],HF[\[Delta]+\[Beta]==0&&!IntegerQ[\[Delta]]]],
MakeRulesForExponents[{HF@HP@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@\[Delta]d[OPS[\[Gamma]_,\[Delta]_]],HF@\[Delta]d[\[Gamma],\[Delta]]}, HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Gamma]],HF[\[Delta]+\[Beta]==0&&!IntegerQ[\[Delta]]]],
MakeRulesForExponents[{HF@HP@\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_],HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Beta]]},{HF@\[Delta]d[OPS[\[Delta]_,\[Gamma]_]],HF@\[Delta]d[\[Delta],\[Gamma]]}, HF@\[Sigma]mat[\[Mu]][\[Alpha],\[Gamma]],HF[\[Delta]+\[Beta]==0&&!IntegerQ[\[Delta]]]]
];

ContractRBilinear[expr_]:=expr//.SU2RMetricRules;
ContractSU2RMetric=ContractRBilinear;


(* ::Subsection:: *)
(*Subscript[SU(2), LG] Metric Product Rules*)


(* ::Input::Initialization:: *)
SU2LGMetricRules := Join[
{\[Delta]lg[A_,B_]/;(A+B)==0&&!IntegerQ[A]:> 2}(*The repeated indices are summed over*),
MakeRulesForExponents[{HF@HP@\[Epsilon]lg[A_,B_],HF@ \[Epsilon]lg[A,B]},{HF@HP@\[Epsilon]lg[C_,D_],HF@ \[Epsilon]lg[C,D]},HF[ -\[Delta]lg[A,C]\[Delta]lg[B,D ]+\[Delta]lg[A,D]\[Delta]lg[B,C ]],HF[And[IfN[A],IfN[B],IfP[C],IfP[D]]]],
MakeRulesForExponents[{HF@HP@\[Epsilon]lg[A_,B_],HF@ \[Epsilon]lg[A,B]},{HF@\[Delta]lg[OPS[C_,D_]],HF@\[Delta]lg[OPS[C,D]]}, HF@ \[Epsilon]lg[A,D],HF[B+C==0&&!IntegerQ[C]]],
MakeRulesForExponents[{HF@HP@\[Epsilon]lg[A_,B_],HF@ \[Epsilon]lg[A,B]},{HF@\[Delta]lg[OPS[C_,D_]],HF@\[Delta]lg[OPS[C,D]]}, HF@ \[Epsilon]lg[D,B],HF[A+C==0&&!IntegerQ[C]]],
MakeRulesForExponents[{HF@\[Delta]lg[OPS[A_,B_]],HF@\[Delta]lg[OPS[A,B]]},{HF@\[Delta]lg[OPS[C_,D_]],HF@\[Delta]lg[OPS[C,D]]},HF@\[Delta]lg[D,B],HF[A+C==0&&!IntegerQ[C]]],

MakeRulesForExponents[{HF@HP@X_[Y___, Z_[J_], W___],HF@X[Y, Z[J], W] },{HF@HP@\[Epsilon]lg[L_, K_],HF@ \[Epsilon]lg[L, K] }, HF[X[Y, Z[L], W]] ,HF[MsQ[Z]&&J + K == 0&&!IntegerQ[K]&&MemberQ[{SHA,SHB,SHAA,SHBB,SHAB,SHBA}, X]]], 
MakeRulesForExponents[{HF@HP@X_[Y___, Z_[J_], W___],HF@X[Y, Z[J], W]},{HF@HP@ \[Epsilon]lg[L_, K_],HF@ \[Epsilon]lg[L, K]} ,HF[ -X[Y, Z[K], W]] ,HF[MsQ[Z]&&J + L == 0&&!IntegerQ[L]&&MemberQ[{SHA,SHB,SHAA,SHBB,SHAB,SHBA}, X]]], 
MakeRulesForExponents[{HF@HP@X_[Y___, Z_[J_], W___],HF@X[Y, Z[J], W]},{HF@ \[Delta]lg[OPS[L_, K_]],HF@\[Delta]lg[L, K]} ,HF@ X[Y, Z[L], W] ,HF[ MsQ[Z]&&J + K == 0&&!IntegerQ[K]&&MemberQ[{SHA,SHB,SHAA,SHBB,SHAB,SHBA}, X]]], 
MakeRulesForExponents[{HF@HP@X_[Y___, Z_[J_], W___],HF@X[Y, Z[J], W]},{ HF@\[Delta]lg[OPS[L_, K_]],HF@\[Delta]lg[L, K]} , HF@X[Y, Z[K], W] ,HF[ MsQ[Z]&&J + L == 0&&!IntegerQ[L]&&MemberQ[{SHA,SHB,SHAA,SHBB,SHAB,SHBA}, X]]],

MakeRulesForExponents[{HF@\[Zeta]_[K_],HF@\[Zeta][K]},{HF@HP@\[Epsilon]lg[L_,M_],HF@\[Epsilon]lg[L,M]},HF@(\[Zeta][L]),HF[MemberQ[{\[Zeta]p,\[Zeta]m},\[Zeta]]&&K+M==0&&!IntegerQ[K]]],
MakeRulesForExponents[{HF@\[Zeta]_[K_],HF@\[Zeta][K]},{HF@HP@\[Epsilon]lg[L_,M_],HF@\[Epsilon]lg[L,M]},HF@(-\[Zeta][M]),HF[MemberQ[{\[Zeta]p,\[Zeta]m},\[Zeta]]&&K+L==0&&!IntegerQ[K]]],
MakeRulesForExponents[{HF@\[Zeta]_[K_],HF@\[Zeta][K]},{HF@\[Delta]lg[OPS[L_,M_]],HF@\[Delta]lg[L,M]},HF@(\[Zeta][L]),HF[MemberQ[{\[Zeta]p,\[Zeta]m},\[Zeta]]&&K+M==0&&!IntegerQ[K]]],

MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@\[CapitalSigma]1_[i_][OPS[c_,d_]],HF@\[CapitalSigma]1[i][c,d]},HF[SignOf[d]Metlg[a,d]],HF[MemberQ[{\[CapitalSigma],\[CapitalOmega]},\[CapitalSigma]1]&&b+c==0&&!IntegerQ[c]&&IfP[b]&&IfN[c]]],
MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@HP@\[Epsilon]lg[c_,d_],HF@\[Epsilon]lg[c,d]},HF@(-\[CapitalSigma]1[i][a,d]),HF[MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&b+c==0&&!IntegerQ[c]]],
MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@HP@\[Epsilon]lg[c_,d_],HF@\[Epsilon]lg[c,d]},HF@(\[CapitalSigma]1[i][a,c]),HF[MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&b+d==0&&!IntegerQ[d]]],
MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@\[Delta]lg[c_,d_],HF@\[Delta]lg[c,d]},HF@(\[CapitalSigma]1[i][a,c]),HF[MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&b+d==0&&!IntegerQ[d]]],
MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@\[Delta]lg[d_,c_],HF@\[Delta]lg[d,c]},HF@(\[CapitalSigma]1[i][a,c]),HF[MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&b+d==0&&!IntegerQ[d]]],
MakeRulesForExponents[{HF@\[CapitalSigma]1_[i_][OPS[a_,b_]],HF@\[CapitalSigma]1[i][a,b]},{HF@X_[a1___,i_[a2_],a3___],HF@X[a1,i[a2],a3]},HF[Sum[\[CapitalSigma]1[i][a,SignOf[b]dummy]X[a1,i[SignOf[a2]dummy],a3],{dummy,1,2}]],HF[MemberQ[{\[CapitalSigma],\[CapitalOmega],\[CapitalDelta]},\[CapitalSigma]1]&&b+a2==0&&!IntegerQ[b]&&IntegerQ[a]]],
MakeRulesForExponents[{HF@\[CapitalSigma][i_][OPS[a_,b_]],HF@\[CapitalSigma][i][a,b]},{HF@\[CapitalOmega][i_][OPS[c_,d_]],HF@\[CapitalOmega][i][c,d]},HF[SignOf[b]\[CapitalDelta][i][a,c]],HF[b+d==0&&!IntegerQ[b]]],

MakeRulesForExponents[{HF@\[CapitalSigma][i_][OPS[a_,b_]],HF@\[CapitalSigma][i][a,b]},{HF@\[CapitalDelta][i_][OPS[c_,d_]],HF@\[CapitalDelta][i][c,d]},HF[SignOf[b]\[CapitalOmega][i][a,c]],HF[b+d==0&&!IntegerQ[b]]],
MakeRulesForExponents[{HF@\[CapitalOmega][i_][OPS[a_,b_]],HF@\[CapitalOmega][i][a,b]},{HF@\[CapitalDelta][i_][OPS[c_,d_]],HF@\[CapitalDelta][i][c,d]},HF[-SignOf[b]\[CapitalSigma][i][a,c]],HF[b+d==0&&!IntegerQ[b]]],

MakeRulesForExponents[{HF@\[CapitalDelta][i_][OPS[a_,b_]],HF@\[CapitalDelta][i][a,b]},{HF@\[CapitalDelta][i_][OPS[c_,d_]],HF@\[CapitalDelta][i][c,d]},HF[-SignOf[d]Metlg[a,d]],HF[b+c==0&&!IntegerQ[c]&&IfP[b]&&IfN[c]]]
];

ContractLGBilinear[expr_]:=expr//.SU2LGMetricRules;
ContractSU2LGMetric=ContractLGBilinear;


(* ::Subsection::Closed:: *)
(*\[Eta] Metric Product Rules*)


LorMetricRules:={
\[Eta][\[Mu]1_,\[Nu]1_]\[Eta][\[Mu]2_,\[Nu]2_]/;\[Mu]1+\[Mu]2==0&&\[Nu]1+\[Nu]2==0:> 4,
\[Eta][\[Mu]1___,\[Nu]_,\[Mu]2___]\[Eta][\[Nu]1___,\[Sigma]_,\[Nu]2___]/;\[Nu]+\[Sigma]==0:> \[Eta][\[Mu]1,\[Mu]2,\[Nu]1,\[Nu]2],
\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]\[Eta][\[Rho]_,\[Sigma]_]/;\[Mu]+\[Rho]==0:> \[Sigma]mat[\[Sigma]][\[Alpha],\[Beta]],
\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]\[Eta][\[Sigma]_,\[Rho]_]/;\[Mu]+\[Rho]==0:> \[Sigma]mat[\[Sigma]][\[Alpha],\[Beta]]};

ContractLorMetric[expr_]:=expr//.LorMetricRules;


(* ::Section::Closed:: *)
(*\[Sigma]matRule*)


(* ::Input::Initialization:: *)
\[Sigma]matRule[expr_]:=expr//.{
\[Sigma]mat[\[Mu]_][\[Alpha]_,\[Beta]_]\[Sigma]mat[\[Nu]_][\[Gamma]_,\[Rho]_]/;\[Mu]+\[Nu]==0:>-MetricConvention 2Met[\[Alpha],\[Gamma]]Metd[\[Beta],\[Rho]], 
\[Sigma]mat[\[Mu]_][\[Beta]_,\[Alpha]_]\[Sigma]mat[\[Nu]_][\[Delta]_,\[Gamma]_]/;\[Beta]+\[Delta]==0&& \[Alpha]+\[Gamma]==0:>-(-CliffordConvention) 2 \[Eta][\[Mu],\[Nu]]
};


ContractPauliMatrix=\[Sigma]matRule;


(* ::Section::Closed:: *)
(*PutSL2CScalar*)


(*HF is necessary for the pattern matching in the MakeRulesForExponents. In other words, for i_ to work.*)
PutSU2RScalar[expr_]:=expr//.MakeRulesForExponents[{SHA[i_,A_],SHA[i,A]},{SHA[j_, -A_],SHA[j,-A]},SHAA[j,i],True];

PutSU2LScalar[expr_]:=expr//.MakeRulesForExponents[{SHB[i_,A_],SHB[i,A]},{SHB[j_, -A_],SHB[j,-A]},SHBB[i,j],True];


PutSL2CScalar[expr_] :=expr //PutSU2RScalar//PutSU2LScalar;


(* ::Section::Closed:: *)
(*PutLGScalarFor*)


(* ::Input::Initialization:: *)
CriteriaMasslessLGScalar[a_,b_,c_]:=HF[Not[MsQ[b1]]&&MatchQ[a1,a|a[_]]&&MatchQ[b1,b|b[___]]&&MatchQ[c1,c|c[_]]];

CriteriaMassiveLGScalar[a_,b_,c_]:=HF[MsQ[b1]&&J+K==0&&MatchQ[a1,a|a[_]]&&MatchQ[b1,b|b[___]]&&MatchQ[c1,c|c[_]]];


MasslessLGScalarForRules[a_,b_,c_]:=Join[
MakeRulesForExponents[{HF[HP[SHAA[a1_,b1_]]],HF@SHAA[a1,b1]},{HF[HP[SHBB[b1_,c1_]]],HF@SHBB[b1,c1]},
HF[-SHAB[a1,b1,c1]],CriteriaMasslessLGScalar[a,b,c]],
MakeRulesForExponents[{HF[HP[SHAA[a1_,b1_]]],HF@SHAA[a1,b1]},{HF[HP[SHBB[c1_,b1_]]],HF@SHBB[c1,b1]},
HF[SHAB[a1,b1,c1]],CriteriaMasslessLGScalar[a,b,c]],
MakeRulesForExponents[{HF[HP[SHAA[b1_,a1_]]],HF@SHAA[b1,a1]},{HF[HP[SHBB[b1_,c1_]]],HF@SHBB[b1,c1]},
HF[SHAB[a1,b1,c1]],CriteriaMasslessLGScalar[a,b,c]],
MakeRulesForExponents[{HF[HP[SHAA[b1_,a1_]]],HF@SHAA[b1,a1]},{HF[HP[SHBB[c1_,b1_]]],HF@SHBB[c1,b1]},
HF[-SHAB[a1,b1,c1]],CriteriaMasslessLGScalar[a,b,c]]];

MassiveLGScalarForRules[a_,b_,c_]:=
Join[
MakeRulesForExponents[{HF@HP@SHAA[a1_,b1_[J_]],HF@SHAA[a1,b1[J]]},{HF@HP@SHBB[b1_[K_],c1_],HF@SHBB[b1[K],c1]},
HF[-SignOf[K]SHAB[a1,b1,c1]],CriteriaMassiveLGScalar[a,b,c]],
MakeRulesForExponents[{HF@HP@SHAA[a1_,b1_[J_]],HF@SHAA[a1,b1[J]]},{HF@HP@SHBB[c1_,b1_[K_]],HF@SHBB[c1,b1[K]]},HF[+SignOf[K]SHAB[a1,b1,c1]],CriteriaMassiveLGScalar[a,b,c]],
MakeRulesForExponents[{HF@HP@SHAA[b1_[J_],a1_],HF@SHAA[b1[J],a1]},{HF@HP@SHBB[b1_[K_],c1_],HF@SHBB[b1[K],c1]},HF[+SignOf[K]SHAB[a1,b1,c1]],CriteriaMassiveLGScalar[a,b,c]],
MakeRulesForExponents[{HF@HP@SHAA[b1_[J_],a1_],HF@SHAA[b1[J],a1]},{HF@HP@SHBB[c1_,b1_[K_]],HF@SHBB[c1,b1[K]]},HF[-SignOf[K]SHAB[a1,b1,c1]],CriteriaMassiveLGScalar[a,b,c]]];


(* ::Input::Initialization:: *)
PutMasslessLGScalarFor[a_,b_,c_][expr_]:=expr//.MasslessLGScalarForRules[a,b,c];

PutMassiveLGScalarFor[a_,b_,c_][expr_]:=expr//.MassiveLGScalarForRules[a,b,c];

PutLGScalarFor[a_,b_,c_][expr_]:=expr//PutMassiveLGScalarFor[a,b,c]//PutMasslessLGScalarFor[a,b,c];


(* ::Section::Closed:: *)
(*PutLGScalar*)


MasslessLGScalarRules=MasslessLGScalarForRules[_,_,_];
MassiveLGScalarRules=MassiveLGScalarForRules[_,_,_];


(* ::Input::Initialization:: *)
PutMasslessLGScalar[expr_]:=expr//.MasslessLGScalarRules;
PutMassiveLGScalar[expr_]:=expr//.MassiveLGScalarRules;

PutLGScalar[expr_]:=PutMasslessLGScalar[PutMassiveLGScalar[expr]];


PutScalar[expr_]:=PutLGScalar[PutSL2CScalar[expr]];


(* ::Section::Closed:: *)
(*NoMasslessLGScalar (Earlier name SplitMassless)*)


NoMasslessLGScalarRules:={
SHAB[a_,i_,b_]/;Not[MsQ[i]] :> SHAA[i,a]SHBB[i,b]};

NoMasslessLGScalar[expr_] :=expr//.NoMasslessLGScalarRules;
SplitMassless=NoMasslessLGScalar;


(* ::Section::Closed:: *)
(*NoMassiveLGScalar (Earlier name SplitMassive)*)


(* ::Input::Initialization:: *)
NoMassiveLGScalarRules:={
	SHAB[i_,a_?MsQ,j_]^l_/;l>0 :> Product[-SHAA[a[-LGidx[{B,i, a, j,k$}]],i] SHBB[j,a[LGidx[{B,i, a, j,k$}]]],{k$,1,l}],
SHAB[i_,a_?MsQ,j_]^l_/;l<0  :> 1/Product[-SHAA[a[-LGidx[{B,i, a, j,k$}]],i] SHBB[j,a[LGidx[{B,i, a, j,k$}]]],{k$,1,Abs[l]}],SHAB[i_,a_?MsQ,j_]  :>-SHAA[a[-LGidx[{i, a, j}]],i] SHBB[j,a[LGidx[{i, a, j}]]]
};

Options[NoMassiveLGScalar] = {dummyLGIndices->lgindicesList};

NoMassiveLGScalar[expr_,OptionsPattern[]]:=Module[{listIndices,expr2,AllLGidxs,ReplaceIdxRules},
listIndices=OptionValue[dummyLGIndices];
expr2 = expr/.NoMassiveLGScalarRules//Refine;
AllLGidxs = Cases[expr2,  LGidx[x___], All]//DeleteDuplicates;
ReplaceIdxRules = Thread[AllLGidxs-> listIndices[[;;Length[AllLGidxs]]]];
expr2//.ReplaceIdxRules//Refine
];

SplitMassive=NoMassiveLGScalar;


(* ::Section::Closed:: *)
(*NoLGScalar*)


(* ::Input::Initialization:: *)
NoLGScalar[expr_]:=expr//NoMasslessLGScalar//NoMassiveLGScalar;


NoScalar[expr_]:=NoSL2CScalar@NoLGScalar@expr;


(* ::Section::Closed:: *)
(*NoMasslessLGScalarWB*)


NoMasslessLGScalarWBRules:=NoMasslessLGScalarRules;

NoMasslessLGScalarWB=NoMasslessLGScalar;

SplitMasslessWB=NoMasslessLGScalarWB;


(* ::Section::Closed:: *)
(*NoMassiveLGScalarWB*)


(* ::Input::Initialization:: *)
NoMassiveLGScalarWBRules:={
	SHAB[i_,a_?MsQ,j_]^l_/;l>0 :> Product[ SHAA[i,a[-LGidx[{A,i, a,k,1}]]]\[Epsilon]lg[LGidx[{A,i, a,k,1}],LGidx[{B, a, j,k,1}]] SHBB[j,a[-LGidx[{B,a, j,k,1}]]],{k,1,l}],
	SHAB[i_,a_?MsQ,j_]^l_/;l<0 :> 1/Product[ SHAA[i,a[-LGidx[{A,i, a,k,-1}]]]\[Epsilon]lg[LGidx[{A,i, a,k,-1}],LGidx[{B, a, j,k,-1}]] SHBB[j,a[-LGidx[{B,a, j,k,-1}]]],{k,1,Abs[l]}],
SHAB[i_,a_?MsQ,j_] :>SHAA[i,a[-LGidx[{A,i, a,0}]]]\[Epsilon]lg[LGidx[{A,i, a,0}],LGidx[{B, a, j,0}]] SHBB[j,a[-LGidx[{B,a, j,0}]]]
};

Options[NoMassiveLGScalarWB] = {dummyLGIndices->lgindicesList};

NoMassiveLGScalarWB[expr_,OptionsPattern[]]:=Module[{listIndices,expr2,AllLGidxs,ReplaceIdxRules},
listIndices=OptionValue[dummyLGIndices];
expr2 = expr/.NoMassiveLGScalarWBRules//Refine;
AllLGidxs = Cases[expr2,  LGidx[x___], All]//DeleteDuplicates;
ReplaceIdxRules = Thread[AllLGidxs-> listIndices[[;;Length[AllLGidxs]]]];
expr2//.ReplaceIdxRules//Refine
];

SplitMassiveWB=NoMassiveLGScalarWB;


(* ::Section::Closed:: *)
(*NoLGScalarWB*)


(* ::Input::Initialization:: *)
NoLGScalarWB[expr_]:=expr//NoMasslessLGScalarWB//NoMassiveLGScalarWB;


(* ::Section::Closed:: *)
(*NoSL2CScalar*)


(* ::Input::Initialization:: *)
NoSU2LScalarRules:= {
SHBB[i_,j_]^x_/;IfP[x]:>Product[ (SHB[i,Lidx[{B,i,j,k}]]SHB[j,-Lidx[{B,i,j,k}]]),{k,x}],SHBB[i_,j_]^x_/;IfN[x]:>Product[ 1/(SHB[i,Lidx[{B,i,j,k}]]SHB[j,-Lidx[{B,i,j,k}]]),{k,SignOf[x]x}],
SHBB[i_,j_]:> (SHB[i,Lidx[{B,i,j,0}]]SHB[j,-Lidx[{B,i,j,0}]])
   };

NoSU2RScalarRules:= {
SHAA[i_,j_]^x_/;IfP[x]:>Product[( SHA[i,-Ridx[{A,i,j,k}]]SHA[j,Ridx[{A,i,j,k}]]),{k,x}],SHAA[i_,j_]^x_/;IfN[x]:>Product[1/( SHA[i,-Ridx[{A,i,j,k}]]SHA[j,Ridx[{A,i,j,k}]]),{k,SignOf[x]x}],SHAA[i_,j_]:>( SHA[i,-Ridx[{A,i,j,0}]]SHA[j,Ridx[{A,i,j,0}]])
   };

Options[NoSU2LScalar]={dummySU2LIndices->leftindicesList};
Options[NoSU2RScalar]={dummySU2RIndices-> rightindicesList};

NoSU2LScalar[expr_,OptionsPattern[]]:=Module[{list\[Beta]Indices,foundindices,expr2,AllLGidxs,AllLidxs,ReplaceLIdxRules},

foundindices=Map[#[[2]]&,Cases[expr,SHB[a_,i_],All]]//.-x_:> x//.x_?Negative:> -x;
list\[Beta]Indices=Complement[OptionValue[dummySU2LIndices],foundindices];

expr2 = expr//.NoSU2LScalarRules//Refine;

AllLidxs = Cases[expr2,  Lidx[x___], All]//DeleteDuplicates;

ReplaceLIdxRules = Thread[AllLidxs-> list\[Beta]Indices[[;;Length[AllLidxs]]]];

expr2//.ReplaceLIdxRules
];

NoSU2RScalar[expr_,OptionsPattern[]]:=Module[{list\[Alpha]Indices,foundindices,expr2,AllLGidxs,AllRidxs,ReplaceRIdxRules},

foundindices=Map[#[[2]]&,Cases[expr,SHA[a_,i_],All]]//.-x_:> x//.x_?Negative:> -x;
list\[Alpha]Indices=Complement[OptionValue[dummySU2RIndices],foundindices];

expr2 = expr//.NoSU2RScalarRules//Refine;

AllRidxs = Cases[expr2,  Ridx[x___], All]//DeleteDuplicates;

ReplaceRIdxRules = Thread[AllRidxs-> list\[Alpha]Indices[[;;Length[AllRidxs]]]];

expr2//.ReplaceRIdxRules
];

NoSL2CScalar[expr_]:=expr//NoSU2LScalar//NoSU2RScalar;


(* ::Section::Closed:: *)
(*NoSL2CScalarWB*)


(* ::Input::Initialization:: *)
NoSU2LScalarWBRules:= {
SHBB[i_,j_]^x_/;IfP[x]:>Product[ (SHB[i,Lidx[{B,i,j,k,1}]]SHB[j,Lidx[{B,i,j,k,2}]]\[Epsilon][-Lidx[{B,i,j,k,1}],-Lidx[{B,i,j,k,2}]]),{k,x}],SHBB[i_,j_]^x_/;IfN[x]:>Product[ 1/(SHB[i,Lidx[{B,i,j,k,1}]]SHB[j,Lidx[{B,i,j,k,2}]]\[Epsilon][-Lidx[{B,i,j,k,1}],-Lidx[{B,i,j,k,2}]]),{k,SignOf[x]x}],
SHBB[i_,j_]:> (SHB[i,Lidx[{B,i,j,0,1}]]SHB[j,Lidx[{B,i,j,0,2}]]\[Epsilon][-Lidx[{B,i,j,0,1}],-Lidx[{B,i,j,0,2}]])
   };

NoSU2RScalarWBRules:= {
SHAA[i_,j_]^x_/;IfP[x]:>Product[( SHA[i,Ridx[{A,i,j,k,2}]]SHA[j,Ridx[{A,i,j,k,1}]]\[Epsilon]d[-Ridx[{A,i,j,k,1}],-Ridx[{A,i,j,k,2}]]),{k,x}],SHAA[i_,j_]^x_/;IfN[x]:>Product[1/( SHA[i,Ridx[{A,i,j,k,2}]]SHA[j,Ridx[{A,i,j,k,1}]]\[Epsilon]d[-Ridx[{A,i,j,k,1}],-Ridx[{A,i,j,k,2}]]),{k,SignOf[x]x}],SHAA[i_,j_]:>( SHA[i,Ridx[{A,i,j,0,2}]]SHA[j,Ridx[{A,i,j,0,1}]]\[Epsilon]d[-Ridx[{A,i,j,0,1}],-Ridx[{A,i,j,0,2}]])
   };

Options[NoSU2LScalarWB]={dummySU2LIndices->leftindicesList};
Options[NoSU2RScalarWB]={dummySU2RIndices-> rightindicesList};

NoSU2LScalarWB[expr_,OptionsPattern[]]:=Module[{list\[Beta]Indices,expr2,AllLGidxs,AllLidxs,ReplaceLIdxRules},
list\[Beta]Indices=OptionValue[dummySU2LIndices];

expr2 = expr//.NoSU2LScalarWBRules//Refine;

AllLidxs = Cases[expr2,  Lidx[x___], All]//DeleteDuplicates;

ReplaceLIdxRules = Thread[AllLidxs-> list\[Beta]Indices[[;;Length[AllLidxs]]]];

expr2//.ReplaceLIdxRules
];

NoSU2RScalarWB[expr_,OptionsPattern[]]:=Module[{list\[Alpha]Indices,expr2,AllLGidxs,AllRidxs,ReplaceRIdxRules},
list\[Alpha]Indices=OptionValue[dummySU2RIndices];

expr2 = expr//.NoSU2RScalarWBRules//Refine;

AllRidxs = Cases[expr2,  Ridx[x___], All]//DeleteDuplicates;

ReplaceRIdxRules = Thread[AllRidxs-> list\[Alpha]Indices[[;;Length[AllRidxs]]]];

expr2//.ReplaceRIdxRules
];

NoSL2CScalarWB[expr_]:=expr//NoSU2LScalarWB//NoSU2RScalarWB;


(* ::Section::Closed:: *)
(*Schouten*)


(* ::Subsection:: *)
(*SplitSchouten A and B*)


SplitSchouten[{X_, Y_}, {Z_, W_}][expr_]:=expr//SplitSchoutenA[{X, Y}, {Z, W}]//SplitSchoutenB[{X, Y}, {Z, W}]


(* ::Input::Initialization:: *)
SplitSchoutenA[{X_, Y_}, {Z_, W_}][expr_]:=expr/.Join[
MakeRulesForExponents[{HF@HP@M_[X1_,Y1_],HF@M[X1,Y1]},{HF@HP@N_[Z1_,W1_],HF@N[Z1,W1]},HF[Metd[X1,W1]Metd[Y1,Z1]-Metd[X1,Z1]Metd[Y1,W1]],HF[(SignOf[X1]X1===X)&&(SignOf[Y1]Y1===Y)&&(SignOf[Z1]Z1===Z)&&(SignOf[W1]W1===W)&&MemberQ[{\[Delta]d,\[Epsilon]d},M]&&MemberQ[{\[Delta]d,\[Epsilon]d},N]]],
MakeRulesForExponents[{HF@HP@M_[X1_,Y1_],HF@M[X1,Y1]},{HF@HP@N_[Z1_,W1_],HF@N[Z1,W1]},HF[Metlg[X1,W1]Metlg[Y1,Z1]-Metlg[X1,Z1]Metlg[Y1,W1]],HF[(SignOf[X1]X1===X)&&(SignOf[Y1]Y1===Y)&&(SignOf[Z1]Z1===Z)&&(SignOf[W1]W1===W)&&MemberQ[{\[Delta]lg,\[Epsilon]lg},M]&&MemberQ[{\[Delta]lg,\[Epsilon]lg},N]]],
MakeRulesForExponents[{HF@HP@SHA[X1_,Y1_],HF@SHA[X1,Y1]},{HF@HP@SHA[Z1_,W1_],HF@SHA[Z1,W1]},HF[SHAA[X1,Z1]Metd[Y1,W1]+SHA[X1,W1]SHA[Z1,Y1]],HF[BaseHead[X1]===X&&BaseHead[Y1]===Y&&BaseHead[Z1]===Z&&BaseHead[W1]===W]],
MakeRulesForExponents[{HF@HP@SHAA[X1_,Y1_],HF@SHAA[X1,Y1]},{HF@HP@SHAA[Z1_,W1_],HF@SHAA[Z1,W1]},HF[SHAA[X1,W1]SHAA[Z1,Y1]+SHAA[X1,Z1]SHAA[Y1,W1]],HF[BaseHead[X1]===X&&BaseHead[Y1]===Y&&BaseHead[Z1]===Z&&BaseHead[W1]===W]]
];

SplitSchoutenB[{X_, Y_}, {Z_, W_}][expr_]:=expr/.Join[
MakeRulesForExponents[{HF@HP@M_[X1_,Y1_],HF@M[X1,Y1]},{HF@HP@N_[Z1_,W1_],HF@N[Z1,W1]},HF[Met[X1,W1]Met[Y1,Z1]-Met[X1,Z1]Met[Y1,W1]],HF[(SignOf[X1]X1===X)&&(SignOf[Y1]Y1===Y)&&(SignOf[Z1]Z1===Z)&&(SignOf[W1]W1===W)&&MemberQ[{\[Delta],\[Epsilon]},M]&&MemberQ[{\[Delta],\[Epsilon]},N]]],
MakeRulesForExponents[{HF@HP@M_[X1_,Y1_],HF@M[X1,Y1]},{HF@HP@N_[Z1_,W1_],HF@N[Z1,W1]},HF[Metlg[X1,W1]Metlg[Y1,Z1]-Metlg[X1,Z1]Metlg[Y1,W1]],HF[(SignOf[X1]X1===X)&&(SignOf[Y1]Y1===Y)&&(SignOf[Z1]Z1===Z)&&(SignOf[W1]W1===W)&&MemberQ[{\[Delta]lg,\[Epsilon]lg},M]&&MemberQ[{\[Delta]lg,\[Epsilon]lg},N]]],
MakeRulesForExponents[{HF@HP@SHB[X1_,Y1_],HF@SHB[X1,Y1]},{HF@HP@SHB[Z1_,W1_],HF@SHB[Z1,W1]},HF[SHBB[X1,Z1]Met[W1,Y1]+SHB[X1,W1]SHB[Z1,Y1]],HF[BaseHead[X1]===X&&BaseHead[Y1]===Y&&BaseHead[Z1]===Z&&BaseHead[W1]===W]],
MakeRulesForExponents[{HF@HP@SHBB[X1_,Y1_],HF@SHBB[X1,Y1]},{HF@HP@SHBB[Z1_,W1_],HF@SHBB[Z1,W1]},HF[SHBB[X1,W1]SHBB[Z1,Y1]+SHBB[X1,Z1]SHBB[Y1,W1]],HF[BaseHead[X1]===X&&BaseHead[Y1]===Y&&BaseHead[Z1]===Z&&BaseHead[W1]===W]]
];


(* ::Subsection:: *)
(*Recursion Schouten*)


MakeSchoutenPairs[{x_}]:={};
MakeSchoutenPairs[pairlist_]:={Splice[Table[If[Intersection[Sequence@@(List@@@#)]==={},#,Nothing]&@{First@pairlist,i},{i,Rest@pairlist}]],Splice[MakeSchoutenPairs[Rest@pairlist]]};


MakeSchoutenRule[f_[a_,b_],f_[c_,d_]]:=(f[a,b]f[c,d]->-PutCanonicalOrder[f[a,c]]PutCanonicalOrder[f[d,b]]-PutCanonicalOrder[f[a,d]]PutCanonicalOrder[f[b,c]]);


GenerateSchoutenRules[exp_]:=Module[{SHAAs,SHBBs,SHAArules,SHBBrules},

SHAAs=Cases[{exp},Times[x__?(Head[#]===SHAA&),y___]:>List[x],\[Infinity]];
SHBBs=Cases[{exp},Times[x__?(Head[#]===SHBB&),y___]:>List[x],\[Infinity]];

SHAArules=MakeSchoutenRule@@@(Union[Join@@(MakeSchoutenPairs/@SHAAs)]);
SHBBrules=MakeSchoutenRule@@@(Union[Join@@(MakeSchoutenPairs/@SHBBs)]);

Return[Join[SHAArules,SHBBrules]]
]


(* ::Input::Initialization:: *)
ConvertToSingleRules[rules_]:=Function[e,e/.#]&/@rules;

ApplySchouten[exp_]:=Module[{testrules=GenerateSchoutenRules[exp]},Simplify[exp,TransformationFunctions->ConvertToSingleRules[testrules]]];

SimplifySchouten[exp_,opts:OptionsPattern[FullSimplify]]:=FullSimplify[PutCanonicalOrder[exp],opts,TransformationFunctions->{Automatic,ApplySchouten}];


(* ::Section:: *)
(*Onshell*)


(* ::Input::Initialization:: *)
OnShellRules:={
SHB[i_?MsQ[-L_],\[Alpha]_]SHB[i_?MsQ[L_],\[Beta]_] :> -SignOf[\[Beta]] m[BaseHead@i] Met[\[Alpha],\[Beta]],
SHA[i_?MsQ[-L_],\[Alpha]_]SHA[i_?MsQ[L_],\[Beta]_] :> -SignOf[\[Beta]]m[BaseHead@i] Metd[\[Alpha],\[Beta]],
X_[a_?MsQ[L_],part2_]X_[a_?MsQ[-L_],part3_]/;MemberQ[{SHAA, SHBB},X] :> (-1)^Boole[X===SHBB] m[BaseHead@a]X[part2,part3],
X_[part2_,a_?MsQ[L_]]X_[part3_,a_?MsQ[-L_]]/;MemberQ[{SHAA, SHBB},X] :> (-1)^Boole[X===SHBB] m[BaseHead@a]X[part2,part3],
X_[a_?MsQ[L_],part2_]X_[part3_,a_?MsQ[-L_]]/;MemberQ[{SHAA, SHBB},X] :> -(-1)^Boole[X===SHBB] m[BaseHead@a]X[part2,part3],
X_[part2_,a_?MsQ[L_]]X_[a_?MsQ[-L_],part3_]/;MemberQ[{SHAA, SHBB},X] :>- (-1)^Boole[X===SHBB] m[BaseHead@a]X[part2,part3],
X_[i_?MsQ[L_],i_?MsQ[J_]]/;MemberQ[{SHAA, SHBB},X] :> (-1)^Boole[X===SHBB] (-1)^HeavisideTheta[SignOf[J]]  m[BaseHead@i]Metlg[L,J],
SHAB[c_?MsQ[L_],c_?MsQ,a_]:> m[BaseHead@c]SHBB[a,c[L]],
SHAB[a_,c_?MsQ,c_?MsQ[L_]]:> m[BaseHead@c]SHAA[a,c[L]]
};

PutOnShell[expr_]:=expr//.OnShellRules//PutCanonicalOrder;


(* ::Section::Closed:: *)
(*SimplifyPolynomial*)


SimplifyPolynomialFunction[expr_]:= expr//PutSL2CScalar//PutOnShell//ContractMetric//PutLGScalar//PutOnShell;

SimplifyPolynomial[expr_]:=expr//RepeatedRule[SimplifyPolynomialFunction];


(* ::Section:: *)
(*Ignore*)


Print["Loaded: PolynomialRules"];
