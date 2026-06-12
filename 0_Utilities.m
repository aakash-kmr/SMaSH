(* ::Package:: *)

(* ::Chapter:: *)
(*Variables*)


(* ::Section::Closed:: *)
(*IfP, IfN, SignOf, MinusSign*)


(* ::Input::Initialization:: *)
(*SignOf[x_]:=With[{first=FactorTermsList[x][[1]]},first/Abs[first]];
IfP[x_]:=SignOf[x]===+1;
IfN[x_]:=!IfP[x];
MinusSign[J1_,J2_]:=If[IfP[J1]&&IfN[J2],1,-1];*)


(* ::Input::Initialization:: *)
IfP[A_]:=If[A[[0]]===Integer, A>=0, Not[(A+A)[[1]]+2===0]];
IfN[A_]:= !IfP[A];
SignOf[A_]:=(-1)^(Boole[IfP[A]]+1);
SignOf[p_Complex]:=SignOf[p/I];
SignOf[p_Times]:=Times@@Map[SignOf,List@@p];
MinusSign[J1_,J2_]:=If[IfP[J1]&&IfN[J2],1,-1]


(* ::Input::Initialization:: *)
ToList[expr_]:=If[Head[expr]===Plus,List@@expr,{expr}]


DefineIndex[]:= {OPS,SignOf,MinusSign,IfP,IfN,counter,GI,OrderFucnt}


(* ::Section::Closed:: *)
(*If Atom*)


RefineAtomQ[expr_]:= AtomQ[expr]//Refine;
RAQ=RefineAtomQ;


(* ::Section::Closed:: *)
(*Base Head*)


BaseHead[expr_]:=expr/.TL:> Identity//.f_[h___]:> f;
BaseHead[expr_?AtomQ]:=expr;


(* ::Input::Initialization:: *)
BaseHead[-x_]:=BaseHead[x];
BaseHead[x_?Negative]:=BaseHead[-x];


(* ::Section::Closed:: *)
(*MsQ, MlQ, MjMlQ, MjMsQ, RlQ*)


(* ::Input::Initialization:: *)
MassiveQ[i_]:=MemberQ[AllMassiveLegs[],BaseHead@i];
MsQ=MassiveQ;
MasslessQ[i_]:=MemberQ[AllMasslessLegs[],BaseHead@i];
MlQ=MasslessQ;


RealLegQ[i_]:=MemberQ[AllRealLegs[],BaseHead@i];
RlQ=RealLegQ;


(* ::Section::Closed:: *)
(*If SHAA, SHBB,SHAB,SHBA*)


SL2CSQ[expr_]:= MatchQ[expr, (SHAA|SHBB)];
LGQ[expr_]:= MatchQ[expr, (SHAB|SHBA)];


(* ::Section::Closed:: *)
(*Counter*)


(* ::Input::Initialization:: *)
counter=1;
GI[x_:1]:=Module[{}, counter=counter+x];


(* ::Input::Initialization:: *)
SetCounterZero[]:=Module[{},
$PrePrint=(counter=0;#)&;
];
UnSetCounterZero[]:=Module[{},
$PrePrint=.;
];
SetCounterZero[];


(* ::Section:: *)
(*Make Index*)


(* ::Input::Initialization:: *)
OPS[A_,B_]:=OrderlessPatternSequence[A,B];
MIL[list_List]:=ToExpression[StringJoin@Map[ToString,list]];
MIL[pref_,n__]:=Table[If[IfN[pref],-MI[-pref,i],MI[pref,i]],{i,n}]
MIL2[list_List]:=StringJoin@Map[ToString,list];


(* ::Input::Initialization:: *)
LIndex[Head_,range_]:=Map[MIL[{Head,#}]&,Range[1,range]]


(* ::Chapter::Closed:: *)
(*Make Rule*)


(* ::Section::Closed:: *)
(*Make Rule for Exponents*)


HF=HoldForm;
HP=HoldPattern;
RHF=ReleaseHold;


(* ::Input::Initialization:: *)
MakeRulesForExponentsBase[{LHS1_,RHS1_},{LHS2_,RHS2_},RHS_,Conditions_:True]:={
(RHF @LHS1) (RHF @LHS2)/;(RHF@Conditions):> RHF@RHS,
(RHF @LHS1) (RHF @LHS2)^cc2_/;FactorTermsList[cc2][[1]]>0&&(RHF@Conditions):> ( RHF@RHS) (RHF@RHS2)^(cc2-1),
(RHF @LHS1)^cc1_ (RHF @LHS2)/;FactorTermsList[cc1][[1]]>0&&(RHF@Conditions):> ( RHF@RHS) (RHF@RHS1)^(cc1-1),(RHF @LHS1)^-1 (RHF @LHS2)^cc2_/;FactorTermsList[cc2][[1]]<0&&NumberQ[-1-cc2]&&-1-cc2>=0&&(RHF@Conditions):> ( RHF@RHS)^-1 (RHF@RHS2)^(cc2+1),(RHF @LHS1)^cc1_ (RHF @LHS2)^-1/;FactorTermsList[cc1][[1]]<0&&NumberQ[cc1+1]&&cc1+1<=0&&(RHF@Conditions):> ( RHF@RHS)^-1 (RHF@RHS1)^(cc1+1),(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;FactorTermsList[cc1][[1]]>0&&NumberQ[cc1-cc2]&&cc1-cc2>=0&&(RHF@Conditions):> ( RHF@RHS)^cc2 (RHF@RHS1)^(cc1-cc2),(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;FactorTermsList[cc1][[1]]>0&&NumberQ[cc1-cc2]&&cc1-cc2<=0&&(RHF@Conditions):> ( RHF@RHS)^cc1 (RHF@RHS2)^(cc2-cc1),(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;FactorTermsList[cc1][[1]]<0&&NumberQ[cc1-cc2]&&cc1-cc2>=0&&(RHF@Conditions):> ( RHF@RHS)^cc1 (RHF@RHS2)^(cc2-cc1),(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;FactorTermsList[cc1][[1]]<0&&NumberQ[cc1-cc2]&&cc1-cc2<=0&&(RHF@Conditions):> ( RHF@RHS)^cc2 (RHF@RHS1)^(cc1-cc2),
(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;LeafCount[cc1]-LeafCount[cc2]>=0&&!NumberQ[cc1-cc2]&&(RHF@Conditions):> ( RHF@RHS)^cc2 (RHF@RHS1)^(cc1-cc2),(RHF @LHS1)^cc1_ (RHF @LHS2)^cc2_/;LeafCount[cc1]-LeafCount[cc2]<0&&!NumberQ[cc2-cc1]&&(RHF@Conditions):> ( RHF@RHS)^cc1 (RHF@RHS2)^(cc2-cc1)
};

MakeRulesForExponentsConjugate[{LHS1_,RHS1_},{LHS2_,RHS2_},RHS_,Conditions_:True]:=MakeRulesForExponentsBase[{Conjugate@LHS1,Conjugate@RHS1},{Conjugate@LHS2,Conjugate@RHS2},Conjugate@RHS,Conditions];

MakeRulesForExponents[{LHS1_,RHS1_},{LHS2_,RHS2_},RHS_,Conditions_:True]:=Join[MakeRulesForExponentsBase[{LHS1,RHS1},{LHS2,RHS2},RHS,Conditions](*,MakeRulesForExponentsConjugate[{LHS1,RHS1},{LHS2,RHS2},RHS,Conditions]*)];


(* ::Section::Closed:: *)
(*RepeatedRule*)


ApplyRule[rule_][expr_]:=ReplaceAll[expr,rule]


(* ::Input::Initialization:: *)
RepeatedRule[rule_][expr_]:=FixedPoint[rule[Expand[#]]&,expr];
RepeatedRule[rule_List][expr_]:=FixedPoint[Composition[Sequence@@Join[rule,{Expand}]][#]&,expr];


(* ::Chapter::Closed:: *)
(*Kinematics*)


(* ::Section::Closed:: *)
(*Declare Massive and Massless*)


(* ::Subsection::Closed:: *)
(*Default Associations*)


MassiveData=<||>;
AllMassiveLegs[]=Keys[MassiveData];
AllMassiveMomenta[]=Values[MassiveData][[;;,1]];
AllMassivePolarizations[]=Values[MassiveData][[;;,2]];


MasslessData=<||>;
AllMasslessLegs[]=Keys[MasslessData];
AllMasslessMomenta[]=Values[MasslessData][[;;,1]];
AllMasslessPolarizations[]=Values[MasslessData][[;;,2]];
AllMasslessFieldStrengths[]=Values[MasslessData][[;;,3]];
AllMasslessHelicities[]=Values[MasslessData][[;;,4]];
AllMasslessReferenceSpinors[]=Values[MasslessData][[;;,5]];


AllMomenta[]=Join[AllMassiveMomenta[],AllMasslessMomenta[]];
AllLegs[]=Join[AllMassiveLegs[],AllMasslessLegs[]];


(* ::Input::Initialization:: *)
AllRealLegs[]={};
AllRealMasslessLegs[]=Select[AllRealLegs[],MlQ];
AllRealMassiveLegs[]=Select[AllRealLegs[],MsQ];


MassivePolarization[leg_]:=Lookup[MassivePolarizationsThread,leg]
MassiveMomenta[leg_]:=Lookup[MassiveMomentaThread,leg]


(* ::Input::Initialization:: *)
Helicity[leg_]:=Lookup[HelicityThread,leg]
MasslessPolarization[leg_]:=Lookup[MasslessPolarizationsThread,leg]
MasslessMomenta[leg_]:=Lookup[MasslessMomentaThread,leg]
ReferenceSpinor[leg_]:=Lookup[ReferenceSpinorThread,leg]
MasslessFieldStrength[leg_]:=Lookup[MasslessFieldStrengthsThread,leg]


(* ::Input::Initialization:: *)
Leg[mom_]:=Lookup[Reverse/@Normal[Join[MasslessMomentaThread,MassiveMomentaThread]],mom]
Momenta[leg_]:=Lookup[Join[MasslessMomentaThread,MassiveMomentaThread],leg]


(* ::Subsection::Closed:: *)
(*Edit Data*)


(* ::Input::Initialization:: *)
ClearAll[EditMassiveData];
SetAttributes[EditMassiveData,HoldAll];
EditMassiveData[targetVar_:MassiveData,assump_:MassiveAssumptions]:=DynamicModule[{tempList,sync,syncassump,syncallassump,throwerror},
tempList=If[AssociationQ[targetVar],Normal[targetVar]/. (k_->v_):>{k,v},{{Null,{Null,Null}}}];
sync[]:=(targetVar=Association[Rule@@@tempList]);
syncassump[]:=(assump=If[tempList[[;;,1]]=={},{},Flatten[DeleteDuplicates[Map[({m[#]!=0,m[#]\[Element]Reals})&,tempList[[;;,1]]]]]]);
syncallassump[]:=($Assumptions=(And@@DeleteDuplicates@Join[MasslessAssumptions,assump]);
$Assumptions;AllMassiveLegs[]=Keys[MassiveData];
AllMassiveMomenta[]=Values[MassiveData][[;;,1]];
AllMassivePolarizations[]=Values[MassiveData][[;;,2]];
AllMomenta[]=Join[AllMassiveMomenta[],AllMasslessMomenta[]];
AllLegs[]=Join[AllMassiveLegs[],AllMasslessLegs[]];MassivePolarizationsThread=AssociationThread[AllMassiveLegs[]->AllMassivePolarizations[]];
MassiveMomentaThread=AssociationThread[AllMassiveLegs[]->AllMassiveMomenta[]];
);
throwerror[]:=If[Intersection[AllMasslessLegs[],tempList[[;;,1]]]=={},sync[];syncassump[];syncallassump[];,Error::MasslessMom=StringJoin["Found Massless Legs : ",ToString[Intersection[AllMasslessLegs[],tempList[[;;,1]]]]];Message[Error::MasslessMom]];
throwerror[];
Column[{Dynamic[
Grid[Join[{{Style["Massive",Bold],SpanFromLeft},{"Legs","Momenta","Polarization","Delete"}},
MapIndexed[Function[{row,idx},{
InputField[Dynamic[tempList[[idx[[1]]]][[1]],(tempList[[idx[[1]]]][[1]]=#;throwerror[];)& ],ImageSize->50,Background->Dynamic[If[MemberQ[AllMasslessLegs[],tempList[[idx[[1]]]][[1]]],Red,White]]],
InputField[Dynamic[tempList[[idx[[1]]]][[2,1]],(tempList[[idx[[1]]]][[2,1]]=#;throwerror[];)& ],ImageSize->100],
InputField[Dynamic[tempList[[idx[[1]]]][[2,2]],(tempList[[idx[[1]]]][[2,2]]=#;throwerror[];)&],ImageSize->100],
Button["\!\(\*
StyleBox[\"\[Times]\",\nStripOnInput->False,\nLineColor->RGBColor[1, 0, 0],\nFrontFaceColor->RGBColor[1, 0, 0],\nBackFaceColor->RGBColor[1, 0, 0],\nGraphicsColor->RGBColor[1, 0, 0],\nFontSize->20,\nFontColor->RGBColor[1, 0, 0]]\)",assump=DeleteElements[assump,{m[tempList[[idx[[1]]]][[1]]]!=0}];tempList=Delete[tempList,idx[[1]]];
throwerror[];,ImageSize->50,Appearance->{"Frameless","Palette"},BaseStyle->{Red,Bold}]}],tempList]],Spacings->{1,0.5},Dividers->{False,{False,True}}]],
Button["+ Add Row",AppendTo[tempList,{Null,{Null ,Null}}];throwerror[];,ImageSize->100,Appearance->"Palette"]},Spacings->1,Frame->True,FrameMargins->10,Background->GrayLevel[0.98]]];


(* ::Input::Initialization:: *)
ClearAll[EditMasslessData];
SetAttributes[EditMasslessData,HoldAll];
EditMasslessData[targetVar_:MasslessData,assump_:MasslessAssumptions]:=DynamicModule[{colmn,tempList,sync,syncassump,syncallassump,throwerror},
tempList=If[AssociationQ[targetVar],Normal[targetVar]/. (k_->v_):>{k,v},{{Null,{Null,Null,Null,Null,Null}}}];
sync[]:=(targetVar=Association[Rule@@@tempList]);
syncassump[]:=(assump=If[tempList[[;;,1]]=={},{},Flatten[DeleteDuplicates[Map[({m[#]==0})&,tempList[[;;,1]]]]]]);
syncallassump[]:=($Assumptions=(And@@DeleteDuplicates@Join[MassiveAssumptions,assump]);
$Assumptions;
AllMasslessLegs[]=Keys[MasslessData];
AllMasslessMomenta[]=Values[MasslessData][[;;,1]];
AllMasslessPolarizations[]=Values[MasslessData][[;;,2]];
AllMasslessFieldStrengths[]=Values[MasslessData][[;;,3]];
AllMasslessHelicities[]=Values[MasslessData][[;;,4]];
AllMasslessReferenceSpinors[]=Values[MasslessData][[;;,5]];
AllMomenta[]=Join[AllMassiveMomenta[],AllMasslessMomenta[]];
AllLegs[]=Join[AllMassiveLegs[],AllMasslessLegs[]];
HelicityThread=AssociationThread[AllMasslessLegs[]->AllMasslessHelicities[]];
MasslessPolarizationsThread=AssociationThread[AllMasslessLegs[]->AllMasslessPolarizations[]];
ReferenceSpinorThread=AssociationThread[AllMasslessLegs[]->AllMasslessReferenceSpinors[]];
MasslessMomentaThread=AssociationThread[AllMasslessLegs[]->AllMasslessMomenta[]];
MasslessFieldStrengthsThread=AssociationThread[AllMasslessLegs[]->AllMasslessFieldStrengths[]];
);
throwerror[]:=If[Intersection[AllMassiveLegs[],tempList[[;;,1]]]=={},sync[];syncassump[];syncallassump[];,Error::MassiveMom=StringJoin["Found Massive Legs : ",ToString[Intersection[AllMassiveLegs[],tempList[[;;,1]]]]];Message[Error::MassiveMom]];
throwerror[];
colmn=Column[{Dynamic[
Grid[Join[{{Style["Massless",Bold],SpanFromLeft},{"Legs","Momenta","Polarization","Field Strength","Helicity","Ref. Spinors","Delete"}},
MapIndexed[Function[{row,idx},{
InputField[Dynamic[tempList[[idx[[1]]]][[1]],(tempList[[idx[[1]]]][[1]]=#;throwerror[];)& ],ImageSize->50,Background->Dynamic[If[MemberQ[AllMassiveLegs[],tempList[[idx[[1]]]][[1]]],Red,White]]],
InputField[Dynamic[tempList[[idx[[1]]]][[2,1]],(tempList[[idx[[1]]]][[2,1]]=#;throwerror[])& ],ImageSize->100],
InputField[Dynamic[tempList[[idx[[1]]]][[2,2]],(tempList[[idx[[1]]]][[2,2]]=#;throwerror[])&],ImageSize->100],
InputField[Dynamic[tempList[[idx[[1]]]][[2,3]],(tempList[[idx[[1]]]][[2,3]]=#;throwerror[])&],ImageSize->100],
InputField[Dynamic[tempList[[idx[[1]]]][[2,4]],(tempList[[idx[[1]]]][[2,4]]=#;throwerror[])&],ImageSize->100],
InputField[Dynamic[tempList[[idx[[1]]]][[2,5]],(tempList[[idx[[1]]]][[2,5]]=#;throwerror[])&],ImageSize->100],
Button["\!\(\*
StyleBox[\"\[Times]\",\nStripOnInput->False,\nLineColor->RGBColor[1, 0, 0],\nFrontFaceColor->RGBColor[1, 0, 0],\nBackFaceColor->RGBColor[1, 0, 0],\nGraphicsColor->RGBColor[1, 0, 0],\nFontSize->20,\nFontColor->RGBColor[1, 0, 0]]\)",assump=DeleteElements[assump,{m[tempList[[idx[[1]]]][[1]]]==0}];tempList=Delete[tempList,idx[[1]]];
throwerror[];,ImageSize->50,Appearance->{"Frameless","Palette"},BaseStyle->{Red,Bold}]}],tempList]],Spacings->{1,0.5},Dividers->{False,{False,True}}]],
Button["+ Add Row",AppendTo[tempList,{Null,{Null ,Null,Null,Null,Null}}];throwerror[];,ImageSize->100,Appearance->"Palette"]},Spacings->1,Frame->True,FrameMargins->10,Background->GrayLevel[1]];
colmn
];


(* ::Subsection::Closed:: *)
(*Add and Remove Data*)


(* ::Input::Initialization:: *)
AddMassiveData[data_]/;AssociationQ[data]:=Module[{values,keys,newvalues,newdata,newtildedata},
	values=Values[data];
keys=Keys[data];
	newvalues=Map[Join[#,Table[Null,2-Length[#]]]&,values];
	newdata=Association[Thread[keys->newvalues]];
	newtildedata=Association[Thread[Map[TildeLeg,keys]->newvalues]];
	MassiveData=Join[MassiveData,newdata,newtildedata];
	EditMassiveData[]; 
];
AddMasslessData[data_]/;AssociationQ[data]:=Module[{values,keys,newvalues,newdata,newtildedata},
	values=Values[data];
keys=Keys[data];
	newvalues=Map[Join[#,Table[Null,5-Length[#]]]&,values];
	newdata=Association[Thread[Keys[data]->newvalues]];
	newtildedata=Association[Thread[Map[TildeLeg,Keys[data]]->newvalues]];
	MasslessData=Join[MasslessData,newdata,newtildedata];
	EditMasslessData[];
]


(* ::Input::Initialization:: *)
RemoveMassiveData[Legs_]:=Module[{tildeLegs,values,removabledata,removabletildedata},
tildeLegs=Map[TildeLeg,Legs];
values=Lookup[MassiveData,Legs];
removabledata=AssociationThread[Legs->values];
removabletildedata=AssociationThread[tildeLegs->values];
MassiveData=DeleteElements[MassiveData,Join[removabledata,removabletildedata]];
EditMassiveData[];
];
RemoveMasslessData[Legs_]:=Module[{tildeLegs,values,removabledata,removabletildedata},
tildeLegs=Map[TildeLeg,Legs];
values=Lookup[MasslessData,Legs];
removabledata=AssociationThread[Legs->values];
removabletildedata=AssociationThread[tildeLegs->values];
MasslessData=DeleteElements[MasslessData,Join[removabledata,removabletildedata]];
EditMasslessData[];
];


(* ::Subsection::Closed:: *)
(*Declare and Undeclare Legs*)


(* ::Input::Initialization:: *)
DeclareMassiveLegs[Legs_List]:=Module[{values,data},
	values=Table[{MIL[{k,iterations$}],MIL[{\[Zeta],iterations$}]},{iterations$,Legs}];
	data=Association[Thread[Legs->values]];
	AddMassiveData[data]; $Assumptions;
];

DeclareMasslessLegs[Legs_List]:=Module[{values,data},
	values=Table[{MIL[{k,iterations$}],MIL[{\[CurlyEpsilon],iterations$}],MIL[{B,iterations$}],1,MIL[{r,iterations$}]},{iterations$,Legs}];
	data=Association[Thread[Legs->values]];
AddMasslessData[data];$Assumptions;
];
DeclareLegs[MassiveLegs_List:{}][MasslessLegs_List:{}]:=(DeclareMassiveLegs[MassiveLegs];DeclareMasslessLegs[MasslessLegs];)


(* ::Input::Initialization:: *)
UndeclareMassiveLegs=RemoveMassiveData;
UndeclareMasslessLegs=RemoveMasslessData;

UndeclareLegs[MassiveLegs_List:{}][MasslessLegs_List:{}]:=(UndeclareMassiveLegs[MassiveLegs];UndeclareMasslessLegs[MasslessLegs];)


(* ::Section::Closed:: *)
(*Add and Remove Assumptions*)


(* ::Subsection::Closed:: *)
(*Clear*)


ClearAllData[]:=Module[{},
MassiveData=<||>; 
MasslessData=<||>;
MassiveData=<||>;
AllMassiveLegs[]={};
AllMassiveMomenta[]={};
AllMassivePolarizations[]={};
MasslessData=<||>;
AllMasslessLegs[]={};
AllMasslessMomenta[]={};
AllMasslessPolarizations[]={};
AllMasslessFieldStrengths[]={};
AllMasslessHelicities[]={};
AllMasslessReferenceSpinors[]={};
AllMomenta[]={};
AllLegs[]={};
AllRealLegs[]={};
AllRealMasslessLegs[]:={};
AllRealMassiveLegs[]:={};
]


ClearAllThreads[]:=Module[{},
HelicityThread={};
ReferenceSpinorThread={};
MasslessFieldStrengthsThread={};
MasslessPolarizationsThread={};
MasslessMomentaThread={};
MassiveMomentaThread={};
MassivePolarizationsThread={};
];


(* ::Input::Initialization:: *)
MassiveAssumptions={};
MasslessAssumptions={};
$Assumptions={};

ClearAssumptions[]:=Module[{},
MassiveAssumptions={};
MasslessAssumptions={};
$Assumptions={}; 
ClearAllThreads[];
ClearAllData[];
ClearMomentumConservation[];
ClearNumerics[];
];
ClearAssumptions[];


(* ::Subsection::Closed:: *)
(*Add *)


(* ::Input::Initialization:: *)
AddAssumptions[assum_]:= Module[{oldassum,newassum},
oldassum=Flatten[MonomialList[$Assumptions]];
newassum=DeleteDuplicates[Join[oldassum,assum]];
$Assumptions=DeleteDuplicates[And@@newassum]
];


(* ::Subsection::Closed:: *)
(*Remove*)


RemoveAssumptions[assum_]:= Module[{oldassum,newassum},
oldassum=Flatten[MonomialList[$Assumptions]];
newassum=DeleteDuplicates[DeleteElements[oldassum,assum]];
$Assumptions=DeleteDuplicates[And@@newassum]
];


(* ::Section::Closed:: *)
(*Reality Condition*)


ImposeReality[Legs_]:=Module[{},
AllRealLegs[]=DeleteDuplicates@(Join[AllRealLegs[],Legs]);
AllRealMasslessLegs[]=Select[AllRealLegs[],MlQ];
AllRealMassiveLegs[]=Select[AllRealLegs[],MsQ];
TildeLeg/:TildeLeg[i_?RlQ]:=i;

];

RemoveReality[Legs_]:=Module[{},
AllRealLegs[]=DeleteDuplicates@DeleteElements[AllRealLegs[],Legs];
AllRealMasslessLegs[]=Select[AllRealLegs[],MlQ];
AllRealMassiveLegs[]=Select[AllRealLegs[],MsQ];
];


(* ::Chapter:: *)
(*Utilities*)


(* ::Section:: *)
(*Mom*)


Mom[leg_,\[Alpha]_,\[Beta]_]/;MsQ[SignOf[leg]leg]:=With[{i=SignOf[leg]leg},-SignOf[leg]SHB[i[MIL[{\[ScriptCapitalI],GI[1]}]],\[Alpha]]SHA[i[-MIL[{\[ScriptCapitalI],GI[0]}]],\[Beta]]]//Simplify;
Mom[leg_,\[Alpha]_,\[Beta]_]/;!MsQ[SignOf[leg]leg]:=With[{i=SignOf[leg]leg}, -SignOf[leg] SHB[i,\[Alpha]]SHA[i,\[Beta]]]//Simplify;


(* ::Section::Closed:: *)
(*Dress SH*)


(* ::Input::Initialization:: *)
DressMom=DressSH;


DressSH[p_,a_,b_] /;(Simplify[p-Total[Thread[Coefficient[p,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]]])===0:= Module[{foundMoms,SHMoms,MomSum},
foundMoms=Select[DeleteDuplicates[AllMomenta[]],!FreeQ[p,#]&];
SHMoms=Map[Mom[#,a,b]&,(foundMoms//.Thread[AllMomenta[]-> AllLegs[]])];
MomSum=Total[Thread[Coefficient[p,foundMoms]*SHMoms]];
MomSum
];	

DressSH[p_,a_,b_]:= Module[{},
Error::FoundUndefMom=StringJoin["Found Undefined Momenta : ",ToString[(p-Total[Thread[Coefficient[p,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]])] ];
Message[Error::FoundUndefMom]];


(* ::Section::Closed:: *)
(*Massive Polarizations*)


(* ::Input::Initialization:: *)
SetSameMsIndices[expr_]:=expr//.{i_[MsIndex[J_,a_]]/;Not[a===i]:>i[ MsIndex[J,i]]}


\[CapitalNu][J_,L_, False]:= Sqrt[2] NORM;
\[CapitalNu][J_,L_, True]:= (1/Sqrt[2] KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],1]+  KroneckerDelta[Abs[J],1]KroneckerDelta[Abs[L],2]+1/Sqrt[2] KroneckerDelta[Abs[J],2]KroneckerDelta[Abs[L],2]);


MsPol[i_,\[Alpha]_,\[Beta]_,LG1_:MsIndex[J,1], LG2_: MsIndex[J,2]]:= \[CapitalNu][LG1,LG2, NormQ] (SHB[i[LG1],\[Alpha]]SHA[i[LG2],\[Beta]]+SHB[i[LG2],\[Alpha]]SHA[i[LG1],\[Beta]])/(2 m[i])//Simplify;
MsPolNonSymm[i_,\[Alpha]_,\[Beta]_,LG1_:MsIndex[J,1], LG2_: MsIndex[J,2]]:=\[CapitalNu][LG1,LG2, NormQ] (SHB[i[LG1],\[Alpha]]SHA[i[LG2],\[Beta]])/ m[i]//Simplify;


(* ::Input::Initialization:: *)
HsPol[j_,leg_,\[Alpha]_,\[Beta]_,J_:MsIndex[J,1],K_:MsIndex[J,1]]:=Times@@Map[MsPol[leg,MIL[{\[Alpha],#}],MIL[{\[Beta],#}],J,K]&,Range[j]]


(* ::Section::Closed:: *)
(*Massless Polarizations*)


Error::MlPol="Require helicity and reference spinor. Consider declaring massless leg or use the syntax MlPol[leg,\[Alpha],\[Beta],hel,ref]";
MlPol[i_,\[Alpha]_,\[Beta]_]:=With[{hel=Helicity[i],ref=ReferenceSpinor[i]},If[hel===+1,Sqrt[2] (SHB[i,\[Alpha]]SHA[ref, \[Beta]])/SHAA[i,ref],
If[hel===-1,Sqrt[2] (SHB[ref,\[Alpha]]SHA[i,\[Beta]])/SHBB[ref,i],Message[Error::MlPol]]]];

MlPol[i_,\[Alpha]_,\[Beta]_,+1,ref_]:=Sqrt[2] (SHB[i,\[Alpha]]SHA[ref, \[Beta]])/SHAA[i,ref];
MlPol[i_,\[Alpha]_,\[Beta]_,-1,ref_]:=Sqrt[2] (SHB[ref,\[Alpha]]SHA[i,\[Beta]])/SHBB[ref,i];


(* ::Section::Closed:: *)
(*Replace Spinors*)


(* ::Input::Initialization:: *)
ReplaceSpinorsFunction[rules_][expr_]:=Module[{expr1},
expr1=expr//NoLGScalar//NoSL2CScalar;
expr1//.rules//ExpandAll//PutSL2CScalar//PutLGScalar
]


(* ::Input::Initialization:: *)
ReplaceSpinors[rules_][x_+ y_] := ReplaceSpinors[rules][x]+ReplaceSpinors[rules][y];
ReplaceSpinors[rules_][x_/ y_] := ReplaceSpinors[rules][x]/ReplaceSpinors[rules][y];
ReplaceSpinors[rules_][x_  y_] := ReplaceSpinors[rules][x ]ReplaceSpinors[rules][y];
ReplaceSpinors[rules_][x_^n_] := ReplaceSpinors[rules][x]^n;
ReplaceSpinors[rules_][x_List]:= Map[ReplaceSpinors[rules],x];

ReplaceSpinors[rules_][x_]/;Length[MonomialList[x]]==1:=ReplaceSpinorsFunction[rules][x];


(* ::Section::Closed:: *)
(*Scale Spinors*)


(* ::Input::Initialization:: *)
ScaleSpinorsFunction[rules_][expr_]:=Module[{expr1},
expr1=expr//NoLGScalar//NoSL2CScalar;
expr1/.rules//ExpandAll//PutSL2CScalar//PutLGScalar
]


(* ::Input::Initialization:: *)
ScaleSpinors[rules_][x_+ y_] := ScaleSpinors[rules][x]+ScaleSpinors[rules][y];
ScaleSpinors[rules_][x_/ y_] := ScaleSpinors[rules][x]/ScaleSpinors[rules][y];
ScaleSpinors[rules_][x_  y_] := ScaleSpinors[rules][x ]ScaleSpinors[rules][y];
ScaleSpinors[rules_][x_^n_] := ScaleSpinors[rules][x]^n;
ScaleSpinors[rules_][x_List]:= Map[ScaleSpinors[rules],x];

ScaleSpinors[rules_][x_]/;Length[MonomialList[x]]==1:=ScaleSpinorsFunction[rules][x];


(* ::Section::Closed:: *)
(*To Basis*)


(* ::Input::Initialization:: *)
ToBasis[i_->{Spinor1_,Spinor2_}][expr_]:=Module[{expr1},
expr1=expr//ReplaceSpinors[{SHA[i,\[Alpha]_]:> SHAA[Spinor2,i]/SHAA[Spinor2,Spinor1] SHA[Spinor1,\[Alpha]]+SHAA[Spinor1,i]/SHAA[Spinor1,Spinor2] SHA[Spinor2,\[Alpha]],SHA[i,-\[Alpha]_]:> SHAA[Spinor2,i]/SHAA[Spinor2,Spinor1] SHA[Spinor1,-\[Alpha]]+SHAA[Spinor1,i]/SHAA[Spinor1,Spinor2] SHA[Spinor2,-\[Alpha]],SHB[i,-\[Alpha]_]:> SHBB[Spinor2,i]/SHBB[Spinor2,Spinor1] SHB[Spinor1,-\[Alpha]]+SHBB[Spinor1,i]/SHBB[Spinor1,Spinor2] SHB[Spinor2,-\[Alpha]],SHB[i,\[Alpha]_]:> SHBB[Spinor2,i]/SHBB[Spinor1,Spinor2] SHB[Spinor1,\[Alpha]]+SHBB[Spinor1,i]/SHBB[Spinor1,Spinor2] SHB[Spinor2,\[Alpha]]}]]


(* ::Section::Closed:: *)
(*Replace Momenta*)


(* ::Input::Initialization:: *)
ReplaceMomentum[h___][expr_List]:=Map[ReplaceMomentum[h],expr];
ReplaceMomentum[Momenta_,ReplacedSpinorMom_][expr_]/;(Simplify[ReplacedSpinorMom-Total[Thread[Coefficient[ReplacedSpinorMom,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]]])===0 := Module[{expr0,expr2,lhsleg,foundMomenta,foundlegs,foundMomcoeffs,expr1},
lhsleg=Momenta//.Thread[AllMomenta[]-> AllLegs[]];
foundMomenta=DeleteDuplicates[Select[AllMomenta[],!FreeQ[ReplacedSpinorMom,#]&]];
foundlegs=foundMomenta//.Thread[AllMomenta[]-> AllLegs[]];
foundMomcoeffs=Coefficient[ReplacedSpinorMom,foundMomenta];
expr0=Map[{Numerator[#],Denominator[#]}&,ToList[expr]];
expr1=expr0//NoLGScalar//NoSL2CScalar;
expr2=expr1//.{
SHA[i_,spinindex1_]SHB[i_,spinindex2_]/;BaseHead[i]===lhsleg&&!MsQ[i]:> -Total@Thread[Map[Mom[#,spinindex2,spinindex1]&,foundlegs]*foundMomcoeffs],
SHA[i_[a_],spinindex1_]SHB[i_[b_],spinindex2_]/;BaseHead[i]===lhsleg&&a+b==0&&!IntegerQ[a]:> SignOf[a]Total@Thread[Map[Mom[#,spinindex2,spinindex1]&,foundlegs]*foundMomcoeffs]
}//ExpandAll//PutSL2CScalar//PutLGScalar;
Map[Thread[#[[1]]*1/#[[2]]]&,expr2]//Total
];

ReplaceMomentum[Momenta_,ReplacedSpinorMom_][expr_]:= Module[{},
Error::FoundUndefMom=StringJoin["Found Undefined Momenta : ",ToString[(ReplacedSpinorMom-Total[Thread[Coefficient[ReplacedSpinorMom,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]])] ];
Message[Error::FoundUndefMom]];

ReplaceMomenta[rules_][expr_]:= Module[{Momenta,ReplacedMom,allreplacements},
Momenta=Keys[rules];
ReplacedMom=Values[rules];
allreplacements=ReplaceMomentum@@@Transpose[{Momenta,ReplacedMom}];
Composition[Sequence@@allreplacements][expr]
];	


(* ::Input::Initialization:: *)
ScaleMomentum[h___][expr_List]:=Map[ScaleMomentum[h],expr];
ScaleMomentum[Momenta_,ReplacedSpinorMom_][expr_]/;Simplify[ReplacedSpinorMom-Total[Thread[Coefficient[ReplacedSpinorMom,DeleteDuplicates[AllMomenta[]]] DeleteDuplicates[AllMomenta[]]]]]===0:=Module[{expr0,expr2,lhsleg,foundMomenta,foundlegs,foundMomcoeffs,expr1},lhsleg=Momenta//. Thread[AllMomenta[]->AllLegs[]];foundMomenta=DeleteDuplicates[Select[AllMomenta[],!FreeQ[ReplacedSpinorMom,#1]&]];
If[!(foundMomenta[[1]]===Momenta),Error::notsamemom="Scaled momentum should be same as the original momentum. Use ReplaceMomenta instead."; Message[Error::notsamemom];Return[$Failed]];
foundlegs=foundMomenta//. Thread[AllMomenta[]->AllLegs[]];foundMomcoeffs=Coefficient[ReplacedSpinorMom,foundMomenta];expr0=({Numerator[#1],Denominator[#1]}&)/@ToList[expr];expr1=NoSL2CScalar[NoLGScalar[expr0]];expr2=PutLGScalar[PutSL2CScalar[ExpandAll[expr1/. {SHA[i_,spinindex1_]/;BaseHead[i]===lhsleg:>-SHA[i,spinindex1]}/. {SHB[i_,spinindex2_]/;BaseHead[i]===lhsleg:>-(foundMomcoeffs[[1]]SHB[i,spinindex2])}]]];Total[(Thread[#1[[1]]/#1[[2]]]&)/@expr2]];

ScaleMomenta[rules_][expr_]:= Module[{Momenta,ReplacedMom,allreplacements},
Momenta=Keys[rules];
ReplacedMom=Values[rules];
allreplacements=ScaleMomentum@@@Transpose[{Momenta,ReplacedMom}];
Composition[Sequence@@allreplacements][expr]
];	


(* ::Input::Initialization:: *)
ShiftMomentum[h___][expr_List]:=Map[ShiftMomentum[h],expr];
ShiftMomentum[Momenta_,ReplacedSpinorMom_][expr_]/;(Simplify[ReplacedSpinorMom-Total[Thread[Coefficient[ReplacedSpinorMom,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]]])===0 := Module[{expr0,expr2,lhsleg,foundMomenta,foundlegs,foundMomcoeffs,expr1},
lhsleg=Momenta//.Thread[AllMomenta[]-> AllLegs[]];
foundMomenta=DeleteDuplicates[Select[AllMomenta[],!FreeQ[ReplacedSpinorMom,#]&]];
foundlegs=foundMomenta//.Thread[AllMomenta[]-> AllLegs[]];
foundMomcoeffs=Coefficient[ReplacedSpinorMom,foundMomenta];
expr0=Map[{Numerator[#],Denominator[#]}&,ToList[expr]];
expr1=expr0//NoLGScalar//NoSL2CScalar;
expr2=expr1/.{
SHA[i_,spinindex1_]SHB[i_,spinindex2_]/;BaseHead[i]===lhsleg&&!MsQ[i]:> -Total@Thread[Map[Mom[#,spinindex2,spinindex1]&,foundlegs]*foundMomcoeffs]}/.{
SHA[i_[a_],spinindex1_]SHB[i_[b_],spinindex2_]/;BaseHead[i]===lhsleg&&a+b==0&&!IntegerQ[a]:> SignOf[a]Total@Thread[Map[Mom[#,spinindex2,spinindex1]&,foundlegs]*foundMomcoeffs]
}//ExpandAll//PutSL2CScalar//PutLGScalar;
Map[Thread[#[[1]]*1/#[[2]]]&,expr2]//Total
];

ShiftMomentum[Momenta_,ReplacedSpinorMom_][expr_]:= Module[{},
Error::FoundUndefMom=StringJoin["Found Undefined Momenta : ",ToString[(ReplacedSpinorMom-Total[Thread[Coefficient[ReplacedSpinorMom,DeleteDuplicates[AllMomenta[]]]*DeleteDuplicates[AllMomenta[]]]])] ];
Message[Error::FoundUndefMom]];

ShiftMomenta[rules_][expr_]:= Module[{Momenta,ReplacedMom,allreplacements},
Momenta=Keys[rules];
ReplacedMom=Values[rules];
allreplacements=ShiftMomentum@@@Transpose[{Momenta,ReplacedMom}];
Composition[Sequence@@allreplacements][expr]
];	


(* ::Section:: *)
(*Differentiate*)


SHA/:D[SHA[i_?(Not[MsQ[#]]&),\[Alpha]_],SHA[j_?(Not[MsQ[#]]&),\[Beta]_]]:=Boole[i===j]Metd[\[Alpha],-\[Beta]];
SHA/:D[SHA[i_?MsQ[J_],\[Alpha]_],SHA[j_?MsQ[K_],\[Beta]_]]:=Boole[i===j]Metd[\[Alpha],-\[Beta]]Metlg[J,-K];
SHB/:D[SHB[i_?(Not[MsQ[#]]&),\[Alpha]_],SHB[j_?(Not[MsQ[#]]&),\[Beta]_]]:=Boole[i===j]Met[\[Alpha],-\[Beta]];
SHB/:D[SHB[i_?MsQ[J_],\[Alpha]_],SHB[j_?MsQ[K_],\[Beta]_]]:=Boole[i===j]Met[\[Alpha],-\[Beta]]Metlg[J,-K];
SHA/:D[SHA[i_,\[Alpha]_],SHB[j_,\[Beta]_]]:=0;
SHB/:D[SHB[i_,\[Alpha]_],SHA[j_,\[Beta]_]]:=0;

SHAA/:D[SHAA[a_,b_],SHAA[c_,d_]]:=ContractMetric[Boole[BaseHead[a]===BaseHead[c]]Boole[BaseHead[b]===BaseHead[d]]If[MsQ[a]&&MsQ[c],Metlg[a[[1]],-c[[1]]],1]If[MsQ[b]&&MsQ[d],Metlg[b[[1]],-d[[1]]],1]-Boole[BaseHead[a]===BaseHead[d]]Boole[BaseHead[b]===BaseHead[b]]If[MsQ[a]&&MsQ[d],Metlg[a[[1]],-d[[1]]],1]If[MsQ[b]&&MsQ[c],Metlg[b[[1]],-c[[1]]],1]];

SHBB/:D[SHBB[a_,b_],SHBB[c_,d_]]:=ContractMetric[Boole[BaseHead[a]===BaseHead[c]]Boole[BaseHead[b]===BaseHead[d]]If[MsQ[a]&&MsQ[c],Metlg[a[[1]],-c[[1]]],1]If[MsQ[b]&&MsQ[d],Metlg[b[[1]],-d[[1]]],1]-Boole[BaseHead[a]===BaseHead[d]]Boole[BaseHead[b]===BaseHead[b]]If[MsQ[a]&&MsQ[d],Metlg[a[[1]],-d[[1]]],1]If[MsQ[b]&&MsQ[c],Metlg[b[[1]],-c[[1]]],1]];

SHAB/:D[SHAB[a_,i_,b_],SHAB[c_,i_,d_]]:=ContractMetric[Boole[BaseHead[a]===BaseHead[c]]Boole[BaseHead[b]===BaseHead[d]]If[MsQ[a]&&MsQ[c],Metlg[a[[1]],-c[[1]]],1]If[MsQ[b]&&MsQ[d],Metlg[b[[1]],-d[[1]]],1]];

SHBA/:D[SHBA[a_,i_,b_],SHBA[c_,i_,d_]]:=ContractMetric[Boole[BaseHead[a]===BaseHead[c]]Boole[BaseHead[b]===BaseHead[d]]If[MsQ[a]&&MsQ[c],Metlg[a[[1]],-c[[1]]],1]If[MsQ[b]&&MsQ[d],Metlg[b[[1]],-d[[1]]],1]];


(* ::Input::Initialization:: *)
Differentiate[SHA[y___]][SHAA[x___]]:=SimplifyPolynomial@Differentiate[SHA[y]][NoSL2CScalar[SHAA[x]]];
Differentiate[SHA[y___]][SHBB[x___]]:=0;
Differentiate[SHA[y___]][SHAB[x___]]:=SimplifyPolynomial@Differentiate[SHA[y]][NoSL2CScalar@NoLGScalar[SHAB[x]]];
Differentiate[SHA[y___]][SHBA[x___]]:=SimplifyPolynomial@Differentiate[SHA[y]][NoSL2CScalar@NoLGScalar[SHBA[x]]];

Differentiate[SHB[y___]][SHAA[x___]]:=0;
Differentiate[SHB[y___]][SHBB[x___]]:=SimplifyPolynomial@Differentiate[SHB[y]][NoSL2CScalar[SHBB[x]]];
Differentiate[SHB[y___]][SHAB[x___]]:=SimplifyPolynomial@Differentiate[SHB[y]][NoSL2CScalar@NoLGScalar[SHAB[x]]];
Differentiate[SHB[y___]][SHBA[x___]]:=SimplifyPolynomial@Differentiate[SHB[y]][NoSL2CScalar@NoLGScalar[SHBA[x]]];


Differentiate[SHAA[y___]][SHBB[x___]]:=0;
Differentiate[SHAA[y___]][SHAB[x___]]:=Differentiate[SHAA[y]][NoLGScalar[SHAB[x]]];
Differentiate[SHAA[y___]][SHBA[x___]]:=Differentiate[SHAA[y]][NoLGScalar[SHBA[x]]];

Differentiate[SHBB[y___]][SHAA[x___]]:=0;
Differentiate[SHBB[y___]][SHAB[x___]]:=Differentiate[SHBB[y]][NoLGScalar[SHAB[x]]];
Differentiate[SHBB[y___]][SHBA[x___]]:=Differentiate[SHBB[y]][NoLGScalar[SHBA[x]]];

Differentiate[SHAB[y___]][SHAA[x___]]:=0;
Differentiate[SHAB[y___]][SHBB[x___]]:=0;
Differentiate[SHAB[y___]][SHBA[x___]]:=0;

Differentiate[SHBA[y___]][SHAA[x___]]:=0;
Differentiate[SHBA[y___]][SHBB[x___]]:=0;
Differentiate[SHBA[y___]][SHAB[x___]]:=0;

Differentiate[Spinors_List][x_]:=Composition[Sequence@@Map[Differentiate[#]&,Spinors]][x];
Differentiate[Spinor_][x_+y_]:=Differentiate[Spinor][x]+Differentiate[Spinor][y];
Differentiate[Spinor_][x_ y_]:=x Differentiate[Spinor][y]+ Differentiate[Spinor][x]y;
Differentiate[Spinor_][x_/y_]:=Differentiate[Spinor][x]/y-x/y^2 Differentiate[Spinor][y];
Differentiate[Spinor_][x_List]:=Map[Differentiate[Spinor][#]&,x];
Differentiate[Spinor_][x_^n_]:=n x^(n-1) Differentiate[Spinor][x];


Differentiate[Spinor_][x_]/;Length[MonomialList[x]]==1:=SimplifyPolynomial@D[x,Spinor];


(* ::Input::Initialization:: *)
HigherSpinDiffA[leg_,Spin_,IndexHead_:\[Beta]][expr_]:=Module[{Aspinortab},
Aspinortab=Map[SHA[leg,MIL[{IndexHead,#}]]&,Range[1,Spin]];

(*If[MsQ[leg],1/(2^Spin Spin!),1/Spin!]*)Differentiate[Join[Aspinortab]][expr]
];
HigherSpinDiffB[leg_,Spin_,IndexHead_:\[Alpha]][expr_]:=Module[{Bspinortab},
Bspinortab=Map[SHB[leg,MIL[{IndexHead,#}]]&,Range[1,Spin]];
(*If[MsQ[leg],1/(2^Spin Spin!),1/Spin!]*)Differentiate[Join[Bspinortab]][expr]
];

HigherSpinDiff[leg_,Spin_,IndexHead1_:\[Alpha],IndexHead2_:\[Beta]][expr_]:=HigherSpinDiffB[leg,Spin,IndexHead1][HigherSpinDiffA[leg,Spin,IndexHead2][expr]]


(* ::Input::Initialization:: *)
OpMlHW[leg_][expr_]:=1/2 (SHA[leg,dummy\[Alpha][GI[1]]]Differentiate[SHA[leg,dummy\[Alpha][GI[0]]]][expr]-SHB[leg,dummy\[Alpha][GI[1]]]Differentiate[SHB[leg,dummy\[Alpha][GI[0]]]][expr])//SimplifyPolynomial//PutLGScalar;
OpMsJ[leg_,I1_,J_][expr_]:=(SHA[leg[I1],dummy\[Alpha][GI[1]]]Differentiate[SHA[leg[J],dummy\[Alpha][GI[0]]]][expr]-SHB[leg[I1],dummy\[Alpha][GI[1]]]Differentiate[SHB[leg[J],dummy\[Alpha][GI[0]]]][expr]);
OpMsHW[leg_,I1_,J_][expr_]:=OpMsJ[leg,I1,J][expr]-1/2 \[Delta]lg[I1,-J]OpMsJ[leg,dummyI[GI[1]],dummyI[GI[0]]][expr]//ContractMetric//PutLGScalar;


(* ::Section:: *)
(*Strip Polarization*)


(* ::Input::Initialization:: *)
StripPolA[leg_,prefixd_:\[Alpha]][expr_]:=Module[{expr1,makereplacemenets},expr1=ToList@NoSL2CScalar@NoLGScalar@expr;

makereplacemenets[term_]:=Module[{MassiveAs,MassiveAsPDs,ABRules},
MassiveAs=Cases[term,SHA[leg[MsIndex[___]],___]|SHA[leg[-MsIndex[___]],___],All];
MassiveAsPDs=Module[{},counter=0;Map[Sqrt[m[leg]]/(2^(1/4) 2) Differentiate[SHA[#[[1]],MIL[{prefixd,GI[]}]]][#]&,MassiveAs]];
ABRules=Thread[MassiveAs-> MassiveAsPDs]
];
Total@PutLGScalar[PutSL2CScalar[ContractMetric[(Map[#//.makereplacemenets[#]&,expr1])]]]
];


(* ::Input::Initialization:: *)
StripPolB[leg_,prefix_:\[Alpha]][expr_]:=Module[{expr1,makereplacemenets},expr1=ToList@NoSL2CScalar@NoLGScalar@expr;

makereplacemenets[term_]:=Module[{MassiveBs,MassiveBsPDs,ABRules},
MassiveBs=Cases[term,SHB[leg[MsIndex[___]],___]|SHB[leg[-MsIndex[___]],___],All];
MassiveBsPDs=Module[{},counter=0;Map[Sqrt[m[leg]]/(2^(1/4) 2) Differentiate[SHB[#[[1]],MIL[{prefix,GI[]}]]][#]&,MassiveBs]];
ABRules=Thread[MassiveBs-> MassiveBsPDs]
];
Total@PutLGScalar[PutSL2CScalar[ContractMetric[(Map[#//.makereplacemenets[#]&,expr1])]]]
];


(* ::Input::Initialization:: *)
StripPol[leg_,prefix_:\[Alpha],prefixd_:\[Beta]][expr_]:=Module[{expr1,makereplacemenets},expr1=ToList@NoSL2CScalar@NoLGScalar@expr;

makereplacemenets[term_]:=Module[{MassiveAs,MassiveBs,MassiveAsPDs,MassiveBsPDs,ABRules},
MassiveAs=Cases[term,SHA[leg[MsIndex[___]],___]|SHA[leg[-MsIndex[___]],___],All];
MassiveBs=Cases[term,SHB[leg[MsIndex[___]],___]|SHB[leg[-MsIndex[___]],___],All];
MassiveAsPDs=Module[{},counter=0;Map[Sqrt[m[leg]]/(2^(1/4) 2) Differentiate[SHA[#[[1]],MIL[{prefixd,GI[]}]]][#]&,MassiveAs]];
MassiveBsPDs=Module[{},counter=0;Map[Sqrt[m[leg]]/(2^(1/4) 2) Differentiate[SHB[#[[1]],MIL[{prefix,GI[]}]]][#]&,MassiveBs]];
ABRules=Join[Thread[MassiveAs-> MassiveAsPDs],Thread[MassiveBs-> MassiveBsPDs]]
];
Total@PutLGScalar[PutSL2CScalar[ContractMetric[(Map[#//.makereplacemenets[#]&,expr1])]]]
];


(* ::Chapter:: *)
(*Miscelleneous*)


(* ::Section::Closed:: *)
(*Canonicalize Indices*)


(* ::Input::Initialization:: *)
lgindicesList= Table[MIL[{\[ScriptCapitalI],i}],{i,1000}];
leftindicesList= Table[MIL[{\[ScriptA],i}],{i,1000}];
rightindicesList= Table[MIL[{\[ScriptB],i}],{i,1000}];


(* ::Input::Initialization:: *)
CanonicalizeIndices[expr_]:=Module[{listLGIndices,list\[Alpha]Indices,list\[Beta]Indices,expr2,AllLGidxs,AllRidxs,AllLidxs,ReplaceLGidxRules,ReplaceRidxRules,ReplaceLidxRules},
listLGIndices=lgindicesList;
list\[Alpha]Indices=rightindicesList;
list\[Beta]Indices=leftindicesList;
expr2 = expr;
AllLGidxs= Cases[expr2,LGidx[x___], All]//DeleteDuplicates;
AllLidxs = Cases[expr2,  Lidx[x___], All]//DeleteDuplicates;
AllRidxs = Cases[expr2,  Ridx[x___], All]//DeleteDuplicates;
ReplaceLGidxRules = Thread[AllLGidxs-> listLGIndices[[;;Length[AllLGidxs]]]];
ReplaceLidxRules = Thread[AllLidxs-> list\[Beta]Indices[[;;Length[AllLidxs]]]];
ReplaceRidxRules = Thread[AllRidxs-> list\[Alpha]Indices[[;;Length[AllRidxs]]]];
expr2//.ReplaceLidxRules//.ReplaceRidxRules//.ReplaceLGidxRules
];


(* ::Input::Initialization:: *)
CanonicalizeSU2RScalars[expr_]:=Module[{exprNum,exprDen,exprNum1,exprDen1,AllLGidxsNum1,AllLGidxsDen1,ReplaceLGidxNum1Rules,ReplaceLGidxDen1Rules},
exprNum=expr//Together//Numerator//PutMassiveLGScalar;
exprDen=expr//Together//Denominator//PutMassiveLGScalar;
exprNum1=exprNum//.SHAB[x_,i_,b_]/;MemberQ[AllMassiveLegs[],i]:>SHAA[i[-LGidx[x]],x]SHBB[i[LGidx[x]],b]//.X_[\[Mu]___,i_?MsQ[a_],\[Nu]___,i_?MsQ[b_],\[Rho]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu],i[SignOf[b]LGidx[a]],\[Rho]]//.Y_[\[Mu]___,i_?MsQ[a_],\[Nu]___]X_[\[Rho]___,i_?MsQ[b_],\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> Y[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]X[\[Rho],i[SignOf[b]LGidx[a]],\[Sigma]]//.X_[\[Mu]___,i_[a_],\[Nu]___]\[CapitalSigma]_[i_][\[Rho]___,b_,\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]\[CapitalSigma][i][\[Rho],SignOf[b]LGidx[a],\[Sigma]] ;
exprDen1=exprDen//.SHAB[x_,i_,b_]/;MemberQ[AllMassiveLegs[],i]:>SHAA[i[-LGidx[x]],x]SHBB[i[LGidx[x]],b]//.X_[\[Mu]___,i_?MsQ[a_],\[Nu]___,i_?MsQ[b_],\[Rho]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu],i[SignOf[b]LGidx[a]],\[Rho]]//.Y_[\[Mu]___,i_?MsQ[a_],\[Nu]___]X_[\[Rho]___,i_?MsQ[b_],\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> Y[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]X[\[Rho],i[SignOf[b]LGidx[a]],\[Sigma]]//.X_[\[Mu]___,i_[a_],\[Nu]___]\[CapitalSigma]_[i_][\[Rho]___,b_,\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]\[CapitalSigma][i][\[Rho],SignOf[b]LGidx[a],\[Sigma]]  ;
AllLGidxsNum1=Cases[exprNum1,LGidx[x___], All]//DeleteDuplicates;
AllLGidxsDen1=Cases[exprDen1,LGidx[x___], All]//DeleteDuplicates;
ReplaceLGidxNum1Rules = Thread[AllLGidxsNum1-> lgindicesList[[;;Length[AllLGidxsNum1]]]];
ReplaceLGidxDen1Rules = Thread[AllLGidxsDen1-> lgindicesList[[Length[AllLGidxsNum1]+1;;Length[AllLGidxsNum1]+Length[AllLGidxsDen1]]]];

(exprNum1//.ReplaceLGidxNum1Rules)/(exprDen1//.ReplaceLGidxDen1Rules)
];

CanonicalizeSU2LScalars[expr_]:=Module[{exprNum,exprDen,exprNum1,exprDen1,AllLGidxsNum1,AllLGidxsDen1,ReplaceLGidxNum1Rules,ReplaceLGidxDen1Rules},
exprNum=expr//Together//Numerator//PutMassiveLGScalar;
exprDen=expr//Together//Denominator//PutMassiveLGScalar;
exprNum1=exprNum//.SHAB[x_,i_,b_]/;MemberQ[AllMassiveLegs[],i]:>SHAA[i[-LGidx[b]],x]SHBB[i[LGidx[b]],b]//.X_[\[Mu]___,i_?MsQ[a_],\[Nu]___,i_?MsQ[b_],\[Rho]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu],i[SignOf[b]LGidx[a]],\[Rho]]//.Y_[\[Mu]___,i_?MsQ[a_],\[Nu]___]X_[\[Rho]___,i_?MsQ[b_],\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> Y[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]X[\[Rho],i[SignOf[b]LGidx[a]],\[Sigma]] //.X_[\[Mu]___,i_[a_],\[Nu]___]\[CapitalSigma]_[i_][\[Rho]___,b_,\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]\[CapitalSigma][i][\[Rho],SignOf[b]LGidx[a],\[Sigma]] ;
exprDen1=exprDen//.SHAB[x_,i_,b_]/;MemberQ[AllMassiveLegs[],i]:>SHAA[i[-LGidx[b]],x]SHBB[i[LGidx[b]],b] //.X_[\[Mu]___,i_?MsQ[a_],\[Nu]___,i_?MsQ[b_],\[Rho]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu],i[SignOf[b]LGidx[a]],\[Rho]]//.Y_[\[Mu]___,i_?MsQ[a_],\[Nu]___]X_[\[Rho]___,i_?MsQ[b_],\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> Y[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]X[\[Rho],i[SignOf[b]LGidx[a]],\[Sigma]]//.X_[\[Mu]___,i_[a_],\[Nu]___]\[CapitalSigma]_[i_][\[Rho]___,b_,\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[a]],\[Nu]]\[CapitalSigma][i][\[Rho],SignOf[b]LGidx[a],\[Sigma]] ;
AllLGidxsNum1=Cases[exprNum1,LGidx[x___], All]//DeleteDuplicates;
AllLGidxsDen1=Cases[exprDen1,LGidx[x___], All]//DeleteDuplicates;
ReplaceLGidxNum1Rules = Thread[AllLGidxsNum1-> lgindicesList[[;;Length[AllLGidxsNum1]]]];
ReplaceLGidxDen1Rules = Thread[AllLGidxsDen1-> lgindicesList[[Length[AllLGidxsNum1]+1;;Length[AllLGidxsNum1]+Length[AllLGidxsDen1]]]];

(exprNum1//.ReplaceLGidxNum1Rules)/(exprDen1//.ReplaceLGidxDen1Rules)];

CanonicalizeSU2LRScalars[expr_]:=CanonicalizeSU2LScalars[CanonicalizeSU2RScalars[expr]];

CanonicalizeTerms[expr_]:=expr//CanonicalizeSU2RScalars//SimplifySchouten//CanonicalizeSU2LScalars//SimplifySchouten;


(* ::Input::Initialization:: *)
CanonicalizeScalars[expr_]:=Module[{expr2,expr3,AllLGidxs,ReplaceLGidxRules},

expr2=expr//PutMassiveLGScalar;

expr3=expr2//.X_[\[Mu]___,i_?MsQ[a_],\[Nu]___,i_?MsQ[b_],\[Rho]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[i]],\[Nu],i[-SignOf[a]LGidx[i]],\[Rho]]//.Y_[\[Mu]___,i_?MsQ[a_],\[Nu]___]X_[\[Rho]___,i_?MsQ[b_],\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> Y[\[Mu],i[SignOf[a]LGidx[i]],\[Nu]]X[\[Rho],i[-SignOf[a]LGidx[i]],\[Sigma]]//.X_[\[Mu]___,i_[a_],\[Nu]___]\[CapitalSigma]_[i_][\[Rho]___,b_,\[Sigma]___]/;!IntegerQ[a]&&!IntegerQ[b]&&a+b==0&&Not[BaseHead[a]===LGidx]&&Not[BaseHead[b]===LGidx]:> X[\[Mu],i[SignOf[a]LGidx[i]],\[Nu]]\[CapitalSigma][i][\[Rho],-SignOf[a]LGidx[i],\[Sigma]];

AllLGidxs=Cases[expr3,LGidx[x___], All]//DeleteDuplicates;
ReplaceLGidxRules = Thread[DeleteDuplicates[AllLGidxs]-> lgindicesList[[;;Length[DeleteDuplicates[AllLGidxs]]]]];
expr3//.ReplaceLGidxRules
];


(* ::Input::Initialization:: *)
Unprotect[PCI];
PCI=PutCanonicalIndices;
Protect[PCI];

PutCanonicalIndices[x_+ y_] := CanonicalizeSU2RScalars[x]+CanonicalizeSU2RScalars[y];
PutCanonicalIndices[x_/ y_] := CanonicalizeSU2RScalars[x/y];
PutCanonicalIndices[x_ y_] := CanonicalizeSU2RScalars[x y];
PutCanonicalIndices[x_^n_] := CanonicalizeSU2RScalars[x^n];
PutCanonicalIndices[x_List]:= Map[CanonicalizeSU2RScalars,x];

PutCanonicalIndices[x_]/;Length[MonomialList[x]]==1:=x;


(* ::Input::Initialization:: *)
UnSetCanonicalIndices[]:=Module[{},
$Post=.;
];


(* ::Input::Initialization:: *)
SetCanonicalIndices[]:=Module[{},
$Post=(PutCanonicalIndices[#])&;
];


(* ::Section::Closed:: *)
(*Symmetrized*)


Symmetrized[list_][expr_]:= Module[{},
	dummies = Table[MI[\[Kappa]\[Tau]\[Zeta],i], {i, Length[list]}];
	exprdummy = expr/.Thread[list->dummies];
	1/Length[dummies]! Sum[exprdummy/.Thread[dummies->perm],{perm, Permutations[list]} ]
]


(* ::Section::Closed:: *)
(*Power Contract*)


(* ::Input::Initialization:: *)
PowerContract[expr_]:=expr/.{m_^q_ n_^q_:>E^(2/q I \[Pi] Floor[1/2-Arg[m]/(2 \[Pi])-Arg[n]/(2 \[Pi])]) (m n)^q/;!IntegerQ[m]&&!IntegerQ[n],
								m_^q_ n_^p_:>E^(-(2/q)I \[Pi] Floor[1/2-Arg[m]/(2 \[Pi])+Arg[n]/(2 \[Pi])]) (m/n)^q/;q>=0&&p==-q&&!IntegerQ[m]&&!IntegerQ[n]};


(* ::Section::Closed:: *)
(*Find Basis*)


(* ::Input::Initialization:: *)
Options[FindBasis]={pattern->SHAA[a___,b___]|SHBB[a___,b___]|SHAB[a___,b___,c___]};
Options[BasisForm]={pattern->SHAA[a_,b_]|SHBB[a_,b_]|SHAB[a_,b_,c_],function->(#1&)};


(* ::Input::Initialization:: *)
FindBasis[OptionsPattern[]][expr_]:=Module[{findbasis,expr2},pat=OptionValue[pattern];findbasis[pp_]:=Times@@(#1^Exponent[pp,#1]&)/@Cases[Variables[pp],pat];expr2=expr//. {x_[]:>x[\[Kappa]\[Tau]\[Zeta]\[Pi]]};(DeleteCases[#1,1]&)[ApplyRule[{x_[\[Kappa]\[Tau]\[Zeta]\[Pi]]:>x[]}][DeleteDuplicates[findbasis/@List@@expr2]]]];


(* ::Input::Initialization:: *)
BasisForm[OptionsPattern[]][expr_]:=Module[{},pat=OptionValue[pattern];func=OptionValue[function];expr2=Expand[expr];scalevars[expr2_]:=Module[{},allvars=Variables[expr];expr2/. Thread[allvars->\[Lambda] allvars]];basis=scalevars[FindBasis[pattern->pat][expr2]];sortedbasis=Sort[basis,Exponent[#1,\[Lambda]]>Exponent[#2,\[Lambda]]&]/. \[Lambda]->1;n=Length[sortedbasis];coefflist=ConstantArray[0,n];For[i=1,i<=n,i=i+1,coefflist[[i]]=Coefficient[expr2,sortedbasis[[i]]];expr2=expr2-coefflist[[i]] sortedbasis[[i]];];If[!MatchQ[FullSimplify[expr2],0],Print[Style["Warning:",Red]," Basis simplified only for sub-expression."]];Total[Thread[func[coefflist] sortedbasis]]+Simplify[expr2]];


(* ::Section::Closed:: *)
(*Swap Rules*)


(* ::Input::Initialization:: *)
BasicObjects={SHA,SHB,SHAA,SHBB,SHAB,SHBA,\[CapitalSigma],\[CapitalOmega],\[CapitalDelta],sm,SM};
Swap[leg1_,leg2_][expr_]:=expr//.{MsIndex[\[Kappa]_,leg1]:>MsIndex[\[Kappa], $rep[leg1]],MsIndex[\[Kappa]_,leg2]:>MsIndex[\[Kappa], $rep[leg2]],X_[dummya___,leg1,dummyb___]/;MemberQ[BasicObjects,X]:> X[dummya, $rep[leg1],dummyb],X_[dummya___,leg1[dummyI___],dummyb___]/;MemberQ[BasicObjects,X]:> X[dummya, $rep[leg1][dummyI],dummyb],X_[dummya___,leg2,dummyb___]/;MemberQ[BasicObjects,X]:> X[dummya, $rep[leg2],dummyb],X_[dummya___,leg2[dummyI___],dummyb___]/;MemberQ[BasicObjects,X]:> X[dummya, $rep[leg2][dummyI],dummyb]}//.{$rep[leg1]:> leg2,$rep[leg2]:> leg1}
