(* ::Package:: *)

BeginPackage["SMaSH`"];


PackageDirectory = "SMaSH"


Get[PackageDirectory<>"/usage.m"]


Begin["`Private`"];


Get[PackageDirectory<>"/0_Utilities.m"];
Get[PackageDirectory<>"/1_BasicObjects.m"];
Get[PackageDirectory<>"/2_PolynomialRules.m"];
Get[PackageDirectory<>"/3_ComponentForm.m"];
Get[PackageDirectory<>"/4_ConversionLortoSH.m"];
Get[PackageDirectory<>"/5_HighEnergy.m"];
Get[PackageDirectory<>"/6_CPT.m"];
Get[PackageDirectory<>"/7_Amplitudes.m"];


Print["                       Authors"]
Print["-------------------------------------------------"]
Print["Aakash Kumar, aakash.kumar.physics@gmail.com"]
Print["Arnab Rudra, rudra19@iiserb.ac.in"]
Print["Rahul Shaw, rahulshaw.phy@gmail.com"]


End[];


EndPackage[];
