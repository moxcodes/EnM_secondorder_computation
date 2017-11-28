(* ::Package:: *)

SetOptions[$FrontEndSession, NotebookAutoSave -> True]
NotebookSave[]


(* ::Text:: *)
(*IMPORTANT: You will need to set the path for the imports to work - set it to wherever you have placed the full package*)


$Path=$Path~Join~{"/home/mox/research/emri_project/emri_notebooks/refactored_EnM_computation/"};


(*$Path=$Path~Join~{"/path/to/these/files"};*)


(* ::Section:: *)
(*General routines*)


(* ::Subsection:: *)
(*Initiation*)


(* ::Subsubsection:: *)
(*Import Calls*)


<<xAct`xTensor`


<<xAct`xCoba`


<<xAct`xPert`


<<xAct`TexAct`


<<"3+1Utils.m"


(* ::Subsubsection:: *)
(*Formatting Calls*)


Unprotect[IndexForm];
IndexForm[LI[x_]]:="("<>ToString[x]<>")";
Protect[IndexForm];


$PrePrint=ScreenDollarIndices;


$DefInfoQ=False;


(* ::Subsubsection:: *)
(*Retarded coordinate definitions and rules*)


<<"Retarded3+1Coords.m"


CD[__][CDelta[__][__]]:=0;


(* ::Section:: *)
(*Physical Tensors in Retarded Basis*)


(* ::Subsection:: *)
(*Integration*)


<<"NullIntegration.m"


CommuteThroughNullInt={FExt,FExtPert,acc,accpert,normp,acc1d,acc1dpert,acc2d,acc2dpert,CDelta[Fra3,Fra3],CDelta[-Fra3,Fra3],CDelta[Fra3,-Fra3],CDelta[-Fra3,-Fra3]};


CommuteThroughNullIntScalar={rp};


CommuteThroughNullIntConst={\[Lambda],\[Epsilon]};


IntegrateByPartsList={SE,SEpert,CurrentDens,CurrentDenspert};


CommuteThroughSNullInt={ChargeCurrent,ChargeCurrentpert,ChargeDipole,ChargeDipolepert,ChargeQuadPole,ChargeQuadPolepert,acc,acc1d};


SIntExclusion=(CurrentDens | CurrentDenspert);


(* ::Subsection:: *)
(*Sum rules import*)


<<"Sumrules.m"


(* ::Subsection:: *)
(*Tensor import*)


<<"EnMTensors.m"


(* ::Subsection:: *)
(*Self field derivation*)


(* ::Text:: *)
(*This import takes a few minutes, due to some internal computations. please be patient. In future releases, I'll include a cache to speed this up if you just want the later results.*)


<<"SelfField.m"


(* ::Subsection:: *)
(*Exact Computations*)


(* ::Subsubsection:: *)
(*Equations of motion - Stress Energy Divergence*)


(* ::Text:: *)
(*So, we need to first expand this out, and split out the components of the uncontracted index.*)


SEDivkCompExact=(((Basis[-b,{k,Fra3}]CD[-a][SE[a,b]])//AbstractToBasis[Ret]//ChangeCovD//AbstractToBasis[Ret]//ExpandAll//Ret31Split)
					//ChristoffelPreCompute)/.RetFrameVectorRules//BasisCanon[NoMetriconVBundle]


SEDiv0FraCompExact=((Ret31Split[Basis[-{b,Ret},{0,Fra}]*(AbstractToBasis[Ret][CD[-a][SE[a,b]]//ChangeCovD]//BreakChristoffel)//ExpandAll]//ChristoffelPreCompute)/.RetFrameVectorRules
			//NoScalar//ExpandAll//BasisCanon[NoMetriconVBundle])


SEDiv0RetCompExact=((Ret31Split[Basis[-{b,Ret},{0,Ret}]*(AbstractToBasis[Ret][CD[-a][SE[a,b]]//ChangeCovD]//BreakChristoffel)//ExpandAll]//ChristoffelPreCompute)/.RetFrameVectorRules
			//NoScalar//ExpandAll//BasisCanon[NoMetriconVBundle])


(* ::Text:: *)
(*I will now try a super brief version:*)


SEConsEqkFra=CD[{-a,-Fra}][SE[{a,Fra},{k,Fra3}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll


Coefficient[Series[SEConsEqkFra,{\[Epsilon],0,4}],\[Epsilon]^4]//NoScalar


Coefficient[Series[%1433,{\[Epsilon],0,4}],\[Epsilon]^4]//NoScalar//BasisCanon[NoMetriconVBundle]


?ToRettauFrameiderivs


CD[{-a,-Fra}][SE[{a,Fra},{k,Fra3}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll//Series[#,{\[Epsilon],0,2}]&//Normal//ExpandAll


PD[{-i,-Fra3}][r[]]


Basis[{-0,-Fra},{0,Ret}]/.RetFrameVectorRules


Basis[{-0,-Fra},{j,Ret3}]/.RetFrameVectorRules


Basis[{-i,-Fra3},{0,Ret}]/.RetFrameVectorRules


Basis[{-i,-Fra3},{j,Ret3}]/.RetFrameVectorRules


SEConsEq0Fra=CD[{-a,-Fra}][SE[{a,Fra},{0,Fra}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll


Basis[{0,Ret},{-a,-Fra}]SE[{a,Fra},{k,Fra3}]//Frame31Split//RetCanon


(((CD[{-a,-Fra}][SE[{a,Fra},{k,Fra3}]]//Frame31Split//FrameCDtoPD)
	/.{PD[{0,-Fra}][exp_]:>Basis[{0,-Fra},{a,Ret}]PD[{-a,-Ret}][exp],PD[{-j_,-Fra3}][exp_]:>Basis[{-j,-Fra3},{a,Ret}]PD[{-a,-Ret}][exp]})
	//Ret31Split)/.RetFrameVectorRules//BasisCanon[NoMetriconVBundle]


CopyToClipboard[TexBreak[TexPrint[((%42)//NoScalar)/.{PD->PD}],450]]


(((CD[{-a,-Fra}][SE[{a,Fra},{0,Fra}]]//Frame31Split//FrameCDtoPD)
	/.{PD[{0,-Fra}][exp_]:>Basis[{0,-Fra},{a,Ret}]PD[{-a,-Ret}][exp],PD[{-j_,-Fra3}][exp_]:>Basis[{-j,-Fra3},{a,Ret}]PD[{-a,-Ret}][exp]})
	//Ret31Split)/.RetFrameVectorRules//BasisCanon[NoMetriconVBundle]


CopyToClipboard[TexBreak[TexPrint[((%43)//NoScalar)/.{PD->PD}],450]]


(((CD[{-a,-Fra}][CurrentDens[{a,Fra}]]//Frame31Split//FrameCDtoPD)
	/.{PD[{0,-Fra}][exp_]:>Basis[{0,-Fra},{a,Ret}]PD[{-a,-Ret}][exp],PD[{-j_,-Fra3}][exp_]:>Basis[{-j,-Fra3},{a,Ret}]PD[{-a,-Ret}][exp]})
	//Ret31Split)/.RetFrameVectorRules//BasisCanon[NoMetriconVBundle]


CopyToClipboard[TexBreak[TexPrint[((%44)//NoScalar)/.{PD->PD}],450]]


CD[{-a,-Fra}][SE[{a,Fra},{0,Fra}]]//Frame31Split//FrameCDtoPD


CD[{-a,-Fra}][CurrentDens[{a,Fra}]]//Frame31Split//FrameCDtoPD


CopyToClipboard[TexBreak[TexPrint[(()//NoScalar)/.{PD->PD}],450]]


Basis[{k,Ret3},{-i,-Fra3}]//RetCanon


CurrDivEq=CD[{-a,-Fra}][CurrentDens[{a,Fra}]]//Frame31Split//FrameCDtoPD//ToRettauFrameiderivs//ExpandAll


(* ::Section:: *)
(*Perturbative Construction*)


(* ::Subsection:: *)
(*Rule generation*)


<<"EnMRuleGeneration.m"


(* ::Subsection:: *)
(*Perturbative definitions*)


SEConsEqkFra


DefTensor[FEff[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[\(F\), \(E\)]\)"];
DefTensorPerturbation[FEffpert[LI[o],a,b],FEff[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[\(F\), \(E\)]\)"];


NZkFraSECons=((SEConsEqkFra - \[Epsilon] CurrentDens[-{a,Fra}]FExt[{k,Fra3},{a,Fra}])/.PD[{0,-Ret}][tens_]:>\[Epsilon] PD[{0,-Ret}][tens])//Frame31Split//BasisCanon[NoScreenNoMetric];


NZ0FraSECons=((SEConsEq0Fra - \[Epsilon] CurrentDens[-{a,Fra}]FExt[{0,Fra},{a,Fra}])/.PD[{0,-Ret}][tens_]:>\[Epsilon] PD[{0,-Ret}][tens])//Frame31Split//BasisCanon[NoScreenNoMetric];


NZCurrDivEq=((CurrDivEq)/.PD[{0,-Ret}][tens_]:>\[Epsilon] PD[{0,-Ret}][tens])//Frame31Split;


(* ::Subsection:: *)
(*Renormalizing Body Parameters*)


(* ::Subsubsection:: *)
(*Harte's moments*)


Perturbation[FExt[{-k,-Fra3},{0,-Fra}],1]


norm[{a,Fra}]r[]CD[{-a,-Fra}][FExt[{j,Fra3},{0,Fra}]]//Frame31Split


ToHarteSpinMomRules[0]={Mom[a_]:>HMom[a]};


FromHarteSpinMomRules[0]={HMom[a_]:>Mom[a]};


DefTensor[ConsCharge[],{M4},PrintAs->"q"];
DefTensorPerturbation[ConsChargepert[LI[o]],ConsCharge[],{M4},PrintAs->"\!\(\*OverscriptBox[\(q\), \(~\)]\)"];


ConsCharge/:PD[{0,-Fra}][ConsCharge[]]:=0;
ConsChargepert/:PD[{0,-Fra}][ConsChargepert[LI[__]]]:=0;


ConsCharge/:CD[__][ConsCharge[]]:=0;
ConsChargepert/:CD[__][ConsChargepert[__]]:=0;


ToConsChargeRules[0]={ChargeCurrent[{0,Fra}]:>ConsCharge[]};


FromConsChargeRules[0]={ConsCharge[]:>ChargeCurrent[{0,Fra}]};


ToHarteSpinMomRules[1]={Mompert[LI[1],{0,Fra}]:>HMompert[LI[1],{0,Fra}],
					   Mompert[LI[1],{i_,Fra3}]:>Module[{k,l},HMompert[LI[1],{i,Fra3}]
																-(2/3)acc[{i,Fra3}]ConsCharge[]^2],
					   Spin[inds__]:>HSpin[inds]};


FromHarteSpinMomRules[1]={HMompert[LI[1],{0,Fra}]:>Mompert[LI[1],{0,Fra}],
		  				HMompert[LI[1],{i_,Fra3}]:>Module[{k,l},Mompert[LI[1],{i,Fra3}]
																	+(2/3)acc[{i,Fra3}]ConsCharge[]^2],
				  		HSpin[inds__]:>Spin[inds]};


ToConsChargeRules[1]={
				ChargeCurrentpert[LI[1],{0,Fra}]:>Scalar[ConsChargepert[LI[1]] + accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[0],{0,Fra},{i,Fra3}] 
														+  PD[-{0,Fra}][ChargeDipolepert[LI[0],{0,Fra},{0,Fra}]] +  accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[0],{i,Fra3},{0,Fra}]]};


FromConsChargeRules[1]={
				ConsChargepert[LI[1]]:>Scalar[ChargeCurrentpert[LI[1],{0,Fra}] -  accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[0],{0,Fra},{i,Fra3}] 
														- PD[-{0,Fra}][ChargeDipolepert[LI[0],{0,Fra},{0,Fra}]] - accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[0],{i,Fra3},{0,Fra}]]};


ToHarteSpinMomRules[2]={Mompert[LI[2],{0,Fra}]:>Scalar[HMompert[LI[2],{0,Fra}]
														- (4/3) ConsCharge[] acc[{-i,-Fra3}] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
														- (4/3) ConsCharge[] acc1d[{i,Fra3}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]ChargeDipole[{j,Fra3},{0,Fra}]],
					   Mompert[LI[2],{i_,Fra3}]:>Module[{k,l},HMompert[LI[2],{i,Fra3}]
																- (8/3)acc[{i,Fra3}]ConsCharge[]ConsChargepert[LI[1]]
																+ (4/3) ConsCharge[] acc[{-k,-Fra3}] PD[{0,-Fra}][ChargeDipole[{i,Fra3},{k,Fra3}]]
																- (4/3) ConsCharge[] PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]]
																- (4/3) acc1d[{i,Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{0,Fra}]
																+ (4/15) acc[{i,Fra3}]acc[{-k,-Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{k,Fra3}]
																- (8/15) ConsCharge[] acc[{-k,-Fra3}]acc[{k,Fra3}] ChargeDipole[{0,Fra},{i,Fra3}]
																+ (4/3) ConsCharge[] acc[{i,Fra3}] acc[{-k,-Fra3}] ChargeDipole[{0,Fra},{k,Fra3}]],
					   Spinpert[LI[1],{i_,Fra3},{j_,Fra3}]:>Module[{k},HSpinpert[LI[1],{i,Fra3},{j,Fra3}]
															- (1/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3},{j,Fra3}]]
															+ (1/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{j,Fra3},{i,Fra3}]]
															- 1 acc[{i,Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{j,Fra3}] 
															+ 1  acc[{j,Fra3}]ConsCharge[] ChargeDipole[{0,Fra},{i,Fra3}]],
						Spinpert[LI[1],{i_,Fra3},{0,Fra}]:>Module[{k},HSpinpert[LI[1],{i,Fra3},{0,Fra}]
															+ (0/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
															- (1/3) ConsCharge[] acc[{-k,-Fra3}] ChargeDipole[{i,Fra3},{k,Fra3}]],
						Spinpert[LI[1],{0,Fra},{i_,Fra3}]:>Module[{k},HSpinpert[LI[1],{0,Fra},{i,Fra3}]
															- (0/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
															+ (1/3) ConsCharge[] acc[{-k,-Fra3}] ChargeDipole[{i,Fra3},{k,Fra3}]]
						};


FromHarteSpinMomRules[2]={HMompert[LI[2],{0,Fra}]:>Scalar[Mompert[LI[2],{0,Fra}]
														 + (4/3) ConsCharge[] acc[{-i,-Fra3}] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
														 + (4/3) ConsCharge[] acc1d[{i,Fra3}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]ChargeDipole[{j,Fra3},{0,Fra}]],
		  				HMompert[LI[2],{i_,Fra3}]:>Module[{k,l},Mompert[LI[2],{i,Fra3}]
																	+ (8/3)acc[{i,Fra3}]ConsCharge[]ConsChargepert[LI[1]]
																	- (4/3) ConsCharge[] acc[{-k,-Fra3}] PD[{0,-Fra}][ChargeDipole[{i,Fra3},{k,Fra3}]]
																	+ (4/3) ConsCharge[] PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]]
																	+ (4/3) acc1d[{i,Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{0,Fra}]
																	- (4/15) acc[{i,Fra3}]acc[{-k,-Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{k,Fra3}]
																	+ (8/15) ConsCharge[] acc[{-k,-Fra3}]acc[{k,Fra3}] ChargeDipole[{0,Fra},{i,Fra3}]
																	- (4/3) ConsCharge[] acc[{i,Fra3}] acc[{-k,-Fra3}] ChargeDipole[{0,Fra},{k,Fra3}]],
				  		HSpinpert[LI[1],{i_,Fra3},{j_,Fra3}]:>Module[{k},Spinpert[LI[1],{i,Fra3},{j,Fra3}]
															+ (1/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{i,Fra3},{j,Fra3}]]
															- (1/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{j,Fra3},{i,Fra3}]]
															+ 1 acc[{i,Fra3}] ConsCharge[] ChargeDipole[{0,Fra},{j,Fra3}] 
															- 1  acc[{j,Fra3}]ConsCharge[] ChargeDipole[{0,Fra},{i,Fra3}]],
						HSpinpert[LI[1],{i_,Fra3},{0,Fra}]:>Module[{k},Spinpert[LI[1],{i,Fra3},{0,Fra}]
															- (0/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
															+ (1/3) ConsCharge[] acc[{-k,-Fra3}] ChargeDipole[{i,Fra3},{k,Fra3}]],
						HSpinpert[LI[1],{0,Fra},{i_,Fra3}]:>Module[{k},Spinpert[LI[1],{0,Fra},{i,Fra3}]
															+ (0/3) ConsCharge[] PD[{0,-Fra}][ChargeDipole[{0,Fra},{i,Fra3}]]
															- (1/3) ConsCharge[] acc[{-k,-Fra3}] ChargeDipole[{i,Fra3},{k,Fra3}]]};


ToConsChargeRules[2]={
				ChargeCurrentpert[LI[2],{0,Fra}]:>Scalar[ConsChargepert[LI[2]]									    
										+ 2 PD[-{0,Fra}][ChargeDipolepert[LI[1],{0,Fra},{0,Fra}]]
										+ 2 accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[1],{i,Fra3},{0,Fra}]
										+ 2 accpert[LI[0],-{k,Fra3}]ChargeDipolepert[LI[1],{0,Fra},{k,Fra3}] 
										- 2 accpert[LI[0],-{i,Fra3}]accpert[LI[0],{i,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{0,Fra},{0,Fra}]
										- 2 accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{j,Fra3}]
										- (12/3)accpert[LI[0],-{i,Fra3}]PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{0,Fra}]]
										-  PD[-{0,Fra}][PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{0,Fra},{0,Fra},{0,Fra}]]]
										+ (2/3)acc1dpert[LI[0],-{i,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{0,Fra},{0,Fra}]
										- (2/3)accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{j,Fra3},{0,Fra}]
										+ (4/3)accpert[LI[0],-{i,Fra3}]PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{i,Fra3},{0,Fra},{0,Fra}]]
										- 2 acc1dpert[LI[0],-{i,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{0,Fra}]
										- (10/3)accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{j,Fra3},{0,Fra}]
										+4*accpert[LI[0], {-i, -Fra3}]*CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}]
																PD[{0, -Fra}][ChargeQuadPolepert[LI[0], {j, Fra3}, {i, Fra3}, {k, Fra3}]]
										-(4/3)*accpert[LI[0], {-i, -Fra3}]*PD[{0, -Fra}][ChargeQuadPolepert[LI[0], {i, Fra3}, {0, Fra}, {0, Fra}]]
										+2 acc1dpert[LI[0], {-i, -Fra3}]*CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}]*ChargeQuadPolepert[LI[0], {j, Fra3}, {i, Fra3}, {k, Fra3}]
										-(2/3) acc1dpert[LI[0], {-i, -Fra3}]*ChargeQuadPolepert[LI[0], {i, Fra3}, {0,Fra}, {0, Fra}]]};


FromConsChargeRules[2]={
				ConsChargepert[LI[2]]:>Scalar[ChargeCurrentpert[LI[2],{0,Fra}]
										- 2 PD[-{0,Fra}][ChargeDipolepert[LI[1],{0,Fra},{0,Fra}]]
										- 2 accpert[LI[0],-{i,Fra3}]ChargeDipolepert[LI[1],{i,Fra3},{0,Fra}]
										- 2 accpert[LI[0],-{k,Fra3}]ChargeDipolepert[LI[1],{0,Fra},{k,Fra3}] 
										+ 2 accpert[LI[0],-{i,Fra3}]accpert[LI[0],{i,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{0,Fra},{0,Fra}]
										+ 2 accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{j,Fra3}]
										+ (12/3)accpert[LI[0],-{i,Fra3}]PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{0,Fra}]]
										+  PD[-{0,Fra}][PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{0,Fra},{0,Fra},{0,Fra}]]]
										- (2/3)acc1dpert[LI[0],-{i,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{0,Fra},{0,Fra}]
										+ (2/3)accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{j,Fra3},{0,Fra}]
										- (4/3)accpert[LI[0],-{i,Fra3}]PD[-{0,Fra}][ChargeQuadPolepert[LI[0],{i,Fra3},{0,Fra},{0,Fra}]]
										+ 2 acc1dpert[LI[0],-{i,Fra3}]ChargeQuadPolepert[LI[0],{0,Fra},{i,Fra3},{0,Fra}]
										+ (10/3)accpert[LI[0],-{i,Fra3}]accpert[LI[0],-{j,Fra3}]ChargeQuadPolepert[LI[0],{i,Fra3},{j,Fra3},{0,Fra}]
										-4*accpert[LI[0], {-i, -Fra3}]*CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}]
																PD[{0, -Fra}][ChargeQuadPolepert[LI[0], {j, Fra3}, {i, Fra3}, {k, Fra3}]]
										+(4/3)*accpert[LI[0], {-i, -Fra3}]*PD[{0, -Fra}][ChargeQuadPolepert[LI[0], {i, Fra3}, {0, Fra}, {0, Fra}]]
										-2 acc1dpert[LI[0], {-i, -Fra3}]*CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}]*ChargeQuadPolepert[LI[0], {j, Fra3}, {i, Fra3}, {k, Fra3}]
										+(2/3) acc1dpert[LI[0], {-i, -Fra3}]*ChargeQuadPolepert[LI[0], {i, Fra3}, {0,Fra}, {0, Fra}]]};


SpinSup:={RSpin[{i_,Fra3},{0,Fra}]:>Module[{j,k},0],
		  RSpin[{0,Fra},{i_,Fra3}]:>Module[{j,k},0],
		  RSpinpert[LI[o_],{i_,Fra3},{0,Fra}]:>0,
		  RSpinpert[LI[o_],{0,Fra},{i_,Fra3}]:>0}


FromHarteSpinMom[order_][expr_]:=expr//.(Join@@FromHarteSpinMomRules/@Range[0,order]);


ToHarteSpinMom[order_][expr_]:=expr//.(Join@@ToHarteSpinMomRules/@Range[0,order]);


FromConsCharge[order_][expr_]:=expr//.(Join@@FromConsChargeRules/@Range[0,order]);


ToConsCharge[order_][expr_]:=expr//.(Join@@ToConsChargeRules/@Range[0,order]);


(* ::Subsubsection:: *)
(*Renormalized tensors*)


(* ::Text:: *)
(*RDipole - The renormalized dipole moment*)


DefTensor[RDipole[a,b],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensorPerturbation[RDipolepert[LI[o],a,b],RDipole[a,b],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];


RDipole[a_,{0,Fra}]:=0;


(* ::Text:: *)
(*Both dipoles require the correction associated with the time derivative change from spatial to null surfaces. The antisymmetric one also requires the removal of the symmetric part.*)


SubRDipole={ChargeDipole[a_,{i_,Fra3}]:>RDipole[a,{i,Fra3}],ChargeDipole[a_,{i_,-Fra3}]:>RDipole[a,{i,-Fra3}],
			  ChargeDipolepert[LI[1],{0,Fra},{i_,Fra3}]:>(RDipolepert[LI[1],{0,Fra},{i,Fra3}] + (CD[{0,-Fra}][ChargeQuadPole[{0,Fra},{i,Fra3},{0,Fra}]]//ScaledFrameCDtoPD)),
			   ChargeDipolepert[LI[1],{k_,Fra3},{l_,Fra3}]:>(RDipolepert[LI[1],{k,Fra3},{l,Fra3}] + (CD[{0,-Fra}][ChargeQuadPole[{k,Fra3},{l,Fra3},{0,Fra}]]//ScaledFrameCDtoPD))};


(ChargeDipolepert[LI[1],{k,Fra3},{i,Fra3}]/.SubRDipole)


CD[{0,-Fra}][CurrentDens[{0,Fra}]]//FrameCDtoPD


CD[{0,-Fra}][CurrentDens[{k,Fra3}]]//FrameCDtoPD


(ChargeDipolepert[LI[1],{0,Fra},{i,Fra3}]/.SubRDipole)


Basis[{0,-Fra},{a,Ret}]PD[{-a,-Ret}][CurrentDens[{0,Fra}]]//Ret31Split//RetCanon


PD[{0,-Fra}][r[] norm[{i,Fra3}]]//NoScalar//BasisCanon[NoMetriconVBundle]


PD[{-j,-Ret3}][r[]^3 norm[{i,Fra3}]]//BasisCanon[NoMetriconVBundle]


DefTensor[RMass[],{M4},PrintAs->"m"];
DefTensorPerturbation[RMasspert[LI[o]],RMass[],{M4},PrintAs->"m"];


DefTensor[RQuadrupole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];


SubResQuadrupole={ChargeQuadPole[a_,{i_,Fra3},{j_,Fra3}]:>RQuadrupole[a,{i,Fra3},{j,Fra3}],
					ChargeQuadPole[a_,{0,Fra},{0,Fra}]:>Module[{i,j},RQuadrupole[a,{i,Fra3},{j,Fra3}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]]};


RQuadrupole[a_,{0,Fra},b_]:=0;
RQuadrupole[a_,b_,{0,Fra}]:=0;


(* ::Text:: *)
(*Note: As written, this yeilds an incorrect solution when applied to an expression in which there is a covariant derivative of the renormalized momentum (rather than a partial derivative)*)


(* ::Text:: *)
(*In the code I call this an 'inertial mass', where in the paper it was referred to as a 'restricted mass' - same thing*)


RMassSub={HMom[{0,Fra}]:>RMass[],
				HMompert[LI[1],{0,Fra}]:>Module[{k,l},RMasspert[LI[1]] - FExt[{k,Fra3},{0,Fra}]ChargeDipole[{l,Fra3},{0,Fra}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]],
				HMompert[LI[2],{0,Fra}]:>Module[{j,k,l},RMasspert[LI[2]] - 2 FExt[{k,Fra3},{0,Fra}]ChargeDipolepert[LI[1],{l,Fra3},{0,Fra}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]
											+(4/3)(ConsCharge[] acc1d[{k,Fra3}] CDelta[-Fra3,-Fra3][{-k,-Fra3},{-l,-Fra3}]ChargeDipole[{l,Fra3},{0,Fra}])
											- 2 ChargeQuadPole[{k,Fra3},{l,Fra3},{0,Fra}]CD[{-l,-Fra3}][FExt[{j,Fra3},{0,Fra}]]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-j,-Fra3}]
											+ 2 acc[{-k,-Fra3}]ChargeQuadPole[{j,Fra3},{k,Fra3},{0,Fra}]FExt[{l,Fra3},{0,Fra}]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-l,-Fra3}]]};


DefTensor[RSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)], \(R\)]\)"];
DefTensorPerturbation[RSpinpert[LI[o],a,b],RSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)], \(R\)]\)"];


HToRSpin={HSpinpert[LI[1],{k_,Fra3},{m_,Fra3}]:>Module[{i,j},RSpinpert[LI[1],{k,Fra3},{m,Fra3}]
													+ ChargeQuadPole[{i,Fra3},{m,Fra3},{0,Fra}] CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] FExt[{k,Fra3},{j,Fra3}]
													- ChargeQuadPole[{i,Fra3},{k,Fra3},{0,Fra}] CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] FExt[{m,Fra3},{j,Fra3}]
													- ChargeQuadPole[{0,Fra},{m,Fra3},{0,Fra}]  FExt[{k,Fra3},{0,Fra}]
													+ ChargeQuadPole[{0,Fra},{k,Fra3},{0,Fra}]  FExt[{m,Fra3},{0,Fra}]],
			HSpinpert[LI[1],{k_,Fra3},{0,Fra}]:>Module[{i,j},RSpinpert[LI[1],{k,Fra3},{0,Fra}]
												- ChargeQuadPole[{0,Fra},{0,Fra},{0,Fra}]FExt[{k,Fra3},{0,Fra}]
												+ ChargeQuadPole[{i,Fra3},{k,Fra3},{0,Fra}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] FExt[{j,Fra3},{0,Fra}]
												+ ChargeQuadPole[{i,Fra3},{0,Fra},{0,Fra}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]FExt[{k,Fra3},{j,Fra3}]],
			HSpinpert[LI[1],{0,Fra},{k_,Fra3}]:>Module[{i,j},RSpinpert[LI[1],{0,Fra},{k,Fra3}]
												+ ChargeQuadPole[{0,Fra},{0,Fra},{0,Fra}]FExt[{k,Fra3},{0,Fra}]
												- ChargeQuadPole[{i,Fra3},{k,Fra3},{0,Fra}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] FExt[{j,Fra3},{0,Fra}]
												- ChargeQuadPole[{i,Fra3},{0,Fra},{0,Fra}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}]FExt[{k,Fra3},{j,Fra3}]]
};


(* ::Subsubsection:: *)
(*Derivative utilities for multipoles*)


DefTensor[DChargeDipole[a,b],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)Q"];
DefTensor[DDChargeDipole[a,b],{M4},PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)Q"];
ConvertToDChargeDipole[expr_]:=expr/.{PD[{0,-Fra}][ChargeDipole[inds__]]:>(PD[{0,-Fra}][ChargeDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][ChargeDipole[inds__]]:>DChargeDipole[inds]};
ConvertToDDChargeDipole[expr_]:=expr/.{PD[{0,-Fra}][DChargeDipole[inds__]]:>(PD[{0,-Fra}][DChargeDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DChargeDipole[inds__]]:>DDChargeDipole[inds]};


AntisymmetrizeDipole={ChargeDipole[{a_,Fra3},{b_,Fra3}]:>Antisymmetrize[ChargeDipole[{a,Fra3},{b,Fra3}],{a,b}]}/.{PD[ind_][FExt[inds__]]:>(PD[ind][FExt[inds]]//ScaledFramePDtoCD)};


DefTensor[DChargeQuadPole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)Q"];
DefTensor[DDChargeQuadPole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)Q"];
ConvertToDChargeQuadPole[expr_]:=expr/.{PD[{0,-Fra}][ChargeQuadPole[inds__]]:>(PD[{0,-Fra}][ChargeQuadPole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][ChargeQuadPole[inds__]]:>DChargeQuadPole[inds]};
ConvertToDDChargeQuadPole[expr_]:=expr/.{PD[{0,-Fra}][DChargeQuadPole[inds__]]:>(PD[{0,-Fra}][DChargeQuadPole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DChargeQuadPole[inds__]]:>DDChargeQuadPole[inds]};


DefTensor[DRDipole[a,b],{M4},PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensor[DDRDipole[a,b],{M4},PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
ConvertToDRDipole[expr_]:=expr/.{PD[{0,-Fra}][RDipole[inds__]]:>(PD[{0,-Fra}][RDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][RDipole[inds__]]:>DRDipole[inds]};
ConvertToDDRDipole[expr_]:=expr/.{PD[{0,-Fra}][DRDipole[inds__]]:>(PD[{0,-Fra}][DRDipole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DRDipole[inds__]]:>DDRDipole[inds]};


FullConvertToDRDipole[n_][expr_]:=(expr//Nest[(#//ConvertToDRDipole//BasisCanon[NoMetriconVBundle])&,#,n]&
										 //Nest[(#//ConvertToDDRDipole//BasisCanon[NoMetriconVBundle])&,#,n-1]&
										//Nest[(#//ConvertToDRDipole//BasisCanon[NoMetriconVBundle])&,#,n-2]&);


AntisymmetrizeRDipole={RDipole[{a_,Fra3},{b_,Fra3}]:>Antisymmetrize[RDipole[{a,Fra3},{b,Fra3}],{a,b}]}/.{PD[ind_][FExt[inds__]]:>(PD[ind][FExt[inds]]//ScaledFramePDtoCD)};


DRDipole[a_,{0,Fra}]:=Module[{k},acc[{-k,-Fra3}]RDipole[a,{k,Fra3}]];
DDRDipole[a_,{0,Fra}]:=Module[{k},acc1d[{-k,-Fra3}]RDipole[a,{k,Fra3}]];


DefTensor[DRQuadrupole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SubscriptBox[\(D\), \(\[Tau]\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
DefTensor[DDRQuadrupole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"\!\(\*SuperscriptBox[SubscriptBox[\(D\), \(\[Tau]\)], \(2\)]\)\!\(\*SubscriptBox[OverscriptBox[\(Q\), \(~\)], \(R\)]\)"];
ConvertToDRQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][RQuadrupole[inds__]]:>(PD[{0,-Fra}][RQuadrupole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][RQuadrupole[inds__]]:>DRQuadrupole[inds]};
ConvertToDDRQuadrupole[expr_]:=expr/.{PD[{0,-Fra}][DRQuadrupole[inds__]]:>(PD[{0,-Fra}][DRQuadrupole[inds]]//ScaledFramePDtoCD)}/.{CD[{0,-Fra}][DRQuadrupole[inds__]]:>DDRQuadrupole[inds]};


DRQuadrupole/:DRQuadrupole[a_,b_,{0,Fra}]:=Module[{i},acc[{-i,-Fra3}]RQuadrupole[a,b,{i,Fra3}]];


FullConvertToDRQuadrupole[n_][expr_]:=(expr//Nest[(#//ConvertToDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n]&
										 //Nest[(#//ConvertToDDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n-1]&
										//Nest[(#//ConvertToDRQuadrupole//BasisCanon[NoMetriconVBundle])&,#,n-2]&);


(* ::Text:: *)
(*Just in case it's still useful to take advantage of the antisymmetry in the spatial indices:*)


DefTensor[DFExt[a,b,c],{M4}];


CovDFext[expr_]:=((expr/.{CD[a_][FExt[inds__]]:>DFExt[a,inds]}
					 /.{PD[a_][DFExt[inds__]]:>(PD[a][DFExt[inds]]//ScaledFramePDtoCD),
						PD[a_][PD[b_][FExt[inds__]]]:>(PD[a][PD[b][FExt[inds]]]//ScaledFramePDtoCD),
						PD[a_][FExt[inds__]]:>(PD[a][FExt[inds]]//ScaledFramePDtoCD)}/.{DFExt[a_,b_,c_]:>CD[a][FExt[b,c]]})
					/.{CD[{i_,-Fra3}][CD[{0,-Fra}][FExt[inds__]]]:>CD[{0,-Fra}][CD[{i,-Fra3}][FExt[inds]]]});


(* ::Subsection:: *)
(*Cascaded rule generation and application*)


ClearAll[NZEoMRules];
ClearAll[NZSumEoMRules];
ClearAll[NZUnprocRules];
ClearAll[NZDerivRules];


NZDerivRules[n_]={};
NZUnprocRules[n_]={};
NZSumEoMRules[n_]={};
NZEoMRules[n_]={};


ClearAll[GeneratedDerivRules]


GeneratedDerivRules[_]:={};


ApplyEoMRules[mm_?IntegerQ][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
	For[ii=mm,ii>=0,ii--,
		NewTempExpr=TempExpr/.NZEoMRules[ii]//ExpandAll;
		NewTempExpr=NewTempExpr//ApplySumRuleList[NZSumEoMRules[ii]]//ExpandAll;
		While[!(NewTempExpr===TempExpr),
			TempExpr=NewTempExpr;
			NewTempExpr=TempExpr/.NZEoMRules[ii]//ExpandAll;
			NewTempExpr=NewTempExpr//ApplySumRuleList[NZSumEoMRules[ii]]//ExpandAll;];
	];
	Return[TempExpr//BasisCanon[NoScreenNoMetric]];];


RepeatedApplyAllBodyParams[maxRepeats_][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
				NewTempExpr=(TempExpr//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);
				For[ii=0,ii<maxRepeats,ii++,
					If[NewTempExpr==TempExpr,Return[NewTempExpr];];
					TempExpr=NewTempExpr;
					NewTempExpr=(TempExpr//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);];
				Return[NewTempExpr];];


ApplyAllRules[order_][expr_]:=Module[{TempExpr=expr,ii,NewTempExpr},
		NewTempExpr=(TempExpr/.Join@@(MomRules[#]&/@Range[0,order])//ExpandAll);
		For[ii=0,ii<order,ii++,
			NewTempExpr=(NewTempExpr//ApplyEoMRules[order]//ApplyAllBodyParams)/.SIntNullRules/.Join@@(MomRules[#]&/@Range[0,order]);];
		NewTempExpr=NewTempExpr//ApplyEoMRules[order]//ApplyAllBodyParams;
	Return[NewTempExpr//BasisCanon[NoScreenNoMetric]];];


DiscardInvR:={R[]^n_/;n<0:>0};


(* ::Subsection:: *)
(*General evaluation functions*)


MaxOrder=3;


Maxwell0Fra=(met[a,b]CD[-a][Fstr[-b,{0,-Fra}]])//AbstractToBasis[Fra]//Frame31Split//ScaleDerivs//ScaledFrameCDtoPD;


MaxwellkFra=(met[a,b]CD[-a][Fstr[-b,{-k,-Fra3}]])//AbstractToBasis[Fra]//Frame31Split//ScaleDerivs//ScaledFrameCDtoPD;


NZ0FraSEConsOrder[0]:=NZ0FraSECons/.\[Epsilon]->0;
NZ0FraSEConsOrder[order_?IntegerQ]/;order>0:=(Perturb[(NZ0FraSECons),order]//ExpandAll//Series[#,{\[Epsilon],0,order}]&//Coefficient[#,\[Epsilon]^order]&)//ExpandAll//NoScalar;
NZkFraSEConsOrder[0]:=NZkFraSECons/.\[Epsilon]->0;
NZkFraSEConsOrder[order_?IntegerQ]/;order>0:=(Perturb[(NZkFraSECons),order]//ExpandAll//Series[#,{\[Epsilon],0,order}]&//Coefficient[#,\[Epsilon]^order]&)//ExpandAll//NoScalar;
NZCurrDivEqOrder[0]:=NZCurrDivEq/.\[Epsilon]->0;
NZCurrDivEqOrder[order_?IntegerQ]/;order>0:=(Perturb[(NZCurrDivEq),order]//ExpandAll//Series[#,{\[Epsilon],0,order}]&//Coefficient[#,\[Epsilon]^order]&)//ExpandAll//NoScalar;


NZ0FraSEConsOrderMoment[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]/;order>0:=((((
			(IntNull[((NZ0FraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//Perturb[#,order]&//ExpandAll
				//Series[#,{\[Epsilon],0,order}]&//Normal)/.ApplyPtoFExt]//NoScalar)//.nstoNsrule//.NullIntparts//.nstoNsrule)//ExpandAll//Coefficient[#,\[Epsilon]^order]&)
				/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZ0FraSEConsOrderMoment[0][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=(((
			((IntNull[((NZ0FraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//ExpandAll//Normal)/.\[Epsilon]->0]//NoScalar)//.nstoNsrule
				//.NullIntparts//.nstoNsrule)//ExpandAll)/.\[Epsilon]->0/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZkFraSEConsOrderMoment[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]/;order>0:=((((
			(IntNull[((NZkFraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//Perturb[#,order]&//ExpandAll
				//Series[#,{\[Epsilon],0,order}]&//Normal)/.ApplyPtoFExt]//NoScalar)//.nstoNsrule//.NullIntparts//.nstoNsrule)//ExpandAll//Coefficient[#,\[Epsilon]^order]&)
				/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZkFraSEConsOrderMoment[0][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=(((
			((IntNull[((NZkFraSECons * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//ExpandAll//Normal)/.\[Epsilon]->0]//NoScalar)//.nstoNsrule
				//.NullIntparts//.nstoNsrule)//ExpandAll)/.\[Epsilon]->0/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);	
NZCurrDivEqOrderMoment[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]/;order>0:=((((
			(IntNull[((NZCurrDivEq * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//Perturb[#,order]&//ExpandAll
				//Series[#,{\[Epsilon],0,order}]&//Normal)/.ApplyPtoFExt]//NoScalar)//.nstoNsrule//.NullIntparts//.nstoNsrule)//ExpandAll//Coefficient[#,\[Epsilon]^order]&)
				/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);
NZCurrDivEqOrderMoment[0][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=(((
			((IntNull[((NZCurrDivEq * r[]^rMoment * (Ns[Sequence@@({#,Fra3}&/@(Unique/@(n&/@Range[NsMoment])))]))//ExpandAll//Normal)/.\[Epsilon]->0]//NoScalar)//.nstoNsrule
				//.NullIntparts//.nstoNsrule)//ExpandAll)/.\[Epsilon]->0/.SurfaceFieldRules)//Map[(BasisCanon[NoScreenNoMetric][Expand[#]]&),#]&//BasisCanon[NoMetriconVBundle]);


NZ0FraSEConsOrderMomentEoM[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=((NZ0FraSEConsOrderMoment[order][NsMoment][rMoment]//ApplyEoMRules[order])/.SIntNullRules);
NZkFraSEConsOrderMomentEoM[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=((NZkFraSEConsOrderMoment[order][NsMoment][rMoment]//ApplyEoMRules[order])/.SIntNullRules);
NZCurrDivEqOrderMomentEoM[order_?IntegerQ][NsMoment_?IntegerQ][rMoment_?IntegerQ]:=((NZCurrDivEqOrderMoment[order][NsMoment][rMoment]//ApplyEoMRules[order])/.SIntNullRules);


(* ::Text:: *)
(*At each order, we'd like to confirm the maxwell field equation through  1/r^3-order *)


Maxwell0FraConfirmation[0]:=(((Qerturb[Perturb[Maxwell0Fra,0],3]//ExpandAll)/.{Fstr[__]:>0,Fstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]:>0}
														/.FstrfieldRulespert//ExpandAll)/.{\[Epsilon]:>0}//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[0]//ApplyAllBodyParams)/.{\[Epsilon]:>0};
Maxwell0FraConfirmation[order_?IntegerQ]/;order>0:=(((Qerturb[Perturb[Maxwell0Fra,order],3-order]//ExpandAll)/.{Fstr[__]:>0,Fstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]^n_/;n>order:>0}
														/.FstrfieldRulespert//ExpandAll)//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[order]//ApplyAllBodyParams);
MaxwellkFraConfirmation[0]:=(((Qerturb[Perturb[MaxwellkFra,0],3]//ExpandAll)/.{Fstr[__]:>0,Fstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]:>0}
														/.FstrfieldRulespert//ExpandAll)/.{\[Epsilon]:>0}//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[0]//ApplyAllBodyParams)/.{\[Epsilon]:>0};
MaxwellkFraConfirmation[order_?IntegerQ]/;order>0:=(((Qerturb[Perturb[MaxwellkFra,order],3-order]//ExpandAll)/.{Fstr[__]:>0,Fstrpert[LI[n_?IntegerQ],__]:>0,q->1}/.{\[Epsilon]^n_/;n>order:>0}
														/.FstrfieldRulespert//ExpandAll)//BasisCanon[NoScreenNoMetric]//ReverseBodyParams
														//ApplyEoMRules[order]//ApplyAllBodyParams);


RegenEoMs=True;


OmitMomentumFromRules=True;


Afieldr[{0,Fra}]/.ScaledAfieldRules


Afieldr[{i,Fra3}]/.ScaledAfieldRules


(* ::Section:: *)
(*Order-by-order field equation expansion*)


(* ::Subsection:: *)
(*0th-order computations*)


(* ::Subsubsection:: *)
(*0th - Order Computations  - Spatial Components*)


(* ::Text:: *)
(*Uncomment to print them all:*)


(*For[inti=0,inti<=4,inti++,
For[intj=0,intj<=4,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[0][inti][intj]//ScreenDollarIndices//Timing];
Print["======"];
Print[NZkFraSEConsOrderMoment[0][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


(* ::Text:: *)
(*Included in the accompanying paper are the outputs for NZkFraSEConsOrderMoment[0][1][1], [0][1], [1][2], [2][2]*)


NZkFraSEConsOrderMomentEoM[0][0][1]


MomRules[0]={};
tempEoM=NZkFraSEConsOrderMomentEoM[0][0][1];
For[ii=0,ii<=3,ii++,
	MomRules[0]=MomRules[0]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];//Timing


(* ::Text:: *)
(*This would be a good candidate for parallelization, but so far it seems like xTensor breaks under standard mathematica parallelization methods*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM0spac.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZSumEoMRulesEM0spac.mx"]||RegenEoMs,
For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
tempEoM=NZkFraSEConsOrderMomentEoM[0][inti][intj];
For[intk=3,intk>=0,intk--,
	If[!(inti===0 &&intj===1 &&OmitMomentumFromRules),
		NZEoMRules[0]=DeleteDuplicates[NZEoMRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
		NZSumEoMRules[0]=DeleteDuplicates[NZSumEoMRules[0]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM0spac.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZSumEoMRulesEM0spac.mx",NZSumEoMRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM0spac.mx"];
DumpGet["~/.EMSelfForceCache/NZSumEoMRulesEM0spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*0th - Order Computations  - Time component*)


(* ::Text:: *)
(*Function to print them all:*)


(*For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
Print["----"];
Print[NZ0FraSEConsOrderMomentEoM[0][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZ0FraSEConsOrderMoment[0][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


(* ::Text:: *)
(*Otherwise, just go ahead and evaluate each, and take what we can for the rules:*)


tempEoM1=NZ0FraSEConsOrderMoment[0][1][1];
tempEoM2=NZ0FraSEConsOrderMoment[0][0][1];
For[ii=0,ii<=3,ii++,
MomRules[0]=(MomRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM1,ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM2,ii])//GenerateNewDummies]);
];


(* ::Text:: *)
(*Included in the accompanying paper are the outputs for NZ0FraSEConsOrderMoment[0][1][1], [0][1], [1][2], [2][2]*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM0time.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZSumEoMRulesEM0time.mx"]||RegenEoMs,
For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
tempEoM=NZ0FraSEConsOrderMomentEoM[0][inti][intj];
For[intk=3,intk>=0,intk--,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),		
	NZEoMRules[0]=DeleteDuplicates[NZEoMRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[0]=DeleteDuplicates[NZSumEoMRules[0]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM0time.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZSumEoMRulesEM0time.mx",NZSumEoMRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM0time.mx"];
DumpGet["~/.EMSelfForceCache/NZDerivRulesEM0time.mx"];
];//Timing


(* ::Subsubsection:: *)
(*0th - Order Computations  - Current Conservation*)


(* ::Text:: *)
(*Function to print them all:*)


(* ::Text:: *)
(*Vanishing leading Current:*)


NZCurrDivEqOrderMoment[0][1][1]


(*For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
Print["----"];
Print[NZCurrDivEqOrderMomentEoM[0][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZCurrDivEqOrderMoment[0][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


(* ::Text:: *)
(*Inlcuded in the accompanying papar are NZCurrDivEqOrderMoment[0][1][1], [2][2], [1][3], and [3][3].*)


CurrentRules[0]={};
CurrentRules[0]=CurrentRules[0]~Join~GenerateRulesFromEoM[NZCurrDivEqOrderMomentEoM[0][1][1]//ExpandAll//GenerateNewDummies];
CurrentRules[0]=CurrentRules[0]~Join~{ChargeCurrent[{i_,Fra3}]->(((ChargeCurrent[{i,Fra3}]//ReverseBodyParams)/.CurrentRules[0])//ExpandAll//ApplyAllBodyParams)};


QuadTraceRule:={CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]ChargeQuadPole[{i_,Fra3},{j_,Fra3},{k_,Fra3}]:>-(1/2)ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}],
				CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]ChargeQuadPole[{i_,Fra3},{k_,Fra3},{j_,Fra3}]:>-(1/2)ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}],
				CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]PD[ind_][ChargeQuadPole[{i_,Fra3},{j_,Fra3},{k_,Fra3}]]:>
																	-(1/2)PD[ind][ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}]],
				CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]PD[ind__][ChargeQuadPole[{i_,Fra3},{k_,Fra3},{j_,Fra3}]]:>
																	-(1/2)PD[ind][ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}]],
				CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]PD[ind1_][PD[ind_][ChargeQuadPole[LI[0],{i_,Fra3},{j_,Fra3},{k_,Fra3}]]]:>
																	-(1/2)PD[ind1][PD[ind][ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}]]],
				CDelta[-Fra3,-Fra3][-{i_,Fra3},-{j_,Fra3}]PD[ind1_][PD[ind__][ChargeQuadPole[{i_,Fra3},{k_,Fra3},{j_,Fra3}]]]:>
																	-(1/2)PD[ind1][PD[ind][ChargeQuadPole[{k,Fra3},{0,Fra},{0,Fra}]]],\[Epsilon]->0};


(* ::Text:: *)
(*Otherwise, just go ahead and evaluate each, and take what we can for the rules:*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZSumEoMRulesEM0curr.mx"]||RegenEoMs,
For[inti=0,inti<=3,inti++,
For[intj=0,intj<=3,intj++,
tempEoM=NZCurrDivEqOrderMomentEoM[0][inti][intj];
For[intk=3,intk>=0,intk--,
If[!(inti==1 && intj==1),
	NZEoMRules[0]=DeleteDuplicates[NZEoMRules[0]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[0]=DeleteDuplicates[NZSumEoMRules[0]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZCurrDivEqOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZSumEoMRulesEM0curr.mx",NZSumEoMRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx"];
DumpGet["~/.EMSelfForceCache/NZSumEoMRulesEM0curr.mx"];
];//Timing


(* ::Text:: *)
(*Now that we have more information about the momentum expression, we can do better with the body rules. This generates a new set of rules for spin and momentum replacement. (because they are non-atomic...)*)


(* ::Text:: *)
(*TODO: More optimization*)


GeneratedMomentumRules={};GeneratedMomentumSumRules={};
baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[0])/.MomRules[0];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[0])/.MomRules[0];
For[ii=0,ii<=3,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[0],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[0],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];//Timing


GeneratedSpinRules={};GeneratedSpinSumRules={};
(*baseSpinExpression0i=(((Spinpert[LI[1],{k,Fra3},{0,Fra}]//ReverseBodyParams//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1])
								-(((Spinpert[LI[1],{k,Fra3},{0,Fra}]//Renormalize[3])/.SpinSup)//RevRenormalize[3]//ExpandAll//ReverseBodyParams//ExpandAll)/.MomRules[0]/.MomRules[1]//ApplyEoMRules[1]);*)
baseSpinExpression0i=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{0,Fra}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{l,Fra3}]r[]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule/.MomRules[0])//ApplyEoMRules[0]);
baseSpinExpressionij=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{k,Fra3}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[0],{a,Fra},{l,Fra3}]r[]Ns[{k,Fra3}]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule)/.MomRules[0]//ApplyEoMRules[0]);
For[ii=0,ii<=3,ii++,
(*derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];*)
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[0],{0,Fra},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpressionij,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[0],{k,Fra3},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
];


MomentumBodyParamRules={};


MomentumBodyParamRules={HMom[{i_,Fra3}]->((HMom[{i,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)//ApplyAllRules[0]),
						Mom[{i_,Fra3}]->((Mom[{i,Fra3}]//ReverseBodyParams)//ApplyAllRules[0])};


ApplyAllBodyParams[expr_]:=(expr/.ChargeMultipoleRules/.GeneratedMomentumRules/.GeneratedSpinRules)//ApplySumRuleList[SpinMomSumRuleList~Join~GeneratedMomentumSumRules~Join~GeneratedSpinSumRules];


DefTensor[RestMass[],{M4},PrintAs->"\!\(\*OverscriptBox[\(m\), \(^\)]\)"];
DefTensorPerturbation[RestMasspert[LI[o]],RestMass[],{M4},PrintAs->"\!\(\*OverscriptBox[\(m\), \(^\)]\)"];


RestMassRules={};
RevRestMassRules={};


RestMassRules=RestMassRules~Join~
				{RestMasspert[LI[0]]->Series[Sqrt[((Perturbed[Scalar[Mom[{0,Fra}]]^2 - CDelta[-Fra3,-Fra3][{-k,-Fra3},{-j,-Fra3}]Mom[{k,Fra3}]Mom[{j,Fra3}],0])/.MomentumBodyParamRules
			//ExpandAll//NoScalar)],{\[Epsilon],0,0}]/.\[Epsilon]->0/.Sqrt[a_^2]:>a//GenerateNewDummies };
RevRestMassRules=RevRestMassRules~Join~
				{HMom[{0,Fra}]->((RestMasspert[LI[0]] - ((RestMasspert[LI[0]]/.RestMassRules) - Mom[{0,Fra}]))//NoScalar//ReverseBodyParams//BasisCanon[NoScreenNoMetric]//ApplyEoMRules[0])}


RestMassRules


(* ::Subsection:: *)
(*1st-order computations*)


(* ::Subsubsection:: *)
(*1st - Order Computations *)


accFull[1]=((((NZkFraSEConsOrderMomentEoM[1][0][0]//ApplyEoMRules[0]))//ApplyAllBodyParams)/.MomRules[0])//ScreenDollarIndices//ScaledFramePDtoCD


spinExpression=NZkFraSEConsOrderMomentEoM[1][1][1];


SpinSolution[1]=(((2*Antisymmetrize[spinExpression,IndicesOf[Free][spinExpression]]//BasisCanon[NoMetriconVBundle]))//ScreenDollarIndices);


(* ::Text:: *)
(*The equation of motion for the spin to this order*)


SpinSolution[1]//ApplyAllBodyParams//ScaledFramePDtoCD


(* ::Text:: *)
(*TODO: I think the several partials on each of these is just wasting time - test without*)


MomRules[1]={};
tempEoM=NZkFraSEConsOrderMomentEoM[1][0][1];
For[ii=0,ii<=2,ii++,
	MomRules[1]=MomRules[1]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];//Timing


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[1][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZkFraSEConsOrderMoment[1][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


If[!FileExistsQ["~/.EMSelfForceCache/NZSumEoMRulesEM1spac.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM1spac.mx"]||RegenEoMs,
For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
If[!(((inti===0 &&intj===1)) &&OmitMomentumFromRules),
tempEoM=NZkFraSEConsOrderMomentEoM[1][inti][intj];
For[intk=2,intk>=0,intk--,
	NZEoMRules[1]=DeleteDuplicates[NZEoMRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[1]=DeleteDuplicates[NZSumEoMRules[1]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZDSumEoMRulesEM1spac.mx",NZSumEoMRules];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM1spac.mx",NZEoMRules];
,
DumpGet["~/.EMSelfForceCache/NZDSumEoMRulesEM1spac.mx"];
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM1spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*1st - Order computations - time component*)


(* ::Text:: *)
(*(also the covariant derivative is zero due to the vanishing momentum, but that's irritating to automate here, so I'll just leave as is.*)


MdotFull[1]=((NZ0FraSEConsOrderMomentEoM[1][0][0]//ApplyEoMRules[0])//ApplyAllBodyParams)/.MomRules[0]//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD


For[ii=0,ii<=2,ii++,
MomRules[1]=(MomRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],NZ0FraSEConsOrderMomentEoM[1][1][1],ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],NZ0FraSEConsOrderMomentEoM[1][0][1],ii])//GenerateNewDummies]);
];


((Mompert[LI[1],{k,Fra3}]//ReverseBodyParams)/.SIntNullRules/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams//ScaledFramePDtoCD


((HMompert[LI[1],{k,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)/.SIntNullRules/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams//ScaledFramePDtoCD


(* ::Text:: *)
(*TODO:These blocks are copy-pasta code, turn it into a function and make things prettier.*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM1time.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZDerivRulesEM1time.mx"]||RegenEoMs,
For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),
	tempEoM=NZ0FraSEConsOrderMomentEoM[1][inti][intj];
For[intk=2,intk>=0,intk--,
	NZEoMRules[1]=DeleteDuplicates[NZEoMRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[1]=DeleteDuplicates[NZSumEoMRules[1]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM0time.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZDerivRulesEM0time.mx",NZDerivRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM0time.mx"];
DumpGet["~/.EMSelfForceCache/NZDerivRulesEM0time.mx"];
];//Timing


(* ::Text:: *)
(*TODO: This method of doing things has led to code duplication - write a general function and cut down on some of this*)


baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1]/.SIntNullRules//ApplyEoMRules[1];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[0]/.MomRules[1]/.SIntNullRules//ApplyEoMRules[1];
For[ii=0,ii<=2,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[1],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[1],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];


baseSpinExpression0i=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{0,Fra}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{l,Fra3}]r[]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule/.MomRules[0]/.MomRules[1])//ApplyEoMRules[1]);
baseSpinExpressionij=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]r[]Ns[{l,Fra3}]] - IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{l,Fra3}]r[]Ns[{k,Fra3}]]
														//Frame31Split)/.RetFrameVectorRules//.nstoNsrule)/.MomRules[0]/.MomRules[1]//ApplyEoMRules[1]);
For[ii=0,ii<=2,ii++,
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpression0i,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[1],{0,Fra},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
derivedSpinExpression=(Nest[PD[{0,-Fra}],baseSpinExpressionij,ii]
						-Nest[PD[{0,-Fra}],Spinpert[LI[1],{k,Fra3},{l,Fra3}],ii]);
GeneratedSpinRules=GeneratedSpinRules~Join~GenerateRulesFromEoM[derivedSpinExpression];
GeneratedSpinSumRules=GeneratedSpinSumRules~Join~GenerateSumRulesFromEoM[derivedSpinExpression];
];


MomentumBodyParamRules=MomentumBodyParamRules~Join~{HMompert[LI[1],{i_,Fra3}]->(((HMompert[LI[1],{i,Fra3}]//FromHarteSpinMom[1]//ReverseBodyParams)//ApplyAllRules[1])/.MomentumBodyParamRules)};
MomentumBodyParamRules=MomentumBodyParamRules~Join~{Mompert[LI[1],{i_,Fra3}]->((Mompert[LI[1],{i,Fra3}]//ToHarteSpinMom[1])/.MomentumBodyParamRules)};


((Sqrt[(Perturb[Mom[{0,Fra}]Mom[{0,Fra}] - Mom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]Mom[{l,Fra3}],1]
										/.{expr_*Mom[inds__]:>expr*(Mom[inds]/.MomentumBodyParamRules),expr_*Mompert[inds__]:>expr*(Mompert[inds]/.MomentumBodyParamRules)})]
										//Series[#,{\[Epsilon],0,1}]&//Normal)
										/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some}//NoScalar//Coefficient[#,\[Epsilon]]&//BasisCanon[NoMetriconVBundle]//GenerateNewDummies)


RestMassRules=RestMassRules~Join~
				{RestMasspert[LI[1]]->((Sqrt[(Perturb[Mom[{0,Fra}]Mom[{0,Fra}] - Mom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]Mom[{l,Fra3}],1]
										/.{expr_*Mom[inds__]:>expr*(Mom[inds]/.MomentumBodyParamRules),expr_*Mompert[inds__]:>expr*(Mompert[inds]/.MomentumBodyParamRules)})]
										//Series[#,{\[Epsilon],0,1}]&//Normal)/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some}
										//NoScalar//Coefficient[#,\[Epsilon]]&//BasisCanon[NoMetriconVBundle]//GenerateNewDummies)};
RevRestMassRules=RevRestMassRules~Join~
				{Mompert[LI[1],{0,Fra}]->(((RestMasspert[LI[1]] - ((RestMasspert[LI[1]]/.RestMassRules) - Mompert[LI[1],{0,Fra}])))//NoScalar//BasisCanon[NoMetriconVBundle])};


RestMassRules


RevRestMassRules


(* ::Subsubsection:: *)
(*1st - Order Computations  - Current Conservation*)


(* ::Text:: *)
(*Function to print them all:*)


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZCurrEoM[1][inti][intj]//ScreenDollarIndices//AbsoluteTiming];
Print["===="];
Print[NZCurrEoMUnprocessed[1][inti][intj]//ScreenDollarIndices//AbsoluteTiming];
];
];*)


(* ::Text:: *)
(*Otherwise, just go ahead and evaluate each, and take what we can for the rules:*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZDerivRulesEM0curr.mx"]||RegenEoMs,
For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
tempEoM=NZCurrDivEqOrderMomentEoM[1][inti][intj];
For[intk=2,intk>=0,intk--,
If[!(inti==1 && intj==1),
	NZEoMRules[1]=DeleteDuplicates[NZEoMRules[1]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[1]=DeleteDuplicates[NZSumEoMRules[1]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZCurrDivEqOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZDerivRulesEM0curr.mx",NZDerivRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM0curr.mx"];
DumpGet["~/.EMSelfForceCache/NZDerivRulesEM0curr.mx"];
];//Timing


CurrentRules[1]={};
CurrentRules[1]=CurrentRules[1]~Join~GenerateRulesFromEoM[NZCurrDivEqOrderMomentEoM[1][1][1]//ExpandAll//GenerateNewDummies];
CurrentRules[1]=CurrentRules[1]~Join~{ChargeCurrentpert[LI[1],{i_,Fra3}]->(((ChargeCurrentpert[LI[1],{i,Fra3}]//ReverseBodyParams)/.CurrentRules[1])//ExpandAll//ApplyAllBodyParams)};


MomRules[1]=MomRules[1]~Join~{PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0};


(* ::Subsection:: *)
(*2nd-order computations*)


(* ::Subsubsection:: *)
(*2nd - Order Computations - spatial*)


accRaw[2]=((((NZkFraSEConsOrderMoment[2][0][0]//ApplyEoMRules[1])/.SIntNullRules//Expand)//RepeatedApplyAllBodyParams[2])/.MomRules[1]/.MomRules[0]
							//ExpandAll//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]//ToHarteSpinMom[1])


((((accRaw[2])/.{HMompert[LI[1],{i_,Fra3}]:>(HMompert[LI[1],{i,Fra3}]/.MomentumBodyParamRules)}//Expand)
		/.CurrentRules[0]//ToHarteSpinMom[0]//Expand//NoScalar//BasisCanon[NoMetriconVBundle])
		/.{PD[ind_][FExt[inds__]]:>(PD[ind][FExt[inds]]//ScaledFramePDtoCD)})//BasisCanon[NoMetriconVBundle]


PreRestrictedAcc[2]=((((accRaw[2])/.{HMompert[LI[1],{i_,Fra3}]:>(HMompert[LI[1],{i,Fra3}]/.MomentumBodyParamRules)}//Expand)
		 /.CurrentRules[1]//ToConsCharge[1]//Expand//NoScalar//BasisCanon[NoMetriconVBundle])
		/.{PD[ind_][FExt[inds__]]:>(PD[ind][FExt[inds]]//ScaledFramePDtoCD)})//BasisCanon[NoMetriconVBundle]


(* ::Text:: *)
(*Final solution, restricted*)


((-PreRestrictedAcc[2]/.RMassSub/.SubRDipole//BasisCanon[NoMetriconVBundle])/.{Spin[___,{0,Fra},___]:>0})/.{Spin[___,{0,Fra},___]:>0}


DRDipole[{i,Fra3},{0,Fra}]


((-PreRestrictedAcc[2]/.RMassSub/.SubRDipole//BasisCanon[NoMetriconVBundle])/.{Spin[___,{0,Fra},___]:>0}//ScaledFramePDtoCD)/.{Spin[___,{0,Fra},___]:>0}


(* ::Text:: *)
(*Prototype method for extracting the expressions to T EX *)


(*CopyToClipboard[TexBreak[TexPrint[(()//NoScalar)/.{\[Epsilon]->0}/.{PD->PD}],450]]*)


(* ::Text:: *)
(*Prototype for printing out all of the equations stored into rules at this order*)


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkCompEoM[2][inti][intj]//ScreenDollarIndices];
];
];*)


spinExpression=NZkFraSEConsOrderMomentEoM[2][1][1];


SpinRaw[2]=((2*Antisymmetrize[spinExpression,IndicesOf[Free][spinExpression]]//BasisCanon[NoMetriconVBundle])/.MomRules[0]/.MomRules[1]);


SpinSolution[2]=(((SpinRaw[2]//RepeatedApplyAllBodyParams[2]//ToConsCharge[1])/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle])
		//ToHarteSpinMom[2]//ToConsCharge[1]//Expand)/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]


(SpinSolution[2]/.HToRSpin//CovDFext)/.SubRDipole/.SubResQuadrupole/.SubResQuadrupole//ScaledFramePDtoCD//BasisCanon[NoMetriconVBundle]


(Spinpert[LI[1],{i,Fra3},{0,Fra}]//ToHarteSpinMom[2])/.HToRSpin//BasisCanon[NoMetriconVBundle]


MomRules[2]={};
tempEoM=NZkFraSEConsOrderMomentEoM[2][0][1];
For[ii=0,ii<=1,ii++,
	MomRules[2]=MomRules[2]~Join~GenerateRulesFromEoM[Nest[PD[{0,-Fra}],tempEoM,ii]//ExpandAll//GenerateNewDummies];];


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZkFraSEConsOrderMomentEoM[1][inti][intj]//ScreenDollarIndices//Timing];
Print["===="];
Print[NZkFraSEConsOrderMoment[1][inti][intj]//ScreenDollarIndices//Timing];
];
];//Timing*)


If[!FileExistsQ["~/.EMSelfForceCache/NZSumEoMRulesEM2spac.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM2spac.mx"]||RegenEoMs,
For[inti=0,inti<=1,inti++,
For[intj=0,intj<=1,intj++,
If[!(((inti===0 &&intj===1)) &&OmitMomentumFromRules),
tempEoM=NZkFraSEConsOrderMomentEoM[2][inti][intj];
For[intk=1,intk>=0,intk--,
	Print[{inti,intj,intk}];
	NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[2]=DeleteDuplicates[NZSumEoMRules[2]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZDSumEoMRulesEM2spac.mx",NZSumEoMRules];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM2spac.mx",NZEoMRules];
,
DumpGet["~/.EMSelfForceCache/NZDSumEoMRulesEM2spac.mx"];
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM2spac.mx"];
];//Timing


(* ::Subsubsection:: *)
(*2nd - Order Computation  - Time Component*)


(((NZ0FraSEConsOrderMomentEoM[2][0][0]//ApplyAllBodyParams)/.MomRules[1]//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle])
	//ToConsCharge[0]//NoScalar//ExpandAll//ScaledFramePDtoCD)


MdotRaw[2]=(((NZ0FraSEConsOrderMomentEoM[2][0][0]//ApplyAllBodyParams)/.MomRules[1]//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle])
				//ToHarteSpinMom[1]//ToConsCharge[0]//NoScalar//ExpandAll)


((MdotRaw[2]/.CurrentRules[1]/.MomentumBodyParamRules//ExpandAll//BasisCanon[NoMetriconVBundle]//ToConsCharge[1])
		/.RMassSub/.SubRDipole//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD)/.{Spin[___,{0,Fra},___]:>0}


tempEoM1=NZ0FraSEConsOrderMomentEoM[2][1][1];
tempEoM2=NZ0FraSEConsOrderMomentEoM[2][0][1];
For[ii=0,ii<=1,ii++,
MomRules[2]=(MomRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM1,ii])//GenerateNewDummies]
						~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM2,ii])//GenerateNewDummies]);
];


(* ::Text:: *)
(*The k-component of the second order momentum,*)


MomkComp[2]=((Mompert[LI[2],{k,Fra3}]//ReverseBodyParams)/.MomRules[2]/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams//ApplyAllBodyParams;


(* ::Text:: *)
(*... and in a tidier form:*)


((((MomkComp[2]/.CurrentRules[1]//Expand//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle])
		//ToConsCharge[1]//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle])/.AntisymmetrizeDipole
		//BasisCanon[NoMetriconVBundle])


(* ::Text:: *)
(*The renormalized spatial, second order momentum,*)


HMomkComp[2]=((HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//ReverseBodyParams)/.MomRules[2]/.MomRules[1]//ApplyAllBodyParams)//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams;


(* ::Text:: *)
(*... and in a tidier form:*)


((1/2)HMomkComp[2]/.CurrentRules[1]//ToConsCharge[1]//NoScalar//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]


(* ::Text:: *)
(*The value of the u dot S in the new spin supplementary condition*)


-((Spinpert[LI[1],{i,Fra3},{0,Fra}]//ToHarteSpinMom[2])/.HToRSpin//BasisCanon[NoMetriconVBundle])/.{RSpinpert[___,{0,Fra},___]:>0}


(*CopyToClipboard[TexBreak[TexPrint[(%2746//NoScalar)/.{\[Epsilon]->0}/.{PD->PD}],450]]*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM2time.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZDerivRulesEM2time.mx"]||RegenEoMs,
For[inti=0,inti<=1,inti++,
For[intj=0,intj<=1,intj++,
If[!(((inti===1 &&intj===1)||(inti===0 &&intj===1)) &&OmitMomentumFromRules),
	tempEoM=NZ0FraSEConsOrderMomentEoM[2][inti][intj];
For[intk=1,intk>=0,intk--,
	NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[2]=DeleteDuplicates[NZSumEoMRules[2]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZ0FraSEConsOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM2time.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZDerivRulesEM2time.mx",NZDerivRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM2time.mx"];
DumpGet["~/.EMSelfForceCache/NZDerivRulesEM2time.mx"];
];//Timing


(* ::Text:: *)
(*TODO:Optimization/simplification by reversing body params before each rule generation above.*)


(* ::Text:: *)
(*TODO: the results from this are not totally satisfactory - we should find a way to incorporate the time-derivative of the zero component of the momentum and the spin into this*)


(* ::Text:: *)
(*No need for the second-order spin supplementary condition*)


(Basis[{0,-Fra},{a,Ret}]PD[{-a,-Ret}][CurrentDens[{i,Fra3}]]//Ret31Split)//RetCanon


MomentumBodyParamRules=MomentumBodyParamRules~Join~{HMompert[LI[2],{k_,Fra3}]->((((((HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//ReverseBodyParams)/.MomRules[2]/.MomRules[1])
												//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)/.CurrentRules[1]//ToConsCharge[1]//NoScalar
												//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams)/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]//ToHarteSpinMom[2]//ExpandAll)
												/.HToRSpin//ExpandAll//BasisCanon[NoMetriconVBundle])/.{PD[a_][FExt[inds__]]:>(PD[a][FExt[inds]]//ScaledFramePDtoCD)}//BasisCanon[NoMetriconVBundle]};


MomentumBodyParamRules=MomentumBodyParamRules~Join~{Mompert[LI[2],{k_,Fra3}]->((Mompert[LI[2],{k,Fra3}]//ToHarteSpinMom[2])/.MomentumBodyParamRules//GenerateNewDummies)};


baseMomExpression0=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[2],{a,Fra},{0,Fra}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[2])/.MomRules[2]/.MomRules[1]/.MomRules[0]/.SIntNullRules//ApplyEoMRules[2];
baseMomExpressionk=(((IntNull[Basis[{0,Ret},{-a,-Fra}]SEpert[LI[1],{a,Fra},{k,Fra3}]]//Frame31Split)/.RetFrameVectorRules/.nstoNsrule)
													//ApplyEoMRules[1])/.MomRules[2]/.MomRules[1]/.MomRules[0]/.SIntNullRules//ApplyEoMRules[2];
For[ii=0,ii<=1,ii++,
(*Print[ii];*)
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpression0,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[2],{0,Fra}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
derivedMomExpression=(Nest[PD[{0,-Fra}],baseMomExpressionk,ii]  - Nest[PD[{0,-Fra}],Mompert[LI[2],{k,Fra3}],ii]);
GeneratedMomentumRules=GeneratedMomentumRules~Join~GenerateRulesFromEoM[derivedMomExpression];
GeneratedMomentumSumRules=GeneratedMomentumSumRules~Join~GenerateSumRulesFromEoM[derivedMomExpression];
];


(* ::Text:: *)
(*Rest mass value*)


RMassvalue[2]=((((2*Sqrt[(((Perturb[Mom[{0,Fra}]Mom[{0,Fra}] - Mom[{k,Fra3}]CDelta[-Fra3,-Fra3][-{k,Fra3},-{l,Fra3}]Mom[{l,Fra3}],2])//GenerateNewDummies)
	//.{expr_*Mompert[ind__]:>expr *(Mompert[ind]/.MomentumBodyParamRules//GenerateNewDummies)})/.MomentumBodyParamRules//ExpandAll]
	//Series[#,{\[Epsilon],0,2}]&)//NoScalar//Coefficient[#,\[Epsilon]^2]&//BasisCanon[NoMetriconVBundle])
	/.{Sqrt[Scalar[some_]^2]:>some,(Scalar[some_]^2)^(-1/2):>1/some,Sqrt[some_^2]:>some,Scalar[some_]:>(some//GenerateNewDummies)}
	//Expand//ToConsCharge[1])/.{Spin[___,{0,Fra},___]:>0})//BasisCanon[NoMetriconVBundle]


(*CopyToClipboard[TexBreak[TexPrint[(%2743//NoScalar)/.{\[Epsilon]->0}/.{PD->PD}],450]]*)


RestMassRules=RestMassRules~Join~
				{RestMasspert[LI[2]]->RMassvalue[2]};//Timing
RevRestMassRules=RevRestMassRules~Join~
				{Mompert[LI[2],{0,Fra}]->(((RestMasspert[LI[2]] - ((RestMasspert[LI[2]]/.RestMassRules) - Mompert[LI[2],{0,Fra}])))//NoScalar//BasisCanon[NoMetriconVBundle])};


(* ::Subsubsection:: *)
(*2nd - Order Computations  - Current Conservation*)


(* ::Text:: *)
(*Function to print them all:*)


(*For[inti=0,inti<=2,inti++,
For[intj=0,intj<=2,intj++,
Print["----"];
Print[NZCurrEoM[2][inti][intj]//ScreenDollarIndices//AbsoluteTiming];
Print["===="];
Print[NZCurrEoMUnprocessed[2][inti][intj]//ScreenDollarIndices//AbsoluteTiming];
];
];*)


If[!FileExistsQ["~/.EMSelfForceCache/NZEoMRulesEM2curr.mx"]||!FileExistsQ["~/.EMSelfForceCache/NZDerivRulesEM2curr.mx"]||RegenEoMs,
For[inti=0,inti<=1,inti++,
For[intj=0,intj<=1,intj++,
tempEoM=NZCurrDivEqOrderMomentEoM[2][inti][intj];
For[intk=1,intk>=0,intk--,
If[!(inti==1 && intj==1),
	NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
	NZSumEoMRules[2]=DeleteDuplicates[NZSumEoMRules[2]~Join~GenerateSumRulesFromEoM[(Nest[PD[{0,-Fra}],tempEoM,intk])//ExpandAll//GenerateNewDummies]];
(*NZDerivRules[0]=DeleteDuplicates[NZDerivRules[0]~Join~GenerateRulesFromEoM[(NZCurrDivEqOrderMoment[0][inti][intj])//GenerateNewDummies]];*)
];
];
];
];
DumpSave["~/.EMSelfForceCache/NZEoMRulesEM2curr.mx",NZEoMRules];
DumpSave["~/.EMSelfForceCache/NZDerivRulesEM2curr.mx",NZDerivRules];
,
DumpGet["~/.EMSelfForceCache/NZEoMRulesEM2curr.mx"];
DumpGet["~/.EMSelfForceCache/NZDerivRulesEM2curr.mx"];
];//Timing


(* ::Text:: *)
(*Add conservation of charge at this order to the set of momentum-rules*)


MomRules[2]=MomRules[2]~Join~{PD[{0,-Fra}][ChargeCurrentpert[LI[1],{0,Fra}]]->(PD[{0,-Fra}][ChargeCurrentpert[LI[1],{0,Fra}]]//ReverseBodyParams//ApplyEoMRules[2]//ApplyAllBodyParams)};


(* ::Text:: *)
(*The current rules for value of the spatial current vector*)


CurrentRules[2]={};
CurrentRules[2]=CurrentRules[2]~Join~GenerateRulesFromEoM[NZCurrDivEqOrderMomentEoM[2][1][1]//ExpandAll//GenerateNewDummies];
CurrentRules[2]=CurrentRules[2]~Join~{ChargeCurrentpert[LI[2],{i_,Fra3}]->(((ChargeCurrentpert[LI[2],{i,Fra3}]//ReverseBodyParams)/.CurrentRules[2])//ExpandAll//ApplyAllBodyParams)};


(* ::Text:: *)
(*Confirmation of the final order of charge-current renormalization:*)


CurrentConf=NZCurrDivEqOrderMomentEoM[3][0][0]//ApplyAllBodyParams;


CurrentConf//ExpandAll


(* ::Text:: *)
(*This being zero indicates we renormalized right, as we've explicitly set the conserved charge to have vanishing derivative*)


CurrentConf//ToConsCharge[2]//BasisCanon[NoMetriconVBundle]


NZEoMRules[2]=DeleteDuplicates[NZEoMRules[2]~Join~GenerateRulesFromEoM[(NZCurrDivEqOrderMomentEoM[3][0][0])//ExpandAll//GenerateNewDummies]];


MomRules[2]=MomRules[2]~Join~{PD[{0,-Fra}][ChargeCurrentpert[LI[2],{0,Fra}]]->(PD[{0,-Fra}][ChargeCurrentpert[LI[2],{0,Fra}]]//ReverseBodyParams//ApplyEoMRules[2]//ApplyAllBodyParams)};


(* ::Subsection:: *)
(*Regular Field Components*)


(* ::Text:: *)
(*Leading field strength renormalization - confirmation of prior result*)


(1/2)(RegFstrpert[LI[{2,0}],{-0,-Fra},{-i,-Fra3}]/.RegFstrfieldRulespert20)/.{ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}


(RegFstrpert[LI[{2,0}],{-j,-Fra3},{-i,-Fra3}]/.RegFstrfieldRulespert20)/.{ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}


TidyFstr[expr_]:=(expr/.{Fstrpert->RegFstrpert,Fstr[__]:>0})/.{RegFstrpert[LI[n_?IntegerQ],inds__]:>RegFstrpert[LI[{n,0}],inds]}/.{RegFstrpert[LI[{n_,a_}],inds__]/;n<2:>0};


(* ::Text:: *)
(*Note that the scaling here is not strictly valid in complete generality - the conversion of i derivatives acting on body params can give promotion, *)
(*	but this is not an important effect for this expression as all orders lower than 2 explicitly vanish.*)


((((((Fstr[{-k,-Fra3},{0,-Fra}]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1//Frame31Split//ExpandAll//TidyFstr)/.{\[Epsilon]^n_/;n>3:>0}/.RegFstrfieldRulespert
	//Expand)/.CurrentRules[1]/.CurrentRules[0])//ToConsCharge[2]//BasisCanon[NoMetriconVBundle])/.{PD[__][acc2d[__]]:>0}
	//NoScalar//BasisCanon[NoMetriconVBundle])


((((((Fstr[{-k,-Fra3},{0,-Fra}]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1//Frame31Split//ExpandAll//TidyFstr)/.{\[Epsilon]^n_/;n>3:>0}/.RegFstrfieldRulespert
	//Expand)/.CurrentRules[1]/.CurrentRules[0])//ToConsCharge[2]//BasisCanon[NoMetriconVBundle])/.{PD[__][acc2d[__]]:>0}
	//NoScalar//BasisCanon[NoMetriconVBundle])


((((((Fstr[{-k,-Fra3},{-j,-Fra3}]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1//Frame31Split//ExpandAll//TidyFstr)/.{\[Epsilon]^n_/;n>3:>0}/.RegFstrfieldRulespert
	//Expand)/.CurrentRules[1]/.CurrentRules[0])//ToConsCharge[2]//BasisCanon[NoMetriconVBundle])/.{PD[__][acc2d[__]]:>0}
	//NoScalar//BasisCanon[NoMetriconVBundle])


kRenormGen=(-IntNull[(Fstr[{-k,-Fra3},{-a,-Fra}]CurrentDens[{a,Fra}]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1]//Frame31Split//ExpandAll//TidyFstr)/.{\[Epsilon]^n_/;n>3:>0}


RenormGen0=(IntNull[(Fstr[{0,-Fra},{-a,-Fra}]CurrentDens[{a,Fra}]//Perturb[#,3]&//Qerturb[#,1]&)/.q->1]//Frame31Split//ExpandAll//TidyFstr)/.{\[Epsilon]^n_/;n>3:>0}


RemoveZeroChargeCurrent={ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0};


IntNull[tens_[inds__]expr_]/;MemberQ[$BodyParams,tens]:=tens[inds]*IntNull[expr];
IntNull[PD[a_][tens_[inds__]]expr_]/;MemberQ[$BodyParams,tens]:=PD[a][tens[inds]]*IntNull[expr];
IntNull[PD[b_][PD[a_][tens_[inds__]]]expr_]/;MemberQ[$BodyParams,tens]:=PD[b][PD[a][tens[inds]]]*IntNull[expr];
IntNull[PD[c_][PD[b_][PD[a_][tens_[inds__]]]]expr_]/;MemberQ[$BodyParams,tens]:=PD[c][PD[b][PD[a][tens[inds]]]]*IntNull[expr];


kRenormExpanded=((kRenormGen/.RegFstrfieldRulespert/.RemoveZeroChargeCurrent/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.RemoveZeroChargeCurrent/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


kRenormExpanded=((kRenormGen/.RegFstrfieldRulespert/.RemoveZeroChargeCurrent/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.RemoveZeroChargeCurrent/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


RenormExpanded0=((RenormGen0/.RegFstrfieldRulespert/.RemoveZeroChargeCurrent/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.RemoveZeroChargeCurrent/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


RenormExpanded0=((RenormGen0/.RegFstrfieldRulespert/.RemoveZeroChargeCurrent/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3->0,PD[_][acc2d[__]]:>0}/.RemoveZeroChargeCurrent/.nstoNsrule//ExpandAll
			//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams);//Timing


((kRenormExpanded/.RemoveZeroChargeCurrent//BasisCanon[NoMetriconVBundle])/.MomRules[2]/.CurrentRules[1]//BasisCanon[NoMetriconVBundle]
		//ToConsCharge[1]//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle])/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]


HMompert[LI[2],{k,Fra3}]//FromHarteSpinMom[2]//NoScalar//BasisCanon[NoMetriconVBundle]


((RenormExpanded0/.RemoveZeroChargeCurrent//BasisCanon[NoMetriconVBundle])/.MomRules[2]/.CurrentRules[1]//BasisCanon[NoMetriconVBundle]
		//ToConsCharge[1]//ExpandAll//NoScalar//BasisCanon[NoMetriconVBundle])/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]


(* ::Subsection:: *)
(*3rd-order computations*)


(* ::Subsubsection:: *)
(*3rd - Order Computations *)


accRaw[3]=NZkFraSEConsOrderMomentEoM[3][0][0];//Timing


(* ::Text:: *)
(*The equation of motion for non-renormalized momentum*)


-((((accRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)/.CurrentRules[1]/.CurrentRules[1]
		/.MomRules[2]//BasisCanon[NoMetriconVBundle]//ToConsCharge[1])/.AntisymmetrizeDipole//NoScalar
		//BasisCanon[NoMetriconVBundle])//ConvertToDChargeDipole//Expand//ConvertToDChargeDipole//ScaledFramePDtoCD
		//BasisCanon[NoMetriconVBundle])//BasisCanon[NoMetriconVBundle]


accRenorm[3]=-((accRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)/.CurrentRules[1]/.CurrentRules[1]
		/.MomRules[2]//BasisCanon[NoMetriconVBundle]//ToConsCharge[1]//ToHarteSpinMom[2])/.AntisymmetrizeDipole//NoScalar//BasisCanon[NoMetriconVBundle]


accExpanded[3]=(accRenorm[3]/.CurrentRules[2]/.MomentumBodyParamRules)//ExpandAll//CovDFext//BasisCanon[NoMetriconVBundle];


(* ::Text:: *)
(*Exclusively the new dipole contributions:*)


((((accExpanded[3]/.CurrentRules[1]//ToHarteSpinMom[2]//ToConsCharge[2])
		/.RMassSub/.SubRDipole/.SpinSup//ExpandAll//FullConvertToDRDipole[4])//ScaledFramePDtoCD)
		/.{(RDipolepert|ChargeDipolepert|ChargeQuadPole|RSpinpert)[__]:>0})


(* ::Text:: *)
(*Just the quadrupole dependence - can safely set to zero dipole and spin, as no terms at this order depend on both quadrupole and either dipole or spin or charge*)


-(Mompert[LI[2],{0,Fra}]//ToHarteSpinMom[2])/.RMassSub//NoScalar//BasisCanon[NoMetriconVBundle]


-(Spinpert[LI[1],{i,Fra3},{k,Fra3}]//ToHarteSpinMom[2])/.HToRSpin//BasisCanon[NoMetriconVBundle]//ScaledFramePDtoCD//BasisCanon[NoMetriconVBundle]


((accExpanded[3]/.CurrentRules[1]//ToHarteSpinMom[2]//ToConsCharge[2])
		/.RMassSub/.SubRDipole/.SpinSup/.QuadTraceRule/.SubResQuadrupole//CovDFext
    	//NoScalar//FullConvertToDRQuadrupole[3]//BasisCanon[NoMetriconVBundle]
		)/.{(RDipole|RDipolepert|RSpinpert|ConsChargepert)[__]:>0}


(* ::Subsubsection:: *)
(*3rd - Order Computation  - Time Component*)


MdotRaw[3]=NZ0FraSEConsOrderMomentEoM[3][0][0];//Timing


MdotRenorm[3]=((MdotRaw[3]//ApplySumRuleList[MomentumSumRuleList]//ApplyAllBodyParams)/.CurrentRules[1]
		/.MomRules[2]//ToConsCharge[1]//ToHarteSpinMom[2]//NoScalar)/.AntisymmetrizeDipole//BasisCanon[NoMetriconVBundle]


MdotExpanded[3]=((MdotRenorm[3]/.CurrentRules[2]//GenerateNewDummies)/.MomentumBodyParamRules)//ExpandAll//CovDFext//BasisCanon[NoMetriconVBundle];


(* ::Text:: *)
(*Just the dipole dependence:*)


((((MdotExpanded[3]/.CurrentRules[1]//ToHarteSpinMom[2]//ToConsCharge[2])
		/.RMassSub/.SubRDipole/.SpinSup//ExpandAll//FullConvertToDRDipole[4]))
		/.{(RDipolepert|ChargeDipolepert|ChargeQuadPole|RSpinpert)[__]:>0})


(* ::Text:: *)
(*Just the quadrupole dependence:*)


((MdotExpanded[3]/.CurrentRules[1]//ToHarteSpinMom[2]//ToConsCharge[2])
		/.RMassSub/.SubRDipole/.SpinSup/.QuadTraceRule/.SubResQuadrupole//CovDFext
    	//NoScalar//FullConvertToDRQuadrupole[3]//BasisCanon[NoMetriconVBundle]
		)/.{(RDipole|RDipolepert|RSpinpert|ConsChargepert)[__]:>0}
