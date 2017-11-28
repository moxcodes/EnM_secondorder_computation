(* ::Package:: *)

(* ::Section:: *)
(*Self field derivation*)


(* ::Subsection:: *)
(*Retarded self - field*)


(* ::Text:: *)
(*Note : This computation is performed in terms of bare multipole moments*)


(* ::Text:: *)
(*TODO:Thoroughly check sub-subleading signs on this. They are not necessary for this computation, but as a point of pride, I'd prefer no further sign errors to be present.*)


(* ::Text:: *)
(*TODO: Re-do the initial derivation to have sign compatible with the signs I've found from the field equations computations later*)


(* ::Text:: *)
(*Some of this will be difficult to understand by reading the code, and may even appear sloppy. See accompanying notes for justification*)


(* ::Text:: *)
(*Start with the expansion for the Green's function given in the paper:*)


DefTensor[DtauSynge[],{M4},PrintAs->"\!\(\*SubscriptBox[\(\[Sigma]\), \(\(,\)\(\[Tau]'\)\)]\)"];


(* ::Text:: *)
(*This is Subscript[g, *)
(*\!\(\*OverscriptBox[\(a\), \(^\)]\)  *)
(*\!\(\*OverscriptBox[\(b\), \(^\)]\)'][x,x'] =  Subscript[g, *)
(*\!\(\*OverscriptBox[\(a\), \(^\)]\)  *)
(*\!\(\*OverscriptBox[\(b\), \(^\)]\)'][z,z'] (due to frame indices and flat space)*)


DefTensor[ParProp[a,b],{M4},PrintAs->"g"];


DefTensor[Sigzpx[a],{M4},PrintAs->"\[Sigma](z',x)"];


DefTensor[Sigzxp[a],{M4},PrintAs->"\[Sigma](z,x')"];


DefTensor[Sigzx[a],{M4},PrintAs->"\[Sigma](z,x)"];


DefTensor[Sigzpxp[a],{M4},PrintAs->"\[Sigma](z,x)"];


WaveEqOrder=2;


(* ::Text:: *)
(*These assume the index is evaluated on the worldline:*)


Sigzpxp[a_]:=Module[{i},-rp[]/\[Lambda](Basis[a,{0,-Fra}] + Basis[a,{-i,-Fra3}]normp[{i,Fra3}])];


Sigzx[a_]:=-r[](Basis[a,{0,-Fra}] - Basis[a,{-i,-Fra3}]norm[{i,Fra3}]);


UnScaledSigzzp[a_]:= ( Tau[] Basis[{0,-Fra},a] -(1/2)\[Epsilon] Tau[]^2 acc[a]+ (1/6)\[Epsilon]^2  Tau[]^3 acc1d[a]);


ScaledSigzzp[a_]:= ( \[Epsilon] Tau[] Basis[{0,-Fra},a] -(1/2)\[Epsilon]^2 Tau[]^2 acc[a]+ (1/6)\[Epsilon]^3  Tau[]^3 acc1d[a]);


DefTensor[Tau[],{M4},PrintAs->"\[Tau]'"];


(* ::Text:: *)
(*We are expanding through dipole order, so the highest order we require is ~\[Tau]';*)


(* ::Text:: *)
(*Parameterizing choices*)


((IntNull[CD[{-0,-Fra}][CurrentDens[{i,Fra3}]](r[]^2 norm[{j,Fra3}])//ScaledFrameCDtoPD//ToRettauFrameiderivs//Series[#,{\[Epsilon],0,1}]&//Normal]
				//ExpandAll)//.NullIntparts//ExpandAll)/.{r[]^3->0}/.nstoNsrule//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams


((IntNull[CD[{-0,-Fra}][CurrentDens[{0,Fra}]](r[]^2 norm[{i,Fra3}])//ScaledFrameCDtoPD//ToRettauFrameiderivs//Series[#,{\[Epsilon],0,1}]&//Normal]
				//ExpandAll)//.NullIntparts//ExpandAll)/.{r[]^3->0}/.nstoNsrule//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams


-((IntNull[CD[{-0,-Fra}][CurrentDens[{i,Fra3}]]((1/2)r[]^2)//ScaledFrameCDtoPD//ToRettauFrameiderivs//Series[#,{\[Epsilon],0,1}]&//Normal]
				//ExpandAll)//.NullIntparts//ExpandAll)/.{r[]^3->0}/.nstoNsrule//BasisCanon[NoMetriconVBundle]//ApplyAllBodyParams


DefConstantSymbol[GC1];DefConstantSymbol[GC2];


WaveEqOrder=2;


(* ::Text:: *)
(*Re-checked 09/23*)


RetGreenFnNC[b_]:=(((IntNull[(DtauSynge[])^(-1)*Basis[b,{-a,-Fra}](CurrentDens[{a,Fra}] -  UnScaledSigzzp[{c,Fra}] CD[{-c,-Fra}][CurrentDens[{a,Fra}]]
	+  (1/2)UnScaledSigzzp[{c,Fra}] UnScaledSigzzp[{d,Fra}] CD[{-c,-Fra}][CD[{-d,-Fra}][CurrentDens[{a,Fra}]]])])//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}
		//Frame31Split//RetCanon//ScaleDerivs)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}


RetGreenFnPP[b_]:=((IntNull[(DtauSynge[])^(-1)*ParProp[b,{-a,-Fra}](CurrentDens[{a,Fra}] - \[Epsilon] Tau[] PD[{0,-Ret}][CurrentDens[{a,Fra}]]
	+  (1/2) \[Epsilon]^2 Tau[]^2 PD[{0,-Ret}][PD[{0,-Ret}][CurrentDens[{a,Fra}]]])])//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}//Frame31Split//RetCanon


ExpandedRetGreenFunction[{0,Fra}]=(((RetGreenFnPP[{0,Fra}])/.{CD[a__][exp___]:>(CD[a][exp]//ScaledFrameCDtoPD)}//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}
					//ToRettauFrameiderivs//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0};//Timing


ExpandedRetGreenFunction[{k_,Fra3}]=(((RetGreenFnPP[{k,Fra3}])/.{CD[a__][exp___]:>(CD[a][exp]//ScaledFrameCDtoPD)}//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}
					//ToRettauFrameiderivs//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0};//Timing


(* ::Text:: *)
(*Given with only errors of order \[Epsilon]^3*)


(* ::Text:: *)
(*Second index is at the 'non-direct index' - so non-primed for this code description*)


(* ::Text:: *)
(*TODO:re-check subleading terms here.*)


ParPropExpand={ParProp[a_,b_]:>Module[{i},Basis[a,b] + \[Epsilon] Tau[](acc[a]Basis[{0,-Fra},b] - Basis[{0,-Fra},a]acc[b]) + (1/2) \[Epsilon]^2 Tau[]^2 acc[a]acc[b] 
										- (1/2) \[Epsilon]^2 Tau[]^2 acc[{i,Fra3}]acc[{-i,-Fra3}] Basis[a,{0,-Fra}]Basis[b,{0,-Fra}]
										+ (1/2)\[Epsilon]^2 Tau[]^2(acc1d[a]Basis[{0,-Fra},b] - acc1d[b]Basis[{0,-Fra},a])]};


(* ::Text:: *)
(*Rechecked 09/23*)


DefConstantSymbol[Sxp1];


SigzxpExpand={Sigzxp[a_]:>Module[{i},(\[Epsilon] Tau[]Basis[{0,-Fra},a] - (1/2)\[Epsilon]^2 Tau[]^2 acc[a] + (1/6)\[Epsilon]^3 Tau[]^3 acc1d[a]) +  \[Epsilon] ParProp[{0,-Fra},a]*(-r[]) -  \[Epsilon] ParProp[{-i,-Fra3},a]r[]norm[{i,Fra3}]]};


(Sigzxp[{0,Fra}]/.SigzxpExpand/.ParPropExpand//Expand)//RetCanon


(Sigzxp[{k,Fra3}]/.SigzxpExpand/.ParPropExpand//Expand)//RetCanon


DefTensor[rp[],{M4},PrintAs->"r'"];DefTensor[normp[a],{M4},PrintAs->"n'"];


normp[{0,(Fra|-Fra)}]:=0;


(* ::Text:: *)
(*The equation which determines Tau:*)


DefScalarFunction[T];DefScalarFunction[Dts];


Sigzxp[{i,Fra3}]/.SigzxpExpand


(-met[{-a,-Fra},{-b,-Fra}]Sigzxp[{a,Fra}]Sigzpxp[{b,Fra}]//Frame31Split)/.RetFrameVectorRules


Sigzxp[a]/.SigzxpExpand


(* ::Text:: *)
(*Re-checked 09/23*)


TauEquationRaw=((((\[Lambda]*(-met[{-a,-Fra},{-b,-Fra}]Sigzxp[{a,Fra}]Sigzpxp[{b,Fra}] + (1/2)met[{-a,-Fra},{-b,-Fra}]Sigzxp[{a,Fra}]Sigzxp[{b,Fra}])/.SigzxpExpand//ExpandAll)
			/.ParPropExpand)//Expand//ContractBasis)/.{\[Epsilon]^n_/;n>4:>0})//Frame31Split//BasisCanon[NoMetriconVBundle];


PerturbativeTauEquation = (TauEquationRaw/.{Tau[]->(T[0,0]+ \[Epsilon] T[1,0] + \[Lambda] \[Epsilon] T[0,1] + \[Epsilon]^2 \[Lambda] T[1,1] + \[Lambda]^2 \[Epsilon]^2 T[0,2] + \[Epsilon]^2 T[2,0])})//Expand;


TauSols={};


((Coefficient[(PerturbativeTauEquation//Expand)/.\[Lambda]->0,\[Epsilon]]/.TauSols)//NoScalar//BasisCanon)


TauSols


((1/rp[])((Coefficient[(PerturbativeTauEquation//Expand)/.\[Lambda]->0,\[Epsilon]^3]/.TauSols)//NoScalar//ExpandAll)+T[2,0])//Expand//BasisCanon[NoMetriconVBundle]


TauSols=TauSols~Join~{T[0,0]->Scalar/@(((1/rp[])((Coefficient[(PerturbativeTauEquation//Expand)/.\[Lambda]->0,\[Epsilon]]/.TauSols)//NoScalar//BasisCanon) + T[0,0])//Expand)};


TauSols=TauSols~Join~{T[0,1]->Scalar/@(((1/rp[])((Coefficient[Coefficient[PerturbativeTauEquation//Expand,\[Lambda]],\[Epsilon]^2]/.TauSols)//NoScalar//BasisCanon) + T[0,1])//Expand)};


TauSols=TauSols~Join~{T[1,0]->Scalar/@(((1/rp[])((Coefficient[(PerturbativeTauEquation//Expand)/.\[Lambda]->0,\[Epsilon]^2]/.TauSols)//NoScalar//BasisCanon) + T[1,0])//Expand)};


TauSols=TauSols~Join~{T[2,0]->(Scalar/@(((1/rp[])((Coefficient[(PerturbativeTauEquation//Expand)/.\[Lambda]->0,\[Epsilon]^3]/.TauSols)//NoScalar//ExpandAll) + T[2,0])//Expand)//BasisCanon[NoMetriconVBundle])};


TauSols=TauSols~Join~{T[1,1]->(Scalar/@(((1/rp[])((Coefficient[Coefficient[PerturbativeTauEquation//Expand,\[Lambda]],\[Epsilon]^3]/.TauSols)//NoScalar//ExpandAll) + T[1,1])//Expand)//BasisCanon[NoMetriconVBundle])};


TauSols=TauSols~Join~{T[0,2]->(Scalar/@(((1/rp[])((Coefficient[Coefficient[PerturbativeTauEquation//Expand,\[Lambda]^2],\[Epsilon]^3]/.TauSols)//NoScalar//ExpandAll) + T[0,2])//Expand)//BasisCanon[NoMetriconVBundle])};


TauSols


TauExpand={Tau[]->(T[0,0]+ \[Epsilon] T[1,0] + \[Lambda] \[Epsilon] T[0,1] + \[Epsilon]^2 \[Lambda] T[1,1] + \[Lambda]^2 \[Epsilon]^2 T[0,2] + \[Epsilon]^2 T[2,0])};


(* ::Text:: *)
(*Re-checked 09/23*)


DefConstantSymbol[DtS1];DefConstantSymbol[DtS2];


DtauSyngeExprRaw=(\[Lambda](((Sigzpxp[{-a,-Fra}]ParProp[{a,Fra},{-b,-Fra}]Basis[{b,Fra},{-0,-Ret}] - Sigzxp[{a,Fra}]ParProp[{-a,-Fra},{-b,-Fra}]Basis[{b,Fra},{-0,-Ret}]//Expand)
								/.ParPropExpand//Expand//Frame31Split//RetCanon)/.SigzxpExpand//Frame31Split//RetCanon)/.ParPropExpand//Expand//RetCanon//BasisCanon);


PerturbativeDtauSynge=((DtauSyngeExprRaw )/.TauExpand);


DtauSyngeExprRaw


Coefficient[PerturbativeDtauSynge/.\[Lambda]->0,\[Epsilon]]/.TauSols//ExpandAll//NoScalar//BasisCanon


(* ::InheritFromParent:: *)
(*acc[{-i, -Fra3}] norm[{i, Fra3}] r[] rp[]-acc[{i, Fra3}] normp[{-i, -Fra3}] r[] rp[]-acc[{i, Fra3}] normp[{-i, -Fra3}] rp[] T[0,0]*)


Scalar[(Coefficient[PerturbativeDtauSynge/.\[Lambda]->0,\[Epsilon]]/.TauSols//NoScalar//BasisCanon)]


DTauSyngeSols={};


DtauSyngeExpand={DtauSynge[]:>(1/\[Lambda])(DtS[0,0]+ \[Epsilon] DtS[1,0] + \[Lambda] \[Epsilon] DtS[0,1] + \[Epsilon]^2 \[Lambda] DtS[1,1] + \[Lambda]^2 \[Epsilon]^2 DtS[0,2] + \[Epsilon]^2 DtS[2,0])};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[0,0]->Scalar[(PerturbativeDtauSynge/.\[Lambda]->0/.\[Epsilon]->0/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[1,0]->Scalar[(Coefficient[PerturbativeDtauSynge/.\[Lambda]->0,\[Epsilon]]/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[2,0]->Scalar[(Coefficient[PerturbativeDtauSynge/.\[Lambda]->0,\[Epsilon]^2]/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[0,1]->Scalar[(Coefficient[Coefficient[PerturbativeDtauSynge,\[Epsilon]],\[Lambda]]/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[1,1]->Scalar[(Coefficient[Coefficient[PerturbativeDtauSynge,\[Epsilon]^2],\[Lambda]]/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols=DTauSyngeSols~Join~{DtS[0,2]->Scalar[(Coefficient[Coefficient[PerturbativeDtauSynge,\[Epsilon]^2],\[Lambda]^2]/.TauSols//NoScalar//BasisCanon)]};


DTauSyngeSols


(ExpandedRetGreenFunction[{0,Fra}]/.ParPropExpand/.RetFrameVectorRules//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}


PropagatedRetGreenFunction[{0,Fra}]=(ExpandedRetGreenFunction[{0,Fra}]/.ParPropExpand/.RetFrameVectorRules//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}


PropagatedRetGreenFunction[{k_,Fra3}]=(ExpandedRetGreenFunction[{k,Fra3}]/.ParPropExpand/.RetFrameVectorRules//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}


((PropagatedRetGreenFunction[{0,Fra}]/.DtauSyngeExpand/.TauExpand//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.IntNull[expr_]:>IntNull[Series[expr,{\[Epsilon],0,2}]//Normal]
							//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}//Coefficient[#,\[Epsilon]]&


(*WaveEqOrder=1;*)


ProcessedRetGreenFunction[{0,Fra}]=(((((PropagatedRetGreenFunction[{0,Fra}]//.CommutedtaudFrame/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.TauExpand)/.{\[Epsilon]^WaveEqOrder*ex_:>\[Epsilon]^WaveEqOrder*(ex/.\[Epsilon]->0)}//ExpandAll)
										/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.DtauSyngeExpand)/.{IntNull[expr_]:>IntNull[Series[expr,{\[Epsilon],0,2}]//Normal]}//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}
										/.DTauSyngeSols/.TauSols//ExpandAll//NoScalar);//Timing


ProcessedRetGreenFunction[{k_,Fra3}]=(((((PropagatedRetGreenFunction[{k,Fra3}]//.CommutedtaudFrame/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.TauExpand)/.{\[Epsilon]^WaveEqOrder*ex_:>\[Epsilon]^WaveEqOrder*(ex/.\[Epsilon]->0)}//ExpandAll)
										/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.DtauSyngeExpand)/.{IntNull[expr_]:>IntNull[Series[expr,{\[Epsilon],0,2}]//Normal]}//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}
										/.DTauSyngeSols/.TauSols//ExpandAll//NoScalar);//Timing


CanonicalizedRetGreenFunction[{0,Fra}]=ProcessedRetGreenFunction[{0,Fra}]//ToCanonical[#,UseMetricOnVBundle->None]&;//Timing
CanonicalizedRetGreenFunction[{k_,Fra3}]=ProcessedRetGreenFunction[{k,Fra3}]//ToCanonical[#,UseMetricOnVBundle->None]&;//Timing


Length[CanonicalizedRetGreenFunction[{0,Fra}]]


Length[CanonicalizedRetGreenFunction[{k,Fra3}]]


IntegratedRetGreenFunction[{0,Fra}]=((CanonicalizedRetGreenFunction[{0,Fra}]//.nstoNsrule//.NullIntparts//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.NullIntparts//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0};//Timing
IntegratedRetGreenFunction[{k_,Fra3}]=((CanonicalizedRetGreenFunction[{k,Fra3}]//.nstoNsrule//.NullIntparts//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0}/.NullIntparts//ExpandAll)/.{\[Epsilon]^n_/;n>WaveEqOrder:>0};//Timing


(Coefficient[IntegratedRetGreenFunction[{0,Fra}],\[Lambda]]/.\[Epsilon]->0)//ApplyAllBodyParams


(Coefficient[IntegratedRetGreenFunction[{l,Fra3}],\[Lambda]]/.\[Epsilon]->0)//ApplyAllBodyParams


((Coefficient[Coefficient[IntegratedRetGreenFunction[{0,Fra}],\[Lambda]],\[Epsilon]])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle])


(* ::InheritFromParent:: *)
(*-((acc[{-i, -Fra3}] ChargeDipole[{0, Fra}, {i, Fra3}])/rp[])-(acc[{-i, -Fra3}] ChargeDipole[{i, Fra3}, {0, Fra}])/rp[]+(acc[{-i, -Fra3}] ChargeDipole[{i, Fra3}, {j, Fra3}] normp[{k, Fra3}] CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}])/rp[]+(acc[{i, Fra3}] ChargeDipole[{0, Fra}, {j, Fra3}] normp[{-i, -Fra3}] normp[{k, Fra3}] CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}])/rp[]-xAct`xTensor`PD[{0, -Fra}][ChargeDipole[{0, Fra}, {0, Fra}]]/rp[]+(normp[{i, Fra3}] CDelta[-Fra3, -Fra3][{-i, -Fra3}, {-j, -Fra3}] xAct`xTensor`PD[{0, -Fra}][ChargeDipole[{0, Fra}, {j, Fra3}]])/rp[]*)


(Coefficient[Coefficient[IntegratedRetGreenFunction[{l,Fra3}],\[Lambda]],\[Epsilon]])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]


(* ::InheritFromParent:: *)
(*-((acc[{l, Fra3}] ChargeDipole[{0, Fra}, {0, Fra}])/rp[])-(acc[{-i, -Fra3}] ChargeDipole[{l, Fra3}, {i, Fra3}])/rp[]+(acc[{l, Fra3}] ChargeDipole[{0, Fra}, {i, Fra3}] normp[{j, Fra3}] CDelta[-Fra3, -Fra3][{-i, -Fra3}, {-j, -Fra3}])/rp[]+(acc[{i, Fra3}] ChargeDipole[{l, Fra3}, {j, Fra3}] normp[{-i, -Fra3}] normp[{k, Fra3}] CDelta[-Fra3, -Fra3][{-j, -Fra3}, {-k, -Fra3}])/rp[]-xAct`xTensor`PD[{0, -Fra}][ChargeDipole[{l, Fra3}, {0, Fra}]]/rp[]+(normp[{i, Fra3}] CDelta[-Fra3, -Fra3][{-i, -Fra3}, {-j, -Fra3}] xAct`xTensor`PD[{0, -Fra}][ChargeDipole[{l, Fra3}, {j, Fra3}]])/rp[]*)


(Coefficient[Coefficient[IntegratedRetGreenFunction[{0,Fra}],\[Lambda]],\[Epsilon]^2])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]


(Coefficient[Coefficient[IntegratedRetGreenFunction[{l,Fra3}],\[Lambda]],\[Epsilon]^2])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]


(Coefficient[Coefficient[IntegratedRetGreenFunction[{0,Fra}],\[Lambda]^2],\[Epsilon]])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]


(Coefficient[Coefficient[IntegratedRetGreenFunction[{l,Fra3}],\[Lambda]^2],\[Epsilon]])//ApplyAllBodyParams//BasisCanon[NoMetriconVBundle]


AfieldRules={
 Afieldr[{0,Fra}]->((IntegratedRetGreenFunction[{0,Fra}]/.{\[Lambda]->1,\[Epsilon]^n_/;n>1:>0}/.nstoNsrule//.NullIntparts//ApplyAllBodyParams)/.{rp->r,normp->norm}//GenerateNewDummies),
 Afieldr[{k_,Fra3}]->((IntegratedRetGreenFunction[{k,Fra3}]/.{\[Lambda]->1,\[Epsilon]^n_/;n>1:>0}/.nstoNsrule//.NullIntparts//ApplyAllBodyParams)/.{rp->r,normp->norm}//GenerateNewDummies)};


(* ::Text:: *)
(*So the above all assumes generic radius, but at this point we want a small radius, so we make the promotion that each order in 1/r gives a 1/eps*)
(*Note that this ensures that each order in epsilon is an assumed expansion in 1/r, despite 1/r being order 1. So, these expansions should never be trusted on their own.*)
(*However, they will be used exclusively to evaluate the 'surface' integrals, for which we want to pick out only the leading r behavior.*)


(* ::Text:: *)
(*NOTE: discarded everything of order q*Qijk or similar. I'm pretty confident that this is justified.*)


ScaledAfieldRules={
Afieldr[{0,Fra}]->(((\[Epsilon]*IntegratedRetGreenFunction[{0,Fra}]//Expand)/.\[Epsilon]^n_/;n>2:>0/.nstoNsrule//.NullIntparts//ApplyAllBodyParams)
					/.{rp[]->r[],normp->norm}//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)/.\[Lambda]->(1/\[Epsilon]),
Afieldr[{k_,Fra3}]->(((\[Epsilon]*IntegratedRetGreenFunction[{k,Fra3}]//Expand)/.\[Epsilon]^n_/;n>2:>0/.nstoNsrule//.NullIntparts//ApplyAllBodyParams)
					/.{rp[]->r[],normp->norm}//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)/.\[Lambda]->(1/\[Epsilon])};


Afieldr[{0,Fra}]/.ScaledAfieldRules


Afieldr[{k,Fra3}]/.ScaledAfieldRules


(* ::Subsection:: *)
(*Advanced field*)


ScaledAfieldRules={Afieldr[{0,Fra}]:>Module[{i,j},
					(1/r[])(ChargeCurrent[{0,Fra}]) + (1/r[]^2)ChargeDipole[{0,Fra},{i,Fra3}]norm[{-i,-Fra3}]
					 + (- \[Epsilon]/r[])ChargeDipole[{i,Fra3},{0,Fra}]acc[{-i,-Fra3}]
					 + (+ \[Epsilon]/r[])(-ChargeDipole[{0,Fra},{i,Fra3}]acc[{-i,-Fra3}])
					 + (- \[Epsilon]/r[])(-ChargeDipole[{i,Fra3},{j,Fra3}] acc[{-i,-Fra3}]norm[{-j,-Fra3}])
					 + (+ \[Epsilon]/r[])(ChargeDipole[{0,Fra},{j,Fra3}]norm[{-j,-Fra3}]acc[{-i,-Fra3}]norm[{i,Fra3}])
					 + (+ \[Epsilon]/r[])(-PD[{0,-Fra}][ChargeDipole[{0,Fra},{0,Fra}]])
					 + (+ \[Epsilon]/r[])(PD[{0,-Fra}][ChargeDipole[{0,Fra},{j,Fra3}]]norm[{-j,-Fra3}])],
Afieldr[{k_,Fra3}]:>Module[{i,j},
					(1/r[])(ChargeCurrent[{k,Fra3}]) + (1/r[]^2)ChargeDipole[{k,Fra3},{i,Fra3}]norm[{-i,-Fra3}]
					 + (- \[Epsilon]/r[])ChargeDipole[{0,Fra},{0,Fra}]acc[{k,Fra3}]
					 + (+ \[Epsilon]/r[])(-ChargeDipole[{k,Fra3},{i,Fra3}]acc[{-i,-Fra3}])
					 + (- \[Epsilon]/r[])(-ChargeDipole[{0,Fra},{j,Fra3}] acc[{k,Fra3}]norm[{-j,-Fra3}])
					 + (+ \[Epsilon]/r[])(ChargeDipole[{k,Fra3},{j,Fra3}]norm[{-j,-Fra3}]acc[{-i,-Fra3}]norm[{i,Fra3}])
					 + (+ \[Epsilon]/r[])(-PD[{0,-Fra}][ChargeDipole[{k,Fra3},{0,Fra}]])
					 + (+ \[Epsilon]/r[])(PD[{0,-Fra}][ChargeDipole[{k,Fra3},{j,Fra3}]]norm[{-j,-Fra3}])]}


Afieldr[{0,Fra}]/.ScaledAfieldRules//ScaledFramePDtoCD


Afieldr[{k,Fra3}]/.ScaledAfieldRules//ScaledFramePDtoCD


DefTensor[ra[],{M4},PrintAs->"\!\(\*SubscriptBox[\(r\), \(+\)]\)"];DefTensor[ChargeCurrenta[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(J\), \(+\)]\)"];DefTensor[acca[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(a\), \(+\)]\)"];DefTensor[norma[a],{M4},PrintAs->"\!\(\*SubscriptBox[OverscriptBox[\(n\), \(^\)], \(+\)]\)"];
DefTensor[ChargeDipolea[a,b],{M4},PrintAs->"\!\(\*SubscriptBox[\(Q\), \(+\)]\)"];


DefTensor[tnorm[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(n\), \(~\)]\)"];DefTensor[ua[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(u\), \(+\)]\)"];DefConstantSymbol[DD];


AdvFieldVal[{0,Fra}]=Module[{i,j},
					(NormalSign/ra[])(ChargeCurrenta[{0,Fra}]) + (NormalSign/ra[]^2)ChargeDipolea[{0,Fra},{i,Fra3}]norma[{-i,-Fra3}]
					 +(-ParPropSign * DipoleRsign \[Epsilon]/ra[])ChargeDipolea[{i,Fra3},{0,Fra}]acca[{-i,-Fra3}]
					 + (+ NormalSign \[Epsilon]/ra[])(-ChargeDipolea[{0,Fra},{i,Fra3}]acca[{-i,-Fra3}])
					 + (- ParPropSign \[Epsilon]/ra[])(-ChargeDipolea[{i,Fra3},{j,Fra3}] acca[{-i,-Fra3}]norma[{-j,-Fra3}])
					 + (+ NormalSign \[Epsilon]/ra[])(ChargeDipolea[{0,Fra},{j,Fra3}]norma[{-j,-Fra3}]acca[{-i,-Fra3}]norma[{i,Fra3}])
					 + (+ NormalSign*DerivSign*DipoleRsign*\[Epsilon]/ra[])(-PD[{0,-Fra}][ChargeDipolea[{0,Fra},{0,Fra}]])
					 + (+ NormalSign*DerivSign*\[Epsilon]/ra[])(PD[{0,-Fra}][ChargeDipolea[{0,Fra},{j,Fra3}]]norma[{-j,-Fra3}])];


AdvFieldVal[{k_,Fra3}]=Module[{i,j},
					(NormalSign/ra[])(ChargeCurrenta[{k,Fra3}]) + ( NormalSign/ra[]^2)ChargeDipolea[{k,Fra3},{i,Fra3}]norma[{-i,-Fra3}]
					 +(-ParPropSign * DipoleRsign \[Epsilon]/ra[])ChargeDipolea[{0,Fra},{0,Fra}]acca[{k,Fra3}]
					 + (+NormalSign \[Epsilon]/ra[])(-ChargeDipolea[{k,Fra3},{i,Fra3}]acca[{-i,-Fra3}])
					 + (- ParPropSign \[Epsilon]/ra[])(-ChargeDipolea[{0,Fra},{j,Fra3}] acca[{k,Fra3}]norma[{-j,-Fra3}])
					 + (+NormalSign \[Epsilon]/ra[])(ChargeDipolea[{k,Fra3},{j,Fra3}]norma[{-j,-Fra3}]acca[{-i,-Fra3}]norma[{i,Fra3}])
					 + (+NormalSign*DerivSign*DipoleRsign*\[Epsilon]/ra[])(-PD[{0,-Fra}][ChargeDipolea[{k,Fra3},{0,Fra}]])
					 + (+NormalSign*DerivSign*\[Epsilon]/ra[])(PD[{0,-Fra}][ChargeDipolea[{k,Fra3},{j,Fra3}]]norma[{-j,-Fra3}])];


ParPropSign=-1;NormalSign=1;DipoleRsign=1;DerivSign=-1;


AdvFieldVal[{0,Fra}]


AdvFieldVal[{k,Fra3}]


TauSub={Tau[]->Scalar[2r[] -  2 \[Epsilon] r[]^2 acc[{-i,-Fra3}]norm[{i,Fra3}] + 2 \[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]norm[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
							+ (2/3)\[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]acc[{i,Fra3}] - (4/3)\[Epsilon]^2 r[]^3 acc1d[{-i,-Fra3}]norm[{i,Fra3}] 
							+ \[Epsilon]^3 r[]^4 ((2/3) acc[{-i,-Fra3}]acc1d[{i,Fra3}] - (4/3) acc[{-i,-Fra3}]acc[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
										 - 2 acc[{-i,-Fra3}]acc[{-k,-Fra3}]acc[{-j,-Fra3}]norm[{i,Fra3}]norm[{k,Fra3}]norm[{j,Fra3}]
										 -(2/3) acc2d[{i,Fra3}]norm[{-i,-Fra3}]
										 + 4 acc[{-i,-Fra3}]norm[{i,Fra3}]acc1d[{j,Fra3}]norm[{-j,-Fra3}])]};


((-r[] + (1/2)(1 + \[Epsilon] r[] acc[{-i,-Fra3}]norm[{i,Fra3}])Tau[] + (\[Epsilon]/6)(\[Epsilon] r[] acc1d[{i,Fra3}]norm[{-i,-Fra3}] - \[Epsilon] r[]acc[{-i,-Fra3}]acc[{i,Fra3}])Tau[]^2
	 + (\[Epsilon]^2/24)(acc[{-i,-Fra3}]acc[{i,Fra3}] + \[Epsilon] r[] acc2d[{i,Fra3}]norm[{-i,-Fra3}] - \[Epsilon] r[] acc2d[{0,Fra}]) Tau[]^3
	 - (\[Epsilon]^3/120)(10 acc[{-i,-Fra3}]acc1d[{i,Fra3}] - 5 acc2d[{0,Fra}])Tau[]^4)/.TauSub//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle]


radv=(-r[] + (1 + \[Epsilon] r[]acc[{i,Fra3}]norm[{-i,-Fra3}])Tau[] + (\[Epsilon]/2)(\[Epsilon] r[] acc1d[{i,Fra3}]norm[{-i,-Fra3}] - \[Epsilon] r[]acc[{-i,-Fra3}]acc[{i,Fra3}])Tau[]^2
				+ (\[Epsilon]^2/6)(acc[{-i,-Fra3}]acc[{i,Fra3}] + \[Epsilon] r[] acc2d[{i,Fra3}]norm[{-i,-Fra3}] - \[Epsilon] r[] acc2d[{0,Fra}]) Tau[]^3
				- (\[Epsilon]^3/24)(10 acc[{-i,-Fra3}]acc1d[{i,Fra3}] - 5 acc2d[{0,Fra}])Tau[]^4);


acc2d[{0,Fra}]:=Module[{i},3 acc[{-i,-Fra3}]acc1d[{i,Fra3}]];


(radv/.TauSub//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle]


acc2d[{-i_,-Fra3}]:=Module[{j},CDelta[-Fra3,-Fra3][{-j,-Fra3},{-i,-Fra3}]acc2d[{j,Fra3}]]


ParPropAdvExpand={ParProp[{0,Fra},{0,-Fra}]:>Module[{i},1 + (1/2)\[Epsilon]^2 Tau[]^2 acc[{-i,-Fra3}]acc[{i,Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{0,Fra}]],
				  ParProp[{0,Fra},{-l_,-Fra3}]:>(\[Epsilon] Tau[]acc[{-l,-Fra3}] + (1/2)\[Epsilon]^2 Tau[]^2 acc1d[{-l,-Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{-l,-Fra3}]),
				  ParProp[{k_,Fra3},{0,-Fra}]:>\[Epsilon] Tau[]acc[{k,Fra3}] + (1/2)Tau[]^2 \[Epsilon]^2 acc1d[{k,Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{k,Fra3}],
				  ParProp[{k_,Fra3},{-l_,-Fra3}]:>CDelta[Fra3,-Fra3][{k,Fra3},{-l,-Fra3}]+ (1/2) \[Epsilon]^2 Tau[]^2 acc[{-l,-Fra3}]acc[{k,Fra3}]
													+(1/6)\[Epsilon]^3 Tau[]^3 (acc[{-l,-Fra3}]acc1d[{k,Fra3}] + 2 acc1d[{-l,-Fra3}]acc[{k,Fra3}])};


FrameAdvExpandJustDipole={ChargeDipolea[a_,b_]:>Module[{},ChargeDipole[a,b] + \[Epsilon] Tau[]PD[{0,-Fra}][ChargeDipole[a,b]]
												+ (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]
												+ (1/6)\[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]]};


FrameAdvExpandTau={Tau[]->Scalar[2r[] -  2 \[Epsilon] r[]^2 acc[{-i,-Fra3}]norm[{i,Fra3}] + 2 \[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]norm[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
									+ (2/3)\[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]acc[{i,Fra3}] - (4/3)\[Epsilon]^2 r[]^3 acc1d[{i,Fra3}]norm[{-i,-Fra3}]]};


FrameAdvExpandua={ua[a_]:>Basis[{0,-Fra},a] + \[Epsilon] Tau[] acc[a] + (1/2)\[Epsilon]^2 Tau[]^2 acc1d[a] + (1/6)\[Epsilon]^2 Tau[]^3 acc2d[a]};


FrameAdvExpand={ra[]->Scalar[r[] + (2/3)\[Epsilon]^2 r[]^3 acc1d[{i,Fra3}]norm[{-i,-Fra3}]
							+\[Epsilon]^3 r[]^4( - (2/3)acc[{-i,-Fra3}]acc[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
										+ (2/3) acc2d[{i,Fra3}]norm[{-i,-Fra3}] 
										- (4/3)acc[{-i,-Fra3}]norm[{i,Fra3}]acc1d[{j,Fra3}]norm[{-j,-Fra3}])],
				acca[a_]:>acc[a] + \[Epsilon] Tau[] PD[{0,-Fra}][acc[a]] + (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][acc[a]]],
				ChargeCurrenta[a_]:>Module[{i},ChargeCurrent[a] - 2 \[Epsilon] PD[{0,-Fra}][ChargeDipolea[a,{0,Fra}]]
											  - 2 \[Epsilon] Basis[a,{-i,-Fra3}]acca[{i,Fra3}]ChargeDipolea[{0,Fra},{0,Fra}] 
											  - 2 \[Epsilon] Basis[{0,-Fra},a]acca[{-i,-Fra3}]ChargeDipolea[{i,Fra3},{0,Fra}]
											  + \[Epsilon] Tau[] PD[{0,-Fra}][ChargeCurrent[a]]
											  + (1/2) \[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][ChargeCurrent[a]]]
											  + (1/6) \[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeCurrent[a]]]]],
				PD[{0,-Fra}][ChargeDipolea[a_,b_]]:>Module[{j},PD[{0,-Fra}][ChargeDipole[a,b]] + \[Epsilon] Tau[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]
																+ (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]
															    + (1/6)\[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]]]};


PDraExpand={PD[{0,-Fra}][ra[]]->Scalar[(( PD[{0,-Fra}][ra[]]/.FrameAdvExpand//NoScalar//Frame31Split//BasisCanon[NoScreenNoMetric])/.{\[Epsilon]^n_/;n>3:>0})],
			PD[{-i_,-Fra3}][ra[]]->((PD[{-i,-Fra3}][ra[]]/.FrameAdvExpand//NoScalar//Frame31Split//BasisCanon[NoScreenNoMetric])
										/.{\[Epsilon]^n_/;n>3:>0,PD[__][acc2d[__]]:>0}//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)};


ApplyPDraExpand[expr_]:=Nest[(#/.{exp_*PD[ind_][ra[]]:>(exp*((PD[ind][ra[]]/.PDraExpand)//GenerateNewDummies)//Expand)}//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}&,expr,4];


(\[Epsilon] PD[{0,-Fra}][ra[]]/.FrameAdvExpand//NoScalar//Frame31Split//BasisCanon[NoMetriconVBundle])/.{\[Epsilon]^n_/;n>3:>0}


(\[Epsilon] PD[{0,-Fra}][ra[]]/.FrameAdvExpand//NoScalar//Frame31Split//BasisCanon[NoMetriconVBundle])/.{\[Epsilon]^n_/;n>3:>0}


normaExpand={norma[{k_,Fra3}]:>Module[{i},CDelta[Fra3,Fra3][{k,Fra3},{i,Fra3}]PD[{-i,-Fra3}][ra[]] -  \[Epsilon] norma[{k,Fra3}] ra[] acca[{-i,-Fra3}]norma[{i,Fra3}]]};


normaExpand={norma[{k_,Fra3}]:>Module[{i,j,l},CDelta[Fra3,Fra3][{k,Fra3},{l,Fra3}]PD[{-l,-Fra3}][ra[]]
											 -  \[Epsilon] ParProp[{k,Fra3},{-l,-Fra3}]norma[{l,Fra3}] ra[] acca[{-i,-Fra3}]norma[{i,Fra3}]]};


normaExpand={norma[{-k_,-Fra3}]:>Module[{i,j,l},ParProp[{l,Fra3},{-k,-Fra3}]PD[{-l,-Fra3}][ra[]]
											+ \[Epsilon] ParProp[{0,Fra},{-k,-Fra3}]PD[{0,-Fra}][ra[]]
											 -  \[Epsilon] norma[{-k,-Fra3}] ra[] acca[{i,Fra3}]norma[{-i,-Fra3}]]};


((norma[{k,Fra3}]/.normaExpand//Frame31Split)/.normaExpand//Expand)


((((((norma[{-i,-Fra3}]/.normaExpand//Frame31Split)/.normaExpand//Expand)/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}
		/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar)/.ParPropAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}


((((((((((((norma[{-i,-Fra3}]/.normaExpand//Frame31Split)/.normaExpand//Expand)/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}
		/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar)/.ParPropAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}//BasisCanon[NoMetriconVBundle])
		//ApplyPDraExpand)//NoScalar//BasisCanon[NoMetriconVBundle])/.FrameAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle])
		/.FrameAdvExpandTau//Expand)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle]


(((((((((norma[{k,Fra3}]/.normaExpand//Frame31Split)/.normaExpand//Expand)/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}
		/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle])/.ParPropAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}
		//NoScalar//ApplyPDraExpand)//NoScalar//BasisCanon[NoMetriconVBundle])/.FrameAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}


((((norma[{k,Fra3}]/.normaExpand//Frame31Split)/.normaExpand)/.{\[Epsilon]^n_/;n>3:>0}//Expand//Frame31Split)/.normaExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}


((((((((((((norma[{0,-Fra}]/.normaExpand/.normaExpand//ExpandAll)/.normaExpand//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}/.normaExpand//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0})
			//Frame31Split)//ScaleDerivs)/.{\[Epsilon]^n_/;n>3:>0}//ApplyPDraExpand)/.PDraExpand)//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}
			//NoScalar//BasisCanon[NoMetriconVBundle])/.FrameAdvExpand//ExpandAll//NoScalar)/.{\[Epsilon]^n_/;n>3:>0}/.FrameAdvExpandTau//ExpandAll//NoScalar)/.{\[Epsilon]^n_/;n>3:>0}//BasisCanon[NoMetriconVBundle]


FrameNormaExpand={(*norma[{0,Fra}]:>-Module[{i,j,k}, -\[Epsilon] r[](acc[{-i,-Fra3}]norm[{i,Fra3}]) 
												+ \[Epsilon]^2 r[]^2(acc[{-i,-Fra3}]norm[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}])
												+ \[Epsilon]^3 r[]^3(-(2/3) acc[{-i,-Fra3}]acc1d[{i,Fra3}]
														    -(2/3) acc[{-i,-Fra3}]acc[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
															- acc[{-i,-Fra3}]acc[{-j,-Fra3}]acc[{-k,-Fra3}]norm[{i,Fra3}]norm[{j,Fra3}]norm[{k,Fra3}]
															+ (2/3)acc2d[{i,Fra3}]norm[{-i,-Fra3}] 
															+ (2/3)acc[{-i,-Fra3}]norm[{i,Fra3}]acc1d[{j,Fra3}]norm[{-j,-Fra3}])],
				 norma[{0,-Fra}]:>Module[{i,j,k}, -\[Epsilon] r[](acc[{-i,-Fra3}]norm[{i,Fra3}]) 
												+ \[Epsilon]^2 r[]^2(acc[{-i,-Fra3}]norm[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}])
												+ \[Epsilon]^3 r[]^3(-(2/3) acc[{-i,-Fra3}]acc1d[{i,Fra3}] 
															-(2/3) acc[{-i,-Fra3}]acc[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
															- acc[{-i,-Fra3}]acc[{-j,-Fra3}]acc[{-k,-Fra3}]norm[{i,Fra3}]norm[{j,Fra3}]norm[{k,Fra3}]
															+ (2/3)acc2d[{i,Fra3}]norm[{-i,-Fra3}] 
															+ (2/3)acc[{-i,-Fra3}]norm[{i,Fra3}]acc1d[{j,Fra3}]norm[{-j,-Fra3}])],*)
				 norma[{-i_,-Fra3}]:>Module[{j,k,l},norm[{-i,-Fra3}] 
													+ \[Epsilon]^2 r[]^2((2/3) acc1d[{j,Fra3}]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] 
																- (2/3)acc1d[{j,Fra3}]norm[{-j,-Fra3}]norm[{-i,-Fra3}])
													 +\[Epsilon]^3 r[]^3( -(2/3) acc[{-i,-Fra3}]acc[{-j,-Fra3}]acc[{j,Fra3}]
															+ (2/3)acc2d[{j,Fra3}]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-i,-Fra3}]
														(*	- 2 acc[{-j,-Fra3}]acc1d[{k,Fra3}]norm[{j,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{-i,-Fra3}]*)
															+ (2/3)acc[{-j,-Fra3}]acc[{j,Fra3}]acc[{-k,-Fra3}]norm[{k,Fra3}]norm[{-i,-Fra3}]
															- (4/3)acc[{j,Fra3}]acc1d[{-i,-Fra3}]norm[{-j,-Fra3}]  (**)
															- (2/3) acc2d[{j,Fra3}]norm[{-j,-Fra3}]norm[{-i,-Fra3}]
															+ (4/3) acc[{-j,-Fra3}]acc1d[{k,Fra3}]norm[{j,Fra3}]norm[{-k,-Fra3}]norm[{-i,-Fra3}])],
				 norma[{i_,Fra3}]:>Module[{j,k,l},norm[{i,Fra3}] 
													+ \[Epsilon]^2 r[]^2((2/3) acc1d[{j,Fra3}]CDelta[-Fra3,-Fra3][{i,Fra3},{-j,-Fra3}] 
																- (2/3)acc1d[{j,Fra3}]norm[{-j,-Fra3}]norm[{i,Fra3}])
													 +\[Epsilon]^3 r[]^3( -(2/3) acc[{i,Fra3}]acc[{-j,-Fra3}]acc[{j,Fra3}]
															+ (2/3)acc2d[{j,Fra3}]CDelta[-Fra3,-Fra3][{-j,-Fra3},{i,Fra3}]
														(*	- 2 acc[{-j,-Fra3}]acc1d[{k,Fra3}]norm[{j,Fra3}]CDelta[-Fra3,-Fra3][{-k,-Fra3},{i,Fra3}]*)
															+ (2/3)acc[{-j,-Fra3}]acc[{j,Fra3}]acc[{-k,-Fra3}]norm[{k,Fra3}]norm[{i,Fra3}]
															- (4/3)acc[{j,Fra3}]acc1d[{i,Fra3}]norm[{-j,-Fra3}]  (**)
															- (2/3) acc2d[{j,Fra3}]norm[{-j,-Fra3}]norm[{i,Fra3}]
															+ (4/3) acc[{-j,-Fra3}]acc1d[{k,Fra3}]norm[{j,Fra3}]norm[{-k,-Fra3}]norm[{i,Fra3}])]};


norma[{0,-Fra}]/.FrameNormaExpand//BasisCanon[NoMetriconVBundle]


norma[{i,Fra3}]/.FrameNormaExpand//ExpandAll//BasisCanon[NoMetriconVBundle]


norma[{-i,-Fra3}]/.FrameNormaExpand//ExpandAll//BasisCanon[NoMetriconVBundle]


norma[{-i,-Fra3}]/.FrameNormaExpand//ExpandAll//BasisCanon[NoMetriconVBundle]


ApplyFrameNormaExpand[maxorder_][expr_Plus]:=ApplyFrameNormaExpand[maxorder]/@expr;
ApplyFrameNormaExpand[maxorder_][\[Epsilon]^n_ *expr_]:=\[Epsilon]^n((expr/.FrameNormaExpand)/.{\[Epsilon]^m_/;m>(maxorder-n):>0})//ExpandAll;
ApplyFrameNormaExpand[maxorder_][expr_]:=((expr/.FrameNormaExpand)/.{\[Epsilon]^m_/;m>(maxorder):>0});


(* ::Text:: *)
(*I've split these out so that each separate rule should only need to be applied once:*)


(* ::Text:: *)
(*Bottom index corresponds to FUTURE points.*)


ParPropAdvExpand={ParProp[{0,Fra},{0,-Fra}]:>Module[{i},1 + (1/2)\[Epsilon]^2 Tau[]^2 acc[{-i,-Fra3}]acc[{i,Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{0,Fra}]],
				  ParProp[{0,Fra},{-l_,-Fra3}]:>(\[Epsilon] Tau[]acc[{-l,-Fra3}] + (1/2)\[Epsilon]^2 Tau[]^2 acc1d[{-l,-Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{-l,-Fra3}]),
				  ParProp[{k_,Fra3},{0,-Fra}]:>\[Epsilon] Tau[]acc[{k,Fra3}] + (1/2)Tau[]^2 \[Epsilon]^2 acc1d[{k,Fra3}] + (1/6)\[Epsilon]^3 Tau[]^3 acc2d[{k,Fra3}],
				  ParProp[{k_,Fra3},{-l_,-Fra3}]:>CDelta[Fra3,-Fra3][{k,Fra3},{-l,-Fra3}]+ (1/2) \[Epsilon]^2 Tau[]^2 acc[{-l,-Fra3}]acc[{k,Fra3}]
													+(1/6)\[Epsilon]^3 Tau[]^3 (acc[{-l,-Fra3}]acc1d[{k,Fra3}] + 2 acc1d[{-l,-Fra3}]acc[{k,Fra3}])};


FrameAdvExpandJustDipole={ChargeDipolea[a_,b_]:>Module[{},ChargeDipole[a,b] + \[Epsilon] Tau[]PD[{0,-Fra}][ChargeDipole[a,b]]
												+ (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]
												+ (1/6)\[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]]};


FrameAdvExpandTau={Tau[]->Scalar[2r[] -  2 \[Epsilon] r[]^2 acc[{-i,-Fra3}]norm[{i,Fra3}] + 2 \[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]norm[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
									+ (2/3)\[Epsilon]^2 r[]^3 acc[{-i,-Fra3}]acc[{i,Fra3}] - (4/3)\[Epsilon]^2 r[]^3 acc1d[{i,Fra3}]norm[{-i,-Fra3}]]};


FrameAdvExpandua={ua[a_]:>Basis[{0,-Fra},a] + \[Epsilon] Tau[] acc[a] + (1/2)\[Epsilon]^2 Tau[]^2 acc1d[a] + (1/6)\[Epsilon]^2 Tau[]^3 acc2d[a]};


(radv/.TauSub//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle]


FrameAdvExpand={ra[]->Scalar[r[] + (2/3)\[Epsilon]^2 r[]^3 acc1d[{i,Fra3}]norm[{-i,-Fra3}]
							+\[Epsilon]^3 r[]^4( - (2/3)acc[{-i,-Fra3}]acc[{i,Fra3}]acc[{-j,-Fra3}]norm[{j,Fra3}]
										+ (2/3) acc2d[{i,Fra3}]norm[{-i,-Fra3}] 
										- (4/3)acc[{-i,-Fra3}]norm[{i,Fra3}]acc1d[{j,Fra3}]norm[{-j,-Fra3}])],
				acca[a_]:>acc[a] + \[Epsilon] Tau[] PD[{0,-Fra}][acc[a]] + (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][acc[a]]],
				ChargeCurrenta[a_]:>Module[{i},ChargeCurrent[a] - 2 \[Epsilon] PD[{0,-Fra}][ChargeDipolea[a,{0,Fra}]]
											  - 2 \[Epsilon] Basis[a,{-i,-Fra3}]acca[{i,Fra3}]ChargeDipolea[{0,Fra},{0,Fra}] 
											  - 2 \[Epsilon] Basis[{0,-Fra},a]acca[{-i,-Fra3}]ChargeDipolea[{i,Fra3},{0,Fra}]
											  + \[Epsilon] Tau[] PD[{0,-Fra}][ChargeCurrent[a]]
											  + (1/2) \[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][ChargeCurrent[a]]]
											  + (1/6) \[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeCurrent[a]]]]],
				PD[{0,-Fra}][ChargeDipolea[a_,b_]]:>Module[{j},PD[{0,-Fra}][ChargeDipole[a,b]] + \[Epsilon] Tau[]PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]
																+ (1/2)\[Epsilon]^2 Tau[]^2 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]
															    + (1/6)\[Epsilon]^3 Tau[]^3 PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][PD[{0,-Fra}][ChargeDipole[a,b]]]]]]};


DefTensor[AdvFieldVal[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(A\), \(+\)]\)"];


ContractDelta={CDelta[Fra3,-Fra3][{k_,Fra3},{-l_,-Fra3}]tens_[first___,{l_,Fra3},last___]:>tens[first,{k,Fra3},last],
				CDelta[Fra3,-Fra3][{k_,Fra3},{-l_,-Fra3}]PD[{0,-Fra}][tens_[first___,{l_,Fra3},last___]]:>PD[{0,-Fra}][tens[first,{k,Fra3},last]],
				CDelta[Fra3,-Fra3][{k_,Fra3},{-l_,-Fra3}]PD[{0,-Fra}][PD[{0,-Fra}][tens_[first___,{l_,Fra3},last___]]]:>PD[{0,-Fra}][PD[{0,-Fra}][tens[first,{k,Fra3},last]]]};


DefTensor[Afielda[a],{M4}];


Afielda[{0,Fra}]=((((((((ParProp[{0,Fra},{-a,-Fra}]AdvFieldVal[{a,Fra}] //Frame31Split)/.ParPropAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}/.RetFrameVectorRules
			//ApplyFrameNormaExpand[3])//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}/.FrameAdvExpand//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//Series[#,{\[Epsilon],0,3}]&
			//Normal//NoScalar//BasisCanon[NoMetriconVBundle])/.RetFrameVectorRules/.FrameAdvExpand/.FrameAdvExpandJustDipole/.FrameAdvExpand//ExpandAll)
			/.{\[Epsilon]^n_/;n>3:>0}/.FrameAdvExpandTau//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//NoScalar//BasisCanon[NoMetriconVBundle]


Afielda[{k_,Fra3}]=((((((((ParProp[{k,Fra3},{-a,-Fra}]AdvFieldVal[{a,Fra}] //Frame31Split)/.ParPropAdvExpand//Expand)/.{\[Epsilon]^n_/;n>3:>0}/.RetFrameVectorRules
			//ApplyFrameNormaExpand[3])//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}/.FrameAdvExpand//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}//Series[#,{\[Epsilon],0,3}]&
			//Normal//NoScalar//BasisCanon[NoMetriconVBundle])/.RetFrameVectorRules/.FrameAdvExpand/.FrameAdvExpandJustDipole/.FrameAdvExpand//ExpandAll)
			/.{\[Epsilon]^n_/;n>3:>0}/.FrameAdvExpandTau//ExpandAll)/.{\[Epsilon]^n_/;n>3:>0}/.ContractDelta//NoScalar//BasisCanon[NoMetriconVBundle]


Afieldr[{k,Fra3}]/.ScaledAfieldRules//BasisCanon[NoMetriconVBundle]


DefConstantSymbol[A0];DefConstantSymbol[Ak];


DefTensor[AretminusAdv[a],{M4}];


AretminusAdv[{0,Fra}]=(((1/2)(Afieldr[{0,Fra}]-Afielda[{0,Fra}])/.ScaledAfieldRules//BasisCanon[NoMetriconVBundle]//GenerateNewDummies))


AretminusAdv[{k_,Fra3}]=(((1/2)(Afieldr[{k,Fra3}]-Afielda[{k,Fra3}])/.ScaledAfieldRules//BasisCanon[NoMetriconVBundle]//GenerateNewDummies))


(* ::Subsubsection:: *)
(*r-perturbation expansion 'qerturb'*)


Q[expr_Plus]:=Q/@expr;
Q[expr_Times]:=Plus@@(((Q[expr[[#]]]*Times@@(Delete[List@@expr,#]))&)/@Range[Length[expr]]);
Q[expr_^n_]:=n*Q[expr]*expr^(n-1);
Q[Fstr[inds__]]:=Fstrpert[LI[{0,1}],inds];
Q[Fstrpert[LI[o_?NumericQ],inds__]]:=Fstrpert[LI[{o,1}],inds];
Q[Fstrpert[LI[{o_,q_}],inds__]]:=Fstrpert[LI[{o,q+1}],inds];
Q[SE[inds__]]:=SEpert[LI[{0,1}],inds];
Q[SEpert[LI[o_?NumericQ],inds__]]:=SEpert[LI[{o,1}],inds];
Q[SEpert[LI[{o_,q_}],inds__]]:=SEpert[LI[{o,q+1}],inds];
Q[norm[__]]:=0;
Q[acc[__]]:=0;
Q[r[]]:=0;
Q[r[]]:=0;
Q[\[Epsilon]]:=0;
Q[expr_?NumericQ]:=0;
Q[CDelta[__][__]]:=0;
Q[PD[-{0,Ret}][expr_]]:=PD[-{0,Ret}][Q[expr]];
Q[PD[junk__][expr_]]:=PD[junk][Q[expr]];


Qerturb[expr_,n_]:=Plus@@((((q^#/#!)Nest[Q,expr,#])&)/@Range[0,n]);


(* ::Subsubsection:: *)
(*Retarded field components*)


ClearAll[FstrfieldRules]


CheckpointGenerate3p1[Fstr[{-a,-Fra},{-b,-Fra}]][FstrfieldRules]["~/.EMSelfForceCache/FstrRules.mx"][\
((((( (#)/.{Fstr[a_,b_]:>Module[{c,d},met[b,{-c,-Fra}]met[a,{d,Fra}]CD[{-d,-Fra}][Afieldr[{c,Fra}]] - met[a,{-c,-Fra}]met[b,{d,Fra}]CD[{-d,-Fra}][Afieldr[{c,Fra}]]]}
	//Frame31Split//ScaleDerivs//ScaledFrameCDtoPD)/.RetFrameVectorRules/.ScaledAfieldRules/.{\[Lambda]->1})//ExpandAll)/.ConvertScalediFraDerivs)/.{r[]->((1/\[Lambda])r[])}//NoScalar//BasisCanon[NoScreenNoMetric]
		//GenerateNewDummies)&];//Timing


(* ::Text:: *)
(*All of this generation is required, unfortunately, for evaluating surface integrals of stress-energy values to their corresponding dependence on the field quantities.*)


(* ::Text:: *)
(*This set could be further optimized, but I'm not going to do so at the moment*)


(* ::Text:: *)
(*This section has grown far uglier than I initially intended. It could use an additional refactor - I had expected only to need a couple of orders of the field strength*)


Unprotect[ScreenDollarIndices];ScreenDollarIndices[xAct`xTensor`Private`expr_Plus]=.;Protect[ScreenDollarIndices];


ClearAll[FstrfieldRulespert01];ClearAll[FstrfieldRulespert11];ClearAll[FstrfieldRulespert21];ClearAll[FstrfieldRulespert31];
ClearAll[FstrfieldRulespert02];ClearAll[FstrfieldRulespert12];ClearAll[FstrfieldRulespert22];
ClearAll[FstrfieldRulespert03];ClearAll[FstrfieldRulespert13];
ClearAll[FstrfieldRulespert04];


CheckpointGenerate3p1[Fstrpert[LI[{0,1}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert01]["~/.EMSelfForceCache/FstrRulespert01.mx"][
(Coefficient[(Perturbed[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1]/.\[Epsilon]->0)//Expand,\[Lambda]]//ExpandAll)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{0,2}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert02]["~/.EMSelfForceCache/FstrRulespert02.mx"][
((2)Coefficient[(Perturbed[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1]/.\[Epsilon]->0)//Expand,\[Lambda]^2]//ExpandAll)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{0,3}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert03]["~/.EMSelfForceCache/FstrRulespert03.mx"][
((6)Coefficient[(Perturbed[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1]/.\[Epsilon]->0)//Expand,\[Lambda]^3]//ExpandAll)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{0,4}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert04]["~/.EMSelfForceCache/FstrRulespert04.mx"][
((24)Coefficient[(Perturbed[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1]/.\[Epsilon]->0)//Expand,\[Lambda]^4]//ExpandAll)&];//Timing


FstrfieldRulespert02


CheckpointGenerate3p1[Fstrpert[LI[{1,1}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert11]["~/.EMSelfForceCache/FstrRulespert11.mx"][\
(Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]])//Expand,\[Lambda]]//ExpandAll//GenerateNewDummies)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{1,2}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert12]["~/.EMSelfForceCache/FstrRulespert12.mx"][\
((2)Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]])//Expand,\[Lambda]^2]//ExpandAll//GenerateNewDummies)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{1,3}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert13]["~/.EMSelfForceCache/FstrRulespert13.mx"][\
((6)Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]])//Expand,\[Lambda]^3]//ExpandAll//GenerateNewDummies)&];//Timing


Perturb[(Fstrpert[{-i,-Fra3},{0,-Fra}]/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,2]


CheckpointGenerate3p1[Fstrpert[LI[{2,1}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert21]["~/.EMSelfForceCache/FstrRulespert21.mx"][\
((2)Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,2],\[Epsilon]^2]
				+ Coefficient[Perturb[Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]],1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]^2])//Expand,\[Lambda]]//ExpandAll//GenerateNewDummies)&];//Timing
CheckpointGenerate3p1[Fstrpert[LI[{2,2}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert22]["~/.EMSelfForceCache/FstrRulespert22.mx"][\
((4)Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,2],\[Epsilon]^2]
				+ Coefficient[Perturb[Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]],1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]^2])//Expand,\[Lambda]^2]//ExpandAll//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[Fstrpert[LI[{3,1}],{-a,-Fra},{-b,-Fra}]][FstrfieldRulespert31]["~/.EMSelfForceCache/FstrRulespert31.mx"][\
((6)Coefficient[(Coefficient[Perturb[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules/.\[Epsilon]->0,3],\[Epsilon]^3]
				+ Coefficient[Perturb[Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]],2],\[Epsilon]^2]
				+ Coefficient[Perturb[Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]^2],1],\[Epsilon]]
				+ Coefficient[(#/.{Fstrpert[a_,b_]:>Fstr[a,b]}//Expand)/.FstrfieldRules,\[Epsilon]^3])//Expand,\[Lambda]]//ExpandAll//GenerateNewDummies)&];//Timing


FstrfieldRulespert=(FstrfieldRulespert01~Join~FstrfieldRulespert02~Join~FstrfieldRulespert03~Join~FstrfieldRulespert04
				~Join~FstrfieldRulespert11~Join~FstrfieldRulespert12~Join~FstrfieldRulespert13
				~Join~FstrfieldRulespert21~Join~FstrfieldRulespert22
				~Join~FstrfieldRulespert31);


(* ::Subsubsection::Closed:: *)
(*Regular field components*)


DefTensor[RegFstr[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[\(F\), \(R\)]\)"];


ClearAll[RegFstrfieldRules];


CheckpointGenerate3p1[RegFstr[{-a,-Fra},{-b,-Fra}]][RegFstrfieldRules]["~/.EMSelfForceCache/RegFstrRules.mx"][\
((((( (#)/.{RegFstr[a_,b_]:>Module[{c,d},met[b,{-c,-Fra}]met[a,{d,Fra}]CD[{-d,-Fra}][Afieldr[{c,Fra}]] - met[a,{-c,-Fra}]met[b,{d,Fra}]CD[{-d,-Fra}][Afieldr[{c,Fra}]]]}
	//Frame31Split//ScaleDerivs//ScaledFrameCDtoPD)/.{\[Epsilon]^n_/;n>3:>0}/.RetFrameVectorRules/.{Afieldr->AretminusAdv}/.{\[Lambda]->1})//ExpandAll)/.ConvertScalediFraDerivs)/.{\[Epsilon]^n_/;n>3:>0}
		/.{r[]->(\[Lambda] r[])}//NoScalar//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)//.ConvertScalediFraDerivs&];//Timing


DefTensorPerturbation[RegFstrpert[LI[o],a,b],RegFstr[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[\(F\), \(R\)]\)"];


ClearAll[RegFstrfieldRulespert20];ClearAll[RegFstrfieldRulespert30];
ClearAll[RegFstrfieldRulespert21];ClearAll[RegFstrfieldRulespert31];


CheckpointGenerate3p1[RegFstrpert[LI[{2,1}],{-a,-Fra},{-b,-Fra}]][RegFstrfieldRulespert21]["~/.EMSelfForceCache/RegFstrRulespert21.mx"][\
((2)Coefficient[(Coefficient[Perturb[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules/.\[Epsilon]->0,2],\[Epsilon]^2]
	  + Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]],1],\[Epsilon]]
				+ Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^2])//Expand,\[Lambda]]//ExpandAll//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[RegFstrpert[LI[{2,0}],{-a,-Fra},{-b,-Fra}]][RegFstrfieldRulespert20]["~/.EMSelfForceCache/RegFstrRulespert20.mx"][\
((2)((Coefficient[Perturb[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules/.\[Epsilon]->0,2],\[Epsilon]^2]
	  + Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]],1],\[Epsilon]]
				+ Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^2])//Expand)/.{\[Lambda]->0}//ExpandAll//GenerateNewDummies)&];//Timing


(1/2)(RegFstrpert[LI[{2,0}],{-0,-Fra},{-i,-Fra3}]/.RegFstrfieldRulespert20)/.{ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}


(RegFstrpert[LI[{2,0}],{-j,-Fra3},{-i,-Fra3}]/.RegFstrfieldRulespert20)/.{ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}


CheckpointGenerate3p1[RegFstrpert[LI[{3,0}],{-a,-Fra},{-b,-Fra}]][RegFstrfieldRulespert30]["~/.EMSelfForceCache/RegFstrRulespert30.mx"][\
((6)((Coefficient[Perturb[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules/.\[Epsilon]->0,3],\[Epsilon]^3]
				+ Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]],2],\[Epsilon]^2]
				+ Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^2],1],\[Epsilon]]
				+ Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^3])//Expand)/.{\[Lambda]->0}//ExpandAll//GenerateNewDummies)&];//Timing


(* ::Text:: *)
(*Double-checking that the field strength is actually regular, as we hope:*)


(((((PD[{-k,-Fra3}][((1/6)(RegFstrpert[LI[{3,0}],{-0,-Fra},{-i,-Fra3}]/.RegFstrfieldRulespert30))]//ExpandAll)/.ConvertScalediFraDerivs)/.{\[Epsilon]->0})//BasisCanon[NoMetriconVBundle])
/.{acc2d[{0,Fra}]:>Module[{i},3 acc[{-i,-Fra3}]acc1d[{i,Fra3}]]}//BasisCanon[NoMetriconVBundle])


(((((PD[{-k,-Fra3}][((1/6)(RegFstrpert[LI[{3,0}],{-l,-Fra3},{-i,-Fra3}]/.RegFstrfieldRulespert30))]//ExpandAll)/.ConvertScalediFraDerivs)/.{\[Epsilon]->0})//BasisCanon[NoMetriconVBundle])
/.{acc2d[{0,Fra}]:>Module[{i},3 acc[{-i,-Fra3}]acc1d[{i,Fra3}]]}//BasisCanon[NoMetriconVBundle])


CheckpointGenerate3p1[RegFstrpert[LI[{3,1}],{-a,-Fra},{-b,-Fra}]][RegFstrfieldRulespert31]["~/.EMSelfForceCache/RegFstrRulespert31.mx"][\
((6)Coefficient[(Coefficient[Perturb[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules/.\[Epsilon]->0,3],\[Epsilon]^3]
				+ Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]],2],\[Epsilon]^2]
				+ Coefficient[Perturb[Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^2],1],\[Epsilon]]
				+ Coefficient[(#/.{RegFstrpert[a_,b_]:>RegFstr[a,b]}//Expand)/.RegFstrfieldRules,\[Epsilon]^3])//Expand,\[Lambda]]//ExpandAll//GenerateNewDummies)&];//Timing


RegFstrfieldRulespert=(RegFstrfieldRulespert20~Join~RegFstrfieldRulespert21
				~Join~RegFstrfieldRulespert30~Join~RegFstrfieldRulespert31);


((PD[{-k,-Fra3}][RegFstrpert[LI[{3,1}],{0,-Fra},{-j,-Fra3}]]/.RegFstrfieldRulespert31)/.{PD[{-i_,-Fra3}][PD[__][PD[__][PD[__][ChargeDipole[__]]]]]:>0,PD[{-i_,-Fra3}][acc2d[__]]:>0}
	/.{ChargeCurrent[{k_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}//.ConvertScalediFraDerivs/.{\[Epsilon]->0})//BasisCanon[NoMetriconVBundle]


((PD[{-k,-Fra3}][RegFstrpert[LI[{3,1}],{-i,-Fra3},{-j,-Fra3}]]/.RegFstrfieldRulespert31)/.{PD[{-i_,-Fra3}][PD[__][PD[__][PD[__][ChargeDipole[__]]]]]:>0,PD[{-i_,-Fra3}][acc2d[__]]:>0}
	/.{ChargeCurrent[{k_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0}//.ConvertScalediFraDerivs/.{\[Epsilon]->0})//BasisCanon[NoMetriconVBundle]


(* ::Subsubsection:: *)
(*Retarded stress energy *)


DefTensor[FstrpertTemp[a,b],{M4}];


ClearAll[SEfieldRulespert02];ClearAll[SEfieldRulespert03];ClearAll[SEfieldRulespert04];ClearAll[SEfieldRulespert05];ClearAll[SEfieldRulespert06];
ClearAll[SEfieldRulespert12];ClearAll[SEfieldRulespert13];ClearAll[SEfieldRulespert14];ClearAll[SEfieldRulespert15];
ClearAll[SEfieldRulespert22];ClearAll[SEfieldRulespert23];ClearAll[SEfieldRulespert24];
ClearAll[SEfieldRulespert32];ClearAll[SEfieldRulespert33];


(* ::Text:: *)
(*This gives too much optimization to not use - the leading current conservation equations imply that the leading current vanishes and the leading total charge (as defined from frame components) is conserved*)


ZeroLeadingCurrent={ChargeCurrent[{i_,Fra3}]:>0,PD[{0,-Fra}][ChargeCurrent[{0,Fra}]]:>0};


CheckpointGenerate3p1[SEpert[LI[{0,2}],{a,Fra},{b,Fra}]][SEfieldRulespert02]["~/.EMSelfForceCache/SEfieldRulespert02.mx"][\
((((((1/2)Q[Q[(#/.{SEpert[a_,b_]:>Module[{c,d,e,f},(1/(4 Pi))(met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}])]}
		//Frame31Split)]])/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2],Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule)/.FstrpertTemp->Fstrpert//GenerateNewDummies)/.FstrfieldRulespert//ExpandAll//BasisCanon[NoScreenNoMetric]
		//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{1,2}],{a,Fra},{b,Fra}]][SEfieldRulespert12]["~/.EMSelfForceCache/SEfieldRulespert12.mx"][\
((((((1/2)Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),1]//Expand,\[Epsilon]]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{2,2}],{a,Fra},{b,Fra}]][SEfieldRulespert22]["~/.EMSelfForceCache/SEfieldRulespert22.mx"][\
((((((2/2)Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),2]//Expand,\[Epsilon]^2]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{3,2}],{a,Fra},{b,Fra}]][SEfieldRulespert32]["~/.EMSelfForceCache/SEfieldRulespert32.mx"][\
((((((6/2)Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),3]//Expand,\[Epsilon]^3]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{0,3}],{a,Fra},{b,Fra}]][SEfieldRulespert03]["~/.EMSelfForceCache/SEfieldRulespert03.mx"][\
((((((1/6)Q@Q@Q[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split)])/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{1,3}],{a,Fra},{b,Fra}]][SEfieldRulespert13]["~/.EMSelfForceCache/SEfieldRulespert13.mx"][\
((((((1/6)Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),1]//Expand,\[Epsilon]]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{2,3}],{a,Fra},{b,Fra}]][SEfieldRulespert23]["~/.EMSelfForceCache/SEfieldRulespert23.mx"][\
((((((2/6)Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),2]//Expand,\[Epsilon]^2]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


(*CheckpointGenerate3p1[SEpert[LI[{3,3}],{a,Fra},{b,Fra}]][SEfieldRulespert33]["~/.EMSelfForceCache/SEfieldRulespert33.mx"][\
((((((1/6)Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),3]//Expand,\[Epsilon]^3]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing*)


DefTensor[SEpert33[a,b],{M4},Symmetric[{a,b}],PrintAs->"\!\(\*SuperscriptBox[\(T\), \((3, 3)\)]\)"];
SEfieldRulespert33={SEpert[LI[{3,3}],inds__]:>SEpert33[inds]};


CheckpointGenerate3p1[SEpert[LI[{0,4}],{a,Fra},{b,Fra}]][SEfieldRulespert04]["~/.EMSelfForceCache/SEfieldRulespert04.mx"][\
((((((1/24)Q@Q@Q@Q[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split)])/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


CheckpointGenerate3p1[SEpert[LI[{1,4}],{a,Fra},{b,Fra}]][SEfieldRulespert14]["~/.EMSelfForceCache/SEfieldRulespert14.mx"][\
((((((1/24)Q@Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),1]//Expand,\[Epsilon]]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


DefTensor[SEpert24[a,b],{M4},Symmetric[{a,b}],PrintAs->"\!\(\*SuperscriptBox[\(T\), \((2, 4)\)]\)"];
SEfieldRulespert24={SEpert[LI[{2,4}],inds__]:>SEpert24[inds]};


(*CheckpointGenerate3p1[SEpert[LI[{2,4}],{a,Fra},{b,Fra}]][SEfieldRulespert24]["~/.EMSelfForceCache/SEfieldRulespert24.mx"][\
((((((1/24)Q@Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),2]//Expand,\[Epsilon]^2]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing*)


CheckpointGenerate3p1[SEpert[LI[{0,5}],{a,Fra},{b,Fra}]][SEfieldRulespert05]["~/.EMSelfForceCache/SEfieldRulespert05.mx"][\
((((((1/120)Q@Q@Q@Q@Q[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split)])/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


(*CheckpointGenerate3p1[SEpert[LI[{1,5}],{a,Fra},{b,Fra}]][SEfieldRulespert15]["~/.EMSelfForceCache/SEfieldRulespert15.mx"][\
((((((1/120)Q@Q@Q@Q[Q[Coefficient[Perturb[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split),1]//Expand,\[Epsilon]]]]//ExpandAll)/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
		/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing*)


DefTensor[SEpert15[a,b],{M4},Symmetric[{a,b}],PrintAs->"\!\(\*SuperscriptBox[\(T\), \((1, 5)\)]\)"];
SEfieldRulespert15={SEpert[LI[{1,5}],inds__]:>SEpert15[inds]};


CheckpointGenerate3p1[SEpert[LI[{0,6}],{a,Fra},{b,Fra}]][SEfieldRulespert06]["~/.EMSelfForceCache/SEfieldRulespert06.mx"][\
((((((1/720)Q@Q@Q@Q@Q@Q[(#/.{SEpert[a_,b_]:>(1/(4 Pi))Module[{c,d,e,f},met[a,{c,Fra}] met[b,{d,Fra}] met[{e,Fra},{f,Fra}]Fstr[{-c,-Fra},{-e,-Fra}]Fstr[{-d,-Fra},{-f,-Fra}]  
								- (1/4)met[a,b]met[{c,Fra},{e,Fra}]met[{d,Fra},{f,Fra}]Fstr[{-c,-Fra},{-d,-Fra}]Fstr[{-e,-Fra},{-f,-Fra}]]}
		//Frame31Split)])/.{Fstrpert[LI[a__],inds1__]Fstrpert[LI[b__],inds2__]:>Fstrpert[LI[a],inds1]FstrpertTemp[LI[b],inds2]}
		//.{Fstr[__]:>0,Fstrpert[LI[n_?NumericQ],inds__]:>0,a_^2:>Scalar[a]^2}/.FstrfieldRulespert)/.FstrpertTemp->Fstrpert//GenerateNewDummies)
/.FstrfieldRulespert/.ZeroLeadingCurrent//NoScalar//Expand)//.nstoNsrule//ExpandAll//(ToCanonical[#,UseMetricOnVBundle->None]&)//BasisCanon[NoScreenNoMetric]//GenerateNewDummies)&];//Timing


FstrfieldRulespert11


SEfieldRulespert04[[1]]


SEfieldRulespert23[[1]]


SEfieldRulespert=(SEfieldRulespert02~Join~SEfieldRulespert03~Join~SEfieldRulespert04~Join~SEfieldRulespert05~Join~SEfieldRulespert06
				~Join~SEfieldRulespert12~Join~SEfieldRulespert13~Join~SEfieldRulespert14~Join~SEfieldRulespert15
				~Join~SEfieldRulespert22~Join~SEfieldRulespert23~Join~SEfieldRulespert24
				~Join~SEfieldRulespert32~Join~SEfieldRulespert33);


(* ::Section:: *)
(*Surface integration rules*)


StressTensorThroughInvr[n_]:={SE[inds__]:>Plus@@( Nest[Q,SE[inds],#]&/@Range[2,n]),
							SEpert[LI[o_],inds__]:>Plus@@(Nest[Q,SEpert[LI[o],inds],#]&/@Range[2,n])};


KeepInvR=False;


If[!KeepInvR,
SIntNull/:SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n<-2&&FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert)=0;
SIntNull/:SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n>=-2&&FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert):=
									SIntNull[expr* r[]^n((Stress[inds])/.StressTensorThroughInvr[2+n]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)];
SIntNull/:SIntNull[expr_ r[] Stress_[inds__]]/;FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert):=
									SIntNull[expr* r[]((Stress[inds])/.StressTensorThroughInvr[3]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)];
SIntNull/:SIntNull[expr_ Stress_[inds__]]/;FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert):=
									SIntNull[expr* ((Stress[inds])/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)];
SIntNull/:SIntNull[Stress_[inds__]]/;(Stress===SE||Stress===SEpert):=
									SIntNull[(Stress[inds]/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule)//GenerateNewDummies];
,
SIntNull/:SIntNull[expr_ Stress_[inds__]]/;(Stress===SE||Stress===SEpert):=
									SIntNull[expr* ((Stress[inds])/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)];
SIntNull/:SIntNull[Stress_[inds__]]/;(Stress===SE||Stress===SEpert):=
									SIntNull[(Stress[inds]/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule)//GenerateNewDummies];];


SIntNull/:SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n<-2&&FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert)=.;
SIntNull/:SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n>=-2&&FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert)=.;
SIntNull/:SIntNull[expr_ r[] Stress_[inds__]]/;FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert)=.;
SIntNull/:SIntNull[expr_ Stress_[inds__]]/;FreeQ[expr,r[]]&&(Stress===SE||Stress===SEpert)=.;
SIntNull/:SIntNull[Stress_[inds__]]/;(Stress===SE||Stress===SEpert)=.;


SurfaceFieldRules={HoldPattern[SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n<-2&&FreeQ[expr,(r[])]&&(Stress===SE||Stress===SEpert)]->0,
HoldPattern[SIntNull[expr_ r[]^n_ Stress_[inds__]]/;n>=-2&&FreeQ[expr,(r[])]&&(Stress===SE||Stress===SEpert)]:>
									SIntNull[expr* r[]^n((Stress[inds])/.StressTensorThroughInvr[2+n]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)],
HoldPattern[SIntNull[expr_ r[] Stress_[inds__]]/;FreeQ[expr,(r[])]&&(Stress===SE||Stress===SEpert)]:>
									SIntNull[expr* r[]((Stress[inds])/.StressTensorThroughInvr[3]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)],
HoldPattern[SIntNull[expr_ Stress_[inds__]]/;FreeQ[expr,(r[])]&&(Stress===SE||Stress===SEpert)]:>
									SIntNull[expr* ((Stress[inds])/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule//GenerateNewDummies)],
HoldPattern[SIntNull[Stress_[inds__]]/;(Stress===SE||Stress===SEpert)]:>
									SIntNull[(Stress[inds]/.StressTensorThroughInvr[2]/.SEfieldRulespert/.nstoNsrule)//GenerateNewDummies]};


(Fstrpert[LI[{1,1}],{-0,-Fra},{-i,-Fra3}]/.FstrfieldRulespert)/.ChargeCurrent[{k_,Fra3}]:>0


SIntNull[(acc[{i,Fra3}] - acc[{-j,-Fra3}]Ns[{j,Fra3},{i,Fra3}])/(4 Pi r[]^2)]//ExpandAll//ToCanonical


(Fstrpert[LI[{1,1}],{-k,-Fra3},{-i,-Fra3}]/.FstrfieldRulespert)/.ChargeCurrent[{k_,Fra3}]:>0


(* ::Text:: *)
(*So, the field renormalization is the first derivative of the angle-averaged 1/r piece of the self-field.*)


SIntNull[((Fstrpert[LI[{1,2}],{-0,-Fra},{-i,-Fra3}]/.FstrfieldRulespert)/.ChargeCurrent[{k_,Fra3}]:>0)/(4Pi)]//.nstoNsrule//ExpandAll//BasisCanon[NoMetriconVBundle]


SE[{0,Fra},{0,Fra}]/.StressTensorThroughInvr[4]/.SEfieldRulespert


SE[{0,Fra},{j,Fra3}]/.StressTensorThroughInvr[4]/.SEfieldRulespert


SE[{i,Fra3},{j,Fra3}]/.StressTensorThroughInvr[5]/.SEfieldRulespert


SE[{i,Fra3},{j,Fra3}]/.StressTensorThroughInvr[4]/.SEfieldRulespert
