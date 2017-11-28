(* ::Package:: *)

(* ::Subsection:: *)
(*Tensor definitions*)


(* ::Text:: *)
(*xTensor definition calls for stress energy T^(\[Mu]\[Vee]), J^\[Mu]*)


DefTensor[SE[a,b],{M4},Symmetric[{a,b}],PrintAs->"T"];
DefTensorPerturbation[SEpert[LI[o],a,b],SE[a,b],{M4},Symmetric[{a,b}],PrintAs->"T"];
DefTensor[CurrentDens[a],{M4},PrintAs->"j"];
DefTensorPerturbation[CurrentDenspert[LI[o],a],CurrentDens[a],{M4},PrintAs->"j"];


(* ::Text:: *)
(*xTensor definitions for the acceleration vector and its first derivative - it will be more convenient to have it as a separate object*)


DefTensor[Afieldr[a],{M4},PrintAs->"\!\(\*SubscriptBox[\(A\), \(-\)]\)"];


DefTensor[Fstr[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*Subsc riptBox[\(F\), \(-\)]\)"];
DefTensorPerturbation[Fstrpert[LI[ord],a,b],Fstr[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SubscriptBox[\(F\), \(-\)]\)"];


DefTensor[FExt[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*SuperscriptBox[\(F\), \((ext)\)]\)"];


DefTensor[ChargeCurrent[a],{M4},PrintAs->"J"];


DefTensorPerturbation[ChargeCurrentpert[LI[o],a],ChargeCurrent[a],{M4},PrintAs->"J"];


DefTensor[ChargeDipole[a,b],{M4},PrintAs->"Q"];


DefTensorPerturbation[ChargeDipolepert[LI[o],a,b],ChargeDipole[a,b],{M4},PrintAs->"Q"];


WLTensors={acc,accpert,acc1d,acc1dpert};


WLTensors=WLTensors~Join~{ChargeCurrent,ChargeCurrentpert,ChargeDipole,ChargeDipolepert};


(* ::Text:: *)
(*For retarded coordinates, it's necessary to deal with worldline quantities off the worldline, as (for instance), the acceleration frame components appear in the basis vectors.*)
(*When expressing these quantities in terms of Frame-projected derivatives, we can take advantage of the constraint that \!\( *)
(*\*SubscriptBox[\(\[PartialD]\), \(i\)]*)
(*\*SuperscriptBox[\(T\), \( *)
(*\*OverscriptBox[\(k\), \(^\)] ... \)]\) = 0. This is effectively parallel transport - contraction with the frame vectors*)


WLFrame3PDConvert[expr_]:=Module[{PDTempForm=expr//.toPDTemp},

Return[((PDTempForm//.{PDTemp[pre__,{i_,-Fra3},post___][tens_[tensinds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{tensinds})):>
						Module[{j},PDTemp[pre][-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]]PDTemp[{0,-Fra},post][tens[tensinds]]
									-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]PDTemp[pre,{0,-Fra},post][tens[tensinds]]],
						PDTemp[{i_,-Fra3},post___][tens_[tensinds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{tensinds})):>
						Module[{j},-CDelta[-Fra3,-Ret3][{i,-Fra3},{-j,-Ret3}]norm[{j,Ret3}]PDTemp[{0,-Fra},post][tens[tensinds]]]})//.fromPDTemp)//Expand];
];


Unprotect[PD];


DefConstantSymbol[\[Lambda]];


PD/:PD[{-i_,-Ret3}][tens_[inds__]]/;MemberQ[WLTensors,tens]&&(And@@(MemberQ[{Fra,Fra3,-Fra,-Fra3},#[[2]]]&/@{inds})):=0;


(* ::Subsubsection:: *)
(*Tensor documentation*)


SE::usage="SE is the symbol \!\(\*SubscriptBox[\(T\), \(\[Upsilon]\[Nu]\)]\) in the accompanying paper - it represents 
the sum of the retarded field contribution and the matter contribution - it is two-index and symmetric";
SEpert::usage"SEpert is the perturbed form of SE. The zeroth order is simply SE. Two index and symmetric.";


CurrentDens::usage="CurrentDens is the symbol \!\(\*SubscriptBox[\(j\), \(\[Upsilon]\)]\) from the accompanying paper 
it represents the charge-current vector, explicitly with compact support on the worldtube. one-index object.";
CurrentDenspert::usage"CurrentDenspert is the perturbed form of CurrentDens. one-index object.";


Afieldr::usage="Afieldr is the retarded vector 4-potential for the electromagnetic field. one-index object.
Replacement rules : AfieldRules and ScaledAfieldRules";


FExtpert::usage="FExt is the external (forcing) field strength. We choose to not expand its possible \[Epsilon] dependence.";


Fstr::usage="Fstr is the field-strength tensor from the retarded self-field Afieldr. It is an antisymmetric two-index object.
Replacement rules: FstrfieldRules.";


Fstrpert::usage="Fstrpert is the perturbed form of the field-strength Fstr. It is an antisymmetric two-index object.
The replacement rules assume a simultaneous expansion in \[Epsilon]^n and 1/r^m, and are written as Fstrpert[LI[{n,m}],a,b].
The set of replacement rules: Fstrfieldrulespert";


(* ::Subsection:: *)
(*Perturbation rules and overrides*)


(* ::Subsubsection:: *)
(*Perturbation rules*)


Unprotect[Perturbation];
Perturbation/:Perturbation[FExt[inds___],0]:=FExt[inds];
Perturbation/:Perturbation[FExt[inds___]]:=Module[{i},r[]Ns[{i,Fra3}]CD[-{i,Fra3}][FExt[inds]] + r[]CD[-{0,Fra}][FExt[inds]]];
Perturbation/:Perturbation[FExt[inds___],1]:=Module[{i},r[]Ns[{i,Fra3}]CD[-{i,Fra3}][FExt[inds]] + r[]CD[-{0,Fra}][FExt[inds]]];
Perturbation/:Perturbation[FExt[inds___],2]:=Module[{i,j},r[]^2 Ns[{i,Fra3},{j,Fra3}]CD[-{i,Fra3}][CD[-{j,Fra3}][FExt[inds]]] + 2 r[]^2 Ns[{i,Fra3}]CD[-{i,Fra3}][CD[-{0,Fra}][FExt[inds]]]
																+ r[]^2 CD[-{0,Fra}][CD[-{0,Fra}][FExt[inds]]]]
Perturbation/:Perturbation[FExt[inds___],n_]:=Module[{indices=(Unique[a]&/@Range[n]),TempExpr=FExt[inds]},
										For[ii=1,ii<=n,ii=ii+1,
											TempExpr=CD[-indices[[ii]]][TempExpr];];
										Return[Ns[Sequence@@indices]r[]^n TempExpr//Frame31Split]];
Protect[Perturbation];


Perturbation[FExt[{k,Fra3},{l,Fra3}],2]


FExt/:FExt[ind_,{-0,-Fra}]:=-FExt[ind,{0,Fra}];
FExt/:FExt[{-0,-Fra},ind_]:=-FExt[{0,Fra},ind];
FExt/:FExt[ind_,{-i_,-Fra3}]:=Module[{j},CDelta[-Fra3,-Fra3][-{i,Fra3},-{j,Fra3}]FExt[ind,{j,Fra3}]];
FExt/:FExt[{-i_,-Fra3},ind_]:=Module[{j},CDelta[-Fra3,-Fra3][-{i,Fra3},-{j,Fra3}]FExt[{j,Fra3},ind]];


CurrentDens/:CurrentDens[{-i_,-Fra3}]:=Module[{j},CDelta[-Fra3,-Fra3][{-i,-Fra3},-{j,Fra3}]CurrentDens[{j,Fra3}]];
CurrentDens/:CurrentDens[-{0,Fra}]:=-CurrentDens[{0,Fra}];


\[Epsilon]/:Perturbation[\[Epsilon],i_]/;i>=1:=0;
\[Epsilon]/:Perturbation[\[Epsilon],0]:=\[Epsilon];
\[Epsilon]/:Perturbation[\[Epsilon]]:=0;


norm/:Perturbation[norm[u_][{ind_,Ret3|Fra3|-Fra3}]]:=0;
norm/:Perturbation[norm[u_][{ind_,Ret3|Fra3|-Fra3}],i_]/;i>=1:=0;


Ns/:Perturbation[Ns[__]]:=0;
Ns/:Perturbation[Ns[__],i_]/;i>=1:=0;


r/:Perturbation[r[],i_]/;i>=1:=0;
r/:Perturbation[r[],0]:=r[];
r/:Perturbation[r[]]:=0;


CDelta/:Perturbation[CDelta[rank__][inds__],i_]/;DeltaValid[CDelta[rank][inds]]&&i>=1:=0;
CDelta/:Perturbation[CDelta[rank__][inds__],0]/;DeltaValid[CDelta[rank][inds]]:=CDelta[rank][inds];
CDelta/:Perturbation[CDelta[rank__][inds__]]/;DeltaValid[CDelta[rank][inds]]:=0;


(* ::Text:: *)
(*Just because the acceleration vector is purely spatial, and the frame indices are orthonormal.*)


acc/:Perturbation[acc[{ind_,-Fra3}]]:=accpert[LI[1],{ind,-Fra3}];
acc/:Perturbation[acc[{ind_,-Fra3}],num_]:=accpert[LI[num],{ind,-Fra3}];


(* ::Subsubsection:: *)
(*Custom perturbation code*)


(* ::Text:: *)
(*I have found that the xtensor perturbation function drags a bit.  I've defined a thin version as an optimization step*)


(* ::Text:: *)
(*TODO:re-write most of these rules to be more consise (a list of objects and perturbations, loop through and generate the 4 rules each pair needs)*)


(* ::Text:: *)
(*This assumes we never reduce order :*)


P[expr_Plus]:=P/@expr;
P[expr_Times]:=Plus@@(((P[expr[[#]]]*Times@@(Delete[List@@expr,#]))&)/@Range[Length[expr]]);
P[expr_^n_]:=n*P[expr]*expr^(n-1);
P[ChargeCurrent[ind_]]           :=ChargeCurrentpert[LI[1],ind];
P[ChargeCurrentpert[LI[o_],ind_]]:=ChargeCurrentpert[LI[o+1],ind];
P[ChargeDipole[inds__]]           :=ChargeDipolepert[LI[1],inds];
P[ChargeDipolepert[LI[o_],inds__]]:=ChargeDipolepert[LI[o+1],inds];
P[ChargeQuadPole[inds__]]           :=ChargeQuadPole[LI[1],inds];
P[ChargeQuadPolepert[LI[o_],inds__]]:=ChargeQuadPolepert[LI[o+1],inds];
P[Fstr[inds__]]:=Fstrpert[LI[1],inds];
P[Fstrpert[LI[o_],inds__]]:=Fstrpert[LI[o+1],inds];
P[acc[ind_]]             :=0;
P[accpert[LI[o_],ind_]]  :=0;
P[acc1d[ind_]]           :=0;
P[acc1dpert[LI[o_],ind_]]:=0;
P[norm[__]]:=0;
P[r[]]:=0;
P[r[]]:=0;
P[\[Epsilon]]:=0;
P[expr_?NumericQ]:=0;
P[CDelta[__][__]]:=0;
P[PD[-{0,Ret}][expr_]]:=PD[-{0,Ret}][P[expr]];
P[PD[junk__][expr_]]:=PD[junk][P[expr]];
P[\[Lambda]]:=0;
P[PD[arg_][expr_]]:=PD[arg][P[expr]];
P[PD[arg_][expr_],n_]:=PD[arg][P[expr,n]];
P[SE[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[1],inds];
P[SE[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[n],inds];
P[SEpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[o+1],inds];
P[SEpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=SEpert[LI[o+n],inds];
P[CurrentDens[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=CurrentDenspert[LI[1],inds];
P[CurrentDens[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=CurrentDenspert[LI[n],inds];
P[CurrentDenspert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=CurrentDenspert[LI[o+1],inds];
P[CurrentDenspert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=CurrentDenspert[LI[o+n],inds];
P[Mom[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[1],inds];
P[Mom[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[n],inds];
P[Mompert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[o+1],inds];
P[Mompert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Mompert[LI[o+n],inds];
P[HMom[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[1],inds];
P[HMom[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[n],inds];
P[HMompert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[o+1],inds];
P[HMompert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMompert[LI[o+n],inds];
P[HMomtemp[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMomtemppert[LI[1],inds];
P[HMomtemp[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMomtemppert[LI[n],inds];
P[HMomtemppert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HMomtemppert[LI[o+1],inds];
P[HMomtemppert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HMomtemppert[LI[o+n],inds];
P[Spin[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[1],inds];
P[Spin[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[n],inds];
P[Spinpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[o+1],inds];
P[Spinpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=Spinpert[LI[o+n],inds];
P[HSpin[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[1],inds];
P[HSpin[inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[n],inds];
P[HSpinpert[LI[o_],inds__]]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[o+1],inds];
P[HSpinpert[LI[o_],inds__],n_]/;FreeQ[{inds},(Ret|Ret3)]:=HSpinpert[LI[o+n],inds];
P[Ns[inds__]]:=0;
P[Scalar[expr_]]:=P[GenerateNewDummies[expr]];


P[IntNull[expr_]]:=IntNull[P[expr]];


P[CD[inds_][tens_]]:=CD[inds][P[tens]];
Q[CD[inds_][tens_]]:=CD[inds][Q[tens]];
Q[CurrentDens[__]]:=0;Q[CurrentDenspert[__]]:=0;


ApplyPtoFExt={P[P[FExt[inds__]]]/;FreeQ[{inds},(Ret|Ret3)]:>Perturbation[FExt[inds],2],
			  P[FExt[inds__]]/;FreeQ[{inds},(Ret|Ret3)]:>Perturbation[FExt[inds]]};


Perturb[expr_,n_]:=Plus@@((((\[Epsilon]^#/#!)Nest[P,expr,#])&)/@Range[0,n]);


(* ::Subsection:: *)
(*Body parameter index*)


(* ::Text:: *)
(*Removed legacy code from here, may need to replace if things break*)


DefTensor[Mom[a],{M4},PrintAs->"P"];
DefTensorPerturbation[Mompert[LI[order],a],Mom[a],{M4},PrintAs->"P"];


DefTensor[HMom[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(P\), \(~\)]\)"];
DefTensorPerturbation[HMompert[LI[o],a],HMom[a],{M4},PrintAs->"\!\(\*OverscriptBox[\(P\), \(~\)]\)"];


DefTensor[Spin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"S"];
DefTensorPerturbation[Spinpert[LI[o],a,b],Spin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"S"];


DefTensor[HSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*OverscriptBox[\(S\), \(~\)]\)"];
DefTensorPerturbation[HSpinpert[LI[o],a,b],HSpin[a,b],{M4},Antisymmetric[{a,b}],PrintAs->"\!\(\*OverscriptBox[\(S\), \(~\)]\)"];


DefTensor[ChargeQuadPole[a,b,c],{M4},Symmetric[{b,c}],PrintAs->"Q"];
DefTensorPerturbation[ChargeQuadPolepert[LI[o],a,b,c],ChargeQuadPole[a,b,c],{M4},PrintAs->"Q"];


$BodyParams={Mom,Mompert,
			 Spin,Spinpert,
             ChargeCurrent,ChargeCurrentpert,
			 ChargeDipole,ChargeDipolepert,
			 ChargeQuadPole,ChargeQuadPolepert};


(* ::Text:: *)
(*-TODO : Move this to a sumrule library. I think 1it is all that I will put in it, but it is sufficiently powerful that it should be in its own file-*)


(* ::Text:: *)
(*This attempts to mitigate the (egregious?) utter lack of support for replacements of sum-terms. There are a few caviats - we assume that the free indices and the coefficients are all that need*)
(*to be matched, and that the terms are given in descending 'strictness' - such that if an expression can match more than one way, the previous expressions in the sum terms sufficiently*)
(*constrain the ambiguous term. This is likely not compatible with all possible terms one would like to match, but this is all I can do at the moment.*)


Unprotect[PD];
PD[{-i_,-Ret3}][tens_[inds__]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
PD[{-i_,-Ret3}][PD[__][tens_[inds__]]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
PD[{-i_,-Ret3}][PD[__][PD[__][tens_[inds__]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[inds,(Ret|Ret3)]:=0;
Protect[PD];


ConvertScalediFraDerivs={PD[{-i_,-Fra3}][tens_[inds__]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][tens[inds]],
PD[{-i_,-Fra3}][PD[pdind__][tens_[inds__]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind][tens[inds]]],
PD[{-i_,-Fra3}][PD[pdind1__][PD[pdind2__][tens_[inds__]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]
				:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind1][PD[pdind2][tens[inds]]]],
PD[{-i_,-Fra3}][PD[pdind1__][PD[pdind2__][PD[pdind3_][tens_[inds__]]]]]/;MemberQ[$BodyParams,tens]&&FreeQ[{inds},(Ret|Ret3)]
				:>-\[Epsilon] norm[{-i,-Fra3}]PD[{0,-Fra}][PD[pdind1][PD[pdind2][PD[pdind3][tens[inds]]]]]};


MomentumSumRuleList=
Module[{partialList={},ii,jj},
	For[jj=0,jj<=3,jj++,
		partialList=partialList~Join~
				{{{Nest[PD[{0,-Fra}],IntNull[(SE[{0,Fra},{i,Fra3}]|SE[{i,Fra3},{0,Fra}])],jj],
		-Nest[PD[{0,-Fra}],IntNull[(SE[{k_,Fra3},{i,Fra3}] | SE[{i,Fra3},{k_,Fra3}])Ns[{l_,Fra3}]],jj]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{i_},{i}},Nest[PD[{0,-Fra}],Mom[{i,Fra3}],jj]},
				{{Nest[PD[{0,-Fra}],IntNull[(SE[{0,Fra},{0,Fra}]|SE[{0,Fra},{0,Fra}])],jj],
		-Nest[PD[{0,-Fra}],IntNull[(SE[{k_,Fra3},{0,Fra}] | SE[{0,Fra},{k_,Fra3}])Ns[{l_,Fra3}]],jj]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{},{}},Nest[PD[{0,-Fra}],Mom[{0,Fra}],jj]}};
		];

	For[ii=1,ii<=3,ii++,
		For[jj=ii,jj<=3,jj++,
		partialList=partialList~Join~
				{{{Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{0,Fra},{i,Fra3}]|SEpert[LI[ii],{i,Fra3},{0,Fra}])],jj-ii],
		-Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{k_,Fra3},{i,Fra3}] | SEpert[LI[ii],{i,Fra3},{k_,Fra3}])Ns[{l_,Fra3}]],jj-ii]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{i_},{i}},Nest[PD[{0,-Fra}],Mompert[LI[ii],{i,Fra3}],jj-ii]},
				{{Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{0,Fra},{0,Fra}]|SEpert[LI[ii],{0,Fra},{0,Fra}])],jj-ii],
		-Nest[PD[{0,-Fra}],IntNull[(SEpert[LI[ii],{k_,Fra3},{0,Fra}] | SEpert[LI[ii],{0,Fra},{k_,Fra3}])Ns[{l_,Fra3}]],jj-ii]
			 (CDelta[-Fra3,-Fra3][{-k_,-Fra3},{-l_,-Fra3}]|CDelta[-Fra3,-Fra3][{-l_,-Fra3},{-k_,-Fra3}])},
			{{},{}},Nest[PD[{0,-Fra}],Mompert[LI[ii],{0,Fra}],jj-ii]}};
		];
		];
	Return[partialList];];


SpinSumRuleList=
Module[{partialList={},ii,jj},
	For[jj=0,jj<=2,jj++,
		partialList=partialList~Join~{{{Nest[PD[{0,-Fra}],IntNull[Ns[{i, Fra3}]*r[]*SE[{0, Fra}, {0, Fra}]],jj],
			 	-Nest[PD[{0,-Fra}],IntNull[r[]*(SE[{0, Fra}, {i, Fra3}]|SE[{i, Fra3}, {0, Fra}])],jj],
			    -(Nest[PD[{0,-Fra}],IntNull[(Ns[{i, Fra3}, {k_, Fra3}]|Ns[{k_, Fra3},{i, Fra3}])*r[]*(SE[{j_, Fra3}, {0, Fra}]|SE[{0, Fra}, {j_, Fra3}])],jj]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}] | CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])),
				 Nest[PD[{0,-Fra}], IntNull[Ns[{j_, Fra3}]*r[]*(SE[{k_, Fra3}, {i, Fra3}]|SE[{i, Fra3}, {k_, Fra3}])],jj]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}]|CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])},
					{{i_},{i}},Nest[PD[{0,-Fra}],Spin[{0,Fra},{i,Fra3}],jj]}
					,
				{{-Nest[PD[{0,-Fra}],IntNull[Ns[{k, Fra3}]*r[]*(SE[{0, Fra}, {j, Fra3}] |SE[{j, Fra3}, {0, Fra}] )],jj],
			 	Nest[PD[{0,-Fra}],IntNull[Ns[{j, Fra3}]*r[]*(SE[{0, Fra}, {k, Fra3}] |SE[{k, Fra3}, {0, Fra}] )],jj],
			   Nest[PD[{0,-Fra}], IntNull[(Ns[{k, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{k, Fra3}])*r[]*(SE[ {i_, Fra3}, {j, Fra3}]|SE[{j, Fra3}, {i_, Fra3}] )],jj]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}]),
				-Nest[PD[{0,-Fra}],IntNull[(Ns[{j, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{j, Fra3} ])*r[]*(SE[{i_, Fra3}, {k, Fra3}] |SE[{k, Fra3}, {i_, Fra3}] )],jj]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}])},
				  {{j_,k_},{j,k}},Nest[PD[{0,-Fra}],Spin[{k,Fra3},{j,Fra3}],jj]}

				};
	];
	For[ii=1,ii<=2,ii++,
		For[jj=ii,jj<=2,jj++,
			partialList=partialList~Join~
					{{{Nest[PD[{0,-Fra}],IntNull[Ns[{i, Fra3}]*r[]*SEpert[LI[ii], {0, Fra}, {0, Fra}]],jj-ii],
			 	-Nest[PD[{0,-Fra}],IntNull[r[]*(SEpert[LI[ii], {0, Fra}, {i, Fra3}]|SEpert[LI[ii], {i, Fra3}, {0, Fra}])],jj-ii],
			    -(Nest[PD[{0,-Fra}],IntNull[(Ns[{i, Fra3}, {k_, Fra3}]|Ns[{k_, Fra3},{i, Fra3}])*r[]*(SEpert[LI[ii], {j_, Fra3}, {0, Fra}]|SEpert[LI[ii], {0, Fra}, {j_, Fra3}])],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}] | CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])),
				  Nest[PD[{0,-Fra}],IntNull[Ns[{j_, Fra3}]*r[]*(SEpert[LI[ii], {k_, Fra3}, {i, Fra3}]|SEpert[LI[ii], {i, Fra3}, {k_, Fra3}])],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-j_, -Fra3}, {-k_, -Fra3}]|CDelta[-Fra3, -Fra3][{-k_, -Fra3},{-j_, -Fra3}])},
					{{i_},{i}},Nest[PD[{0,-Fra}],Spinpert[LI[ii],{0,Fra},{i,Fra3}],jj-ii]}
					,
					{{-Nest[PD[{0,-Fra}],IntNull[Ns[{k, Fra3}]*r[]*(SEpert[LI[ii], {0, Fra}, {j, Fra3}] |SEpert[LI[ii], {j, Fra3}, {0, Fra}] )],jj-ii],
			 	Nest[PD[{0,-Fra}],IntNull[Ns[{j, Fra3}]*r[]*(SEpert[LI[ii], {0, Fra}, {k, Fra3}] |SEpert[LI[ii], {k, Fra3}, {0, Fra}] )],jj-ii],
			    Nest[PD[{0,-Fra}],IntNull[(Ns[{k, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{k, Fra3}])*r[]*(SEpert[LI[ii], {i_, Fra3}, {j, Fra3}]|SEpert[LI[ii], {j, Fra3}, {i_, Fra3}] )],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}]),
				-Nest[PD[{0,-Fra}],IntNull[(Ns[{j, Fra3}, {l_, Fra3}]|Ns[{l_, Fra3},{j, Fra3} ])*r[]*(SEpert[LI[ii], {i_, Fra3}, {k, Fra3}] |SEpert[LI[ii], {k, Fra3}, {i_, Fra3}] )],jj-ii]
							*(CDelta[-Fra3, -Fra3][{-i_, -Fra3}, {-l_, -Fra3}]|CDelta[-Fra3, -Fra3][{-l_, -Fra3},{-i_, -Fra3}])},
				  {{j_,k_},{j,k}},Nest[PD[{0,-Fra}],Spinpert[LI[ii],{k,Fra3},{j,Fra3}],jj-ii]}};
			];
		];
	Return[partialList];
];


SpinMomSumRuleList=SpinSumRuleList~Join~MomentumSumRuleList;


(* ::Text:: *)
(*Omitted spin-squared rule. I hope it does not turn out that I badly needed it*)


ChargeMultipoleRules={
IntNull[CurrentDens[{a_,bas_}]]/;MemberQ[{Fra3,Fra},bas]:>ChargeCurrent[{a,bas}],
IntNull[CurrentDenspert[LI[o_],{a_,bas_}]]/;MemberQ[{Fra3,Fra},bas]:>ChargeCurrentpert[LI[o],{a,bas}]
,
IntNull[CurrentDens[{a_,basa_}] r[] Ns[{i_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>Module[{k},ChargeDipole[{a,basa},{i,Fra3}]],
IntNull[CurrentDens[{a_,basa_}]r[]]/;MemberQ[{Fra,Fra3},basa]:>ChargeDipole[{a,basa},{0,Fra}],
IntNull[CurrentDenspert[LI[o_],{a_,basa_}] r[] Ns[{i_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>Module[{k},ChargeDipolepert[LI[o],{a,basa},{i,Fra3}]],
IntNull[CurrentDenspert[LI[o_],{a_,basa_}]r[]]/;MemberQ[{Fra,Fra3},basa]:>ChargeDipolepert[LI[o],{a,basa},{0,Fra}]
,
IntNull[CurrentDens[{a_,basa_}]r[]^2]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPole[{a,basa},{0,Fra},{0,Fra}],
IntNull[CurrentDens[{a_,basa_}]r[]^2 Ns[{i_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPole[{a,basa},{0,Fra},{i,Fra3}],
IntNull[CurrentDens[{a_,basa_}]r[]^2 Ns[{i_,Fra3},{j_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPole[{a,basa},{i,Fra3},{j,Fra3}],
IntNull[CurrentDenspert[LI[o_],{a_,basa_}]r[]^2]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPolepert[LI[o],{a,basa},{0,Fra},{0,Fra}],
IntNull[CurrentDenspert[LI[o_],{a_,basa_}]r[]^2 Ns[{i_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPolepert[LI[o],{a,basa},{0,Fra},{i,Fra3}],
IntNull[CurrentDenspert[LI[o_],{a_,basa_}]r[]^2 Ns[{i_,Fra3},{j_,Fra3}]]/;MemberQ[{Fra,Fra3},basa]:>ChargeQuadPolepert[LI[o],{a,basa},{i,Fra3},{j,Fra3}]
};


ApplyAllBodyParams[expr_]:=(expr/.ChargeMultipoleRules)//ApplySumRuleList[SpinMomSumRuleList];


RevBodyParamSubRule:={
Mompert[LI[o_],{a_,basa_}]/;MemberQ[{Fra3,Fra},basa]:>Module[{j,i},IntNull[SEpert[LI[o],{0,Fra},{a,basa}]]
								-IntNull[SEpert[LI[o],{j,Fra3},{a,basa}]Ns[{i,Fra3}]]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] ],
Mom[{a_,basa_}]/;MemberQ[{Fra,Fra3},basa]:>Module[{j,i},IntNull[SE[{0,Fra},{a,basa}]]
								-IntNull[SE[{j,Fra3},{a,basa}]Ns[{i,Fra3}]]CDelta[-Fra3,-Fra3][{-i,-Fra3},{-j,-Fra3}] ]
,
Spinpert[LI[o_],{0,Fra},{i_,Fra3}]:>Module[{k,j},-IntNull[SEpert[LI[o],{0,Fra},{i,Fra3}]r[]]+ IntNull[Ns[{i,Fra3}]r[] SEpert[LI[o],{0,Fra},{0,Fra}]]
						- IntNull[Ns[{i,Fra3},{k,Fra3}] SEpert[LI[o],{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						+ IntNull[Ns[{j,Fra3}]SEpert[LI[o],{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spinpert[LI[o_],{i_,Fra3},{0,Fra}]:>Module[{k,j},IntNull[SEpert[LI[o],{0,Fra},{i,Fra3}]r[]]- IntNull[Ns[{i,Fra3}]r[] SEpert[LI[o],{0,Fra},{0,Fra}]]
						+ IntNull[Ns[{i,Fra3},{k,Fra3}] SEpert[LI[o],{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						- IntNull[Ns[{j,Fra3}]SEpert[LI[o],{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spin[{0,Fra},{i_,Fra3}]:>Module[{k,j},-IntNull[SE[{0,Fra},{i,Fra3}]r[]]+ IntNull[Ns[{i,Fra3}]r[] SE[{0,Fra},{0,Fra}]]
						- IntNull[Ns[{i,Fra3},{k,Fra3}] SE[{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						+ IntNull[Ns[{j,Fra3}]SE[{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spin[{i_,Fra3},{0,Fra}]:>Module[{k,j},IntNull[SE[{0,Fra},{i,Fra3}]r[]]- IntNull[Ns[{i,Fra3}]r[] SE[{0,Fra},{0,Fra}]]
						+ IntNull[Ns[{i,Fra3},{k,Fra3}] SE[{j,Fra3},{0,Fra}]r[]]CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]
						- IntNull[Ns[{j,Fra3}]SE[{k,Fra3},{i,Fra3}]r[]] CDelta[-Fra3,-Fra3][{-j,-Fra3},{-k,-Fra3}]],
Spinpert[LI[o_],{j_,Fra3},{k_,Fra3}]:>Module[{i,l},-IntNull[SEpert[LI[o],{0,Fra},{j,Fra3}] Ns[{k,Fra3}]r[]] + IntNull[SEpert[LI[o],{0,Fra},{k,Fra3}]Ns[{j,Fra3}]r[]]
											+CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{k,Fra3},{l,Fra3}]SEpert[LI[o],{i,Fra3},{j,Fra3}]r[]]
											- CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{j,Fra3},{l,Fra3}]SEpert[LI[o],{i,Fra3},{k,Fra3}]r[]]],
Spin[{j_,Fra3},{k_,Fra3}]:>Module[{i,l},-IntNull[SE[{0,Fra},{j,Fra3}] Ns[{k,Fra3}]r[]] + IntNull[SE[{0,Fra},{k,Fra3}]Ns[{j,Fra3}]r[]]
											+CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{k,Fra3},{l,Fra3}]SE[{i,Fra3},{j,Fra3}]r[]]
											- CDelta[-Fra3,-Fra3][{-i,-Fra3},{-l,-Fra3}]IntNull[Ns[{j,Fra3},{l,Fra3}]SE[{i,Fra3},{k,Fra3}]r[]]]
,
ChargeCurrent[{a_,basa_}]/;MemberQ[{Fra,Fra3},basa]:>IntNull[CurrentDenspert[LI[0],{a,basa}]],
ChargeCurrentpert[LI[o_],{a_,basa_}]/;MemberQ[{Fra,Fra3},basa]:>IntNull[CurrentDenspert[LI[o],{a,basa}]]
,
ChargeDipole[{a_,basa_},{b_,basb_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basa,basb}):>IntNull[Ns[{b,basb}] r[] CurrentDenspert[LI[0],{a,basa}]],
ChargeDipolepert[LI[o_],{a_,basa_},{b_,basb_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basa,basb}):>IntNull[Ns[{b,basb}] r[] CurrentDenspert[LI[o],{a,basa}]]
,
ChargeQuadPole[{a_,basa_},{b_,basb_},{c_,basc_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basa,basb,basc}):>IntNull[r[]^2 Ns[{b,basb},{c,basc}] CurrentDenspert[LI[0],{a,basa}]],
ChargeQuadPolepert[LI[o_],{a_,basa_},{b_,basb_},{c_,basc_}]/;And@@(MemberQ[{Fra,Fra3},#]&/@{basa,basb,basc}):>IntNull[r[]^2 Ns[{b,basb},{c,basc}] CurrentDenspert[LI[o],{a,basa}]]};


ReverseBodyParams[expr_]:=expr/.RevBodyParamSubRule;
