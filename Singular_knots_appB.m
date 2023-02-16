(* ::Package:: *)

(* ::Title:: *)
(*App B: Context of Subscript[\[Rho], 1]^s(t,s)*)


(* ::Text:: *)
(*Preamble (see http://www.math.toronto.edu/~drorbn/)*)


{SuperStar[p],SuperStar[x],SuperStar[\[Pi]],SuperStar[\[Xi]]}={\[Pi],\[Xi],p,x}; SuperStar[(Subscript[u_, i_])]:=Subscript[(SuperStar[u]), i]; SuperStar[l_List]:=SuperStar[#]& /@ l;


Subscript[\[DoubleStruckCapitalE], s1_][\[Omega]Q1__]\[Congruent]Subscript[\[DoubleStruckCapitalE], s2_][\[Omega]Q2__]:=s1===s2\[And]Simplify[{\[Omega]Q1}=={\[Omega]Q2}]
Subscript[\[DoubleStruckCapitalE], A1_->B1_][\[Omega]1_,Q1_]Subscript[\[DoubleStruckCapitalE], A2_->B2_][\[Omega]2_,Q2_]^:=Subscript[\[DoubleStruckCapitalE], A1\[Union]A2->B1\[Union]B2][\[Omega]1 \[Omega]2,Q1+Q2]


CF=ExpandNumerator@*ExpandDenominator@*PowerExpand@*Factor;


(Subscript[\[DoubleStruckCapitalE], A1_->B1_][\[Omega]1_,Q1_]//Subscript[\[DoubleStruckCapitalE], A2_->B2_][\[Omega]2_,Q2_])/; (SuperStar[B1]===A2):=Module[{i,j,E1,F1,G1,E2,F2,G2,I,M=Table},
I=IdentityMatrix@Length@B1;
E1=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q1\),{i,A1},{j,B1}]; E2=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q2\),{i,A2},{j,B2}];
F1=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q1\),{i,A1},{j,A1}]; F2=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q2\),{i,A2},{j,A2}];
G1=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q1\),{i,B1},{j,B1}]; G2=M[\!\(
\*SubscriptBox[\(\[PartialD]\), \(i, j\)]Q2\),{i,B2},{j,B2}];
Subscript[\[DoubleStruckCapitalE], A1->B2][CF[\[Omega]1 \[Omega]2 Det[I-F2 . G1]^(-1/2)],CF@Plus[
If[A1==={}\[Or]B2==={},0,A1 . E1 . Inverse[I-F2 . G1] . E2 . B2],
If[A1==={},0,1/2 A1 . (F1+E1 . F2 . Inverse[I-G1 . F2] . Transpose[E1]) . A1],
If[B2==={},0,1/2 B2 . (G2+Transpose[E2] . G1 . Inverse[I-F2 . G1] . E2) . B2]]]]


A_\[Backslash]B_:=Complement[A,B];
(Subscript[\[DoubleStruckCapitalE], A1_->B1_][\[Omega]1_,Q1_]//Subscript[\[DoubleStruckCapitalE], A2_->B2_][\[Omega]2_,Q2_])/; (SuperStar[B1]=!=A2):=Subscript[\[DoubleStruckCapitalE], A1\[Union](A2\[Backslash]SuperStar[B1])->B1\[Union]SuperStar[A2]][\[Omega]1,Q1+Sum[SuperStar[\[Zeta]] \[Zeta],{\[Zeta],A2\[Backslash]SuperStar[B1]}]]//Subscript[\[DoubleStruckCapitalE], SuperStar[B1]\[Union]A2->B2\[Union](B1\[Backslash]SuperStar[A2])][\[Omega]2,Q2+Sum[SuperStar[z] z,{z,B1\[Backslash]SuperStar[A2]}]]


(* ::Text:: *)
(*The crossings are given by:*)


(* the positive, negative, curl (anticlockwise), inverse curl (clockwise), and singular crossing, defined according to our conventions *)
Subscript[R, i_,j_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)], 
\*SubscriptBox[\(p\), \(j\)], 
\*SubscriptBox[\(x\), \(j\)]}\)]\)[T^(-1/2),(1-T^-1)Subscript[p, j] Subscript[x, j]-(1-T^-1)Subscript[p, i] Subscript[x, j]];
Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), i_,j_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)], 
\*SubscriptBox[\(p\), \(j\)], 
\*SubscriptBox[\(x\), \(j\)]}\)]\)[T^(1/2),(1-T)Subscript[p, j] Subscript[x, j]-(1-T)Subscript[p, i] Subscript[x, j]];
Subscript[C, i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)]}\)]\)[T^(-1/2),0]; Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)]}\)]\)[T^(1/2),0];
Subscript[sR, i_,j_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)], 
\*SubscriptBox[\(p\), \(j\)], 
\*SubscriptBox[\(x\), \(j\)]}\)]\)[T,-c Subscript[p, i] Subscript[x, i]+c Subscript[p, j] Subscript[x, i]+(c/T-(-1+T)/T) Subscript[p, i] Subscript[x, j]+(-(c/T)-(1-T)/T) Subscript[p, j] Subscript[x, j]];


(* The empty element *)
Subscript[\[Eta], i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {
\*SubscriptBox[\(p\), \(i\)], 
\*SubscriptBox[\(x\), \(i\)]}\)]\)[1,0]


(* The rule for stitchin elements together *)
Subscript[m, i_,j_->k_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({
\*SubscriptBox[\(\[Pi]\), \(i\)], 
\*SubscriptBox[\(\[Xi]\), \(i\)], 
\*SubscriptBox[\(\[Pi]\), \(j\)], 
\*SubscriptBox[\(\[Xi]\), \(j\)]} \[Rule] {
\*SubscriptBox[\(p\), \(k\)], 
\*SubscriptBox[\(x\), \(k\)]}\)]\)[1,-Subscript[\[Xi], i] Subscript[\[Pi], j]+(Subscript[\[Pi], i]+Subscript[\[Pi], j])Subscript[p, k]+(Subscript[\[Xi], i]+Subscript[\[Xi], j])Subscript[x, k]]


(* ::Text:: *)
(*Reidemeister moves*)


(* ::Code:: *)
(*(Subscript[R, 1,2] Subscript[R, 4,3] Subscript[R, 5,6]//Subscript[m, 1,4->1] Subscript[m, 2,5->2] Subscript[m, 3,6->3])\[Congruent](Subscript[R, 2,3] Subscript[R, 1,6] Subscript[R, 4,5]//Subscript[m, 1,4->1] Subscript[m, 2,5->2] Subscript[m, 3,6->3])(*RM3*)*)
(*{(Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 1,2] Subscript[R, 3,4]//Subscript[m, 1,3->1] Subscript[m, 2,4->2])\[Congruent]Subscript[\[Eta], 1] Subscript[\[Eta], 2],(Subscript[R, 1,4] Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 5,2] Subscript[C, 3]//Subscript[m, 5,1->1]//Subscript[m, 4,3->3]//Subscript[m, 3,2->2])\[Congruent]Subscript[C, 1] Subscript[\[Eta], 2]} (*RM2b, R2c*)*)
(*{(Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), 2] Subscript[R, 1,3]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1])\[Congruent]Subscript[\[Eta], 1], (Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), 2] Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 3,1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1])\[Congruent]Subscript[\[Eta], 1],(Subscript[C, 2] Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 1,3]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1])\[Congruent]Subscript[\[Eta], 1],(Subscript[C, 2] Subscript[R, 3,1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1])\[Congruent]Subscript[\[Eta], 1]} (*RM1*)*)


(* ::Text:: *)
(*Singular Reidemeister moves*)


(* ::Code:: *)
(*(Subscript[R, 5,6] Subscript[sR, 4,3] Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 2,1]//Subscript[m, 1,4->1]//Subscript[m, 2,5->2]//Subscript[m, 3,6->3])\[Congruent](Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 5,4] Subscript[sR, 1,6] Subscript[R, 2,3]//Subscript[m, 3,6->3]//Subscript[m, 2,5->2]//Subscript[m, 1,4->1])(*sRM3*)*)
(*(Subscript[sR, 1,2] Subscript[R, 3,4]//Subscript[m, 1,4->1]//Subscript[m, 2,3->2])\[Congruent](Subscript[R, 1,2] Subscript[sR, 3,4]//Subscript[m, 1,4->1]//Subscript[m, 2,3->2])(*sRM2*)*)


(* ::Text:: *)
(*From the solutions for Subscript[R, 1] in the Heisenberg algebra we can derive the g-rules*)


(* ::Text:: *)
(*(* positive/negative crossings: *)*)
(*Subscript[g, i,\[Beta]_]:>Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], i,\[Beta]],*)
(*Subscript[g, j,\[Beta]_]:>T^s Subscript[g, SuperPlus[j],\[Beta]]+(1-T^s)Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], j,\[Beta]],*)
(*Subscript[g, \[Alpha]_,i]:>Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]]+(1-T^-s)Subscript[g, \[Alpha],SuperPlus[j]]-(1-T^-s)Subscript[\[Delta], \[Alpha],SuperPlus[j]],*)
(*Subscript[g, \[Alpha]_,j]:>T^-s Subscript[g, \[Alpha],SuperPlus[j]]-T^-s Subscript[\[Delta], \[Alpha],SuperPlus[j]]*)
(**)
(*(* singular crossing: *)*)
(*Subscript[g, i,\[Beta]_]:>(1+c)/(1+c+c T) Subscript[g, SuperPlus[i],\[Beta]]+(c T)/(1+c+c T) Subscript[g, SuperPlus[j],\[Beta]]+Subscript[\[Delta], i,\[Beta]],*)
(*Subscript[g, j,\[Beta]_]:>((1+c) T)/(1+c+c T) Subscript[g, SuperPlus[j],\[Beta]]+(1+c-T)/(1+c+c T) Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], j,\[Beta]],*)
(*Subscript[g, \[Alpha]_,i]:>(1+c)(Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])-(1+c-T)/T (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]]),*)
(*Subscript[g, \[Alpha]_,j]:>(1+c)/T (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]])-c(Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])*)


(* ::Text:: *)
(*These are used in sec. 4 to solve for the crossings, and they can also be used to derive the A-matrix elements which is related to the Gamma-calculus; A=-\[CapitalGamma]^T*)


(* ::Input:: *)
(*A={{-1,0},{T^s-1,-T^s}}//MatrixForm*)


(* ::Input:: *)
(*Asing={{-((1+c)/(1+c+c T)),-((c T)/(1+c+c T))},{-((1+c-T)/(1+c+c T)) ,-(((1+c) T)/(1+c+c T))}}/.{c->(1-s)/(-1+s+s T)}//Simplify//MatrixForm*)


(* ::Text:: *)
(*So the singular g-rules for this choice of c are:*)
(**)
(*Subscript[g, i,\[Beta]_]:>s Subscript[g, SuperPlus[i],\[Beta]]-(-1+s) Subscript[g, SuperPlus[j],\[Beta]]+Subscript[\[Delta], i,\[Beta]],*)
(*Subscript[g, j,\[Beta]_]:>(1-s T) Subscript[g, SuperPlus[i],\[Beta]]+s T Subscript[g, SuperPlus[j],\[Beta]]+Subscript[\[Delta], j,\[Beta]],*)
(*Subscript[g, \[Alpha]_,i]:>(s T)/(-1+s+s T) (Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])+(-1+s T)/(-1+s+s T) (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]]),*)
(*Subscript[g, \[Alpha]_,j]:>s/(-1+s+s T) (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]])+(-1+s)/(-1+s+s T) (Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])*)
