(* ::Package:: *)

(* ::Title:: *)
(*2. The Subscript[\[CapitalGamma], s] Calculus*)


(* ::Text:: *)
(*The non-singular code used in this paper is taken from Dror Bar-Natan's website, please see http://www.math.toronto.edu/~drorbn/ for the original source.*)


(* ::Subsection:: *)
(*Introducing Subscript[\[CapitalGamma], s]*)


(* Fromatting and Multiplication rules: *)
\[CapitalGamma]/:\[CapitalGamma][\[Omega]1_,A1_]\[CapitalGamma][\[Omega]2_,A2_]:=\[CapitalGamma][\[Omega]1 \[Omega]2,A1+ A2]
\[CapitalGamma]/:\[CapitalGamma][\[Omega]1_,A1_]\[Congruent]\[CapitalGamma][\[Omega]2_,A2_]:=Simplify[\[Omega]1 -\[Omega]2==0&&A1- A2==0]
\[CapitalGamma]Collect[\[CapitalGamma][\[Omega]_,A_]]:=\[CapitalGamma][Simplify[\[Omega]]//Expand,Collect[A,Subscript[r, _],Collect[#,Subscript[c, _],Factor]&]]
\[CapitalGamma]Format[\[CapitalGamma][\[Omega]_,A_]]:=Module[{S,M},
S=Union@Cases[\[CapitalGamma][\[Omega],A],Subscript[(r|c), a_]:> a,Infinity];
M=Outer[Factor[\!\(
\*SubscriptBox[\(\[PartialD]\), \(
\*SubscriptBox[\(c\), \(#1\)], 
\*SubscriptBox[\(r\), \(#2\)]\)]A\)]&,S,S];
M=Prepend[M,Subscript[r, #]&/@S]//Transpose;
M=Prepend[M,Prepend[Subscript[c, #]&/@S,\[Omega]]];
M//MatrixForm
]
(* The positivie, negative, and singular crossings : *)
Subscript[X, a_,b_]:=\[CapitalGamma][1,Subscript[r, a] Subscript[c, a]+(1-t)Subscript[r, a] Subscript[c, b]+t Subscript[r, b] Subscript[c, b]]
Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), a_,b_]:=Subscript[X, a,b]/.t->t^-1
Subscript[S, a_,b_]:=\[CapitalGamma][1,s Subscript[c, a] Subscript[r, a]+(1-s t) Subscript[c, b] Subscript[r, a]+(1-s) Subscript[c, a] Subscript[r, b]+s t Subscript[c, b] Subscript[r, b]]
(* Definition of the stitching : *)
Subscript[m, a_,b_->k_][\[CapitalGamma][\[Omega]_,A_]]:=\[CapitalGamma][(\[Mu]=1-\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(r\), \(a\)]]\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(c\), \(b\)]]A\)\))\[Omega],A+(\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(r\), \(a\)]]A\))(\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(c\), \(b\)]]A\))/\[Mu]]/.{(Subscript[c, b]|Subscript[r, a])->0,Subscript[c, a]->Subscript[c, k],Subscript[r, b]->Subscript[r, k]}//\[CapitalGamma]Collect


(* ::Subsection:: *)
(*Derivation of Definition 2 (Crossings)*)


(* ::Text:: *)
(*The Definition for the non-singular crossings were proven in [1]*)
(*Taking the definition of the singular crossing (named Subscript[SS, a,b] here) to be a sum with unknown coefficients (named e, f, g, h).*)


(* ::Code:: *)
(*Subscript[SS, a_,b_]:=\[CapitalGamma][1,e Subscript[r, a] Subscript[c, a]+f Subscript[r, a] Subscript[c, b]+g Subscript[r, b] Subscript[c, a]+ h Subscript[r, b] Subscript[c, b]]*)


(* ::Text:: *)
(*Then solve for the Reidemeister moves (the RM moves are the first input in Coefficients[]).*)
(*The condition for solving the RM moves is that*)


(* ::Code:: *)
(*{sol}=Solve[Thread[Join[*)
(*Flatten@Table[Coefficient[(Subscript[SS, 1,2] Subscript[X, 3,4]//Subscript[m, 1,4->6]//Subscript[m, 2,3->5])[[2]]-(Subscript[SS, 3,4] Subscript[X, 1,2]//Subscript[m, 1,4->6]//Subscript[m, 2,3->5])[[2]],Subscript[r, v] Subscript[c, w]],{v,{5,6}},{w,{5,6}}],*)
(*Flatten@Table[Coefficient[(Subscript[X, 5,6] Subscript[SS, 4,3] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 2,1]//Subscript[m, 1,4->1]//Subscript[m, 2,5->2]//Subscript[m, 3,6->3])[[2]]-(Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 5,4] Subscript[SS, 1,6] Subscript[X, 2,3]//Subscript[m, 3,6->3]//Subscript[m, 2,5->2]//Subscript[m, 1,4->1])[[2]],Subscript[r, v] Subscript[c, w]],{v,{1,2,3}},{w,{1,2,3}}]]==0],*)
(*{e,f,g,h}]*)


(* ::Text:: *)
(*Or in Matrix form:*)


(* ::Input:: *)
(*Subscript[SS, a,b]/.sol //Simplify// \[CapitalGamma]Format*)


(* ::Text:: *)
(*We rename the free variable e as s.*)
(*Switching the order of the columns gives the expression in Definition 2. *)


(* ::Input:: *)
(*Subscript[S, 1,2] Subscript[X, 3,4] Subscript[X, 5,6]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,6->1]//Simplify*)


(* ::Input:: *)
(*Subscript[S, 1,2] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 4,3] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 6,5]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,6->1]//Simplify*)


(* ::Subsection:: *)
(*Singular Knot Examples*)


(* ::Text:: *)
(*Right-handed trefoil:*)


(* ::Input:: *)
(*RHT=Subscript[X, 1,2] Subscript[X, 3,4] Subscript[X, 5,6]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,6->1]*)


(* ::Text:: *)
(*The left-handed trefoil is proportional to right-handed trefoil:*)


(* ::Input:: *)
(*LHT=Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 2,1] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 4,3] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 6,5]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,6->1];*)
(*\[CapitalGamma][LHT[[1]]*t^3//Expand,LHT[[2]]]*)


(* ::Text:: *)
(*The trefoil with all singular crossings:*)


(* ::Input:: *)
(*Subscript[S, 1,2] Subscript[S, 3,4] Subscript[S, 5,6]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,6->1]//Simplify*)


(* ::Subsection:: *)
(* Kinoshita - Terasaka and Conway knots*)


(* ::Text:: *)
(*The Kinoshita-Terasaka knot :*)


(* ::Input:: *)
(*KTKnot=Subscript[X, 1,2] Subscript[X, 3,4] Subscript[X, 5,6] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 8,7] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 10,9] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 12,11] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,13] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 16,15] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 18,17] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 20,19] Subscript[X, 21,22] Subscript[X, 23,24]//Subscript[m, 1,20->1]//Subscript[m, 1,17->1]//Subscript[m, 1,6->1]//Subscript[m, 1,3->1]//Subscript[m, 1,2->1]//Subscript[m, 1,7->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,12->1]//Subscript[m, 1,13->1]//Subscript[m, 1,16->1]//Subscript[m, 1,21->1]//Subscript[m, 1,24->1]//Subscript[m, 1,19->1]//Subscript[m, 1,18->1]//Subscript[m, 1,15->1]//Subscript[m, 1,14->1]//Subscript[m, 1,5->1]//Subscript[m, 1,4->1]*)


(* ::Text:: *)
(*The Conway knot:*)


(* ::Input:: *)
(*CKnot=Subscript[X, 1,2] Subscript[X, 3,4] Subscript[X, 5,6] Subscript[X, 7,8] Subscript[X, 9,10] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 12,11] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,13] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 16,15] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 18,17] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 20,19] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 22,21] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 24,23]//Subscript[m, 1,18->1]//Subscript[m, 1,15->1]//Subscript[m, 1,6->1]//Subscript[m, 1,3->1]//Subscript[m, 1,2->1]//Subscript[m, 1,7->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,14->1]//Subscript[m, 1,19->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,20->1]//Subscript[m, 1,21->1]//Subscript[m, 1,24->1]//Subscript[m, 1,17->1]//Subscript[m, 1,16->1]//Subscript[m, 1,13->1]//Subscript[m, 1,12->1]//Subscript[m, 1,5->1]//Subscript[m, 1,4->1]*)


(* ::Text:: *)
(*The Alexander polynomial does not distinguish these two knots and says they are equivalent to the unknot.*)


(* ::Text:: *)
(*The Kinoshita-Terasaka knot with one singular crossing (outside of mutation area):*)


(* ::Input:: *)
(*SingKTKnot=Subscript[S, 1,2] Subscript[X, 3,4] Subscript[X, 5,6] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 8,7] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 10,9] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 12,11] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,13] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 16,15] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 18,17] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 20,19] Subscript[X, 21,22] Subscript[X, 23,24]//Subscript[m, 1,20->1]//Subscript[m, 1,17->1]//Subscript[m, 1,6->1]//Subscript[m, 1,3->1]//Subscript[m, 1,2->1]//Subscript[m, 1,7->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,12->1]//Subscript[m, 1,13->1]//Subscript[m, 1,16->1]//Subscript[m, 1,21->1]//Subscript[m, 1,24->1]//Subscript[m, 1,19->1]//Subscript[m, 1,18->1]//Subscript[m, 1,15->1]//Subscript[m, 1,14->1]//Subscript[m, 1,5->1]//Subscript[m, 1,4->1];*)
(*\[CapitalGamma][SingKTKnot[[1]]*t^2//Expand,SingKTKnot[[2]]]*)


(* ::Text:: *)
(*The Conway knot with one singular crossing (outside of mutation area, the same crossing is chosen as in the Kinoshita-Terasaka example): *)


(* ::Input:: *)
(*SingCKnot=Subscript[S, 1,2] Subscript[X, 3,4] Subscript[X, 5,6] Subscript[X, 7,8] Subscript[X, 9,10] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 12,11] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,13] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 16,15] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 18,17] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 20,19] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 22,21] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 24,23]//Subscript[m, 1,18->1]//Subscript[m, 1,15->1]//Subscript[m, 1,6->1]//Subscript[m, 1,3->1]//Subscript[m, 1,2->1]//Subscript[m, 1,7->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,14->1]//Subscript[m, 1,19->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,20->1]//Subscript[m, 1,21->1]//Subscript[m, 1,24->1]//Subscript[m, 1,17->1]//Subscript[m, 1,16->1]//Subscript[m, 1,13->1]//Subscript[m, 1,12->1]//Subscript[m, 1,5->1]//Subscript[m, 1,4->1];*)
(*\[CapitalGamma][SingCKnot[[1]]*t^2//Expand,SingCKnot[[2]]]*)


(* ::Subsection:: *)
(*Example knot Sec. 3.2*)


(* ::Text:: *)
(*Unlike with the trefoil, also the singular Alexander polynomial does not distinguish these knots.*)


(* ::Input:: *)
(*Ex2knotLHS=Subscript[S, 25,1] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 2,12] Subscript[X, 3,27] Subscript[X, 36,4] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 15,5] Subscript[X, 7,20] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 8,31] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 9,18] Subscript[X, 10,33] Subscript[X, 24,11] Subscript[X, 13,26] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,37] Subscript[X, 16,21] Subscript[X, 30,17] Subscript[S, 19,32] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 35,22] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 23,28] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 29,34]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,7->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,12->1]//Subscript[m, 1,13->1]//Subscript[m, 1,14->1]//Subscript[m, 1,15->1]//Subscript[m, 1,16->1]//Subscript[m, 1,17->1]//Subscript[m, 1,18->1]//Subscript[m, 1,19->1]//Subscript[m, 1,20->1]//Subscript[m, 1,21->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,24->1]//Subscript[m, 1,25->1]//Subscript[m, 1,26->1]//Subscript[m, 1,27->1]//Subscript[m, 1,28->1]//Subscript[m, 1,29->1]//Subscript[m, 1,30->1]//Subscript[m, 1,31->1]//Subscript[m, 1,32->1]//Subscript[m, 1,33->1]//Subscript[m, 1,34->1]//Subscript[m, 1,35->1]//Subscript[m, 1,36->1]//Subscript[m, 1,37->1]*)


(* ::Input:: *)
(*Ex2knotRHS=Subscript[S, 25,1] Subscript[X, 34,2] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 17,3] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 4,10] Subscript[X, 5,29] Subscript[X, 7,20] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 8,31] Subscript[X, 22,9] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 11,16] Subscript[X, 12,35] Subscript[X, 13,26] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 14,37] Subscript[X, 28,15] Subscript[X, 18,23] Subscript[S, 19,32] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 21,30] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 33,24] Subscript[\!\(\*OverscriptBox[\(X\), \(_\)]\), 27,36]//Subscript[m, 1,2->1]//Subscript[m, 1,3->1]//Subscript[m, 1,4->1]//Subscript[m, 1,5->1]//Subscript[m, 1,7->1]//Subscript[m, 1,8->1]//Subscript[m, 1,9->1]//Subscript[m, 1,10->1]//Subscript[m, 1,11->1]//Subscript[m, 1,12->1]//Subscript[m, 1,13->1]//Subscript[m, 1,14->1]//Subscript[m, 1,15->1]//Subscript[m, 1,16->1]//Subscript[m, 1,17->1]//Subscript[m, 1,18->1]//Subscript[m, 1,19->1]//Subscript[m, 1,20->1]//Subscript[m, 1,21->1]//Subscript[m, 1,22->1]//Subscript[m, 1,23->1]//Subscript[m, 1,24->1]//Subscript[m, 1,25->1]//Subscript[m, 1,26->1]//Subscript[m, 1,27->1]//Subscript[m, 1,28->1]//Subscript[m, 1,29->1]//Subscript[m, 1,30->1]//Subscript[m, 1,31->1]//Subscript[m, 1,32->1]//Subscript[m, 1,33->1]//Subscript[m, 1,34->1]//Subscript[m, 1,35->1]//Subscript[m, 1,36->1]//Subscript[m, 1,37->1]*)


(* ::Input:: *)
(*Ex2knotLHS[[1]]==Ex2knotRHS[[1]]*)


(* ::Title:: *)
(*References*)


(* ::Text:: *)
(*[1] A. Mashaghi and R. van der Veen, "Polynomial invariant of molecular circuit topology," arXiv preprint arXiv:2109.02391, 2021.*)
(*[2] H. Vo, "Alexander Invariants of Tangles via Expansions. PhD thesis, University of Toronto (Canada), 2018.*)
(**)
(**)
