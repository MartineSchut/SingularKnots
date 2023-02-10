(* ::Package:: *)

(* ::Title:: *)
(*3. Perturbed Singular Alexander*)


(* ::Text:: *)
(*Note : in this notebook the variable that appears in the singular invariant which is called 's' in the paper, is here called ' e' due to the sign of the crossing already being denoted 's'.*)


(* Definition of the delta-function *)
Subscript[\[Delta], i_,j_]:=If[i===j,1,0];
(* Notation property *)
SuperPlus[(SuperPlus[\[Alpha]_])]:=\!\(\*SuperscriptBox[\(\[Alpha]\), \("\<++\>"\)]\);


(* ::Text:: *)
(*The (singular) g-rules are derived from the (singular) crossing. *)


(* For positive crossings (s=1) and for negative crossings (s=-1)*)
Subscript[gRules, s_,i_,j_]:={
Subscript[g, i,\[Beta]_]:>Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], i,\[Beta]],
Subscript[g, j,\[Beta]_]:>T^s Subscript[g, SuperPlus[j],\[Beta]]+(1-T^s)Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], j,\[Beta]],
Subscript[g, \[Alpha]_,i]:>Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]]+(1-T^-s)Subscript[g, \[Alpha],SuperPlus[j]]+(T^-s-1)Subscript[\[Delta], \[Alpha],SuperPlus[j]],
Subscript[g, \[Alpha]_,j]:>T^-s Subscript[g, \[Alpha],SuperPlus[j]]-T^-s Subscript[\[Delta], \[Alpha],SuperPlus[j]]
}

(* For singular crossings *)
Subscript[sgRules, i_,j_]:={
Subscript[g, i,\[Beta]_]:>e Subscript[g, SuperPlus[i],\[Beta]]-(-1+e) Subscript[g, SuperPlus[j],\[Beta]]+Subscript[\[Delta], i,\[Beta]],
Subscript[g, j,\[Beta]_]:>(1-e T) Subscript[g, SuperPlus[i],\[Beta]]+e T Subscript[g, SuperPlus[j],\[Beta]]+Subscript[\[Delta], j,\[Beta]],
Subscript[g, \[Alpha]_,i]:>(e T)/(-1+e+e T) (Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])+(-1+e T)/(-1+e+e T) (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]]),
Subscript[g, \[Alpha]_,j]:>e/(-1+e+e T) (Subscript[g, \[Alpha],SuperPlus[j]]-Subscript[\[Delta], \[Alpha],SuperPlus[j]])+(-1+e)/(-1+e+e T) (Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]])
}


(* ::Subsection:: *)
(*Finding non-singular solutions*)


(* ::Text:: *)
(*We solve the non-singular Reidemeister moves first and then the singular Reidemeister moves. One can also solve simultaneously, which would give a bigger set of solutions. Solving them separately is easier computationally.*)


(* ::Text:: *)
(*We define the positive (Subscript[R, 1][1,i,j]) and negative (Subscript[R, 1][-1,i,j]) crossings in terms of coefficients r and q, respectively, at zeroth, first and second order in Subscript[g, a,b]. The curl is defined at zeroth and first order in Subscript[g, a,b] with unknown coefficients c.*)


(* ::Code::Initialization:: *)
Subscript[R, 1][1,i_,j_]:=DeleteDuplicates[Times@@#&/@Tuples[Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}],2]] . Table[Subscript[r, i],{i,10}]+Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}] . Table[Subscript[r, i],{i,11,14}]+ Subscript[r, 15]
Subscript[R, 1][-1,i_,j_]:=DeleteDuplicates[Times@@#&/@Tuples[Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}],2]] . Table[Subscript[q, i],{i,10}]+Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}] . Table[Subscript[q, i],{i,11,14}]+Subscript[q, 15]
CC[s_,i_]:=s Subscript[c, 1] Subscript[g, i,i]+s Subscript[c, 2]


(* ::Text:: *)
(*The Reidemeister moves (as in illustrated in the paper) are given by:*)


(*R3*)
lhs3=Subscript[R, 1][1,j,k]+Subscript[R, 1][1,i,SuperPlus[k]]+Subscript[R, 1][1,SuperPlus[i],SuperPlus[j]]//.Subscript[gRules, 1,j,k]\[Union]Subscript[gRules, 1,i,SuperPlus[k]]\[Union]Subscript[gRules, 1,SuperPlus[i],SuperPlus[j]];
rhs3=Subscript[R, 1][1,i,j]+Subscript[R, 1][1,SuperPlus[i],k]+Subscript[R, 1][1,SuperPlus[j],SuperPlus[k]]//.Subscript[gRules, 1,i,j]\[Union]Subscript[gRules, 1,SuperPlus[i],k]\[Union]Subscript[gRules, 1,SuperPlus[j],SuperPlus[k]];

(*R2c*)
lhs2c=Subscript[R, 1][-1,i,SuperPlus[j]]+Subscript[R, 1][1,SuperPlus[i],j]+CC[1,SuperPlus[j]]//.Subscript[gRules, -1,i,SuperPlus[j]]\[Union]Subscript[gRules, 1,SuperPlus[i],j];
rhs2c=CC[1,SuperPlus[(SuperPlus[j])]];

(*R1l*)
lhs1l=Subscript[R, 1][1,SuperPlus[i],i]+CC[1,SuperPlus[i]]//.{
Subscript[g, SuperPlus[i],\[Beta]_]:>Subscript[g, \!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\),\[Beta]]+Subscript[\[Delta], SuperPlus[i],\[Beta]],
Subscript[g, i,\[Beta]_]:>T Subscript[g, SuperPlus[i],\[Beta]]+(1-T)Subscript[g, \!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\),\[Beta]]+Subscript[\[Delta], i,\[Beta]],
Subscript[g, \[Alpha]_,SuperPlus[i]]:>T Subscript[g, \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]-T Subscript[\[Delta], \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]+(1-T)Subscript[\[Delta], \[Alpha],SuperPlus[i]],
Subscript[g, \[Alpha]_,i]:>T^-1 Subscript[g, \[Alpha],SuperPlus[i]]-T^-1 Subscript[\[Delta], \[Alpha],SuperPlus[i]]
};
rhs1l=0;

(*R1r*)
lhs1r=Subscript[R, 1][1,i,SuperPlus[i]]+CC[-1,SuperPlus[i]]//.{
Subscript[g, i,\[Beta]_]:>Subscript[g, SuperPlus[i],\[Beta]]+Subscript[\[Delta], i,\[Beta]],
Subscript[g, SuperPlus[i],\[Beta]_]:>Subscript[g, \!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\),\[Beta]]+T^-1 Subscript[\[Delta], SuperPlus[i],\[Beta]],
Subscript[g, \[Alpha]_,i]:>Subscript[g, \[Alpha],SuperPlus[i]]-Subscript[\[Delta], \[Alpha],SuperPlus[i]]+(1-T^-1)Subscript[g, \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]+(T^-1-1)Subscript[\[Delta], \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)],
Subscript[g, \[Alpha]_,SuperPlus[i]]:>T^-1 Subscript[g, \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]-T^-1 Subscript[\[Delta], \[Alpha],\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]
};
rhs1r=0;

(*Sw^+*)
lhssw=Subscript[R, 1][1,SuperPlus[i],SuperPlus[j]]+CC[-1,SuperPlus[i]]+CC[-1,SuperPlus[j]]+CC[1,\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]+CC[1,\!\(\*SuperscriptBox[\(j\), \("\<++\>"\)]\)]//.Subscript[gRules, 1,SuperPlus[i],SuperPlus[j]];
rhssw=Subscript[R, 1][1,SuperPlus[i],SuperPlus[j]]//.Subscript[gRules, 1,SuperPlus[i],SuperPlus[j]];


(* ::Text:: *)
(*Solve for the coefficients with the Reidemeister moves*)


(* ::Code::Initialization:: *)
(* List of all possible combinations upto second order for the g's *)
V=Flatten@Table[Subscript[g, a,b],{a,{SuperPlus[(SuperPlus[i])],SuperPlus[(SuperPlus[j])],SuperPlus[(SuperPlus[k])]}},{b,{SuperPlus[(SuperPlus[i])],SuperPlus[(SuperPlus[j])],SuperPlus[(SuperPlus[k])]}}];
(* The equations from the RM moves for each coefficient Subscript[g, a,b] *)
eq3=Thread[Last/@CoefficientRules[lhs3-rhs3,V]==0];
eq2c=Thread[Last/@CoefficientRules[lhs2c-rhs2c,V]==0];
eq1l=Thread[Last/@CoefficientRules[lhs1l-rhs1l,V]==0];
eq1r=Thread[Last/@CoefficientRules[lhs1r-rhs1r,V]==0];
eqsw=Thread[Last/@CoefficientRules[lhssw-rhssw,V]==0];


(* ::Input::Initialization:: *)
(* The RM equations solved in terms of the unknown coefficients *)
{sol}=Solve[Join[eq3,eq2c,eq1l,eq1r,eqsw],Join[Table[Subscript[q, i],{i,1,15}],Table[Subscript[r, i],{i,1,15}],Table[Subscript[c, i],{i,1,2}]]]


(* ::Text:: *)
(*Filling in the solution in the curl, positive and negative crossing expressions still leaves some free variables, for which we provide a choice*)


(* ::Input:: *)
(*CC[s,i]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->(-1-Subscript[r, 12])/(-1+T)}//Simplify*)


(* ::Input:: *)
(*Subscript[R, 1][1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->(-1-Subscript[r, 12])/(-1+T)}/.{Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify//Expand*)
(*Subscript[R, 1][-1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->(-1-Subscript[r, 12])/(-1+T)}/.{Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify//Expand*)


(* ::Text:: *)
(*Note: these solutions are exactly the same as the solution in [1] before they use their g-rules (which are different due to different choices/conventions) to rewrite the crossing solutions.*)


(* ::Text:: *)
(*The positive and negative crossing are related by an overall sign and by the substitution T->T^-1*)


(* ::Input:: *)
(*(Subscript[R, 1][1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->(-1-Subscript[r, 12])/(-1+T)}/.{Subscript[r, 12]->-T,Subscript[r, 2]->3+T})//Simplify*)
(*-(Subscript[R, 1][-1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->(-1-Subscript[r, 12])/(-1+T)}/.{Subscript[r, 12]->-T,Subscript[r, 2]->3+T}/.{T->T^-1})//Simplify*)


(* ::Subsection:: *)
(*Finding singular solutions*)


(* ::Text:: *)
(*We define the singular crossings in terms of coefficients t, at zeroth, first and second order in Subscript[g, a,b].*)


Subscript[sR, 1][i_,j_]:=DeleteDuplicates[Times@@#&/@Tuples[Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}],2]] . Table[Subscript[t, i],{i,10}]+Flatten@Table[Subscript[g, a,b],{a,{i,j}},{b,{i,j}}] . Table[Subscript[t, i],{i,11,14}]+ Subscript[t, 15]


(* ::Text:: *)
(*The singular Reidemeister moves are given by: (we fill in the solution found from the non-singular RM moves)*)


(* ::Code::Initialization:: *)
(* sR3 with the solution for the non-singular crossings filled in *)
{slhs3}=(Subscript[sR, 1][j,k]+Subscript[R, 1][1,i,SuperPlus[k]]+Subscript[R, 1][1,SuperPlus[i],SuperPlus[j]]//.Join[Subscript[sgRules, j,k],Subscript[gRules, 1,i,SuperPlus[k]],Subscript[gRules, 1,SuperPlus[i],SuperPlus[j]]])/.{sol};
{srhs3}=(Subscript[R, 1][1,i,j]+Subscript[R, 1][1,SuperPlus[i],k]+Subscript[sR, 1][SuperPlus[j],SuperPlus[k]]//.Join[Subscript[gRules, 1,i,j],Subscript[gRules, 1,SuperPlus[i],k],Subscript[sgRules, SuperPlus[j],SuperPlus[k]]])/.{sol};
(* sR2 with the solution for the non-singular crossing filled in *)
{slhs2}=(Subscript[sR, 1][i,j]+Subscript[R, 1][1,SuperPlus[j],SuperPlus[i]]//.Join[Subscript[sgRules, i,j],Subscript[gRules, 1,SuperPlus[j],SuperPlus[i]]])/.{sol};
{srhs2}=(Subscript[R, 1][1,i,j]+Subscript[sR, 1][SuperPlus[j],SuperPlus[i]]//.Join[Subscript[gRules, 1,i,j],Subscript[sgRules, SuperPlus[j],SuperPlus[i]]])/.{sol};
(* Sw^s with the solution for the curl filled in *)
{slhssw}=(Subscript[sR, 1][SuperPlus[i],SuperPlus[j]]//.Subscript[sgRules, SuperPlus[i],SuperPlus[j]])/.{sol};
{srhssw}=(Subscript[sR, 1][SuperPlus[i],SuperPlus[j]]+CC[-1,SuperPlus[i]]+CC[-1,SuperPlus[j]]+CC[1,\!\(\*SuperscriptBox[\(i\), \("\<++\>"\)]\)]+CC[1,\!\(\*SuperscriptBox[\(j\), \("\<++\>"\)]\)]//.Subscript[sgRules, SuperPlus[i],SuperPlus[j]])/.{sol};


(* ::Code::Initialization:: *)
(* The equations from the RM moves for each coefficient Subscript[g, a,b] *)
seq3=Thread[Last/@CoefficientRules[slhs3-srhs3,V]==0];
seq2=Thread[Last/@CoefficientRules[slhs2-srhs2,V]==0];
seqsw=Thread[Last/@CoefficientRules[slhssw-srhssw,V]==0];


(* ::Input:: *)
(*(* The sRM equations solved in terms of the unknown coefficients *)*)
(*{ssol}=Solve[Join[seq3,seq2,seqsw],Table[Subscript[t, i],{i,1,15}]]*)


(* ::Text:: *)
(*Filling in the singular solution in the singular crossing expressions still leaves some free variables.*)
(*- We fill in the variables r that we have chosen also for the non-singular crossing.*)
(*- We choose the remaining variables t such that when we set e->1 the singular crossing expression matches the expression for the positive crossing.*)


(* ::Input:: *)
(*Subscript[sR, 1][i,j]/.ssol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}/.{e->1}/.{Subscript[t, 15]->-(1/2),Subscript[t, 13]->0,Subscript[t, 1]->0}//Simplify*)


(* ::Input:: *)
(*Subscript[R, 1][1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify*)


(* ::Text:: *)
(*The coefficients in the expression Subscript[sR, 1][i,j] are given by:*)


(* ::Input:: *)
(*CoefficientRules[(-1+T) (-1+e+e T)^2 (Subscript[sR, 1][i,j]/.ssol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}/.{Subscript[t, 15]->-(1/2),Subscript[t, 13]->0,Subscript[t, 1]->0}//Simplify),{Subscript[g, i,i],Subscript[g, i,j],Subscript[g, j,i],Subscript[g, j,j]}]//Simplify*)


(* ::Subsection:: *)
(*Summary of solution*)


(* ::Text:: *)
(*Thus the free variables were: Subscript[r, 2], Subscript[r, 4], Subscript[r, 11], Subscript[r, 12], Subscript[t, 1], Subscript[t, 13], Subscript[t, 15]*)
(*We choose these such that the solutions for the crossings are quadratic in Subscript[g, a,b] and the solution for the curl in linear in Subscript[g, a,b] and such that the positive, negative and singular crossing are related in a familiar way.*)
(*Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T,Subscript[t, 15]->-(1/2),Subscript[t, 13]->0,Subscript[t, 1]->0*)
(*This gives the solutions:*)


(* ::Code:: *)
(*Subscript[R, 1][1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify//Expand*)
(*Subscript[R, 1][-1,i,j]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify//Expand*)
(*CC[s,i]/.sol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T}//Simplify*)
(*Subscript[sR, 1][i,j]/.ssol/.{Subscript[r, 4]->-1,Subscript[r, 11]->1,Subscript[r, 12]->-T,Subscript[r, 2]->3+T,Subscript[t, 15]->-(1/2),Subscript[t, 13]->0,Subscript[t, 1]->0}//Simplify*)


(* ::Subsection:: *)
(*Definition of the knot invariant*)


(* ::Text:: *)
(*The R-matrix Subscript[R, 1][x,s,i,j] where:*)
(*- x = 1 for the singular crossing and x = 0 for non-singular crossings.*)
(*- s = 0 for the singular crossing and s = \[PlusMinus]1 for the positive/negative crossing. *)
(*- For the singular crossing the left strand is labelled i and the right strand is labelled j, for the non-singular crossing the overstrand is labelled i and the understrand is labelled j. *)
(*is given below:*)


(* ::Input::Initialization:: *)
Subscript[R, 1][0,1,i_,j_]:=-(1/2)-(-2+T+T^2)\!\(\*SubsuperscriptBox[\(g\), \(i, j\), \(2\)]\)+Subscript[g, i,i](1+(3+T)Subscript[g, i,j]-Subscript[g, j,j])-Subscript[g, i,j](T+Subscript[g, j,i]+2 Subscript[g, j,j]);
Subscript[R, 1][0,-1,i_,j_]:=1/2-Subscript[g, i,i]+Subscript[g, i,j]/T-3 Subscript[g, i,i] Subscript[g, i,j]-(Subscript[g, i,i] Subscript[g, i,j])/T-2 \!\(\*SubsuperscriptBox[\(g\), \(i, j\), \(2\)]\)+\!\(\*SubsuperscriptBox[\(g\), \(i, j\), \(2\)]\)/T^2+\!\(\*SubsuperscriptBox[\(g\), \(i, j\), \(2\)]\)/T+Subscript[g, i,j] Subscript[g, j,i]+Subscript[g, i,i] Subscript[g, j,j]+2 Subscript[g, i,j] Subscript[g, j,j];
Subscript[R, 1][1,0,i_,j_]:=-(1/(2 (-1+T) (-1+e+e T)^2))(-1+2 e-e^2+T-e^2 T-2 e T^2+e^2 T^2+e^2 T^3+2 e (-1+T) T^2 (-1-e+e^2 T (1+T)) \!\(\*SubsuperscriptBox[\(g\), \(i, j\), \(2\)]\)+2 e \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e^2 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e^3 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e^4 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e T \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e^2 T \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e^3 T \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e^4 T \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e^3 T^2 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e^4 T^2 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e^3 T^3 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)-2 e^4 T^3 \!\(\*SubsuperscriptBox[\(g\), \(j, i\), \(2\)]\)+2 e Subscript[g, j,i] Subscript[g, j,j]-4 e^2 Subscript[g, j,i] Subscript[g, j,j]+2 e^3 Subscript[g, j,i] Subscript[g, j,j]+2 e T Subscript[g, j,i] Subscript[g, j,j]-2 e^2 T Subscript[g, j,i] Subscript[g, j,j]+4 e^3 T Subscript[g, j,i] Subscript[g, j,j]-4 e^4 T Subscript[g, j,i] Subscript[g, j,j]+4 e T^2 Subscript[g, j,i] Subscript[g, j,j]-2 e^2 T^2 Subscript[g, j,i] Subscript[g, j,j]+2 e^3 T^2 Subscript[g, j,i] Subscript[g, j,j]-4 e^4 T^2 Subscript[g, j,i] Subscript[g, j,j]-4 e^3 T^3 Subscript[g, j,i] Subscript[g, j,j]+4 e^4 T^3 Subscript[g, j,i] Subscript[g, j,j]-4 e^3 T^4 Subscript[g, j,i] Subscript[g, j,j]+4 e^4 T^4 Subscript[g, j,i] Subscript[g, j,j]+2 e T \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e^3 T \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e^3 T^2 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)+2 e^4 T^2 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e T^3 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)+2 e^4 T^3 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)+2 e^3 T^4 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e^4 T^4 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)+2 e^3 T^5 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e^4 T^5 \!\(\*SubsuperscriptBox[\(g\), \(j, j\), \(2\)]\)-2 e Subscript[g, i,i] (-1+2 e-e^2+T-e^2 T-2 e T^2+e^2 T^2+e^2 T^3+T (-1-3 T+e^2 T (-1+T^2)+e (1+T+2 T^2)) Subscript[g, i,j]-2 (-1+e) (1-e (1+T)^2+e^2 T (1+T)^2) Subscript[g, j,i]+3 e T Subscript[g, j,j]-3 e^2 T Subscript[g, j,j]+2 T^2 Subscript[g, j,j]+3 e T^2 Subscript[g, j,j]-6 e^2 T^2 Subscript[g, j,j]+2 e^3 T^2 Subscript[g, j,j]-5 e^2 T^3 Subscript[g, j,j]+4 e^3 T^3 Subscript[g, j,j]-2 e^2 T^4 Subscript[g, j,j]+2 e^3 T^4 Subscript[g, j,j])+2 e T Subscript[g, i,j] ((-1+T) (-1+e+e T)^2-(2 T+3 e (1+T)+2 e^3 T (1+T)^2-e^2 (3+6 T+5 T^2+2 T^3)) Subscript[g, j,i]+2 (-1-T+T^2+e^3 T^2 (1+T)^2+e (1+2 T+2 T^2)-e^2 T (2+3 T+2 T^2+T^3)) Subscript[g, j,j]));


(* ::Text:: *)
(*The Subscript[sing\[Rho], 1] invariant is given by:*)


(* Input a list of crossings 'Cs' and a list of rotation numbers '\[CurlyPhi]' for each edge on the diagram *)
Subscript[sing\[Rho], 1][Cs_,\[CurlyPhi]_]:=Module[{n,A,s,i,j,k,\[CapitalDelta],G,\[Rho]1},
n=Length[Cs];
A=IdentityMatrix[2n+1];
(* To the Identity matrix we add the minus Alexander matrices for each of the crossings at the appropriate spot *)
Cases[Cs,{x_,s_,i_,j_}:>(A[[{i,j},{i+1,j+1}]]+=s^2 \!\(\*
TagBox[
RowBox[{"(", "", GridBox[{
{
RowBox[{"-", "1"}], "0"},
{
RowBox[{
RowBox[{"-", "1"}], "+", 
SuperscriptBox["T", "s"]}], 
RowBox[{"-", 
SuperscriptBox["T", "s"]}]}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "Rows" -> {{Baseline}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}], "", ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\)+x \!\(\*
TagBox[
TagBox[
RowBox[{"(", "", GridBox[{
{
RowBox[{"-", "e"}], 
RowBox[{
RowBox[{"-", "1"}], "+", "e"}]},
{
RowBox[{
RowBox[{"-", "1"}], "+", 
RowBox[{"e", " ", "T"}]}], 
RowBox[{
RowBox[{"-", "e"}], " ", "T"}]}
},
GridBoxAlignment->{"Columns" -> {{Center}}, "Rows" -> {{Baseline}}},
GridBoxSpacings->{"Columns" -> {Offset[0.27999999999999997`], {Offset[0.7]}, Offset[0.27999999999999997`]}, "Rows" -> {Offset[0.2], {Offset[0.4]}, Offset[0.2]}}], "", ")"}],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]],
Function[BoxForm`e$, MatrixForm[BoxForm`e$]]]\))];
(* The Alexander polynomial is then given by the deterimant of the resulting matrix, with some normalisation to make it a palindrome *)
\[CapitalDelta]=T^(-Total[Cs[[All,1]]]/2) T^((Total[\[CurlyPhi]]-Total[Cs[[All,2]]])/2) Det[A];
(* The matrix G is defined as the inverse of A *)
G=Inverse[ A];
(* Subscript[\[Rho], 1] is defined as the sum over the crossings and curls *)
\[Rho]1=\!\(
\*SubsuperscriptBox[\(\[Sum]\), \(k = 1\), \(n\)]\(
\*SubscriptBox[\(R\), \(1\)] @@ Cs[[k]]\)\) + \!\(
\*SubsuperscriptBox[\(\[Sum]\), \(k = 1\), \(2  n\)]\(\[CurlyPhi][[k]] \((
\*SubscriptBox[\(g\), \(k\[InvisibleComma]k\)] - 
\*FractionBox[\(1\), \(2\)])\)\)\);
(* The final output is the Alexander polynomial and the Subscript[\[Rho], 1] with values for the g's filled in as the elements of G *)
Factor@{\[CapitalDelta],-\[CapitalDelta]^2\[Rho]1/.SuperPlus[\[Alpha]_]:>\[Alpha]+1/.Subscript[g, \[Alpha]_,\[Beta]_]:>G[[\[Alpha],\[Beta]]]}];


(* ::Subsection:: *)
(*Knot examples*)


(* ::Text:: *)
(*The trefoil without singular crossings reproduces the Alexander polynomial as first entry and the Subscript[\[Rho], 1](t) from [1]*)
(*The Subscript[\[Rho], 1]-part distinguishes the left-and right-handed variants.*)


(* ::Code:: *)
(*Subscript[sing\[Rho], 1][{{0,-1,4,1},{0,-1,6,3},{0,-1,2,5}},{0,0,0,-1,0,0}](*left-handed trefoil*)*)
(*Subscript[sing\[Rho], 1][{{0,1,1,4},{0,1,3,6},{0,1,5,2}},{0,0,0,-1,0,0}](*right-handed trefoil*)*)


(* ::Text:: *)
(*The trefoil with singular crossings reproduces the singular Alexander polynomial as first entry.*)
(*The singular Alexander-part already distinguishes the left-and right-handed variants.*)


(* ::Code:: *)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{0,-1,6,3},{0,-1,2,5}},{0,0,0,-1,0,0}](*left-handed trefoil with one singular crossing*)*)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{0,1,3,6},{0,1,5,2}},{0,0,0,-1,0,0}](*right-handed trefoil with one singular crossing*)*)


(* ::Text:: *)
(*For s=1 it becomes the right-handed trefoil without singular crossings*)


(* ::Input:: *)
(*%/.{e->1}//Simplify*)


(* ::Input:: *)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{0,1,3,6},{0,1,5,2}},{0,0,0,-1,0,0}]*)


(* ::Code:: *)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{1,0,3,6},{0,-1,2,5}},{0,0,0,-1,0,0}](*left-handed trefoil with two singular crossings*)*)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{1,0,3,6},{0,1,5,2}},{0,0,0,-1,0,0}](*right-handed trefoil with two singular crossings*)*)


(* ::Input:: *)
(*Subscript[sing\[Rho], 1][{{1,0,1,4},{1,0,3,6},{1,0,5,2}},{0,0,0,-1,0,0}](*trefoil with three singular crossings*)*)


(* ::Subsection:: *)
(*Knot example Sec. 3.2*)


(* ::Text:: *)
(*(The Subscript[\[CapitalGamma], s] value for this example can be found in Singular_knots _sec2 . nb)*)


(* ::Input:: *)
(*Ex2knotLHS=Subscript[sing\[Rho], 1][{{1,0,24,1},{0,-1,2,11},{0,1,3,26},{0,1,35,4},{0,-1,14,5},{0,1,6,19},{0,-1,7,30},{0,-1,8,17},{0,1,9,32},{0,1,23,10},{0,1,12,25},{0,-1,13,36},{0,1,15,20},{0,1,29,16},{1,0,18,31},{0,-1,34,21},{0,-1,22,27},{0,-1,28,33}},{0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,1,-1,1,0}]*)


(* ::Input:: *)
(*Ex2knotRHS=Subscript[sing\[Rho], 1][{{1,0,24,1},{0,1,33,2},{0,-1,16,3},{0,-1,4,9},{0,1,5,28},{0,1,6,19},{0,-1,7,30},{0,1,21,8},{0,-1,10,15},{0,1,11,34},{0,1,12,25},{0,-1,13,36},{0,1,27,14},{0,1,17,22},{1,0,18,31},{0,-1,20,29},{0,-1,32,23},{0,-1,26,35}},{0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,-1,1,1,0,0,0}]*)


(* ::Input:: *)
(*Ex2knotLHS[[1]]===Ex2knotRHS[[1]]*)
(*Ex2knotLHS[[2]]===Ex2knotRHS[[2]]*)


(* ::Title:: *)
(*References*)


(* ::Text:: *)
(*[1] Bar-Natan, D., & van der Veen, R. (2022). A Perturbed-Alexander Invariant. arXiv preprint arXiv:2206.12298.*)
