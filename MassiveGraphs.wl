(* ::Package:: *)

(* ::Title:: *)
(*Graphs and massive contact terms*)


BeginPackage["MassiveGraphs`",{"GraphGenerator`","SpinorHelicity`","HelicityVariables`"}]


(* ::Section:: *)
(*Messages*)


MomentumConservation::usage ="MomentumConservation is an option for IndependentSpinStructures and HelicityCategoryBasis specifying whether or not momentum conservation identities must be taken into account in the basis classification.\n It takes boolean values, True and False."
MassSquared::usage ="MassSquared is an option for IndependentSpinStructures specifying whether or not terms proportional to \!\(\*SubsuperscriptBox[\(M\),\(i\),\(2\)]\).\n It takes boolean values, True and False."
Echos::usage ="Echos is an option for HelicityCategoryBasis specifying whether or not to show intermediate graph-based steps in the classification of independent structures within the given helicity category and mass dimension.\n It takes boolean values, True and False."

KinematicBasis::usage = "KinematicBasis[dim,opts][{label1,spin1,category1},{label2,helicity2},...] gives a basis of kinematically independent structures. Any spin structure, within the specified helicity category (category1,helicity2,...) and mass dimension dim can be written as a linear combination of element of this basis.\n dim must be a positive integer. \n opts are the options of the function. \n The particle configuration is given as a sequence of lists: \n \t - massive particles are given as three-element lists {label,spin,category} (spin and category are half-integers, such that -spin  \[LessEqual] category  \[LessEqual] spin and spin  \[GreaterEqual] 0). \n \t - massless particles are given as two-element lists {label,helicity} (helicity is an half-integer)."
HelicityCategoryBasis::usage = "HelicityCategoryBasis[dim,opts][{label1,spin1,category1},{label2,helicity2},...] gives a list of structures, within the specified helicity category (category1,helicity2,...) and mass dimension dim, which are not related by any kinematic relation (also considering the relation mixing different helicity categories). \n opts are the options of the function. \n The particle configuration is given as a sequence of lists: \n \t - massive particles are given as three-element lists {label,spin,category} (spin and category are half-integers, such that -spin  \[LessEqual] category  \[LessEqual] spin and spin  \[GreaterEqual] 0). \n \t - massless particles are given as two-element lists {label,helicity} (helicity is an half-integer)."


(* ::Section:: *)
(*Private*)


(* ::Subsection::Closed:: *)
(*Begin*)


Begin["`Private`"]


(* ::Subsection::Closed:: *)
(*Independent Spin Structures*)


Options[KinematicBasis] = {MomentumConservation -> True, MassSquared -> False};

SetAttributes[KinematicBasis,ReadProtected];

KinematicBasis[dim_Integer, opts:OptionsPattern[]][list__?((Length[#] == 2 && IntegerQ[2*#[[2]]]) || (Length[#] == 3 && IntegerQ[2*#[[2]]] && IntegerQ[2*#[[3]]] && #[[2]] >= Abs[#[[3]]]) &)] :=
 Module[
  {
   massivespins = Table[If[Length[i] == 2(*if massless*), 0, i[[2]]], {i, {list}}],(*a list of all the spins, for massless particles is zero*)
   x = Table[If[Length[i] == 2, 0, i[[3]]], {i, {list}}], (*a list of all the transversality, for massless particles is zero*)
   momenta = dim - Sum[i[[2]], {i, {list}}], (*the number of momenta insertions in the structures*)
   n = Length[{list}]
   },
  
  If[momenta < 0, {}];
  
  massivespins = Tuples[(Range[-#, #, 1]) & /@ massivespins]; (*all the possible transversality combinations for the spins*)
  massivespins = {(*Abs[*)# - x(*]*), #} & /@ massivespins; (*for each transversality configuration gives the difference (not in absolute value, it does distinguish between m and OverTilde[m])*)
  massivespins = {
      Product[If[#[[1, i]] > 0, MassUntilde[{list}[[i, 1]]]^#[[1, i]], MassTilde[{list}[[i, 1]]]^(-#[[1, i]])], {i, n}],(*the masses to compensate the mass dimensions*)
      Total@Abs[#[[1]]],(*the total difference*)
      Table[If[Length[{list}[[i]]] == 2, {list}[[i]], {{list}[[i, 1]], {list}[[i, 2]], #[[2, i]]}], {i, n}](*if massive, changes the original transversalities in all their possible combinations*)
      } & /@ massivespins;
  
  massivespins = SortBy[massivespins, #[[1]] &];
  
  massivespins = #[[1]]*HelicityCategoryBasis[dim - #[[2]], MomentumConservation->OptionValue[MomentumConservation]][Sequence @@ #[[3]]] & /@ massivespins; (*applies the algorithm with uniform mass powers*)
  
  If[momenta - 2 >= 0 && OptionValue[MassSquared], (*if we want to consider terms proportional to M^2*)
   
   x = If[Length[#] == 2, Nothing, #[[1]]] & /@ {list};
   (*x=Subsets[x,{1,Floor[Echo@momenta/2]}];*)
   x = Map[MassTilde[#]*MassUntilde[#] &, x, {1}];
   (*x=Flatten/@GatherBy[Times@@@x,Length[#]&]//Echo;*)
   x = Map[Times @@ Thread[Power[x, #]] &, Table[Flatten[Permutations /@ (PadRight[#, Length@x] & /@ IntegerPartitions[i, Length@x]), 1], {i, Floor[momenta/2]}], {2}];
   
   massivespins =
    Join[
     massivespins,
     (Times @@@
       Flatten[
        Tuples /@
         (Transpose@{
            x,
            KinematicBasis[dim - #, opts][list] & /@ (2*Range@Floor[momenta/2])
            }),
        1])
     ]
   ];
  
  Return[Flatten@massivespins]
  
  ]


(* ::Subsection::Closed:: *)
(*Uniform Mass Structures*)


Options[HelicityCategoryBasis] = {MomentumConservation -> True, Echos -> False};

SetAttributes[HelicityCategoryBasis,ReadProtected];

HelicityCategoryBasis[dim_Integer, OptionsPattern[]][list__] :=
 Module[{labels = Part[#, 1] & /@ {list}, spins = Delete[#, 1] & /@ {list}, angles, squares, structures},
  
  {angles, squares} =
   Transpose[(*gives the number of angles and the number of squares for each particle*)
    If[Length[#] == 1(*if massless*),
       {Abs[#[[1]]] - #[[1]], Abs[#[[1]]] + #[[1]]},
       {#[[1]] - #[[2]], #[[1]] + #[[2]]}(*the definition of transversality for massive particles*)
       ] & /@ spins
    ];
  
  If[
   TrueQ@OptionValue[MomentumConservation],(*structures given the possible distributions of momentum insertions*)
   structures = (Append[#, 0] & /@ PermutationsOfPartitions[dim - Total[angles]/2 - Total[squares]/2, Length[angles] - 1]),(*if we consider structures modulo momentum conservation, we can ignore the momentum of the nth-particle*)
   structures = PermutationsOfPartitions[dim - Total[angles]/2 - Total[squares]/2, Length[angles]]
   ];
  
  structures = {{angles + #, squares + #}, #} & /@ structures;(*each momentum add an angle and a square*)
  
  structures = If[Length[#[[1]]] < 2(*IsLoopLessDoable returns Nothing if no graph is possible*), Nothing, #] & /@ (MapAt[Map[IsLoopLessDoable, #, {1}] &, #, 1] & /@ structures)(*we check if a loop-less graph can be done for both angles and squares*);
  
  structures = SpinStructures[#, labels, Length /@ spins, MomentumConservation -> OptionValue[MomentumConservation], Echos -> OptionValue[Echos]] & /@ structures;
  
  structures = Flatten[structures, 1];
  
  Return[(*Flatten@*)structures]
  
  ]


(* ::Subsection:: *)
(*Auxiliary functions*)


(* ::Subsubsection::Closed:: *)
(*Spin Structures*)


Options[SpinStructures]={MomentumConservation->True,Echos->False,GraphOnly->False};

SpinStructures[{{anglestructure_List,squarestructure_List},momenta_List},labels_List,spins_List(*1 or 2 if the corresponding particle is massless or massive, respectively*),OptionsPattern[]]:=
Module[{formfactors,angles,squares},

angles=AllNonIntersectingGraphs[anglestructure];
squares=AllNonIntersectingGraphs[squarestructure];

formfactors=Tuples[{angles,squares}];

If[OptionValue[Echos], (*Printing intermediate sterps*)
Echo[momenta,"Momenta:"];
If[OptionValue[MomentumConservation],Echo[Map[DrawStructure[#,labels]&,formfactors,{1}],"Graphs before momentum conservation:"]]; (*Draw all the structures, without distinguishing between free massive spinors and momenta*)
If[MemberQ[spins,2],Echo[FreeSpinorsAndMomenta[#,momenta,labels,spins]&/@formfactors,"Graphs with momenta:"]] (*if there is a massive particle, draw the corresponding graph with free spinors and momenta*)
];

If[
OptionValue[MomentumConservation],
formfactors=PlanarMomentumConservation[#,momenta,Echos->OptionValue[Echos]]&/@formfactors;

If[momenta[[1]]!=0&&anglestructure[[-1]]!=0&&squarestructure[[-1]]!=0,

squares=Length[spins];
angles=
Flatten[(*flatten permutations*)
Permutations/@Flatten[ (*flatten table and permute each element to give both the subtractions for angles and squares*)
Table[
({Join[PadRight[{i},squares-2],#],Join[PadRight[{i},squares-2],Reverse@#]})&/@(PadRight[#,2]&/@IntegerPartitions[i,2])(*the momentum p_1 is contracted with spinors of (n-1) and n*),
{i,momenta[[1]]}],
1],
1](*this are the possible contractions of momentum p_1 with (n-1) and n*);
angles=({anglestructure,squarestructure}-#)&/@angles(*subtractions of the structures*);
angles=If[MemberQ[Flatten[#],_?(#<0&)],Nothing,#]&/@angles(*eliminating the structures for which the valencies becomes negative*);
angles=Map[IsLoopLessDoable,angles,{2}](*checking if structures are doable*);
angles=If[Length[#]==2(*if structures are possible for both angles and squares*),ExtraGraphs[#,{anglestructure,squarestructure}-#,momenta,labels,spins,squares],Nothing]&/@angles(*ExtraGraphs gives the graphs with compatible valencies and <(n-1)|p_1|n] or <n|p_1|(n-1)] appearing explicitly*);
angles=Flatten[angles,1];

If[OptionValue[Echos],
Echo[DrawStructure[#,labels]&/@angles,"Extra momentum conservation:"]
];

angles=IndependentConstrainQ/@angles (*we must exclude the structures which are planar, because they do not correspond to extra constraints*);

If[OptionValue[Echos],
Echo[DrawStructure[#,labels]&/@angles,"Extra momentum conservation:"]
];

formfactors=ExtraMomentumConservation[formfactors,Length[Join[angles]]];
];

If[MatchQ[Take[RotateRight[momenta,2],{1,4}],{0,0,0,_?(#!=0&)}]&&MatchQ[Take[RotateRight[spins,2],{1,3}],{2,2,2}],

squares=Length[spins];

angles=
Table[
RotateLeft[#,2]&/@(
PadRight[#,squares]&/@
{{i,i,i,i},{i,i,i,i}}
),
{i,#}
]&@Min[Join[Take[RotateRight[anglestructure],{1,3}],Take[RotateRight[squarestructure],{1,3}],{momenta[[2]]}]];
angles=({anglestructure,squarestructure}-#)&/@angles(*subtractions of the structures*);
angles=If[MemberQ[Flatten[#],_?(#<0&)],Nothing,#]&/@angles(*eliminating the structures for which the valencies becomes negative*);
angles=Map[IsLoopLessDoable,angles,{2}](*checking if structures are doable*);
angles=If[Length[#]==2(*if structures are possible for both angles and squares*),ExtraMassiveGraphs[#,momenta,labels,spins,squares,anglestructure[[1]]-#[[1,1]]],Nothing]&/@angles(*ExtraGraphs gives the graphs with compatible valencies and <(n-1)|p_1|n] or <n|p_1|(n-1)] appearing explicitly*);
angles=Flatten[angles,1](*The ExtraMassivegraphs gives a nested structure*);

If[OptionValue[Echos],
Echo[DrawStructure[#,labels]&/@angles,"Extra massive momentum conservation:"]
];

{formfactors,angles}={Complement[formfactors,angles],Complement[angles,formfactors]};

If[OptionValue[Echos],
Echo[DrawStructure[#,labels]&/@angles,"Extra massive momentum conservation:"]
];

formfactors=ExtraMassiveMomentumConservation[formfactors,squares,Length[Join[angles]]];
]
];

If[OptionValue[Echos],
If[\[Not]MatchQ[formfactors,{}],Echo[Map[DrawStructure[#,labels]&,formfactors,{1}],"Graphs:"],Echo["No graph survided."]] (*Draw the graph which survived momentum conservation*)
];

If[\[Not]OptionValue[GraphOnly],
formfactors=FromMatrixToSpinors[#,momenta,labels,spins,MomentumConservation->OptionValue[MomentumConservation],Echos->OptionValue[Echos]]&/@formfactors;
];

Return[formfactors];
]


(* ::Subsubsection::Closed:: *)
(*Splitting Free Spinors and Momenta*)


FreeSpinorsAndMomenta[{adjAngle_,adjSquare_},momenta_List,labels_List,spins_List]:=
Module[{newlabels,types,positions,nonmomenta,newangles,newsquares,n,forbiddenEdges},

newlabels=If[#[[3]]==2,ConstantArray[#[[1]],#[[2]]+1],{#[[1]]}]&/@Transpose[{labels,momenta,spins}]; (*if the vertex is massive, we made the label appear (d+1) times, where d is the number of its momentum insertions. If it is massless, it must appear only once*)
positions=FoldPairList[TakeDrop,Range@Length[Flatten@newlabels],Length/@newlabels];(*given {1,...m} where m is the number of particles + the number of massive momentum insertions, it splits this list into sublist each corresponding to free spinor + momenta for massive particles and massless vertex*)
forbiddenEdges=Flatten[
Map[
Subsets[#,{2}]&,
If[Length[#]<2,Nothing(*excluding massless vertices and massive states with no momentum insertions*),#]&/@positions,
{1}
],
1];(*the list of edges which connect a momentum vertex with the corresponding free spinor vertex*)

nonmomenta =Part[#,1]&/@positions;

n=Length[Flatten@newlabels];

newangles=
SparseArray[
MapAt[
ReplaceAll[#,Thread[Rule[Range@Length[labels],nonmomenta]]]&,(*change the labels with the position of free spinor vertices*)
#,
{1}(*ArrayRules gives {non-zero position -> non-zero value}, and we should act only on the positions*)
]&/@ArrayRules[adjAngle],{n,n}(*the dimension of the array must be specified*)];
newsquares=SparseArray[MapAt[ReplaceAll[#,Thread[Rule[Range@Length[labels],nonmomenta]]]&,#,{1}]&/@ArrayRules[adjSquare],{n,n}];

Do[
n=i[[-1]];
Do[
{newangles[[Sequence@@#]]--,newangles[[Sequence@@ReplaceAll[#,{n->j}]]]++}&@
Part[
Join[
Sort[Select[#,MatchQ[#,{n,_}]&]],
Sort[Select[#,MatchQ[#,{_,n}]&]]
]&@newangles["NonzeroPositions"],
1];
{newsquares[[Sequence@@#]]--,newsquares[[Sequence@@ReplaceAll[#,{n->j}]]]++}&@
Part[Join[Sort[Select[#,MatchQ[#,{n,_}]&]],Sort[Select[#,MatchQ[#,{_,n}]&]]]&@newsquares["NonzeroPositions"],1],
{j,Delete[i,-1]}
],
{i,Reverse/@positions}
];

{newangles,newsquares}=Planarise[#,forbiddenEdges]&/@{newangles,newsquares};(*checks if the algorithm above did a good job!*)

newlabels=Flatten@newlabels;

DrawStructure[{newangles,newsquares},newlabels]

]


Planarise[matrix_,forbiddenEdges_]:=
Module[{x=matrix},
While[
IsGraphNonIntesercting[x]==Nothing,
Print["OPS! If you are not Stefano, please ignore!"];
x=(If[IntersectingQ[#["NonzeroPositions"],forbiddenEdges],Nothing,#]&/@SchoutenCrossing[x]);
x=Part[x,1]
];
Return[x]
]


(* ::Subsubsection::Closed:: *)
(*Planar Momentum Conservation*)


Options[PlanarMomentumConservation]={Echos->False};

PlanarMomentumConservation[{angles_,squares_},momenta_List,OptionsPattern[]]:=
Module[{nonzeroangles=angles["NonzeroPositions"],nonzerosquares=squares["NonzeroPositions"],forbidden={},n=Length[momenta]},

If[momenta[[-2]]!=0,
AppendTo[forbidden,MemberQ[nonzeroangles,{n-1,n}]||MemberQ[nonzerosquares,{n-1,n}]]
];

If[
momenta[[1]]!=0,
forbidden=
Join[
forbidden,
{
MemberQ[nonzeroangles,{1,n-1}]&&MemberQ[nonzerosquares,{1,n}],
MemberQ[nonzeroangles,{1,n}]&&MemberQ[nonzerosquares,{1,n-1}]
}
];
If[
momenta[[-2]]!=0,
forbidden=
Join[
forbidden,
{
MemberQ[nonzeroangles,{1,n-1}]&&MemberQ[nonzerosquares,{1,n-1}]
}
]
]
];

If[If[OptionValue[Echos],Echo[Or@@Echo[forbidden,"Conditions:"]],Or@@forbidden],Return[Nothing],Return[{angles,squares}]]
]


ReinstateFirst[list_List,n_Integer]:=SparseArray[Table[{1,i}->list[[i]],{i,(*2, all of them, (n-1) just the one which are restricted to appear*)n-1,n}],{n,n}]


ExtraGraphs[structures_List,valencies_List,momenta_List,labels_List,spins_List,n_Integer]:=(#+(ReinstateFirst[#,n]&/@valencies (*the angles and squares which are going to be reinstated*)))&/@
SpinStructures[
{
structures,
MapAt[
Min[{structures[[1,-2]],structures[[2,-2]],momenta[[-2]]}],
MapAt[
(#-valencies[[1,1]])&,
momenta,
{1}
],
{-2}
]
},
labels,
spins,
GraphOnly->True];


IndependentConstrainQ[{angles_SparseArray,squares_SparseArray}]:=If[MatchQ[IsGraphNonIntesercting[angles],Nothing]||MatchQ[IsGraphNonIntesercting[squares],Nothing],{angles,squares},Nothing]


ExtraMomentumConservation[formfactors_List,n_Integer]:=DeleteCases[formfactors,_?(ExtraConditions[#]&),1,n]


ExtraConditions[formfactor_List]:=(formfactor[[1,-2,-1]]!=0&&formfactor[[2,1,-1]]!=0)||(formfactor[[2,-2,-1]]!=0&&formfactor[[1,1,-1]]!=0)||(formfactor[[1,1,-1]]!=0&&formfactor[[2,1,-1]]!=0&&Sum[formfactor[[1,i,-2]]+formfactor[[2,i,-2]],{i,2,Length[formfactor[[1]]]-2}]!=0)


ReinstateMassive[m_Integer,n_Integer]:={SparseArray[{{1,n}->m,{2,n-1}->m},{n,n}],SparseArray[{{n-1,n}->m,{1,2}->m},{n,n}]}


ExtraMassiveGraphs[structures_List,momenta_List,labels_List,spins_List,n_Integer,m_Integer(*the number of "factorised" structures*)]:=(#+(ReinstateMassive[m,n] (*the angles and squares which are going to be reinstated (the "factorised" structure)*)))&/@SpinStructures[{structures,MapAt[(#-m)&,momenta,{2}](*we subtract the number of momenta p_2, in the "factorised" structure <1 n>^m [(n-1) n]^m <(n-1)|p_2|n]^m*)},labels,spins,GraphOnly->True];


ExtraMassiveMomentumConservation[formfactors_List,m_Integer(*number of particles*),n_Integer]:=DeleteCases[formfactors,_?(ExtraMassiveConditions[#,m]&),1,n]


ExtraMassiveConditions[formfactor_List,m_Integer]:=
formfactor[[1,1,m]]!=0&&formfactor[[2,1,2]]!=0&&formfactor[[2,m-1,m]]!=0&&
(
(formfactor[[1,1,m]]!=0&&Sum[formfactor[[1,2,i]],{i,3,m-2}]!=0)(*type 1*)||
(formfactor[[1,1,2]]!=0&&Sum[formfactor[[1,i,m-1]],{i,3,m-2}]!=0)(*type 2*)||
(formfactor[[1,m-1,m]]!=0&&Sum[formfactor[[1,2,i]],{i,3,m-2}]!=0)(*type 3*)||
(formfactor[[1,2,m]]!=0&&Sum[formfactor[[1,i,m-1]],{i,3,m-2}]!=0)(*type 4*)||
(formfactor[[1,1,m]]>1&&Sum[formfactor[[1,2,i]],{i,3,m-2}]!=0&&Sum[formfactor[[1,i,m-1]],{i,3,m-2}]!=0)(*type 5*)||
(formfactor[[1,m-1,m]]!=0&&formfactor[[1,1,2]]!=0&&Sum[formfactor[[1,i,j]],{i,3,m-3},{j,i+1,m-2}]!=0) (*type 6*)
)


(* ::Subsubsection::Closed:: *)
(*From Matrix to Spinors structures*)


Options[FromMatrixToSpinors]={MomentumConservation->True,Echos->True};

FromMatrixToSpinors[{adjAngle_,adjSquare_},momenta_List,labels_List,spins_List,OptionsPattern[]]:=
If[MemberQ[spins,2],
Module[{newlabels,types,positions,nonmomenta,newangles,newsquares,n,forbiddenEdges},

(*Echo[{{adjAngle,adjSquare},momenta}];*)

newlabels=If[#[[3]]==2,ConstantArray[#[[1]],#[[2]]+1],{#[[1]]}]&/@Transpose[{labels,momenta,spins}];
positions=FoldPairList[TakeDrop,Range@Length[Flatten@newlabels],Length/@newlabels];
forbiddenEdges=Flatten[Map[Subsets[#,{2}]&,If[Length[#]<2,Nothing,#]&/@positions,{1}],1];

nonmomenta =(* Table[1+Sum[Length[newlabels[[i]]],{i,1,j-1}],{j,1,Length@momenta}]*)Part[#,1]&/@positions;

(*newlabels=Flatten[newlabels];*)
n=Length[Flatten@newlabels];

newangles=SparseArray[MapAt[ReplaceAll[#,Thread[Rule[Range@Length[labels],nonmomenta]]]&,#,{1}]&/@ArrayRules[adjAngle],{n,n}];
newsquares=SparseArray[MapAt[ReplaceAll[#,Thread[Rule[Range@Length[labels],nonmomenta]]]&,#,{1}]&/@ArrayRules[adjSquare],{n,n}];

(*newlabels=Flatten[newlabels];*)
(*Echo[{newangles,newsquares}];*)

Do[
n=i[[-1]];
Do[
{newangles[[Sequence@@#]]--,newangles[[Sequence@@ReplaceAll[#,{n->j}]]]++}&@(*Part[Sort[Select[newangles["NonzeroPositions"],MatchQ[#,{n,_}|{_,n}]&]],1]*)
Part[Join[Sort[Select[#,MatchQ[#,{n,_}]&]],Sort[Select[#,MatchQ[#,{_,n}]&]]]&@newangles["NonzeroPositions"],1];
{newsquares[[Sequence@@#]]--,newsquares[[Sequence@@ReplaceAll[#,{n->j}]]]++}&@(*Part[Sort[Select[newsquares["NonzeroPositions"],MatchQ[#,{n,_}|{_,n}]&]],1]*)
Part[Join[Sort[Select[#,MatchQ[#,{n,_}]&]],Sort[Select[#,MatchQ[#,{_,n}]&]]]&@newsquares["NonzeroPositions"],1],
{j,Delete[i,-1]}
],
{i,Reverse/@positions}
];

{newangles,newsquares}=Planarise[#,forbiddenEdges]&/@{newangles,newsquares};

types=Flatten@Table[If[spins[[i]]==1,1,{2,ConstantArray[3,momenta[[i]]]}],{i,Length@positions}];
newlabels=Flatten@newlabels;

(*If[OptionValue[Echos],Echo[DrawStructure[{newangles,newsquares},newlabels],"New graph:"]];*)

(*If[
TrueQ@OptionValue[MomentumConservation],
If[PlanarMomentumConservation[{newangles,newsquares},positions,spins],Return[Nothing]]
];*)

Return[(*{newangles,newsquares}*)
ContractLittleGroup[
Times@@((AngleB[
If[types[[#[[1,1]]]]==1,SpinorUndottedML[][newlabels[[#[[1,1]]]]],If[types[[#[[1,1]]]]==2,SpinorUndottedMV[][newlabels[[#[[1,1]]]]],SpinorUndottedMV[$up][newlabels[[#[[1,1]]]],StringJoin["I",ToString[newlabels[[#[[1,1]]]]],ToString[#[[1,1]]]]]]],
If[types[[#[[1,2]]]]==1,SpinorUndottedML[][newlabels[[#[[1,2]]]]],If[types[[#[[1,2]]]]==2,SpinorUndottedMV[][newlabels[[#[[1,2]]]]],SpinorUndottedMV[$up][newlabels[[#[[1,2]]]],StringJoin["I",ToString[newlabels[[#[[1,2]]]]],ToString[#[[1,2]]]]]]]]^#[[2]]
)&/@Delete[ArrayRules[newangles],-1])*
Times@@((SquareB[
If[types[[#[[1,1]]]]==1,SpinorDottedML[][newlabels[[#[[1,1]]]]],If[types[[#[[1,1]]]]==2,SpinorDottedMV[][newlabels[[#[[1,1]]]]],SpinorDottedMV[$down][newlabels[[#[[1,1]]]],StringJoin["I",ToString[newlabels[[#[[1,1]]]]],ToString[#[[1,1]]]]]]],
If[types[[#[[1,2]]]]==1,SpinorDottedML[][newlabels[[#[[1,2]]]]],If[types[[#[[1,2]]]]==2,SpinorDottedMV[][newlabels[[#[[1,2]]]]],SpinorDottedMV[$down][newlabels[[#[[1,2]]]],StringJoin["I",ToString[newlabels[[#[[1,2]]]]],ToString[#[[1,2]]]]]]]]^#[[2]]
)&/@Delete[ArrayRules[newsquares],-1])
]
]

]
,

If[
TrueQ@OptionValue[MomentumConservation],
If[PlanarMomentumConservation[{adjAngle,adjSquare},FoldPairList[TakeDrop,Range@Length[Flatten@#],Length/@#],spins]&@(If[#[[3]]==2,ConstantArray[#[[1]],#[[2]]+1],{#[[1]]}]&/@Transpose[{labels,momenta,spins}]),Return[Nothing]]
];

Times@@(AngleB[SpinorUndottedML[][labels[[#[[1,1]]]]],SpinorUndottedML[][labels[[#[[1,2]]]]]]^#[[2]]&/@Transpose[{adjAngle["NonzeroPositions"],adjAngle["NonzeroValues"]}])*Times@@(SquareB[SpinorDottedML[][labels[[#[[1,1]]]]],SpinorDottedML[][labels[[#[[1,2]]]]]]^#[[2]]&/@Transpose[{adjSquare["NonzeroPositions"],adjSquare["NonzeroValues"]}])
]


(* ::Subsubsection::Closed:: *)
(*Draw Structures*)


DrawStructure[{adjacencyAngle_,adjacencySquare_},labels_List]:=Show[{DrawAdjacencyGraph[adjacencyAngle,Colour->Red],DrawAdjacencyGraph[adjacencySquare,Colour->Blue,Labels->labels]}]


(* ::Subsection::Closed:: *)
(*End*)


End[]


(* ::Section:: *)
(*Attributes*)


Protect@@Names["MassiveGraphs`*"]


EndPackage[]
