Read("sss_nielsen.g");

# This function is a modified copy of inner function indentify() from function FoldFlowerAutomaton from package "automata".
IdentifyVerices := function(T, na, ns, p1, p2)
  local a, q;
  if p2 = 1 then # let the initial state never be removed
    p2 := p1;
    p1 := 1;
  fi;
  for a in [1..na] do # all occurrences of p2 in the transition matrix are substituted by p1.
    for q in [1..ns] do
      if p2 in T[a][q] then
        T[a][q] := Union(T[a][q],[p1]);
        T[a][q] := Difference(T[a][q],[p2]);
      fi;
    od;
  od;
  for a in [1..na] do 
    T[a][p1] := Union(T[a][p1], T[a][p2]);
    if not p1 = p2 then
      T[a][p2] := [];
    fi;
  od;
  T[a][p1] := Set(Flat(T[a][p1]));
  SubtractSet(T[a][p1], [0]);
end;


# This function is a modified copy of inner function deleteAndRename() from function FoldFlowerAutomaton from package "automata".
DeleteAndRenameVertices := function(T, c) 
  local TR, acc, nt, newtable, n1, n2, newnewtable, r, s;
  TR := TransposedMat(T);
  acc := Difference([1..Length(T[1])],c);
  nt := TR{acc};
  newtable := TransposedMat(nt);
  n1 := Length(newtable);
  n2 := Length(newtable[1]);
  newnewtable := NullMat(n1,n2);
  for r in [1 .. n1] do
    for s in [1 .. n2] do
      if newtable[r][s] <> 0 then
        if Position(acc, newtable[r][s]) <> fail then
          newnewtable[r][s] := Position(acc, newtable[r][s]);
        fi;
      else
        newnewtable[r][s] := 0;
      fi;
    od;
  od;
  return newnewtable;
end;


# Glues two vertices.
GlueTwoVerticesOfAutomaton := function(A, i, j)
  local T, t, na, ns;
  if not A!.type = "nondet" then
    Error(" A must be non deterministic");
  fi;
  if not (A!.initial = [1] and A!.accepting = [1]) then
    Error(" 1 must be initial and accepting state");
  fi;
  if i > j then
    t := i;
    i := j;
    j := t;
  fi;
  T := StructuralCopy(A!.transitions);
  na := A!.alphabet;
  ns := A!.states;
  IdentifyVerices(T, na, ns, i, j);
  return Automaton("nondet", ns, AlphabetOfAutomatonAsList(A), T, [1], [1]); 
end;


# Inserts a path of length l to A between i and j.
InsertArcToAutomaton := function(A, i, j, l)
  local k, s, T, t, na, ns;
  if not A!.type = "nondet" then
    Error(" A must be non deterministic");
  fi;
  if not (A!.initial = [1] and A!.accepting = [1]) then
    Error(" 1 must be initial and accepting state");
  fi;
  T := StructuralCopy(A!.transitions);
  na := A!.alphabet;
  ns := A!.states;
  s := [];
  for k in [1..ns] do
    Add(s, []);
  od;
  for k in [1..l - 2] do
    Add(s, [ns + k + 1]);
  od;
  if l > 1 then
    s[i] := [ns + 1];
    s[ns + l - 1] := [j];
  else
    s[i] := [j];
  fi;
  Add(T, s);
  return Automaton("nondet", ns + l - 1, letters{[1..(na + 1)]}, T, [1], [1]); 
end;


# Folds an automaton.
# This function is a modified copy of function FoldFlowerAutomaton from package "automata".
FoldAutomaton := function(A)
  local ug, na, ns, T, changes1, changes2, a, q, p, c1, c2, c, newtable, b, aut, s, r;
  if not A!.type = "nondet" then
    Error(" A must be non deterministic");
  fi;
  if not (A!.initial = [1] and A!.accepting = [1]) then
    Error(" 1 must be initial and accepting state");
  fi;
  na := A!.alphabet;
  ns := A!.states;
  T := StructuralCopy(A!.transitions);
  changes1 := true;
  changes2 := true;
  while changes1 or changes2 do 
    while changes1 do
      changes1 := false;
      for a in [1..na] do
        for q in [1..ns] do
          if Length(T[a][q]) > 1 then
            changes1 := true;
            changes2 := true;
            IdentifyVerices(T, na, ns, T[a][q][1],T[a][q][2]);
          fi;
        od;
      od;
    od;
    while changes2 do
      changes2 := false;
      for a in [1..na] do
        for p in [1..ns] do
          for q in [1..ns] do
            if p <> q and Intersection(T[a][p],T[a][q]) <> [] then
              changes1 := true;
              changes2 := true;
              IdentifyVerices(T, na, ns, p, q);
            fi;
          od;
        od;
      od;
    od;
  od;
  for a in [1..na] do
    for q in [1..ns] do
      if T[a][q] <> [] then
        T[a][q] := T[a][q][1];
      else
        T[a][q] := 0;
      fi;
    od;
  od;
  ### computes the inaccessible states
  c1 := Filtered([1..ns], q -> ForAll([1..na],a -> T[a][q] = 0));
  c2 := Difference([1..ns],Set(Flat(T)));
  c := Intersection(c2,c1);  
  newtable := DeleteAndRenameVertices(T,c); ## removes the inaccessible states
  ## remove states of degree 1
  b := true;
  while b do
    b := false;
    aut := Automaton("det", Length(newtable[1]), na, newtable,[1],[1]);
    ug := UnderlyingMultiGraphOfAutomaton(aut);
    T := aut!.transitions;
    s := []; #list of vertices of degree 1
    for r in [2..aut!.states] do
      if AutoVertexDegree(ug,r) = 1 then
        Add(s,r);
      fi;
    od;
    if s <> [] then
      b := true;
      newtable := DeleteAndRenameVertices(T,s); ## removes states of degree 1
    fi;
  od;
  return Automaton("det", Length(newtable[1]), na, newtable,[1],[1]);
end;

# Transforms a deterministic automaton A to non-deterministic.
DetToNonDet := function(A)
  return Automaton("nondet", 
      NumberStatesOfAutomaton(A), 
      AlphabetOfAutomatonAsList(A), 
      TransitionMatrixOfAutomaton(A), 
      InitialStatesOfAutomaton(A), 
      FinalStatesOfAutomaton(A)); 
end;

# Enumerates all pairs of vertices and glues an automaton on these pairs.
GetSecretsForGluedAutomatons := function(A)  
  local i, j, B, gs, result; 
  result := []; 
  for i in [1..NumberStatesOfAutomaton(A)] do
    for j in [(i + 1)..NumberStatesOfAutomaton(A)] do
      B := FoldAutomaton(GlueTwoVerticesOfAutomaton(A, i, j));
      gs := InverseAutomatonToGenerators(B);
      AddSet(result, GetSecretSum(gs{[2..Length(gs)]}));
    od;
  od;
  return result;
end;


# Enumerates all pairs of vertices and glues an automaton on these pairs.
GetSecretsForExtendedAutomatons := function(A, L)  
  local i, j, l, B, gs, result; 
  result := []; 
  for i in [1..NumberStatesOfAutomaton(A)] do
    for j in [i..NumberStatesOfAutomaton(A)] do
      for l in [1..L] do
        B := FoldAutomaton(InsertArcToAutomaton(A, i, j, l));
        gs := InverseAutomatonToGenerators(B);
        AddSet(result, GetSecretSum(gs{[2..Length(gs)]}));
      od;
    od;
  od;
  return result;
end;


# Implementation of the attack.
GetPossibleSecrets := function(words, L)
  local qws, gs, A, s1, s2;
  qws := [q];
  Append(qws, List(words, w -> ConvertWordToString(w)));
  A := DetToNonDet(SubgroupGenToInvAut(qws));
  s1 := GetSecretsForGluedAutomatons(A);
  s2 := GetSecretsForExtendedAutomatons(A, L);
  return Union(s1, s2);
end;

