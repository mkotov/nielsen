# This is an implementation of the secret sharing scheme based on Nielsen transformations from 
# A. Moldenhauer, G. Rosenberger "Criptogrphic protocols based on Nielsen transformations", Section 4. 
#
# Alexander Ushakov, Matvei Kotov, 2015.

LoadPackage("automata");

# The number of the free generators of F<x1, x2, ..., xq>, must be in 2..8.
q := 2;

# The number of the participants.
n := 3;

# The threshold. t <= n.
t := 2;

m := Binomial(n, t - 1);

letters := ["a", "b", "c", "d", "e", "f", "g", "h"];

Letters := ["A", "B", "C", "D", "E", "F", "G", "H"];

# The platform group
F := FreeGroup(letters{[1..q]});


# Converts a pair (g, e), to the string "gg...g" of length e. If e < 0, then the result is "GG...G".
ConvertSyllableToString := function(g, e)
  if e = 0 then
    return "";
  elif e > 0 then 
    return Concatenation(List([1..e], i -> letters[g]));
  else 
    return Concatenation(List([1..-e], i -> Letters[g]));
  fi;
end;


# Transforms a word to the corresponding string. For example, WordToString(a^-1*b*c) = "Abc".
ConvertWordToString := function(w)
    return Concatenation(List([1..NumberSyllables(w)], i -> ConvertSyllableToString(GeneratorSyllable(w, i), ExponentSyllable(w, i))));
end;


# Transfroms a char to the element of F.
ConvertCharToSymbol := function(F, c)
  local pos;
  pos := Position(letters, [c]);
  if pos <> fail then
    return GeneratorsOfGroup(F)[pos];
  fi;
  pos := Position(Letters, [c]);
  if pos <> fail then
    return GeneratorsOfGroup(F)[pos]^-1;
  fi;
  return fail;
end;


# Transforms a string to the corresponding word. For example, StringToWord("AbbC") = a^-1*b*b*c^-1.
ConvertStringToWord := function(F, s)
  return Product(List(s, c -> ConvertCharToSymbol(F, c)));
end;


# Returns the sum S = \sum_{i = 1}^m {1 / |u_i|} for a set {u_1, u_2, \ldots, u_m}
GetSecretSum := function(words)
  return Sum(words, w -> 1 / Length(w));
end;


# Applies a Nielsen transformation of type I: u_i --> u_i^-1.
ApplyT1 := function(words, i)
   words[i] := words[i]^-1;
end;


# Applies a Nielsen transformation of type II: u_i --> u_i*u_j, i != j.  
ApplyT2 := function(words, i, j)
  words[i] := words[i] * words[j];
end;


# Applies a random sequence of Nielsen transformations.
ApplyRandomNielsenTransform := function(words, numberOfTransforms)
  local i, j, k, t, ws;
  ws := ShallowCopy(words);
  for i in [1..numberOfTransforms] do
    t := Random([1..2]);
    if t = 1 then
      j := Random([1..Length(ws)]);
      ApplyT1(ws, j);
    else 
      j := Random([1..Length(ws)]);
      k := Random([1..(Length(ws)-1)]);
      if k >= j then
        k := k + 1;
      fi;
      ApplyT2(ws, j, k);
    fi;
  od;
  return ws;
end;


# Returns a random list of size m of words of a free group F.
GenerateRandomListOfWords := function(F, m, d, D)
  local i, w, ws;
  ws := [];
  for i in [1..m] do
    repeat
      w := PseudoRandom(F: radius := Random([d, D]));
    until not IsOne(w);
    Add(ws, w);
  od;
  return ws;
end;


# Reduces a set of words.
ReduceSet := function(words)
  local gs, L;
  L := [q];
  Append(L, List(words, w -> ConvertWordToString(w)));
  gs := InverseAutomatonToGenerators(SubgroupGenToInvAut(L));
  return List(gs{[2..Length(gs)]}, s -> ConvertStringToWord(F, s));
end;


# Returns true if the lengths of all words in an interval [1, D].
TestLongWordLengths := function(gs, D)
  local g;
  for g in gs do
    if Length(g) > D then
      return false;    
    fi;
  od;
  return true;
end;


# Returns true if the lengths of all words in an interval [d, D].
TestWordLengths := function(gs, d, D)
  local g;
  for g in gs do
    if Length(g) < d or Length(g) > D then
      return false;    
    fi;
  od;
  return true;
end;


# Generates a random reduced set.
GenerateRandomReducedSet := function(F, m, d, D)
  local ws, reduced;
  repeat
    ws := GenerateRandomListOfWords(F, m, d, D);
    reduced := ReduceSet(ws);
  until Length(reduced) = m and TestWordLengths(reduced, d, D);
  return reduced;
end;


# Shares a secret.
ShareSecret := function(n, t, words)
  local i, j, as, rs;
  as := Combinations([1..n], t - 1);
  rs := [];
  for i in [1..n] do
    Add(rs, []);
    for j in [1..Length(as)] do
      if not i in as[j] then
        Add(rs[i], words[j]);
      fi;
    od;
  od;
  return rs;
end;


# Returns the secret sum.
FindSecret := function(parts)
  local v, vs, us;
  vs := [];
  for v in parts do
    UniteSet(vs, v);
  od;
  us := ReduceSet(vs);
  return GetSecretSum(us);
end;
