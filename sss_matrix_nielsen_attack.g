# This is an implementation of the attack on the secret sharing scheme based on Nielsen transformations. 
#
# Alexander Ushakov, Matvei Kotov, 2015.

LoadPackage("singular");

# Returns a random rational number in [from, to].
GetRandomRational := function(from, to, DENOMS)
  local d, n;
  d := Random(DENOMS);
  n := Random(from * d, to * d);
  return n/d;
end;


# Returns a random matrix in the form [[-r, -1 + r^2], [1, - r]], where r in [from, to].
GetRandomSLMatrix := function(from, to, DENOMS)
  local r;
  r := GetRandomRational(from, to, DENOMS);
  return [[-r, -1 + r^2], [1, -r]];
end;


# Transforms a word to the corresponding matrix: w(x1, ..., xn) -> w(M1, ..., Mn). 
# ms = [M1, ..., Mn], invms = [M1^-1, ..., Mn^-1].
TransformWordToMatrix := function(w, ms, invms)
    if Length(w) = 0 then
      return [[1, 0], [0, 1]];
    fi;
    return Product(List([1..NumberSyllables(w)], function(i)
        local g, e;
        g := GeneratorSyllable(w, i);
        e := ExponentSyllable(w, i);
        if e >= 0 then
          return ms[g]^e;
        else
          return invms[g]^-e;
        fi;
      end));
end;


# Returns the sum S = \sum_{i = 1}^m {1 / |tr(M_i)|}.
GetSecretSum := function(ms)
  return Sum(ms, m -> 1 / AbsoluteValue(Trace(m)));
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


# Returns the number of letters from xs in a word w.
LengthXS := function(w, xs)
  local i, l;
  l := 0;
  for i in [1..Length(w)] do
    if Subword(w, i, i) in xs or Subword(w, i, i)^-1 in xs then
      l := l + 1;
    fi;
  od;
  return l;   
end; 


# ws in F[xs, as]. Returns ws' s.t. SUM|w'|_xs <= SUM|w|_xs.
ReduceWS := function(ws, xs, as)
  local TryReduceWords, epsilon, u, us, lt, lv, i, j, w, k, t, v, best_delta, best_epsilon, best_u, best_t, best_v;

  TryReduceWords := function(us, i, t)
    local j;
    for j in [1..Length(us)] do
      if i <> j and PositionWord(us[j], t, 1) <> fail then
        return j;
      fi;
    od;
    return fail;
  end; 

  us := ShallowCopy(ws);  
  while true do
    best_delta := 0;
    for i in [1..Length(us)] do
      for epsilon in [-1, 1] do
        for j in [0..Length(us[i]) - 1] do
          for k in [j + 1..Length(us[i])] do
            w := us[i]^epsilon;
            t := Subword(w, j + 1, k); 
            v := Subword(w, 1, j)^-1 * Subword(w, k + 1, Length(us[i]))^-1;
            lt := LengthXS(t, xs); 
            lv := LengthXS(v, xs);
            if lt - lv > best_delta then
              u := TryReduceWords(us, i, t);
              if u <> fail then
                best_delta := lt - lv; 
                best_u := u; 
                best_t := t; 
                best_v := v;
              fi;
            fi;
          od;
        od;
      od;
    od;
    if best_delta = 0 then
      break;
    fi;
    us[best_u] := SubstitutedWord(us[best_u], best_t, 1, best_v); 
  od;
  return us;   
end;


ApplyShortSubs := function(ws, xs)
  local i, j, ts, zs, length, l, best_length, subs;
  zs := ShallowCopy(ws);
  subs := ShallowCopy(xs);
  best_length := Sum(List(zs, z -> Length(z)));
  while true do
    l := best_length;
    for i in [1..Length(xs)] do
      for j in [1..Length(xs)] do
        if i <> j then
          ts := List(zs, w -> EliminatedWord(w, xs[i], xs[i]*xs[j]));
          length := Sum(List(ts, z -> Length(z)));
          if length < best_length then
            best_length := length;
            zs := ts;
            subs[i] := subs[i] * subs[j]^-1;
          fi;
          ts := List(zs, w -> EliminatedWord(w, xs[i], xs[j]*xs[i]));
          length := Sum(List(ts, z -> Length(z)));
          if length < best_length then
            best_length := length;
            zs := ts;
            subs[i] := subs[j]^-1 * subs[i];
          fi;
          ts := List(zs, w -> EliminatedWord(w, xs[i], xs[i]*xs[j]^-1));
          length := Sum(List(ts, z -> Length(z)));
          if length < best_length then
            best_length := length;
            zs := ts;
            subs[i] := subs[i] * subs[j];
          fi;
          ts := List(zs, w -> EliminatedWord(w, xs[i], xs[j]^-1*xs[i]));
          length := Sum(List(ts, z -> Length(z)));
          if length < best_length then
            best_length := length;
            zs := ts;
            subs[i] := subs[j] * subs[i];
          fi;
        fi;
      od;
    od;
    if l = best_length then
      break;
    fi;
  od;
  return [subs, zs];
end;


# Transforms a number to the nearest rational number with the denominator in DENOMS.
ToRat := function(r, DENOMS)
  local d, t, s, best, bestdist;
  bestdist := r;
  for d in DENOMS do
    t := Int(Round(r * d * 1.)) / d;
    s := AbsoluteValue(t - r);
    if s < bestdist then
      best := t;
      bestdist := s;
    fi;
  od;
  return best;
end;


# Splits a word w to two words u and v s. t. |u| and |v| approx. equal |w|/2.
SplitWord := function(w, xs)
  local left, right, l, i;
  l := LengthXS(w, xs);
  i := 1;
  while LengthXS(Subword(w, 1, i), xs) < l / 2 do
    i := i + 1;
  od;
  left := Subword(w, 1, i);
  right := Subword(w, i + 1, Length(w));
  return [left, right];
end;


# Generates algebraic equations by matrix equation L = R
GenerateEquationsByLR := function(L, R)
  return [L[1][1] - R[1][1], L[1][2] - R[1][2], L[2][1] - R[2][1], L[2][2] - R[2][2]];
end;


# Genetates algebraic equations by equation w = e.
GenerateEquationsByWMs := function(w, Ns, invNs, Xs, invXs, xs)
  local uv, L, R;
  uv := SplitWord(w, xs);
  L := TransformWordToMatrix(uv[1], Concatenation(Xs, Ns), Concatenation(invXs, invNs));
  R := TransformWordToMatrix(uv[2]^-1, Concatenation(Xs, Ns), Concatenation(invXs, invNs));
  return GenerateEquationsByLR(L, R);
end;


SolveSystem := function(R, fs)
  local I, S;
  StartSingular();
  I := Ideal(R, Filtered(fs, f -> (f <> 0)));
  Exec("date");
  SetInfoLevel( InfoSingular, 3 ); 
  SingularLibrary("modstd.lib");
  SingularInterface("ideal I = modStd", [I], "");;
  SingularInterface("print(I[1]); print", "\"\"", "");;
  SingularInterface("print(I[2]); print", "\"\"", "");;
  SingularInterface("print(I[3]); print", "\"\"", "");;
  SingularInterface("print(I[4]); print", "\"\"", "");;
  SingularLibrary("solve.lib");
  SingularInterface("def AC = solve(I, 50, 0); print", "\"\"", "");;
  SingularInterface("setring AC; print", "\"\"", "");;
  S := SingularInterface("SOL; print", "\"\"", "list");;
  if Length(S) = 0 then
    return fail;
  fi;
  return S[1];
  CloseSingular();
end;

# Applies the attack.
ApplyAttack := function(F, n, ws, Ns, DENOMS)
  local subs, reducesws, as, R, pxs, xs, Xs, invNs, invXs, fs, I, S;

  R := PolynomialRing(Rationals, n : old);;
  pxs := IndeterminatesOfPolynomialRing(R);;

  xs := GeneratorsOfGroup(F){[1..n]};
  as := GeneratorsOfGroup(F){[n + 1..2*n]};

  invNs := List(Ns, N -> N^-1);

  Xs := List(pxs, px -> [[-px, -1 + px^2], [1, -px]]);
  invXs := List(pxs, px -> [[-px, 1 - px^2], [-1, -px]]);

  reducesws := ReduceWS(ListN(ws, as{[1..Length(ws)]}, function(w, a) return w*a^-1; end), xs, as);
  Print("Rd:", reducesws, "\n");
  reducesws := ApplyShortSubs(reducesws, xs);
  subs := reducesws[1];
  reducesws := reducesws[2];
  Print("Rd: ", reducesws, "\n");
  Print("Subs: ", subs, "\n");
  Print("Length ws: ", List(ws, w -> Length(w)), "\n");
  Print("Length rws: ", List(reducesws, w -> LengthXS(w, xs)), "\n");

  fs := Concatenation(List(reducesws, w -> GenerateEquationsByWMs(w, Ns, invNs, Xs, invXs, xs)));
  S := SolveSystem(R, fs);
  if Length(S) < n then
    return fail;
  fi;
  Print("Step 2");
  fs := Concatenation(List(ListN(subs, as{[1..Length(subs)]}, function(s, a) return s*a^-1; end), 
      w -> GenerateEquationsByWMs(w, S, List(S, s -> S^-1), Xs, invXs, xs)));
  S := SolveSystem(R, fs);
  if Length(S) < n then
    return fail;
  fi;
  return List(List(S, r -> ToRat(r, DENOMS)), r -> [[-r, -1 + r^2], [1, -r]]);
end;


# Test suite.
TestAttack := function(n, numOfTransforms)
  local Ms, invMs, i, DENOMS, F, A, us, Ns;

  F := FreeGroup(2 * n);

  # Possible denominators.
  DENOMS := [1..10];
  Ms := [];
  for i in [1..n] do
    Add(Ms, GetRandomSLMatrix(2 + i * 6, 5 + i * 6, DENOMS));
  od;  
  invMs := List(Ms, M -> M^-1); 
 
  us := ApplyRandomNielsenTransform(GeneratorsOfGroup(F){[1..n]}, numOfTransforms);
 
  Ns := List(us, u -> TransformWordToMatrix(u, Ms, invMs));

  Exec("date");
  A := ApplyAttack(F, n, us{[1..n-1]}, Ns, DENOMS);
  Exec("date");
  if A = fail then
    Print("FAIL\b");
  else
    if GetSecretSum(A) = GetSecretSum(Ms) then
      Print("OK\n");
    else
      Print("ERROR\n");
    fi;
  fi;
end;


# Example from the presentation.
TestAttackPr := function()
  local DENOMS, w1, w2, w3, F, A, M1, M2, M3, M4, us, N1, N2, N3, n;

  # Possible denominators.
  DENOMS := [1..10];

  n := 4;

  F := FreeGroup(2 * n);

  M1 := [[-2, 3], [1, -2]];
  M2 := [[-11/2, 117/4], [1, -11/2]];
  M3 := [[-10, 99], [1, -10]];
  M4 := [[-27/2, 725/4], [1, -27/2]];

  N1 := [[665425964279561878285821966811999177576276873/524288, -7140686598826606434552873787092386902748912043/1048576],
    [-2853270865183114296500013723359238554463352269/4194304, 30618452124714071336436267510627140548281900727/8388608]];;
  N2 := [[-1200231440541196696282428781047241429934830789229664300138373164373042322250637795602133/562949953421312,
    32317202130608840477510994802545162192543628980433478881354803514076560407470703930775509/1125899906842624],
    [111872268320131798128475609529813765961140972007517948822483093672004026471348520653931/281474976710656,
    -3012251292535035397614756767324041716696327418018486874077592680911203058443053924346731/562949953421312]];;
  N3 := [[-17274718784827820759613292350041627442169501421072947928184581776518095089429309/35184372088832,
    465135772869752741329431664014905210283617966614809684008911971064867155893869629/70368744177664],
    [-1609794077912542401777325081836598849358539831783165811585876116215648997682179/17592186044416,
    43345007343832398092074993797699781408476274086506590850498428957455449152060163/35184372088832]];;

  w1 := F.1 * F.2 * (F.4 * F.1 * F.2)^3 * (F.3 * F.4^2 * F.2^-1 * F.1^-1 * F.2^-1)^4 * F.4 * F.1 * F.2;
  w2 := F.2 * F.1 * F.2 * F.4^-2 * F.3^-1 * ((F.2^-1 * F.1^-1 * F.4^-1)^3 * F.2^-1 * F.1^-1)^5 * F.4 * F.1 * F.2 * F.3 * F.4^2;
  w3 := ((F.2^-1 * F.1^-1 * F.4^-1)^3 * F.2^-1 * F.1^-1)^5 * F.4 * F.1 * F.2 * F.3 * F.4^2;

  us := [w1, w2, w3];
  Exec("date");
  A := ApplyAttack(F, n, [us[1], us[2], us[3]], [N1, N2, N3], DENOMS);
  Exec("date");
  if A = fail then
    Print("FAIL\b");
  else
    if GetSecretSum(A) = GetSecretSum([M1, M2, M3, M4]) then
      Print("OK\n");
    else
      Print("ERROR\n");
    fi;
  fi;
end;
