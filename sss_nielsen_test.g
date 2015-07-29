# This is a test of the attack on the secret sharing scheme based on Nielsen transformations. 
#
# Alexander Ushakov, Matvei Kotov, 2015.

Read("sss_nielsen_attack.g");

# Minimal size of u_i.
d := 5;

# Maximal size of u_i.
D := 8;

N := 15;

for i in [1..100] do
  us := GenerateRandomReducedSet(F, m, d, D);
  Print("us: ", us, "\n");
  Print("lengths of us: ", (List(us, u -> Length(u))), "\n");
  vs := ApplyRandomNielsenTransform(us, N);
  Print("vs: ", vs, "\n");
  Print("lengths of vs: ", (List(vs, v -> Length(v))), "\n");
  sharedSecret := ShareSecret(n, t, vs);
  secret := FindSecret(sharedSecret{[2..Length(sharedSecret)]});
  Print("secret: ", secret, "\n");
  startTime := Runtime();
  possible := GetPossibleSecrets(sharedSecret[1], d, D);
  endTime := Runtime();
  Print("count of possible secrets: ", Length(possible), "\n");
  Print("possible secrets: ", possible, "\n");
  Print("time (ms): ", endTime - startTime, "\n");
  if not secret in possible then
    Print("FAIL\n");
  else 
    Print("OK\n");
  fi;
od;
