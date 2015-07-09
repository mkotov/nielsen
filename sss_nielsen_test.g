Read("sss_nielsen_attack.g");

us := GenerateRandomReducedSet(F, m);

sharedSecret := ShareSecret(n, t, ApplyRandomNielsenTransform(us, 10));

secret := FindSecret(sharedSecret{[2..Length(sharedSecret)]});

Display(secret);

GetPossibleSecrets(sharedSecret[1], 5);
