# This is a test of the attack on the secret sharing scheme based on Nielsen transformations from 
# A. Moldenhauer, G. Rosenberger "Criptogrphic protocols based on Nielsen transformations", Section 4. 
#
# Matvei Kotov, Alexander Ushakov, 2015.

Read("sss_nielsen_attack.g");

us := GenerateRandomReducedSet(F, m);

sharedSecret := ShareSecret(n, t, ApplyRandomNielsenTransform(us, 10));

secret := FindSecret(sharedSecret{[2..Length(sharedSecret)]});

Display(secret);

GetPossibleSecrets(sharedSecret[1], 5);
