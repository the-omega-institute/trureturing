---
bibkey: fermat2026jacobilift
authors: trureturing research continuation
year: 2026
title: Finite-extension Jacobi lift for Fermat character sums
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: The repository theorem neg_jacobiSum_norm_lift gives the negative Jacobi-sum compatibility under finite-field norm and trace pullback; extension-field point counts and zeta factorization remain future targets.
strata_touched:
  - D5/S3/CharacterSums/Fermat/JacobiNormLift
license: repository-original
triage: anchor
---

# Finite-extension Jacobi lift

This note records the research direction attached to `D5/S3/CharacterSums/Fermat/JacobiNormLift`.

The repository already contains two relevant ingredients:

- `D5/S3/CharacterSums/Fermat/CharacterPointCount` counts the actual affine and projective Fermat subtypes over one finite field and proves the Weil bound;
- `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift` proves the Langlands-normalized Gauss-sum lift under norm and trace pullback.

The new theorem `neg_jacobiSum_norm_lift` supplies the missing compatibility between them:

$$-J_K(\chi\circ N,\phi\circ N)=(-J_k(\chi,\phi))^{[K:k]}.$$

The sign is part of the normalization. In ordinary Jacobi-sum notation this is equivalent to `J_K = (-1)^{r-1} J_k^r`; dropping the sign would be false for even extension degree.

The theorem is a formalization bridge, not a claim to have solved an open problem. The next target is to substitute this lift into the existing projective Fermat count and obtain one base-field spectral family governing all finite extension counts. A later capstone would derive the corresponding formal zeta-function factorization. Neither the all-extension count nor the zeta factorization is asserted here.
