---
bibkey: chensun2024doublecharacters
authors: "Deyi Chen and Zhi-Wei Sun"
year: 2024
title: "On determinants involving (j+k/p) plus or minus (j-k/p)"
doi: 10.48550/arXiv.2409.08213
url: https://arxiv.org/html/2409.08213v4#S1.E11
claim: "Conjecture 1.1(1.11) gives all four mod8 branches modulo16 for the inclusive double Legendre sum d_p, including the actual imaginary quadratic ideal class number in the p=3 mod4 branches."
strata_touched:
  - D5/S3/Arith/CharacterSums/ChenSunOriginal
  - D5/S3/Arith/CharacterSums/ChenSunModSixteen
  - D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter
license: citation-only
triage: anchor
---
<!-- GID: D5/L/CharacterSums/chensun2024doublecharacters -->
# The full double-character congruence modulo sixteen

## Verified locator

DOI: `10.48550/arXiv.2409.08213`.
URL: https://arxiv.org/html/2409.08213v4#S1.E11.
The verified scope is arXiv:2409.08213v4, Conjecture 1.1, equation (1.11),
with the inclusive double sum defined in equation (1.8). This locator binds
all four modulo-eight branches, including the actual imaginary quadratic
class number; it does not assert a later-literature priority result.

The source is arXiv:2409.08213v4, 1 April 2025, Conjecture 1.1,
equation (1.11), with the inclusive double sum defined in (1.8).
For every prime p>3 and n=(p-1)/2 it predicts, modulo16,

- p=1 mod8: d_p = 4(1-(-1)^((p-1)/8));
- p=5 mod8: d_p = -2;
- p=3 mod8: d_p = p+1-(-1)^((h-1)/2)h;
- p=7 mod8: d_p = 2-(-1)^((h-1)/2)h.

Here d_p is the sum over 1<=j,k<=n of the Legendre symbol of j^2+jk.
The h in the last two branches is the class number of Q(sqrt(-p)),
with fundamental discriminant -p. It is not defined by a finite sum.
The authors say immediately afterwards that they cannot confirm Conjecture 1.1;
their Theorem 1.3 proves a congruence modulo4. This describes that version's
state, rather than all subsequent literature.

The finite proof being formalized uses the existing repository shifted
quadratic-character sum, a restricted Gram identity, integral prefix vectors,
and factorial-product parity. Its two intermediate conclusions are
`d_p = -2m^2 (mod16)` for p=4m+1 and
`2d_p = c^2+4m^2-3 (mod32)` for p=4m+3, where c is the lower-half character sum.
These intermediate statements are not separate solved-original credits.

The formal class-number route proves enough for all branches without choosing
the sign of the quadratic Gauss sum. It constructs the genuine maximal order,
discriminant, signature, regulator and torsion units; proves all rational-prime
Euler factors and convergent zeta factorization; compares the residue at one;
and squares the primitive self-dual odd-character functional equation.
The result is c^2=(2-chi(2))^2 h^2 and oddness of the actual h. The L(0)
weighted-sum supplier is the existing licensed Yao Xu/cadamcat port,
`CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum`, documented in
`Library/ArithUnits/yaoxu2026catalanmoment.md`. This adaptation does not
claim new authorship of that upstream proof.

The independently approved ordinary source instead invokes the classical
exact Dirichlet formula W=-p h. The consulted ordinary reference is Jerry
Shurman, The Ideal Class Number Formula for an Imaginary Quadratic Field,
Proposition14.3 pp27-31 and Theorem16.1 p36; Definition8.2 p17 and the extra-unit
exceptions pp4-5 identify the actual class number. This PDF is an ordinary
reference, not a Lean axiom. The original's [BS] means Borevich-Shafarevich,
Number Theory, Theorem3 p346; it does not mean Berndt-Sun.

Bounded screening on 4 November2026 inspected v4, relevant author follow-ups,
Legendre-symbol/congruence searches and the source manifest preserved with the
research task. No exact resolution was located in that scope. The solved
Li-Wu prime-power determinant and Li-Yan Jacobi determinant targets were
excluded. Completeness of the literature screen, novelty and priority remain
unverified. Ordinary proof approval is separate from native Lean, independent
formal review, CI merge, publication and official acceptance. OriginalKPI is0
until complete reviewed delivery.

Four-slot escape registration is unfinished for the newly authored theorem
family, tracked in https://github.com/the-omega-institute/trureturing/issues/26321.
The source-specific realization, equivalence, variation, sensitivity and
observational-dependence proofs are not certified. No declared_validated status
is claimed. This audit debt is separate from native mathematical proof.
