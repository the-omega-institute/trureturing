---
bibkey: looijenga1997prym
authors: Eduard Looijenga
year: 1997
title: Prym representations of mapping class groups
doi: 10.1023/A:1004909416648
claim: Finite abelian cover homology gives independent arithmetic Prym representations on suitable finite-index mapping-class subgroups; this does not identify a prescribed quotient of the whole mapping-class group.
license: citation-only
triage: anchor
---

# The universal mod-two cover: independent blocks and global factorization

## Primary sources and exact reading scope

Eduard Looijenga, Geometriae Dedicata 64 (1997), 69-83.
https://research-portal.uu.nl/en/publications/prym-representations-of-mappings-class-groups/
https://doi.org/10.1023/A:1004909416648

The Utrecht bibliographic record and the author's annotated publication list
were inspected. The latter explicitly describes independence and almost
surjectivity of the Prym representations. The original fifteen-page proof
was not successfully retrieved in this increment. No new discovery of Prym
representations, their arithmeticity, or their qualitative independence is
claimed.
https://webspace.science.uu.nl/~looij101/annotated-publication-list.html

Philipp Bader, *Prym representations of the handlebody group*, Geometriae
Dedicata 218, 59 (2024), published March 29, 2024.
https://link.springer.com/article/10.1007/s10711-024-00911-5

The full primary publisher HTML was read, especially Section 2.2 on the
covering construction, lift ambiguity, deck-module homology, projectivization,
and its Theorem 1.5 quoting Looijenga's cyclic-cover image result. Section 2.1
also records the ordinary mapping-class symplectic surjection. Bader's main
handlebody result is not substituted for a theorem about the full mapping
class group. In the appended argument, square twists supported in a
complementary subsurface supply the odd-prime surjectivity directly; no
unsupported passage from finite index over the integers to every prime is
used.

Adam Klukowski, *Congruence subgroup property for nilpotent groups and
subsurface subgroups of Mapping Class Groups*, arXiv:2411.06867v2.
https://arxiv.org/html/2411.06867v2

Definition 3 and Conjecture 13 retain the finite characteristic quotient and
simple-curve orbit requirements. The new positive inputs are explicitly
constructed congruence subgroups, not arbitrary prescribed finite-index
subgroups. Thus they verify a concrete known-type family and do not solve
the general conjecture. Johnson-kernel facts and the same-quotient Torelli
surjectivity input remain those cited in the existing Klukowski Library
record and theory Sections 16-18.

Finite symplectic simplicity is a classical input: PSp(2n,q) is nonabelian
simple for n>=2 and odd q, including PSp(4,3). The rank-one exceptions of
PSL(2,q) and the even-field PSp(4,2) exception are not in the theorem's domain.
The primary Fong-Wong 1969 article's publisher extract explicitly confirms
the PSp(4,q), q odd, case; its full proof was not read here.
https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/characterization-of-the-finite-simple-groups-psp4-q-g2q-i/BB3D4102BB1B6EAF63FDD05AB059E1ED

## The actual new ordinary proof chain

The fixed cover is N2=ker(pi_g->H1(Sigma_g,F2)), with deck group S=(C2)^(2g).
For every odd prime l, form the genuine characteristic quotient
Q=pi_g/[N2,N2]N2^l. Its homology kernel splits into one 2g-dimensional trivial
block and 4^g-1 nontrivial 2g-2-dimensional sign blocks. Lift ambiguity is
removed projectively on each block, without falsely using the centerless-base
normalization from the preceding theory.

For a separating curve of type (h,g-h), the canonical lift is the product of
twists along all lifts of the curve. Its homology increment has exact rank
(4^h-1)(4^(g-h)-1) and square zero; the actual quotient OUTER order is l.
This is a formula for a specified canonical lift, not for every arbitrary
deck-modified lift.

The projective maps on the Johnson kernel are surjective onto
D=PSp(2g-2,Fl). Different sign characters have distinct kernels, witnessed
by the SAME genuine genus-one separating twists with different support.
The existing simple-subdirect argument yields the actual full joint image
D^(4^g-1). Full mapping classes permute the character blocks through
Sp(2g,F2), giving the explicit global congruence quotient
D^(4^g-1) semidirect Sp(2g,F2). The theory constructs a nonnormal subgroup
Gamma_chi,l of index (4^g-1)|D| and its exact normal core Delta_l. The inclusion
Delta_l<=Gamma_chi,l solves the orbit condition for every simple curve for
these particular inputs. These Gamma do not contain the Torelli group.

For any SAME epimorphism f:M_g->F to a nonabelian finite simple group,
factorization through Out(Q)'s actual image is equivalent to factorization
through ordinary homology modulo 2l. Normality and transitive permutation of
all independent simple blocks prevent selecting one Prym factor as a global
simple quotient. An elementary abelian two-group kernel and a precise
mod-2l argument account for the remaining ambiguity. This conclusion is
stronger than merely comparing abstract isomorphism types or image sizes.

The relative Frattini result from Section 30 removes all deeper prime-power
layers over N2. For finite joint families at different primes, the actual
joint group is a fiber product over the common ABELIAN deck group. The error
between joint innerness and separate innerness is a quotient of S^(t-1),
not assumed zero. A nonabelian simple target kills that two-group error.
Thus the same previously fixed nonhomological f, and hence the same genuine
simple-curve pair (Gamma,alpha), defeat this entire specified refinement
family. This does not exclude arbitrary finite characteristic surface
quotients or other base covers.

Finally, for a centerless base with trivial outer action, at primes not
dividing |S| the corrected homology representation has invariant isotypic
multiplicity spaces of dimensions (2g-2)dim(U_chi)+2 delta_(chi,1). A fixed
simple target factors through the full corrected image iff it factors
through one such actual block image. No successful nonabelian base, prime,
block or paired quantum generator packet is produced by this reduction.
Defining-characteristic natural representations cannot be substituted into
the stated cross-characteristic semisimple decomposition without new work.

## Verification, limits and bounded search

September 14, 2026: repository search for Prym returned no matching owner in
the indexed default branch. The actual PR head and current dev were read.
Primary searches included Prym/Johnson/finite-field combinations and the
current Conjecture 13 statement. No general solution was found; this is not
an exhaustive literature or priority certificate. The explicit ordinary
proofs combine classical topology, finite group theory and the existing
research deductions. No mathematical first-discovery claim is made.

Exact diagnostics actually run:

- 68886 ordered distinct nonzero character pairs in genera 2,3,4, verifying
  the symplectic-plane separation construction over F2.
- 28 genus/side cases in genera 2 through 8, checking the active-character
  count against the displayed rank formula.
- 2718 actual sign-character cellular-chain calculations over F3,F5,F7,
  using all nonzero characters and every standard separating type in
  genera 2,3,4. Fox derivatives of the actual relator and the actual
  partial-conjugation twist were used. Boundary compatibility, the
  2g-2-dimensional twisted H1, exact rank zero/one, and square-zero induced
  increment were checked. There were 2106 rank-one cases.

The genus-two diagnostics are only boundary checks of the rank calculation;
the full-product and global-simple-quotient theorems require g>=3. These
calculations do not enumerate the full mapping-class group, prove its image
surjectivity by computation, or evaluate the prescribed quantum quotient.
The group-image and factorization conclusions have separate ordinary proofs.

No Lean/lake or .NET executable is present. The three existing Lean/Scribe
pairs remain unchanged and uncompiled here. This increment adds no wrapper,
custom axiom, new frozen state, CI code or scratch diagnostic to the repo.
No independent expert/admission review or priority certification is claimed.
