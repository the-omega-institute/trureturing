---
slug: ta-2025-problem-11-7-good-involution-bound-refutation
bibkey: ta2025goodinvolutions
doi: 10.48550/arXiv.2505.08090
url: https://arxiv.org/abs/2505.08090v5
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Groups/TaGoodInvolutionBoundRefutation.result
---

# Ta Problem 11.7: the good-involution bound need not be strict

## Problem

Lực Ta, *Good involutions of conjugation subquandles*, arXiv:2505.08090v5,
Problem 11.7 (printed page 27), asks:

> In the setting of Corollary 6.12, suppose that |Z(H)|, |X/H| ≥ 2 (so, in
> particular, Conj X is not connected). Is the upper bound on |Good(Conj X)|
> in Corollary 6.12 always strict?

Corollary 6.12 gives the bound
`|Good(Conj X)| <= min(|Aut(Conj X)|, |Z(H)|^(|X/H|))`.

## Motivation

The question asks whether the displayed upper bound is always a strict
inequality under the two lower bounds on the center and orbit count. A single
finite conjugation subquandle attaining the bound refutes that universal
strictness reading. Issue #9433 preregistered the verbatim question, its finite
group formal reading, and the literature check before implementation.

## Gap

The cited arXiv version presents Problem 11.7 as an open problem. The source,
its cited references, and the repository's bounded open-problem search did not
identify a prior settlement of this question. This bounded check does not
establish exhaustive publication coverage or priority.

## Route

Take `G = QuaternionGroup 2` and
`X = {QuaternionGroup.a 1, QuaternionGroup.a 3, QuaternionGroup.xa 0,
QuaternionGroup.xa 2}`, the subquandle `{±i, ±j}`. Its generated subgroup is
all of `Q8`, whose center has cardinality two. The two conjugation orbits are
`{a 1, a 3}` and `{xa 0, xa 2}`, so `orbitCount X = 2`. Kernel reduction gives
`Fintype.card (Good X h) = 4` and `Fintype.card (Aut X h) = 8`; hence the
right-hand bound is `min(8, 2^2) = 4`, attained rather than strict.

## Falsifier

The refutation would fail if the displayed finite subset were not closed under
conjugation, did not generate `Q8`, had a center or orbit count different from
two, or had either good-involution or automorphism cardinality different from
the certified values. Each condition is checked in the Lean proof.

## Evidence

`D5/S0/Certificates/Groups/TaGoodInvolutionBoundRefutation.result` is a
kernel-checked theorem of type `¬ claim`. The claim quantifies over finite
groups, finite subsets, closure proofs, and the two lower-bound hypotheses; the
finite witness therefore refutes the unrestricted question as formalized. The
result uses the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Triage

`theorem`; resolution `refuted` for the literal strictness question. The result
does not classify other subquandles, assert a corrected strictness theorem, or
make a claim about infinite cardinal arithmetic.

### What the settlement shows

- The two hypotheses `|Z(H)| >= 2` and `k(X) >= 2` do not force strictness
  of the minimum bound, even for finite groups. This is the universal assertion
  negated by the settling result.
  [proved: D5/S0/Certificates/Groups/TaGoodInvolutionBoundRefutation.result]

- For `X = {±i, ±j}`, conjugation fixes the conjugator's own pair and swaps
  the other pair. Multiplication by `-1` on either pair separately therefore
  commutes with every conjugation map, preserves that map, and squares to the
  identity. The four good involutions are exactly the identity, the swap
  `(i -i)`, the swap `(j -j)`, and their product. Thus all four independent
  orbitwise central choices occur; having two components introduces no
  compatibility loss in this witness. The eight automorphisms consist of the
  independent pair swaps and the possible exchange of the pairs. The center
  term, rather than the automorphism term, is attained:
  `4 = min(8, 2^2)`.
  [computed: python3, construct the Q8 multiplication table, compute closure/center/orbits, and test all 24 permutations against the Good and Aut identities; output (|H|, |Z(H)|, k, |Good|, |Aut|, |Z(H)|^k) = (8, 2, 2, 4, 8, 4)]

- A finite family separates equality from strictness. Let
  `D_(2m) = <r,s | r^m = 1, srs^-1 = r^-1, s^2 = 1>` and
  `Dic_(m/2) = <r,s | r^m = 1, srs^-1 = r^-1, s^2 = r^(m/2)>`,
  both of order `2m`, and take `X = {r^a s : 0 <= a < m}`. For each of
  `m = 4,6,8,10,12,14,16`, in both groups `H` is the whole group,
  `|Z(H)| = k = 2`, and the center term is four. In that order,
  `(|Good|, |Aut|) = (4,8), (2,12), (4,32), (2,40), (4,48), (2,84), (4,128)`.
  The tested cases divisible by four attain the bound: the central twist
  preserves each parity orbit, allowing independent choices. In the other
  tested cases it exchanges the two orbits, so the involution condition forces
  matching choices, leaving two good involutions and strict inequality.
  In particular, equality in `D_24` and `Dic_6` does not require a 2-group;
  their six-element orbits cannot be cosets of any subgroup of the two-element
  center. These are finite computations, not a claim for all even `m`.
  [computed: python3, build the presented group tables, enumerate bijections by propagation of the rack identities, and independently enumerate orbitwise central twists with the Good identities; output (m, |Good|, |Aut|, |Z(H)|^k) = (4,4,8,4), (6,2,12,4), (8,4,32,4), (10,2,40,4), (12,4,48,4), (14,2,84,4), (16,4,128,4) in each family]

- Equality also occurs with a larger center in a nonabelian group of order
  32. On `F_2^3 x F_2^2`, use the multiplication
  `(v,w)(a,b) = (v+a, w+b+f(v,a))`, where
  `f(v,a) = (v_1 a_2 + v_2 a_3, v_1 a_3 + v_2 a_3)` over `F_2`.
  Let `X` consist of `(e_i,w)` for the three standard basis vectors `e_i`
  and all four `w`. It generates the group, has center `{0} x F_2^2`, and
  has three four-element conjugation orbits. All `4^3` orbitwise central
  translations are good involutions, giving `64 = min(384, 4^3)`.
  Thus even restricting to nonabelian groups does not make center order two
  necessary for equality.
  [computed: python3, check the 32-element table's group laws and enumerate Good/Aut; independently test all 6*(4!)^3 = 82944 bijections between equal-conjugation-row classes for Aut; output (|H|, |Z(H)|, k, |Good|, |Aut|, |Z(H)|^k) = (32, 4, 3, 64, 384, 64)]

- The minimum's two terms require separate treatment. In additive `C_3`,
  `X = {1,2}` gives `(Good,Aut,|Z(H)|^k) = (2,2,9)`: equality can instead
  come from the automorphism term. In additive `C_4`, `X = {1,2}` is not
  inverse-closed but still gives `(2,2,16)`, attaining the minimum while
  remaining strictly below the center term. By contrast, the inverse-closed
  subset `{0,1,3}` gives `(4,6,64)` and strictness. Even having singleton
  orbits, each a coset of the trivial central subgroup, does not by itself
  force equality. For a nonabelian comparison, in `Q8 x C_3` the subset
  `{±i,±j} x {1}` generates the whole group and gives `(4,8,36)` with
  `|Z(H)| = 6`, `k = 2` and strictness.
  [computed: python3, construct these four finite group/subset tables and enumerate Good/Aut and generated-subgroup orbits; output (|H|, |Z(H)|, k, |Good|, |Aut|, |Z(H)|^k) = (3,3,2,2,2,9), (4,4,2,2,2,16), (4,4,3,4,6,64), (24,6,2,4,8,36)]

- The nearest general survivors to verify are Corollary 6.12's non-strict
  inequality and its separate strict *center-term* bound for subsets that
  are not inverse-closed. The result supplies no general kernel proof of
  either source assertion. A sharper question suggested by Theorem 6.7's
  orbitwise parametrization is whether, for `|Z(H)| >= 2`, equality with
  `|Z(H)|^k` is equivalent to `z O^-1 = O` for every `H`-orbit `O` and every
  `z in Z(H)`. Equality through a smaller automorphism term requires its own
  criterion. The tested dicyclic and dihedral cases also suggest strictness
  for the full range `m = 2 mod 4`; that unbounded statement is not certified
  by the finite list above. [open]

- The witness provides finite instances for Section 11's neighbouring
  classification questions. For this four-element quandle,
  `|Anti| = |Aut| = 8`, while the four good involutions have automorphism
  conjugacy-orbit sizes `1,1,2`: the identity, the simultaneous pair swap,
  and the two isomorphic single-pair swaps. These give three symmetric-quandle
  isomorphism types for this underlying quandle, a finite case of Problem
  11.5 alongside the counts relevant to Problems 11.1–11.3. Its two components
  and involutory conjugation maps supply no case in the connected,
  noninvolutory range of Conjectures 11.8–11.9. Passing to the entire group
  changes the bound: both `Conj Q8` and `Conj D8` have
  `(k,Good,Aut,|Z(H)|^k) = (5,16,96,32)`, hence strictness for those whole
  quandles despite the subquandle equality. None of these tested inequalities
  violates the non-strict Corollary 6.12.
  [computed: python3, test all 24 witness permutations for Anti, conjugate its Good maps by Aut, and enumerate the two whole-group quandles; output |Anti| = 8, Good conjugacy-orbit sizes = (1,1,2), k(X) = 2, all s_x^2 = id, and (|G|, |Z(G)|, k(G), |Good|, |Aut|, |Z(G)|^k) = (8,2,5,16,96,32) for each whole-group quandle]

- Problem 11.6 concerns whether `(n, |Z(G)|, k(G))` determines `Good(Conj G)`
  for the whole group. Equal counts for the two order-eight examples neither
  establish that assertion nor give a counterexample with identical triples
  and different counts. The broader classifications in Problems 11.1–11.3
  and 11.5, and the n-fold extension in Problem 11.4, likewise require
  conclusions beyond these finite instances. No general conclusion about
  those questions, or about Conjectures 11.8–11.9, follows from this settlement
  alone. [open]

## ASSUMED-UNVERIFIED

The correspondence between the paper's rack terminology and the finite Lean
encoding is a source-faithfulness judgment, not a kernel theorem. The
literature search was bounded to the cited version, its references, and the
recorded repository search surfaces; exhaustive coverage and publication
priority remain unverified.
