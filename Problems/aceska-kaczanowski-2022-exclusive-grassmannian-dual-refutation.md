---
slug: aceska-kaczanowski-2022-exclusive-grassmannian-dual-refutation
bibkey: aceska2022crossframe
doi: 10.1080/01630563.2022.2128818
url: https://arxiv.org/abs/2205.05613v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result
---

# An exclusive Grassmannian dual need not be canonical

## Problem

R. Aceska and M. Kaczanowski, *Cross-Frame Potential*, arXiv:2205.05613v3,
Section 4.2, Conjecture 42, p. 17:

> If a frame F for F^n forms an exclusive Grassmannian pair with one of its duals, then that dual must be the canonical dual frame of F.

Definition 1 requires k ≥ n vectors in an n-dimensional Hilbert space and
positive finite frame bounds. Definition 3 requires both dual reconstruction
identities. Definition 34 minimizes the maximum off-diagonal cross-Gramian
magnitude over all dual frames. The explanation in Section 4.2 says that an
exclusive pair has exactly one dual attaining this minimum. The canonical
dual is S⁻¹F for the frame operator S.

The exact real finite-family reading is:

```lean
∀ n k (F G : Fin k → EuclideanSpace ℝ (Fin n)), n ≤ k →
  IsFrame F → IsDualFrame F G →
  (∀ H, IsDualFrame F H → mu F G ≤ mu F H) →
  (∀ H, IsDualFrame F H → mu F H ≤ mu F G → H = G) →
  G = canonicalDual F
```

IsDualFrame records the first reconstruction identity. Over the reals,
its adjoint gives the second; reconstruction forces both finite families
to span the space, hence to be frames. A real counterexample refutes the
source's assertion for real or complex Hilbert spaces. Zero-based indexing
only relabels the finite families. The empty off-diagonal maximum is zero;
the counterexample has three vectors and a nonempty off-diagonal set.

## Motivation

Issue #12319 preregisters the verbatim conjecture, Tier 1 classification,
quantified reading, literature scope and the witness before Lean. The
settling declaration is result : ¬ claim. This is an external named
problem and uses deposit-uncovered without an atom or coverage edge.

## Gap

The source v3 retains Conjecture 42. The literature check in #12319 reports
no settlement in arXiv:2502.17760, 2601.08028 and 2609.14861, and zero
solutions in MathDB problem 354604. Those later-work and MathDB readings
are attributed to the search seat and orchestrator. They establish only
not-found-in-searched-scope; no priority or exhaustive literature claim
is made. The journal text has not been compared with the arXiv conjecture.

## Route

Let n = 1, k = 3, F = (3, 2, 1), and G = (1/5, 2/15, 2/15).
The frame energy is 14x² and dual reconstruction holds. Every dual H
satisfies 3h₀ + 2h₁ + h₂ = 1. Off-diagonal entries give
2|h₀| ≤ mu(F,H), 3|h₁| ≤ mu(F,H), and 3|h₂| ≤ mu(F,H).
Consequently 1 ≤ (5/2)mu(F,H), while mu(F,G) = 2/5.

If mu(F,H) ≤ 2/5, each coordinate has the upper bound attained by G.
The reconstruction identity forces equality in all three bounds. Thus G
is the unique minimizer over every dual, including duals with negative
coordinates. The frame operator is multiplication by 14. Its inverse
sends F₀ to 3/14, whereas G₀ = 1/5, so the minimizer is not canonical.

## Falsifier

Failure of the positive frame bound, reconstruction, the off-diagonal
maximum, the universal lower bound, uniqueness over all duals, or the
inverse-operator computation would invalidate the witness. The inline
proof verifies each of these and derives a contradiction from claim.
There is no restriction of the competitor family to positive duals.

## Evidence

The public surface contains IsFrame, IsDualFrame, mu, frameOperator,
canonicalDual, claim and the single theorem result. There are no private
named theorem or lemma wrappers. All intermediate arguments are inline.
The only import is Mathlib.Analysis.InnerProductSpace.PiL2; there are no
D5 prerequisite modules. The result uses propext, Classical.choice and
Quot.sound.

proof_shape: result: bind-only. Finite coordinate and maximum normalization,
projection of reconstruction, linear arithmetic, and the direct use of
Function.leftInverse_invFun supply the refutation. escape_witness: none.
admission_basis: open-problem-resolution (#12319; Refuted).
The certified-instance utility is the typed refutation of claim by result.
The Scribe theorem node carries OpenProblemResolutionClaim(Refuted) for
this dossier.

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1 external named conjecture. The dossier triage is theorem and its
Scribe resolution kind is Refuted. The mathematical target is Conjecture 42.

### What the settlement shows

- Proved in this module: exclusivity of the coherence-minimizing dual does
  not force canonicality, already for a one-dimensional real frame with
  three nonzero vectors. The unique minimizer balances the off-diagonal
  column bounds; the canonical inverse-operator prescription gives a
  different first coordinate.
- Proved in this module: this particular frame retains a dual attaining
  the minimum and that dual is unique. The failure concerns canonicality,
  not existence or uniqueness of the minimizer.
- Computed: the canonical dual is (3/14, 1/7, 1/14), with coherence 3/7;
  the minimizing coherence is 2/5, and the gap is 1/35. Exact rational
  reproduction command:

  ```sh
  python3 -c 'from fractions import Fraction as Q; F=[Q(3),Q(2),Q(1)]; G=[Q(1,5),Q(2,15),Q(2,15)]; C=[f/sum(x*x for x in F) for f in F]; mu=lambda H:max(abs(F[i]*H[j]) for i in range(3) for j in range(3) if i!=j); print(C,mu(C),mu(G),mu(C)-mu(G))'
  ```

- Open here: whether a version restricted to normalized vectors or to
  dimensions at least two has a canonicality conclusion. The witness
  does not satisfy a unit-norm restriction and uses dimension one.
- Open here: Conjecture 43 and any complete classification of exclusive
  pairs. This delivery asserts no separate settlement of that conjecture.
  The source's proved lemmas and examples are not negated by the refutation
  of Conjecture 42; any conclusion that assumes its universal canonicality
  assertion needs an independent argument or additional hypotheses.

## ASSUMED-UNVERIFIED

The journal version retains the arXiv conjecture: its full text was not
read. The arXiv v3 statement is the authoritative target of this delivery.
The later-work and MathDB literature readings are search-seat/orchestrator
reports, not new implementation-worker measurements. Absence of a result
in this scope does not establish priority or absence from all literature.
Model-family distinctness between codex-cli and ChatGPT Pro is
ASSUMED-UNVERIFIED; independent carrier assignments do not prove it.
