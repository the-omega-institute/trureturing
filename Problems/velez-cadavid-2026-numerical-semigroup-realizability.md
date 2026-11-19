---
slug: velez-cadavid-2026-numerical-semigroup-realizability
bibkey: velezcaicedo2026reconstructing
doi: 10.48550/arXiv.2611.14316
url: https://arxiv.org/abs/2611.14316v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result
---

# Complete variable-maximum numerical-semigroup realizability

## Problem

The source's final discussion, located and attributed in
`Library/Semigroups/velezcaicedo2026reconstructing.md`, asks:

> Second, it would be useful to characterize intrinsically which numerical
> semigroups can arise in the form $\langle M,M-s,M+s:s\in S\rangle$ and which
> spectral data are necessary for their reconstruction.

The target is exactly the first realizability clause. For every additive
submonoid $T\subseteq\mathbb N$ with finite complement, there exist $M\in
\mathbb N$ and a finite set $S\subseteq\mathbb N$ such that
$M>0$, $S\ne\varnothing$, every $s\in S$ is positive, $\max S=M$,
$\gcd S=1$, and

$$T=\operatorname{closure}_{+}\bigl(\{M\}\cup\{M-s:s\in S\}\cup\{M+s:s\in S\}\bigr).$$

The order is $\forall T\,\exists M\,\exists S$. The full monoid
$T=\mathbb N$ is included. Natural subtraction agrees with the ordinary
nonnegative difference since $s\le M$. The generated monoid includes zero.

| Source condition | Lean counterpart in `NumericalSemigroupRealizability.result` |
| --- | --- |
| Any numerical semigroup | `T : AddSubmonoid ℕ`, `hT : (↑T : Set ℕ)ᶜ.Finite` |
| Existential maximum | `∃ (M : ℕ) (S : Finset ℕ)`, with `0 < M` |
| Finite nonempty positive jumps | `Finset ℕ`, `S.Nonempty`, `∀ s ∈ S, 0 < s` |
| Maximum equals M | `S.sup id = M` |
| Primitive jump set | `S.gcd id = 1` |
| Entire generated monoid equals T | `AddSubmonoid.closure ({M} ∪ (fun s => M-s) '' ↑S ∪ (fun s => M+s) '' ↑S) = T` |
| Full monoid allowed | No properness hypothesis on T |

## Motivation

The external Tier 1 target is preregistered in
[#29915](https://github.com/the-omega-institute/trureturing/issues/29915),
with its unchanged prospective event in
[the preregistration comment](https://github.com/the-omega-institute/trureturing/issues/29915#issuecomment-6846936600).
The additive subject placement follows the existing sumset and additive-monoid
neighbourhood; the motivating frozen declaration records a separate additive
problem resolution, not a proof dependency. The candidate settling declaration
is `D5/S3/Arith/Additive/NumericalSemigroupRealizability.result`.

## Gap

Finite generation alone does not state the required maximum, positivity and
gcd conditions. A conductor bound lets the construction add two consecutive
members of T and keep every plus generator in T. The complete theorem supplies
all clauses together for one S and one M. No mathematical gap remains in its
compiled statement. Independent source-fidelity, form and mirror assessment
and the subsequent freeze/publication checks are still required.

## Route

Choose a finite generating set H by `Nat.addSubmonoid_fg` and an upper bound
N for the complement. Put c=N+1, G=H∪{c,c+1}, M=max(G)+1, and
S={M}∪{M−a:a∈G}. Every a∈G belongs to T and lies below M. Consequently
S is nonempty, positive, and has maximum M. Its jumps M−c and M−(c+1)
are consecutive, so gcd(S)=1.

M and each M+s exceed N. Each M−s is zero or an element of G, giving one
closure inclusion. Each generator a∈H appears as M−(M−a), giving the
reverse inclusion. The proof uses no nonempty-complement or properness
assumption; it applies equally to T=ℕ.

## Falsifier

A missing positivity, maximum, coprimality or closure-equality clause, a fixed
M hidden in the quantifier order, or an excluded full monoid would defeat
this resolution claim. A verified prior solution defeats its resolution-novelty
claim. The compound sentence's spectral-data question is not part of the
claim, and its remaining openness is not a counterexample to realizability.

## Evidence

The sole public D5 declaration is the universal theorem `result`; its proof
uses eighteen local haves and no separate mathematical helper declarations.
The canonical Scribe uses a typed `FromAuthor` formula carrying every clause
and a typed Proved `OpenProblemResolutionClaim` for this dossier. The Lean
proof's axiom closure is restricted to `propext`, `Classical.choice`, and
`Quot.sound`. The classification is conservatively `proof_shape: bind-only`,
`admission_basis: open-problem-resolution`; no escape witness is claimed.
This is an arbitrary-semigroup existence result rather than a finite
enumeration, numerical reduction or certified finite instance (`utility: none`).

The mirrored `Reg/D5/S3/Arith/Additive/NumericalSemigroupRealizability.lean`
uses the enrolled `DependentFamily.realize` template. Its actual observation
is the entire generated additive submonoid as a function of M and S, not a
constant truth value or a finite surrogate. Its law retains the complete
original quantifiers, finite-complement premise, and all six conclusion
clauses. The source-equivalence bridge, actual positive law, whole-family
variation, sensitivity and observational dependence have Lean proofs.
The actual readout distinguishes S=∅ from S={1} at M=0; this establishes
nonconstancy of the observation family, without imposing M=0 on the positive
existential witnesses in the law. The continuation is explicitly unknown;
this asserts neither undecidability nor an inexhaustible residual.

## Triage

| Item | Result and boundary |
| --- | --- |
| Complete variable-M realizability clause | Proved in Lean: every numerical semigroup is realizable with one finite nonempty positive primitive S and its maximum M |
| Full monoid boundary | Included by the same universal theorem; no properness or nonempty-complement premise |
| Construction mechanism | Finite generation plus a conductor bound keeps every defect generator in T; two consecutive tail members enforce gcd one |
| Computed results | None: no finite search or numerical experiment supplies the universal conclusion |
| Prescribed fixed M | Unresolved; the theorem chooses M after T |
| Necessary spectral data for reconstruction | Unresolved; the other clause of the source sentence |
| Smaller families of congruence restrictions | Unresolved; the separate preceding source direction |
| Literature novelty | Suspected only in the inspected scope recorded by the Library note; not a global priority claim |
| Theorem status | The complete variable-maximum statement is proved in Lean; spectral reconstruction and prescribed-M classification remain unresolved |

## ASSUMED-UNVERIFIED

Absence of every earlier solution and completeness of the literature search
are `ASSUMED-UNVERIFIED`. MathDB candidate-specific status is unread, not a
mandatory unavailable-site gate. The source-to-Lean interpretation and
proof-shape classification await independent review. Fixed-M and both
inverse-spectral neighbours remain unresolved.
