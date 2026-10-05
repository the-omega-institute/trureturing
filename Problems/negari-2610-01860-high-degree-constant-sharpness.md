---
slug: negari-2610-01860-high-degree-constant-sharpness
bibkey: negari2026gaussianapproximation
doi: 10.48550/arXiv.2610.01860
url: https://arxiv.org/abs/2610.01860v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result
---

# Sharpness of the high-degree fermionic Gaussian constants

## Problem

A.-R. Negari, F. Salek, Z. Zimborás, A. Harrow, P. Hayden and J. Eisert,
*Approximation theorems for fermionic Gaussian states*, arXiv:2610.01860v1
(2026), Section VI, printed page 26, state:

> It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy--Schwarz, and only the operator-norm normalization of the interactions.

The source estimates are Theorem III.1, equation (44), and Theorem III.5,
equation (79), both with prefactor `sqrt(2m/D)`. The formal claim asks whether,
for every `m >= 1`, every `c < 1` and every degree cutoff `D0`, a finite
regular graph and admissible quadratic fermionic edge interactions attain the
energy value `sqrt(2m/D)` and have a finite positive inverse temperature whose
free-energy gap is larger than `c * sqrt(2m/D)`.

## Motivation

Issue [#13091](https://github.com/the-omega-institute/trureturing/issues/13091)
preregistered this Tier 1 named question, its quantified statement and the
literature screen before implementation. The motivation declaration is the
frozen Lean result
`D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result`.

## Gap

The source explicitly leaves optimality of the two downstream constants open.
The bounded search recorded in issue #13091 found only arXiv:2610.01860v1 and
found no settlement in the searched title, identifier, author, sharpness,
MathDB, formal-conjecture and repository scopes. The citation indexes and
MathDB endpoint were incomplete, so worldwide absence and priority remain
ASSUMED-UNVERIFIED.

## Route

For `q = 2m`, choose a power-of-two conference order `s` with
`2m(s - 1) >= D0` and use the Cartesian product of `q` complete graphs on
`s` vertices. The recursive skew conference matrices satisfy
`C^2 = -(s - 1) I` and provide real, self-adjoint, norm-one quadratic edge
interactions. The coordinate Hamiltonian is a normalized sum over all edges.

The coordinate skew identity gives a flat Clifford spectrum. A joint minus
sign projector is a trace-one physical ground density, so the physical ground
energy is `-sqrt(2m/D)`. Site parity conjugation changes the sign of each edge
term and therefore makes every physical product energy zero; the energy gap is the stated bound.
The kernel-verified route (`D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound`) proves an entropy-budget
lower bound. The maximally mixed marginals and the exact log-cosh formula are derived below and are not kernel-verified. Fibre parity makes
each one-site Gibbs marginal maximally mixed. The Gibbs product entropy is bounded by the Fock dimension, and a finite
positive beta chosen from `c` gives the strict free-gap inequality.

## Falsifier

The settlement would fail if the conference matrices did not have the claimed
skew-square and off-diagonal properties, if the coordinate graph were not
regular with the stated degree and edge count, if the joint-sign projection
were not a physical trace-one ground density, or if site parity did not force
all physical product energies to zero. It would also fail if the Gibbs-marginal
and entropy estimates did not yield a finite positive beta for every `c < 1`.
The result does not assert equality at finite beta, sharpness at every degree,
or sharpness at a fixed beta independent of system size.

## Evidence

The Lean module is
`D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.lean`. Its public
settlement is `result : claim`; the definitions expose the source claim and
the coordinate witness family. The result and its supporting modules compile
with the pinned toolchain. The axiom closure of every public declaration is
contained in `{propext, Classical.choice, Quot.sound}`. The Scribe result node carries
`OpenProblemResolutionClaim` with `ResolutionKind.Proved` for this dossier.

## Triage

`theorem`; Tier 1 external named open problem, preregistered in issue #13091
before implementation. Resolution is `Proved` and the module admission basis
is `open-problem-resolution (#13091; Proved)`. The coordinate conference
family, joint ground sector, parity cancellation and finite-beta entropy bound
are the live proof content. Information-escape registration is paused under
CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module:** the energy constant is attained uniformly for
  every positive mode count and every degree cutoff by the coordinate family;
  the physical product energy is zero and the ground energy is exactly the
  negative bound.
- **Proved in this module:** for every real `c < 1`, a finite positive inverse
  temperature gives a free-energy gap strictly larger than `c` times the same
  bound. Thus the prefactor one cannot be lowered uniformly in degree in either
  estimate.
- **Kernel-verified:** `D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound` proves the entropy-budget
  lower bound used by the settlement. The maximally mixed marginals and the
  exact log-cosh formula are derived below and are not kernel-verified.
- **Derived, not kernel-verified:** for the witness family, let `L = m|V|`
  and `α = 1/(L√(s−1))`. Then
  `Z = (2 cosh(βα))^L` and
  `F_gap(β) = (L/β) log cosh(β/(L√(s−1)))`. Since
  `e^x/2 < cosh x < e^x` for `x > 0`,
  `a − L log 2/β < F_gap(β) < a` with
  `a = 1/√(s−1) = √(2m/D)`. Hence `F_gap → a` as `β → ∞`, and
  `F_gap < a` at every finite `β > 0`, so the bound is not attained on this
  family.
- **Derived:** the two source parity phases differ for odd mode count. `main.tex:429–433`
  gives `P = i^m ∏γ` and `main.tex:439–445` gives `(−i)^m ∏γ`; they
  differ by `(−1)^m`. For one mode, `c = [[0,1],[0,0]]`, so `γ₁γ₂ = diag(−i,i)`: `iγ₁γ₂ = diag(1,−1)` agrees with `exp(iπc†c)`, while `−iγ₁γ₂` is its negative.
  Both give the same commutation and physical-state conditions, so the settled
  statement is unaffected. The Lean carrier's parity is `e^{iπN̂}` by the
  definition; its occupation-basis form is `FockMajoranaCarrier.numberParity_eq_diagonal`.
- **Proved boundary:** the argument extends to all power-of-two conference
  orders and their unbounded degree sequence. It does not prove equality at
  finite beta or at every integer degree.
- **Open:** sharpness at a degree outside the power-of-two conference sequence
  requires a construction or obstruction for that degree; sharpness at one beta
  independent of system size requires a uniform beta bound across the witness
  family; finite-beta equality requires a state attaining the entropy-budget
  bound together with equality in the displayed logarithmic squeeze; and a
  pointwise-in-degree optimality theorem requires a construction or obstruction
  for every sufficiently large integer degree. These are distinct missing
  inputs, and none is supplied by the current Lean result.
- **Source consequence:** any later use of either published estimate may retain
  prefactor one as a uniform sharp constant, while claims of finite-beta
  equality or pointwise-in-degree optimality require the missing inputs above.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and queries recorded in issue
#13091 and the cited Library note; it does not establish exhaustive absence of
later or unindexed work. The semantic identification between the source's
fermionic conventions and the Lean carrier is supported by the formal source
and mirror but remains a fidelity obligation separate from kernel truth.
