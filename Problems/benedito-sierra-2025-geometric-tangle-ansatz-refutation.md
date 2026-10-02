---
slug: benedito-sierra-2025-geometric-tangle-ansatz-refutation
bibkey: benedito2025visualizing
doi: null
url: https://arxiv.org/abs/2505.23638v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.result
---

# A type-4c diagonal state refutes the geometric tangle ansatz

## Problem

A. Benedito and G. Sierra, *Visualizing Three-Qubit Entanglement*,
arXiv:2505.23638v2, p. 7, Eq. (15), state:

> “τ(r⃗) = 1 − |r⃗|²/3 − d(r⃗, V_line) · F(r⃗) where |ψ⟩ ∈ GHZ excluding type 5 and F(r⃗) ≥ 0.”

The canonical state is
`λ₀|000⟩ + λ₁ e^{iφ}|100⟩ + λ₂|101⟩ + λ₃|110⟩ + λ₄|111⟩`, with
`0 ≤ λⱼ ≤ 1`, `Σ λⱼ² = 1` and `0 ≤ φ ≤ π` (p. 3, Eqs. (3)–(4)).
The vector `r⃗ = (r_A,r_B,r_C)` contains the lengths of the three reduced
one-qubit Pauli vectors. `V_line = {(t,t,t)}` is the main diagonal in ℝ³,
and `d` is its Euclidean distance, defined as the infimum of distances to points on that line. The canonical three-tangle is
`τ(ψ) = 4|Hdet(t_ijk)| = 4λ₀²λ₄²` (p. 5, Eq. (10)).

Issue #11500 preregisters the existence of a nonnegative real function F
satisfying the equation for every normalized canonical GHZ state that is
not type 5. The formal `claim` retains exactly this state domain.
Type 5 means every λⱼ ≠ 0 and every Jₖ ≠ 0. The J invariants are the
Acín invariants cited by the paper, with μⱼ = λⱼ² and
Δ = |λ₁λ₄ exp(iφ) − λ₂λ₃|²:
J₁ = Δ, J₂ = μ₀μ₂, J₃ = μ₀μ₃, J₄ = μ₀μ₄ and
J₅ = μ₀(Δ + μ₂μ₃ − μ₁μ₄). Their canonical definitions are Eq. (23)
of arXiv:quant-ph/0003050, the paper's cited classification source.
The witness has λ₁ = 0, which excludes it from the full type-5 predicate
without evaluating any J invariant.

The complex tensor `amplitudes` gives all eight coefficients of the state.
`jointDensity` is its outer product, with entries
`t_ijk conjugate(t_i'j'k')`. `rhoA`, `rhoB` and `rhoC` are finite-sum
partial traces using the frozen `partialTraceLeft` and `partialTraceRight`.
The frozen `bloch` map extracts
`(2 Re ρ₀₁, −2 Im ρ₀₁, Re ρ₀₀ − Re ρ₁₁)`.
`blochLengths` takes the Euclidean lengths of these actual vectors.
`cayley` is the full complex hyperdeterminant quartic;
`tangle` is `4 ‖cayley (amplitudes ψ)‖`, with no coordinate shortcut
in the definition of the claim.

The source and the formal distance definition agree as follows:

| Source definition | Lean definition |
| --- | --- |
| “the distance from that point to the straight line spanned by the main diagonal is the length of the vector connecting it to a point on the line such that this vector is perpendicular to the line” (arXiv v2, Appendix B, before the displayed distance formula) | `V_line : Set (EuclideanSpace ℝ (Fin 3)) := Set.range (fun t : ℝ => WithLp.toLp 2 ![t,t,t])`; `euclideanVector r := WithLp.toLp 2 ![r.1,r.2.1,r.2.2]`; `distanceToDiagonal r := Metric.infDist (euclideanVector r) V_line` |

The vector embedding and the diagonal set both live in `EuclideanSpace ℝ (Fin 3)`.
The local distance step in `result` applies `Metric.infDist_zero_of_mem` with
range witness `t = 1/2`.

## Motivation

The declaration
`D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.result`
refutes the geometric ansatz with a normalized type-4c state whose three
Bloch lengths are equal. The diagonal distance vanishes, yet the proposed
leading term disagrees with the canonical tangle.

## Gap

The preregistration classifies this as a tier-1 conjecture announced in the
abstract of a 2025 quant-ph paper. Its literature readings are: arXiv v1 and
v2 with no withdrawal, Semantic Scholar citing-work count 0, and no matching
MathDB entry for “geometric tangle three qubit”, “Cayley hyperdeterminant
geometric ansatz” or “Benedito Sierra”. These are orchestrator-reported
readings in #11500. They establish `not-found-in-searched-scope`, with no
claim of exhaustive novelty or priority. The journal statement is unverified.

## Route

For `ψ = (|000⟩ + |101⟩ + |110⟩ + |111⟩)/2`, take
`(λ₀,λ₁,λ₂,λ₃,λ₄;φ) = (1/2,0,1/2,1/2,1/2;0)`.
The three Pauli vectors are `(0,0,−1/2)`, `(1/2,0,0)` and `(1/2,0,0)`.
Their lengths are `(1/2,1/2,1/2)`, with squared norm `3/4` and diagonal
distance zero. The ansatz demands `τ = 3/4`, while Eq. (10) gives `τ = 1/4`.
The proof instantiates the universal equation at this state and normalizes
the resulting contradictory equality. Nonnegativity of F is unused.

## Falsifier

The refutation depends on the source admitting type 4c, including equal
Bloch lengths, and on the printed canonical-tangle expression. An alternative
statement that excludes this state or imposes strictly positive diagonal
distance is a different problem. No continuity or boundedness assumption
on F repairs an equation whose distance coefficient is zero here.

## Evidence

The source note is `Library/QuantumStates/benedito2025visualizing.md`.

The canonical Lean source is
`D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.lean`.
Its sole explicitly authored public theorem is `result : ¬ claim`.
Its public definitions are `CanonicalState`, `isCanonical`, `amplitudes`,
`jointDensity`, `rhoA`, `rhoB`, `rhoC`, `blochVectors`, `blochLengths`,
`cayley`, `tangle`, `jInvariants`, `isGHZ`, `isType5`, `normSquared`,
`V_line`, `euclideanVector`, `distanceToDiagonal` and `claim`. No private theorem or lemma is added.
The general partial-trace coordinate identities and the canonical
hyperdeterminant/tangle identities are local `have`s used in `result`.
Lean verifies the refutation with `propext`, `Classical.choice` and
`Quot.sound`. The source imports the frozen modules
`PartialTraceMutualInformation` and `ActualPureQubitGeometry`.

The Scribe mirror displays each public definition's expression, including
all eight complex coefficients, the outer product, the partial traces,
the five J invariants, the full Cayley quartic, the literal tangle, the diagonal set,
the Euclidean embedding and the infimum distance.

## Triage

Tier 1; `theorem`; resolution `Refuted`; preregistration #11500.
`proof_shape: bind-only`; `escape_witness: none`;
`admission_basis: open-problem-resolution`.
The utility is `certified-instance` with `basis=refutes`, the closed `claim`,
and its designated `result`. 逃逸审计未完成 (CLAUDE.md §3.9 exception): the obstruction and missing evidence
are recorded in https://github.com/the-omega-institute/trureturing/issues/11500#issuecomment-5943413667. The current raw report has 6049 modules, including 383 `Reg.` modules; no faithful registration for this existential-function statement is delivered.

### What the settlement shows

- **Proved in this module:** the encoded existence claim is false. The
  type-4c witness satisfies normalization, the GHZ condition and the
  full type-5 exclusion. Its zero diagonal distance makes the unknown
  correction term vanish and forces the contradictory equality `1/4 = 3/4`.
- **Computed:** exact rational arithmetic gives unit normalization, Pauli
  vectors `(0,0,−1/2)`, `(1/2,0,0)`, `(1/2,0,0)`, squared Bloch lengths
  `(1/4,1/4,1/4)`, tangle `1/4` and diagonal leading term `3/4`.
  Command: `python3 -c 'from fractions import Fraction as Q; q=Q(1,2); a=(0,0,-q); b=c=(q,0,0); s=tuple(sum(x*x for x in v) for v in (a,b,c)); print(4*q*q,a,b,c,s,4*q**4,1-sum(s)/3)'`
  outputs `1`, the three Pauli vectors, squared Bloch lengths
  `(1/4,1/4,1/4)`, `1/4` and `3/4`.
- **Computed:** the type-2b control `|000⟩/2 + (√3/2)|111⟩` has the same
  Bloch lengths and tangle `3/4`, agreeing with the diagonal leading term.
  Command: `python3 -c 'from fractions import Fraction as Q; a,b=Q(1,4),Q(3,4); print((a-b)**2,4*a*b,1-(a-b)**2)'`
  outputs `1/4 3/4 3/4`. This control is not a theorem in this module.
- **Computed:** the weaker upper inequality holds at this witness: `1/4 ≤ 3/4`.
  Command: `python3 -c 'from fractions import Fraction as Q; print(Q(1,4) <= Q(3,4))'`
  outputs `True`. Its universal validity is open in this module.
- **Open:** a characterization of nongeneric GHZ states on the diagonal,
  a corrected expression away from the diagonal, and the additional
  invariant data needed to recover tangle from local Bloch lengths.
- **Open:** the source’s geometric-hyperdeterminant conclusion and applications
  of Eq. (15) to all nongeneric GHZ states require replacement arguments. The witness also contradicts the source's
  assertion that all type-4c states deviate from the diagonal; no separate
  theorem for that assertion is added. The source's independent canonical
  formula Eq. (10) is used here, and other independent results are not
  adjudicated by this refutation.

## ASSUMED-UNVERIFIED

The preregistration's journal-version comparison is seat-reported; this
module settles the arXiv v2 ansatz. External-source authentication, exhaustive
worldwide literature coverage and priority are outside Lean's kernel.
The J invariants define the source predicate; no independent classification
theorem for them is asserted. The matrix-to-coordinate and canonical
hyperdeterminant identities are verified inside `result`.
