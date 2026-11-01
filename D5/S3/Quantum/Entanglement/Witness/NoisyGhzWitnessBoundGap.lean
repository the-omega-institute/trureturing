/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim; result=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result; claim=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim
   digest: The optimized GHZ witness bound is strictly below the convex roof. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The geometric GME measure and optimized witness bound of Xu et al.,
arXiv:2211.05563v1, Section "Estimating entanglement measures" and Appendix
"Multipartite states admitting Schmidt decomposition". -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

/-- Computational words for `n` parties of local dimension `d`. -/
def Word (n d : ℕ) := Fin n → Fin d

/-- Normalization of a pure-state amplitude vector. -/
def IsUnit {n d : ℕ} (ψ : Word n d → ℂ) : Prop := ∑ x, Complex.normSq (ψ x) = 1

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
def rankOne {n d : ℕ} (ψ : Word n d → ℂ) : Matrix (Word n d) (Word n d) ℂ :=
  vecMulVec ψ (star ψ)

/-- The normalized equal superposition of the constant computational words. -/
def ghz (n d : ℕ) : Word n d → ℂ := fun x =>
  if ∃ j : Fin d, ∀ i, x i = j then (Real.sqrt d : ℂ)⁻¹ else 0

/-- Unit pure states that factor across some nonempty proper bipartition. -/
def IsBiseparable {n d : ℕ} (φ : Word n d → ℂ) : Prop :=
  IsUnit φ ∧ ∃ a : Finset (Fin n), a.Nonempty ∧ aᶜ.Nonempty ∧
    ∃ u : (a → Fin d) → ℂ, ∃ v : (↥aᶜ → Fin d) → ℂ,
      ∀ x, φ x = u (fun i => x i) * v (fun i => x i)

/-- The source's sum over the orthogonal set `S` of distinct arrangements:
precisely the diagonal projector onto words with at most two distinct symbols. -/
def supportProjector (n d : ℕ) : Matrix (Word n d) (Word n d) ℂ :=
  diagonal fun x => if (Finset.univ.image x).card ≤ 2 then 1 else 0

/-- The optimized source witness `P/d − |GHZ⟩⟨GHZ|`. -/
def witnessOp (n d : ℕ) : Matrix (Word n d) (Word n d) ℂ :=
  (1 / (d : ℝ)) • supportProjector n d - rankOne (ghz n d)

/-- White noise mixed with the `n`-party `d`-dimensional GHZ state. -/
def noisyGhz (n d : ℕ) (p : ℝ) : Matrix (Word n d) (Word n d) ℂ :=
  (p / (d : ℝ) ^ n) • 1 + (1 - p) • rankOne (ghz n d)

/-- Real quadratic expectation of an operator. -/
def expectation {n d : ℕ} (a : Matrix (Word n d) (Word n d) ℂ)
    (ψ : Word n d → ℂ) : ℝ := (star ψ ⬝ᵥ a *ᵥ ψ).re

/-- Witness readout on the noisy GHZ state. -/
def witnessValue (n d : ℕ) (p : ℝ) : ℝ :=
  (trace (noisyGhz n d p * witnessOp n d)).re

/-- Pure-state geometric GME measure, optimized over all biseparable unit vectors. -/
def geometricMeasurePure {n d : ℕ} (ψ : Word n d → ℂ) : ℝ :=
  1 - sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)}

/-- The convex roof over arbitrary finite normalized pure-state ensembles. -/
def geometricMeasure {n d : ℕ} (ρ : Matrix (Word n d) (Word n d) ℂ) : ℝ :=
  sInf {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word n d → ℂ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnit (ψ i)) ∧
    ρ = ∑ i, p i • rankOne (ψ i) ∧ t = ∑ i, p i * geometricMeasurePure (ψ i)}

/-- The source's two pure-state optimizations defining the convex conjugate. -/
def hatE (n d : ℕ) (r : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ ψ φ, IsUnit ψ ∧ IsBiseparable φ ∧
    t = expectation (r • witnessOp n d + rankOne φ) ψ - 1}

/-- The optimized witness lower bound on geometric GME. -/
def epsilonO (n d : ℕ) (p : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ r : ℝ, t = r * witnessValue n d p - hatE n d r}

/-- The open equality question, for all party counts, dimensions, and noise probabilities. -/
def claim : Prop :=
  ∀ n d : ℕ, 3 ≤ n → 3 ≤ d → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    epsilonO n d p = geometricMeasure (noisyGhz n d p)

private def q : Matrix (Word 3 3) (Word 3 3) ℂ := 1 - supportProjector 3 3
private def b : Matrix (Word 3 3) (Word 3 3) ℂ :=
  -(2 / 3 : ℝ) • witnessOp 3 3 + (1 / 9 : ℝ) • q
private def dmat : Matrix (Word 3 3) (Word 3 3) ℂ :=
  (2 / 3 : ℝ) • rankOne (ghz 3 3) +
    (4 / 3 : ℝ) • (supportProjector 3 3 - rankOne (ghz 3 3)) + q
private def dinv : Matrix (Word 3 3) (Word 3 3) ℂ :=
  (3 / 2 : ℝ) • rankOne (ghz 3 3) +
    (3 / 4 : ℝ) • (supportProjector 3 3 - rankOne (ghz 3 3)) + q
private def testPsi : Word 3 3 → ℂ := fun x =>
  (if x = (fun _ => 0) then 4 else
    if x = (fun _ => 1) ∨ x = (fun _ => 2) then 1 else 0) / (Real.sqrt 18 : ℂ)
private def basis (x : Word 3 3) : Word 3 3 → ℂ := Pi.single x 1

private lemma cs {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by sorry

private lemma expectation_rank_one (φ ψ : Word 3 3 → ℂ) :
    expectation (rankOne φ) ψ = Complex.normSq (star φ ⬝ᵥ ψ) := by sorry

private lemma finite_ranks : trace (supportProjector 3 3) = 21 ∧ trace q = 6 := by sorry
private lemma ghz_unit : IsUnit (ghz 3 3) := by sorry
private lemma witness_value : witnessValue 3 3 (3 / 8) = -(1 / 3) := by sorry
private lemma basis_unit (x : Word 3 3) : IsUnit (basis x) := by sorry
private lemma zero_biseparable : IsBiseparable (basis (fun _ => 0)) := by sorry
private lemma test_unit : IsUnit testPsi := by sorry
private lemma test_expectation : expectation (witnessOp 3 3) testPsi = -(1 / 3) := by sorry
private lemma test_overlap : Complex.normSq (star (basis (fun _ => 0)) ⬝ᵥ testPsi) = 8 / 9 := by sorry

private lemma hat_bdd (r : ℝ) : BddAbove {t : ℝ | ∃ ψ φ : Word 3 3 → ℂ,
    IsUnit ψ ∧ IsBiseparable φ ∧
      t = expectation (r • witnessOp 3 3 + rankOne φ) ψ - 1} := by sorry

private lemma hat_lower (r : ℝ) : -r / 3 - 1 / 9 ≤ hatE 3 3 r := by sorry
private lemma epsilon_upper : epsilonO 3 3 (3 / 8) ≤ 1 / 9 := by sorry

private lemma biseparable_overlap (φ : Word 3 3 → ℂ) (hφ : IsBiseparable φ) :
    3 * expectation (rankOne (ghz 3 3)) φ ≤ expectation (supportProjector 3 3) φ := by sorry

private lemma inverse_bound (φ : Word 3 3 → ℂ) (hφ : IsBiseparable φ) :
    expectation dinv φ ≤ 1 := by sorry
private lemma d_positive : dmat.PosDef := by sorry
private lemma d_inverse : dmat * dinv = 1 := by sorry

private lemma weighted_cs (φ ψ : Word 3 3 → ℂ) :
    Complex.normSq (star φ ⬝ᵥ ψ) ≤ expectation dinv φ * expectation dmat ψ := by sorry

private lemma pure_lower (ψ : Word 3 3 → ℂ) (hψ : IsUnit ψ) :
    expectation b ψ - 1 / 9 ≤ geometricMeasurePure ψ := by sorry

private lemma ensemble_nonempty :
    {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word 3 3 → ℂ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnit (ψ i)) ∧
      noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOne (ψ i) ∧
      t = ∑ i, p i * geometricMeasurePure (ψ i)}.Nonempty := by sorry

private lemma average_lower (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word 3 3 → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnit (ψ i))
    (he : noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOne (ψ i)) :
    13 / 108 ≤ ∑ i, p i * geometricMeasurePure (ψ i) := by sorry

private lemma roof_lower : 13 / 108 ≤ geometricMeasure (noisyGhz 3 3 (3 / 8)) := by sorry

/-- At three parties and three levels, noise `3/8` gives a strict gap. -/
theorem result : ¬ claim := by
  intro h
  have he := h 3 3 (by norm_num) (by norm_num) (3 / 8) (by norm_num) (by norm_num)
  have hu := epsilon_upper
  have hl := roof_lower
  rw [he] at hu
  linarith

end D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap
