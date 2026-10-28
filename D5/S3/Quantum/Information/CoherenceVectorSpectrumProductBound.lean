/- GID: D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CoherenceVectorSpectrumProductBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coherence majorization bounds and the largest eigenvalue have product at least 1/d. -/

import D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
import D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
import Mathlib.Data.Fin.Tuple.Sort

/-! The coherence set of Alvarez–Losada–Portesi–Bosyk, Eqs. (11)–(12), and Conjecture 5. -/

set_option autoImplicit false
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
  (coherenceVector IsDecomposition)
open D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState)
open D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation (Majorizes)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

noncomputable section
namespace D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound

/-- The decreasing rearrangement of a finite real vector. -/
def decreasingRearrangement {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  x ∘ Tuple.sort (α := ℝᵒᵈ) x

/-- The set in Eq. (11): averages of decreasing pure-state squared-amplitude vectors. -/
def coherenceSet {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Set (Fin d → ℝ) :=
  {u | ∃ k p ψ, IsDecomposition ρ k p ψ ∧
    u = fun i => ∑ j, p j * decreasingRearrangement (coherenceVector (ψ j)) i}

/-- A decreasing probability vector majorizing every member of the source coherence set. -/
def IsMajorizationUpperBound {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ν : Fin d → ℝ) : Prop :=
  Antitone ν ∧ (∀ i, 0 ≤ ν i) ∧ (∑ i, ν i) = 1 ∧
    ∀ u ∈ coherenceSet ρ,
      Majorizes (List.ofFn ν) (List.ofFn (decreasingRearrangement u))

/-- The largest Hermitian eigenvalue; the value on non-Hermitian matrices is immaterial. -/
def maxEigenvalue {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  if h : ρ.IsHermitian then sSup (Set.range h.eigenvalues) else 0

private lemma column_ensemble {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsState ρ) :
    ∃ (p : Fin d → ℝ) (ψ : Fin d → Fin d → ℂ),
      IsDecomposition ρ d p ψ ∧
      (∀ j, p j = (ρ j j).re) ∧
      ∀ i j, p j * Complex.normSq (ψ j i) = Complex.normSq (CFC.sqrt ρ i j) := by
  sorry

private lemma first_component_bound {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (ν : Fin d → ℝ)
    (hν : IsMajorizationUpperBound ρ ν)
    (p : Fin d → ℝ) (ψ : Fin d → Fin d → ℂ)
    (hdec : IsDecomposition ρ d p ψ)
    (hcol : ∀ i j, p j * Complex.normSq (ψ j i) = Complex.normSq (CFC.sqrt ρ i j)) :
    (∑ j, (CFC.sqrt ρ j j).re ^ 2) ≤ ν ⟨0, hd⟩ := by
  sorry

private lemma diagonal_cauchy_schwarz {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (CFC.sqrt ρ).trace.re ^ 2 ≤ (d : ℝ) * ∑ j, (CFC.sqrt ρ j j).re ^ 2 := by
  sorry

private lemma spectral_bound {d : ℕ} (hd : 1 ≤ d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsState ρ) :
    0 < maxEigenvalue ρ ∧ 1 / Real.sqrt (maxEigenvalue ρ) ≤ (CFC.sqrt ρ).trace.re := by
  sorry

private lemma assemble_bound (d : ℕ) (hd : 1 ≤ d) (v l t s : ℝ)
    (hl : 0 < l) (ht : 1 / Real.sqrt l ≤ t)
    (hcs : t ^ 2 ≤ (d : ℝ) * s) (hv : s ≤ v) : 1 / (d : ℝ) ≤ v * l := by
  sorry

/-- Every majorization upper bound of the source coherence set satisfies the product bound.
The supremum ν(ρ) of Eq. (12) is such an upper bound, so this implies Conjecture 5, Eq. (20),
without constructing the majorization-lattice supremum. -/
theorem result (d : ℕ) (hd : 1 ≤ d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : IsState ρ) (ν : Fin d → ℝ) (hν : IsMajorizationUpperBound ρ ν) :
    1 / (d : ℝ) ≤ ν ⟨0, hd⟩ * maxEigenvalue ρ := by
  obtain ⟨p, ψ, hdec, _, hcol⟩ := column_ensemble hd ρ hρ
  obtain ⟨hl, ht⟩ := spectral_bound hd ρ hρ
  exact assemble_bound d hd _ _ _ _ hl ht (diagonal_cauchy_schwarz ρ)
    (first_component_bound hd ρ ν hν p ψ hdec hcol)

end D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
