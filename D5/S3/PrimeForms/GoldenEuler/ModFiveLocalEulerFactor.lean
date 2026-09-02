/- GID: D5/S3/PrimeForms/GoldenEuler/ModFiveLocalEulerFactor
   generality: I
   mirror-B: D5/B/S3/PrimeForms/GoldenEuler/ModFiveLocalEulerFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The mod-five local observer determinant splits into its even and odd channel factors. -/

import D5.S3.Observer.GoldenCoding.GoldenBranchObserverDecomposition

/- Library-search audit trail (2026-09-02):
   * Exact body-shape search found the frozen canonical operator family in
     `GoldenLocalBranchClassification`: it owns `evenBranchProjection`,
     `oddBranchProjection`, and `goldenLocalBranchOperator`. Those objects are
     imported and used directly rather than restated.
   * `GoldenBranchObserverDecomposition` owns the exact two-embedding carrier,
     its even and odd channels, their complementary decomposition, and the
     projection formulas. Its theorem is applied to derive the channel actions.
   * The local branch-classification theorem is also applied: its determinant
     clause supplies the quadratic-character determinant of the same operator.
     No D5 theorem combines these owners with the inverse determinant,
     `p ^ (-s)` specialization, and both restricted channel factors.
   * Pinned Mathlib supplies the two-by-two determinant/trace identities and
     totalized field inverse law. Other installed Lean packages have no exact
     mod-five observer determinant theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.GoldenEuler.ModFiveLocalEulerFactor

open D5.S3.Observer.GoldenCoding.GoldenBranchObserverDecomposition
open D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
open Matrix

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The canonical golden local branch operator has the generic inverse
determinant factorization and its `p ^ (-s)` specialization. The complementary
canonical even and odd channels carry the trivial and quadratic-character
actions, and their one-dimensional inverse determinants are respectively the
Riemann and quadratic Dirichlet local factors. -/
theorem mod_five_local_observer_determinant
    (p : Nat.Primes) (x s : Complex) :
    let chi : Complex := (legendreSym 5 p.1 : Complex)
    let localObserverOperator : Matrix (Fin 2) (Fin 2) Complex :=
      goldenLocalBranchOperator p.1
    let primeScale : Complex := (p.1 : Complex) ^ (-s)
    (Matrix.det (1 - x • localObserverOperator))⁻¹ =
        1 / ((1 - x) * (1 - chi * x)) ∧
      (Matrix.det (1 - primeScale • localObserverOperator))⁻¹ =
        (1 - primeScale)⁻¹ * (1 - chi * primeScale)⁻¹ ∧
      IsCompl evenChannel oddChannel ∧
      (∀ value ∈ evenChannel,
        localObserverOperator *ᵥ value = value) ∧
      ∀ value ∈ oddChannel,
        localObserverOperator *ᵥ value = chi • value := by
  classical
  dsimp only
  have operatorDeterminant :
      Matrix.det (goldenLocalBranchOperator p.1) =
        (legendreSym 5 p.1 : Complex) :=
    (golden_local_branch_classification p.1).1 p.2
  obtain ⟨_, _, evenProjectionFormula, oddProjectionFormula, _, _, _,
      complementaryChannels, evenConjugation, oddConjugation⟩ :=
    golden_branch_observer_decomposition
  have operatorTrace :
      Matrix.trace (goldenLocalBranchOperator p.1) =
        1 + (legendreSym 5 p.1 : Complex) := by
    simp [goldenLocalBranchOperator, evenBranchProjection, oddBranchProjection,
      bitFlip, Matrix.trace_fin_two]
  have determinantPencil (scale : Complex) :
      Matrix.det (1 - scale • goldenLocalBranchOperator p.1) =
        (1 - scale) *
          (1 - (legendreSym 5 p.1 : Complex) * scale) := by
    calc
      Matrix.det (1 - scale • goldenLocalBranchOperator p.1) =
          1 - scale * Matrix.trace (goldenLocalBranchOperator p.1) +
            scale ^ 2 * Matrix.det (goldenLocalBranchOperator p.1) := by
        rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
        simp
        ring
      _ = (1 - scale) *
          (1 - (legendreSym 5 p.1 : Complex) * scale) := by
        rw [operatorTrace, operatorDeterminant]
        ring
  constructor
  · rw [determinantPencil]
    simp only [one_div]
  constructor
  · rw [determinantPencil, _root_.mul_inv_rev]
    ring
  constructor
  · exact complementaryChannels
  constructor
  · intro value valueEven
    rw [goldenLocalBranchOperator, Matrix.add_mulVec, Matrix.smul_mulVec]
    change evenProjection value +
      (legendreSym 5 p.1 : Complex) • oddProjection value = value
    rw [evenProjectionFormula, oddProjectionFormula]
    simp [evenConjugation value valueEven]
    module
  · intro value valueOdd
    rw [goldenLocalBranchOperator, Matrix.add_mulVec, Matrix.smul_mulVec]
    change evenProjection value +
      (legendreSym 5 p.1 : Complex) • oddProjection value =
        (legendreSym 5 p.1 : Complex) • value
    rw [evenProjectionFormula, oddProjectionFormula]
    simp [oddConjugation value valueOdd]
    module

#print axioms mod_five_local_observer_determinant

end


end D5.S3.PrimeForms.GoldenEuler.ModFiveLocalEulerFactor
