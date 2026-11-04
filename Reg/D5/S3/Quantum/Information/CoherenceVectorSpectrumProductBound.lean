import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the coherence-vector and spectral product lower bound. -/

namespace Reg.D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound

open _root_.D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
open _root_.D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
  (coherenceVector IsDecomposition)
open _root_.D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState)
open _root_.D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation (Majorizes)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the order relation applied to the two sides of the product bound. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Every dimension, state and majorization hypothesis remains in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (hd : 1 ≤ d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (_hρ : IsState ρ) (ν : Fin d → ℝ) (_hν : IsMajorizationUpperBound ρ ν),
    R.readout () () (1 / (d : ℝ)) (ν ⟨0, hd⟩ * maxEigenvalue ρ)

private theorem one_state : IsState (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  exact ⟨Matrix.PosSemidef.one, by simp⟩

private theorem one_upper_bound :
    IsMajorizationUpperBound (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j _
    exact le_rfl
  · intro i
    norm_num
  · simp
  · intro u hu
    obtain ⟨k, p, ψ, hdec, rfl⟩ := hu
    have hv (j : Fin k) (i : Fin 1) :
        decreasingRearrangement (coherenceVector (ψ j)) i = 1 := by
      change Complex.normSq
        (ψ j (Tuple.sort (α := ℝᵒᵈ) (coherenceVector (ψ j)) i)) = 1
      rw [show Tuple.sort (α := ℝᵒᵈ) (coherenceVector (ψ j)) i =
        (0 : Fin 1) from Subsingleton.elim _ _]
      simpa only [Fin.sum_univ_one] using hdec.2.2.1 j
    have huone : (fun i : Fin 1 =>
        ∑ j, p j * decreasingRearrangement (coherenceVector (ψ j)) i) =
        (fun _ => 1) := by
      funext i
      simpa only [hv, mul_one] using hdec.2.1
    rw [huone]
    change Majorizes (List.ofFn (fun _ : Fin 1 => (1 : ℝ)))
      (List.ofFn (fun _ : Fin 1 => (1 : ℝ)))
    exact ⟨fun _ _ _ => le_rfl, rfl⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 1 one_state (fun _ => 1) one_upper_bound

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have hzero : (0 : ℝ) ≤ 0 := le_rfl
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp he hzero)

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.CoherenceVectorSpectrumProductBound
