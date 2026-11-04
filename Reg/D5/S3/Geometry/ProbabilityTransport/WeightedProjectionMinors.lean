import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors

/-! Source-bound real comparison for the exact orthonormal minor theorem. -/

noncomputable section
open scoped BigOperators
open _root_.AlternatingArrayContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors

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
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, ∀ (x y z : EuclideanSpace ℝ (Fin n)),
    Orthonormal ℝ ![x,y,z] → ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, A i j = A j i) → (∀ i j, 0 < A i j) →
      R.readout () ()
        (∑ i, ∑ j, if i < j then A i j * Matrix.det !![x i,x j; y i,y j] ^ 2 else 0)
        (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
          max (A i j) (max (A i k) (A j k)) *
            Matrix.det !![x i,x j,x k; y i,y j,y k; z i,z j,z k] ^ 2 else 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hb : Orthonormal ℝ ![b 0,b 1,b 2] := by
    have he : (![b 0,b 1,b 2] : Fin 3 → EuclideanSpace ℝ (Fin 3)) = b := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact b.orthonormal
  exact h (b 0) (b 1) (b 2) hb (fun _ _ => 1) (by intros; rfl) (by intros; norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at bad
  have : (1 : ℝ) ≤ 0 := Eq.mp bad (le_refl 0)
  norm_num at this

def family : Registration arena (type_of% (@weighted_minors)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_minors, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_minors) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors.unit
  realizationName := `Reg.D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors
