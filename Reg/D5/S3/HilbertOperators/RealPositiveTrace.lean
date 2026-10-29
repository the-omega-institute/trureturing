import D5.S3.HilbertOperators.RealPositiveTrace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full-telescope intrinsic-trace observation. Raw source occurrence binding remains explicit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace Reg.D5.S3.HilbertOperators.RealPositiveTrace
open _root_.D5.S3.HilbertOperators.RealPositiveTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal InnerProductSpace

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {ι : Type u} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ (e : HilbertBasis ι ℝ E) (A : E →L[ℝ] E) (d : ι → ℝ),
    (∀ i, 0 ≤ d i) → (∀ x i, e.repr (A x) i = d i * e.repr x i) →
    A.IsPositive ∧ obs.readout () () (positiveTrace A) = ∑' i, ENNReal.ofReal (d i)

theorem actual_law : arena.{u,v}.Law actual := @positive_trace_diagonal.{u,v}

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let E := EuclideanSpace ℝ (ULift.{v} Empty)
  let e : HilbertBasis (ULift.{u} Empty) ℝ E :=
    HilbertBasis.mk (v := fun _ => (0 : E)) (by
      classical
      rw [orthonormal_iff_ite]
      intro i
      exact i.down.elim) (by
        intro x _
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx]
        exact zero_mem _)
  have ht := h e (0 : E →L[ℝ] E) (fun _ => 0) (fun _ => le_rfl)
    (by intro x i; exact i.down.elim)
  have hz : (⊤ : ℝ≥0∞) = 0 := by simpa [rejected,realize] using ht.2
  exact top_ne_zero hz

def familyRegistration : Registration arena.{u,v} (type_of% (@positive_trace_diagonal.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := actual_dependence

/-- Typed attempt; raw original occurrence selection is not supplied or validated. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_trace_diagonal.{u,v})
    (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.HilbertOperators.RealPositiveTrace.unit,
  realizationName := `Reg.D5.S3.HilbertOperators.RealPositiveTrace.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
end Reg.D5.S3.HilbertOperators.RealPositiveTrace
