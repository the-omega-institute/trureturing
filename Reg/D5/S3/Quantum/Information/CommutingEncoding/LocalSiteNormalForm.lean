import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of local commutation and the local unitary normal form. -/

namespace Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm

open _root_.D5.S3.Quantum.Information.CommutingEncodingReflectionClass
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Signs

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ A B => A * B) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
    (∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) →
    ∀ a b j, R.readout () () (U a j) (U b j) = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ _ => one_mem _) (fun _ _ => rfl) (0 : Fin (2 ^ 1)) 0 0
  rcases hb with hb | hb <;>
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hb <;>
    norm_num [rejected, realize, Matrix.one_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa [actual, realize] using congrFun h (1 : Matrix (Fin 2) (Fin 2) ℂ)
  exact zero_ne_one he

def source_registration : Registration arena (type_of% @local_commutation_signs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_commutation_signs, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@local_commutation_signs) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm.Signs.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm.Signs.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A B => A * B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Signs

namespace Form
universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Submonoid (Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ G V => V ∈ G) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : Type u} (B : κ → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
    (∀ a b, B a * B b = B b * B a ∨ B a * B b = -(B b * B a)) →
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
      R.readout () () (Matrix.unitaryGroup (Fin 2) ℂ) V ∧
      ((∀ a, ∃ d : Fin 2 → ℂ, V * B a * Vᴴ = diagonal d) ∨
        (∃ (c : κ → ℂ) (p : κ → Pauli), (∀ a, star (c a) * c a = 1) ∧
          (∀ a, V * B a * Vᴴ = c a • pauliMatrix (p a))))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨V, hV, _⟩ := h (fun _ : PUnit.{u + 1} => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ => one_mem _) (fun _ _ => Or.inl rfl)
  exact hV

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⊥, ⊤, ?_⟩
  intro h
  have hz : (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      (⊥ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)) :=
    (congrFun h 0).mpr (Submonoid.mem_top 0)
  exact zero_ne_one (Submonoid.mem_bot.mp hz)

def source_registration : Registration arena.{u} (type_of% @local_site_normal_form.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_site_normal_form.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@local_site_normal_form.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm.Form.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm.Form.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ G V => V ∈ G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Form
end
end Reg.D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm
