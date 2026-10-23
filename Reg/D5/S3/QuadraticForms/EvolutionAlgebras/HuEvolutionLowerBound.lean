import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound

/-- One dimension observation over all natural states; no complex domain is enumerated. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original dependent telescope is retained, including all multiplication and subspace hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d n : ℕ} (μ : Product d) (_hc : commutative μ) (hp : perfect μ)
    (W : Submodule ℂ (Coord d)) (hW : square μ W = ⊥)
    (he : hasEvolutionEmbedding μ n), d + Module.finrank ℂ W ≤ R.readout () () n


theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ, hL, hc, hp, hn, hs, hd⟩ := jordan_family 1 (by omega)
  have he : hasEvolutionEmbedding μ 3 := by
    obtain ⟨ν,f,hb,hf,hmul,hfirst,hsecond⟩ := hs
    exact ⟨ν,f,hb,hf,hmul⟩
  have hbot : square μ (⊥ : Submodule ℂ (Coord 2)) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    have hx0 : x = 0 := hx
    subst x
    simp
  have h0 := h μ hc hp.1 ⊥ hbot he
  change 2 + Module.finrank ℂ (⊥ : Submodule ℂ (Coord 2)) ≤ 0 at h0
  omega


def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨square_zero_embedding_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound.square_zero_embedding_lower_bound) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound.unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
    definition := none
    coordinates := #[1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
end
