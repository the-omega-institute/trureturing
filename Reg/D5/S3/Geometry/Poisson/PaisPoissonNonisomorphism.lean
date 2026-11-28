import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism
import Reg.Support.SingleDependentReadout

/-! The signed second-sector bracket is the selected readout. Replacing the
negative sign by the positive sign makes the identity equivalence preserve
the resulting identical brackets, so this intervention changes the law. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism
open Omega.PaisPoisson
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => -s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n m : ℕ) (hn : Odd n) (hm : Odd m) (Ω : ℝ), Ω ≠ 0 →
    ¬ ∃ e : Paper n m ≃ₐ[ℝ] Paper n m,
      PreservesBracket e
        (paperPoisson n m hn.pos hm.pos Ω (R.readout () () 1)).bracket
        (paperPoisson n m hn.pos hm.pos Ω 1).bracket

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : Odd (1 : ℕ) := by decide
  apply h 1 1 h1 h1 1 (by norm_num)
  refine ⟨AlgEquiv.refl, ?_⟩
  intro f g
  rfl

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism.signed_second_sector
  realizationName := `Reg.D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => -s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism
