import D5.S3.Quantum.Routing.HannRouterProfiles
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.Routing.HannRouterProfiles

open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.HannRouterProfiles
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, Qutrit × Router (n + 1))
    (fun p => Address (p.1 + 1)) (fun _ => Qutrit)

def actual : Realization signature :=
  realize signature (fun _ p a => loadedLabel (p.1 + 1) a p.2.1 p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Qutrit.zero) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (q : Router (n + 1) → ℝ),
    (∀ (a a' : Address (n + 1)) (bus bus' : Qutrit),
      (∀ v, q v < 1 → R.readout () ⟨n, bus, v⟩ a = loadedLabel (n + 1) a' bus' v) →
        a = a') ↔ ∀ u : Address n, q (deepest n u) < 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h 0 (fun _ => 0)).mpr (by intro u; norm_num)
  have he := hs (true, ()) (false, ()) Qutrit.wait Qutrit.wait (by
    intro v hv
    cases v with
    | none => rfl
    | some v => exact v.2.elim)
  cases he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Qutrit.wait, none⟩, (false, ()), (true, ()), ?_⟩
  intro h
  change Qutrit.zero = Qutrit.one at h
  cases h

def family : Registration arena (type_of% profile_separation_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨profile_separation_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    profile_separation_iff (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannRouterProfiles.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => loadedLabel (p.1 + 1) a p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannRouterProfiles
    definition := none
    coordinates := #[0, 4, 6]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body", "body",
        "domain", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.Quantum.Routing.HannRouterProfiles
