import D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The selected real-part observation retains the whole large-prime telescope. -/

noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} (hp : p.Prime) (hlarge : 5000000 ≤ p),
    (23 / 50 : ℝ) * p ≤ R.readout () ()
      (_root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p 1)
private theorem rejected_law (p : ℕ) (hp : p.Prime) (hlarge : 5000000 ≤ p) :
    ¬ arena.Law rejected := by
  intro h
  have he := h hp hlarge
  change (23 / 50 : ℝ) * p ≤ -1 at he
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family (p : ℕ) (hp : p.Prime) (hlarge : 5000000 ≤ p) :
    Registration arena (type_of% @principal_smoothedCharacterSum_large) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@principal_smoothedCharacterSum_large, rejected, rejected_law p hp hlarge⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (rejected_law p hp hlarge)
  dependence := dependence
def audit (p : ℕ) (hp : p.Prime) (hlarge : 5000000 ≤ p) :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@principal_smoothedCharacterSum_large) (Realization signature) Unit Unit where
  unitName := ((`D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower).str
    "principal_smoothedCharacterSum_large").str "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family p hp hlarge⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower
