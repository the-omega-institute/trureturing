import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.AffineJacobiCorrelation
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset
open _root_.D5.S3.CharacterSums.AffineJacobiCorrelation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.AffineJacobiCorrelation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ b => corr b) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (b m p r A L : ℕ),
    (0 ≤ corr b m p p A L ∧ corr b m p p A L ≤ (L : ℤ)) ∧
    (b % 4 = 3 → 4 ∣ m → p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      m.Coprime p → m.Coprime r →
      V.readout () () b m p r A (p*r) = 0 ∧ |corr b m p r A L| ≤ (L % (p*r) : ℕ))

private theorem constant_fails : ¬ arena.Law constantOne := by
  intro h
  have bad := ((h 3 4 3 5 0 0).2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).1
  exact (by decide : (1 : ℤ) ≠ 0) bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 3, 7, ?_⟩
  change corr 3 ≠ corr 7
  intro he
  have h := congrFun (congrFun (congrFun (congrFun (congrFun he 4) 3) 1) 0) 1
  have hz : jacobiSym 3 3 = 0 := jacobiSym.eq_zero_iff.2 (by decide)
  have h7 : jacobiSym 3 7 ≠ 0 := fun h => (jacobiSym.eq_zero_iff_not_coprime.mp h) (by decide)
  apply h7
  simpa [corr, hz, jacobiSym.one_left] using h.symm

def family : Registration arena (type_of% @affine_jacobi_correlation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_jacobi_correlation, constantOne, constant_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constant_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_jacobi_correlation) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.AffineJacobiCorrelation.affine_jacobi_correlation
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.AffineJacobiCorrelation "family"
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
    (fun _ _ b => corr b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.AffineJacobiCorrelation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn",
        "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.AffineJacobiCorrelation
