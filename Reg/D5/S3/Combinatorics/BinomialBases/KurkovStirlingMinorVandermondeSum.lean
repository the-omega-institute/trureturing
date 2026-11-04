import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum

/-! Four-slot dependent-family reading of the complete Stirling-minor identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum

abbrev signature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ km n => B n km.1 km.2) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (n k m : ℕ), 1 ≤ m → R.readout () (k,m) n = sourceRHS n k m

private theorem source_bridge : claim ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual := result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 0 0 1 (by decide)
  have good := result 0 0 1 (by decide)
  change (0 : ℚ) = sourceRHS 0 0 1 at bad
  have hb : B 0 0 1 = 1 := Matrix.det_fin_zero
  rw [hb] at good
  linarith

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(1,1), 0, 1, ?_⟩
  change B 0 1 1 ≠ B 1 1 1
  change Matrix.det (Matrix.of (fun i j : Fin 1 =>
      (Nat.stirlingFirst (0+1+(i.val+1)) (0+(j.val+1)) : ℚ))) ≠
    Matrix.det (Matrix.of (fun i j : Fin 1 =>
      (Nat.stirlingFirst (1+1+(i.val+1)) (1+(j.val+1)) : ℚ)))
  rw [Matrix.det_fin_one, Matrix.det_fin_one]
  norm_num [Nat.stirlingFirst_succ_succ]

def familyRegistration : DependentFamily.Registration arena claim where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := .str ``result "__information_unit"
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization signature) from ⟨actual⟩)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ km n => B n km.1 km.2) (fun e => nomatch e))
  variation := .evidence ⟨familyRegistration.variation⟩ trivial
  sensitivity := .evidence ⟨familyRegistration.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum
    definition := some {
      owner := `D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum
      name := `D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum
