import D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Ring.Hom.InjSurj

open _root_.D5.S1.Dynamics.Symbolic.KhetanLaurent
open _root_.D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra
open _root_.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer

noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State R := Configuration R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := Configuration R
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ h => h) (fun e => Empty.elim e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ _ h x => if x = 0 then h 0 else h (1, 0))
    (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law s := ∀ {R : Type u} [inst : CommRing R] [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (v : Lattice) (hv : v ≠ 0)
    (q : Polynomial R) (hq : q ≠ 0)
    (hann : coefficientAct (linePolynomial v q) h = 0),
      Periodic (s.readout () R h)

private theorem bad_law : ¬ arena.{u}.Law bad := by
  intro hb
  letI : IsDomain (ULift.{u} ℤ) := Function.Injective.isDomain
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) ULift.ringEquiv.injective
  let h : Configuration (ULift.{u} ℤ) := fun x => if x.1 % 2 = 0 then 0 else 1
  have hh : FiniteRange h := by
    apply ((Set.finite_singleton (1 : ULift.{u} ℤ)).insert 0).subset
    rintro y ⟨x, rfl⟩
    dsimp [h]
    split <;> simp
  have hq : (Polynomial.X ^ 2 - 1 : Polynomial (ULift.{u} ℤ)) ≠ 0 := by
    intro hz
    have he := congrArg (fun p : Polynomial (ULift.{u} ℤ) => p.coeff 2) hz
    norm_num [Polynomial.coeff_one] at he
  have hann : coefficientAct
      (linePolynomial (1, 0) (Polynomial.X ^ 2 - 1)) h = 0 := by
    have hpoly : linePolynomial (R := ULift.{u} ℤ) (1, 0) (Polynomial.X ^ 2 - 1) =
        AddMonoidAlgebra.single (2, 0) 1 - 1 := by
      simp [linePolynomial, AddMonoidAlgebra.single_pow]
    rw [hpoly]
    have hsub : coefficientAct (AddMonoidAlgebra.single (2, 0) 1 - 1) h =
        coefficientAct (AddMonoidAlgebra.single (2, 0) 1) h - h := by
      simp [coefficientAct]
    rw [hsub, coefficientAct_single]
    funext x
    simp [shift, h, Int.add_emod]
  have hp := @hb (ULift.{u} ℤ) inferInstance inferInstance
    h hh (1, 0) (by simp) (Polynomial.X ^ 2 - 1) hq hann
  obtain ⟨v, hv, hperiod⟩ := hp
  have he := hperiod 0
  have hz : (1 : ULift.{u} ℤ) = 0 := by
    simpa [bad, realize, hv, h] using he
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} ℤ, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have h := congrArg (fun h => (h (0 : Lattice)).down) he
  norm_num [actual, realize] at h

def recurrenceEvidence : Registration arena.{u}
    (∀ {R : Type u} [CommRing R] [IsDomain R]
      (h : Configuration R) (hh : FiniteRange h) (v : Lattice) (hv : v ≠ 0)
      (q : Polynomial R) (hq : q ≠ 0)
      (hann : coefficientAct (linePolynomial v q) h = 0), Periodic h) where
  actual := realize signature (fun _ _ h => h) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@nonzero_line_annihilator_periodic.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def nonzero_line_annihilator_periodic_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.recurrence_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer.recurrenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨recurrenceEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ h => h) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
