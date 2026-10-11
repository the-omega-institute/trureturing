import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.PolynomialPowerRanks
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.PolynomialPowerRanks

namespace Reg.D5.S3.Quantum.SpinChains.PolynomialPowerRanks

universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {ι : Type v} {σ : Type w}
    [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ K)) (x0 : σ → K) (H : ℕ)
    (_hnil : A.map (MvPolynomial.eval x0) ^ H = 0)
    (_hbound : ∀ (x : σ → K) (r : ℕ),
      (A.map (MvPolynomial.eval x) ^ r).rank ≤
        (A.map (MvPolynomial.eval x0) ^ r).rank),
    ∃ P : MvPolynomial σ K, MvPolynomial.eval x0 P = 1 ∧
      ∀ (x : σ → K), MvPolynomial.eval x P ≠ 0 → ∀ r : ℕ,
        R.readout () () (A.map (MvPolynomial.eval x) ^ r).rank
          (A.map (MvPolynomial.eval x0) ^ r).rank

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro law
  let x0 : ULift.{w} Empty → ULift.{u} ℚ := fun e => nomatch e.down
  obtain ⟨P, hP, h⟩ := law (K := ULift.{u} ℚ) (ι := ULift.{v} Empty)
    (0 : Matrix (ULift.{v} Empty) (ULift.{v} Empty)
      (MvPolynomial (ULift.{w} Empty) (ULift.{u} ℚ))) x0 1
    (by simp) (by intro x r; simp)
  exact h x0 (by rw [hP]; exact one_ne_zero) 0

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have h := congrFun eq 0
  change (0 = 0) = (1 = (0 : ℕ)) at h
  exact Nat.one_ne_zero (h.mp rfl)

def family : Registration arena.{u,v,w}
    (type_of% @exists_polynomial_power_rank_certificate.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_polynomial_power_rank_certificate.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@exists_polynomial_power_rank_certificate.{u,v,w})
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.PolynomialPowerRanks.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.PolynomialPowerRanks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.PolynomialPowerRanks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.SpinChains.PolynomialPowerRanks
