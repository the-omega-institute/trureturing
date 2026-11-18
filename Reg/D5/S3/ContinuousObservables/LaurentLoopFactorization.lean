import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ContinuousObservables.LaurentLoopFactorization

/-! Source-domain registration of the complete ordered Laurent factorization theorem. -/

open LeanInformationAudit
open Matrix
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ContinuousObservables.LaurentLoopFactorization

noncomputable section

namespace Reg.D5.S3.ContinuousObservables.LaurentLoopFactorization

/-- Observe the ordered primitive factors over the original list carrier. -/
abbrev signature : Signature where
  Params := Unit
  State _ := List M₂
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Loop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature (fun _ _ Ps => Ps.map primitive) (fun a => nomatch a)
def rejected := realize signature (fun _ _ _ => [0]) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ Ps : List M₂, (∀ P ∈ Ps, RankOneProjector P) →
      InClass Ps.length (r.readout () () Ps).prod) ∧
    ∀ (n : ℕ) (C : ℤ →₀ M₂),
      (∀ j : ℤ, (n : ℤ) < |j| ∨ j % 2 ≠ (n : ℤ) % 2 → C j = 0) →
      (C n ≠ 0 ∨ C (-(n : ℤ)) ≠ 0) → CircleSU (ofCoefficients C) →
      ∃! r : M₂ × List M₂, Factorization n (ofCoefficients C) r

theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hc := (h.1 [] (by simp)).2 1 (by simp)
  have hz := hc.1
  change (evaluate (0 : Loop) 1)ᴴ * evaluate (0 : Loop) 1 = 1 at hz
  have he := congrArg (fun A : M₂ => A 0 0) hz
  simp [evaluate] at he

theorem actualDependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), [!![1, 0; 0, 0]], [!![0, 0; 0, 1]], ?_⟩
  intro h
  change [primitive !![1, 0; 0, 0]] = [primitive !![0, 0; 0, 1]] at h
  have hm := (List.cons.inj h).1
  have he := congrArg (fun F : Loop => (F 0 0).coeff 1) hm
  norm_num [primitive, constant, Matrix.smul_apply, smul_eq_mul,
    LaurentPolynomial.T_apply] at he

def family : Registration arena (type_of% haah_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨haah_factorization, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := actualDependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    haah_factorization (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ContinuousObservables.LaurentLoopFactorization.unit
  realizationName := `Reg.D5.S3.ContinuousObservables.LaurentLoopFactorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Ps => Ps.map primitive) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.LaurentLoopFactorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ContinuousObservables.LaurentLoopFactorization
