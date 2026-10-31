import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.CommonPhasePolynomial
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.PhasePolynomial
open MvPolynomial

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.CommonPhasePolynomial
universe u

abbrev Parameters := Σ ι : Type u, Fintype ι

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := (p.1 ⊕ p.1) →₀ ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Poly p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ _ m => monomial m (1 : ℂ)) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ p _ => if h : Nonempty p.1 then X (.inl (Classical.choice h)) else 0)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] (m : (ι ⊕ ι) →₀ ℕ),
    holo m = anti m → R.readout () ⟨ι, fi⟩ m ∈ quadraticAlgebra (ι := ι)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let ι := ULift.{u} Unit
  have hx : (X (.inl (default : ι)) : Poly ι) ∈ quadraticAlgebra (ι := ι) := by
    simpa [rejected, realize, ι, holo, anti, Subsingleton.elim (Classical.choice (inferInstance : Nonempty ι)) (default : ι)]
      using h (ι := ι) 0 (by simp [holo, anti])
  have hb := (common_phase_polynomial_theorem (X (.inl (default : ι)) : Poly ι)).1.mp
    ((common_phase_polynomial_theorem _).2.mpr hx)
  have hc : (X (.inl (default : ι)) : Poly ι).coeff
      (Finsupp.single (.inl (default : ι)) 1) ≠ 0 := by simp [X]
  have hh := hb _ hc
  simp [holo, anti, Finsupp.single_apply] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} Unit
  refine ⟨⟨ι, inferInstance⟩, 0, Finsupp.single (.inl (default : ι)) 1, ?_⟩
  intro h
  have he := congrArg (fun p : Poly ι => p.coeff 0) h
  simpa [actual, realize, Finsupp.single_ne_zero] using he

def family : Registration arena.{u} (type_of% (@balanced_monomial_mem_quadratic_adjoin.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@balanced_monomial_mem_quadratic_adjoin, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration
    (@balanced_monomial_mem_quadratic_adjoin.{u}) (Realization signature.{u})
    (type_of% (@MvPolynomial.monomial)) Unit := {
  unitName := `D5.S3.Quantum.Algebra.PhasePolynomial.balanced_monomial_mem_quadratic_adjoin.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.CommonPhasePolynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => monomial m (1 : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@MvPolynomial.monomial)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.CommonPhasePolynomial
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Algebra.CommonPhasePolynomial
