import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
import Reg.Support.DependentFamily

/-! The root assertion observes exact native evaluation as the real imaginary part varies. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open LeanInformationAudit

attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := Σ n : ℕ, SimpleGraph (Fin n)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p b => Polynomial.eval₂ (Int.castRingHom ℂ) (Complex.I * (b : ℂ))
      (independencePolynomial p.2 Finset.univ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (b : ℝ),
    Irrational b ∧ R.readout () ⟨n, G⟩ b = 0

private lemma partition_zero {α : Type} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) :
    partition G V (fun _ => (0 : ℂ)) = 1 := by
  induction V using Finset.induction_on with
  | empty => exact partition_empty G _
  | @insert a V ha ih =>
      have h := partition_delete G (insert a V) a (by simp) (fun _ => (0 : ℂ))
      simpa [Finset.erase_insert ha, ih] using h

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨n, G, b, _, h⟩
  change (1 : ℂ) = 0 at h
  exact one_ne_zero h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨n, G, b, _, hroot⟩ :=
    _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.result
  refine ⟨⟨n, G⟩, b, 0, ?_⟩
  intro h
  change Polynomial.eval₂ (Int.castRingHom ℂ) (Complex.I * (b : ℂ))
      (independencePolynomial G Finset.univ) =
    Polynomial.eval₂ (Int.castRingHom ℂ) (Complex.I * ((0 : ℝ) : ℂ))
      (independencePolynomial G Finset.univ) at h
  rw [hroot] at h
  simp only [Complex.ofReal_zero, mul_zero, independencePolynomial_eval, partition_zero] at h
  exact zero_ne_one h

def family : Registration arena
    (type_of% _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def resultRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.result
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms resultRegistration

abbrev polynomialSignature : Signature where
  Params := Unit
  State _ := Polynomial ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def factor : Polynomial ℤ :=
  (1 + 2 * Polynomial.X ^ 2) * (1 + 128 * Polynomial.X + 128 * Polynomial.X ^ 2)

def polynomialActual : Realization polynomialSignature :=
  realize polynomialSignature (fun _ _ p => decide (p = factor)) (fun e => nomatch e)

def polynomialRejected : Realization polynomialSignature :=
  realize polynomialSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev polynomialArena : Arena where
  signature := polynomialSignature
  Law R :=
    R.readout () () (independencePolynomial
      _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.graph Finset.univ) = true ∧
    (independencePolynomial
      _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.graph Finset.univ).natDegree = 4 ∧
    (∀ k : ℕ, ((configurations
      _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.graph Finset.univ).filter
        (fun S => S.card = k)).card =
      if k = 0 then 1 else if k = 1 then 128 else if k = 2 then 130
      else if k = 3 then 256 else if k = 4 then 256 else 0)

private theorem polynomial_bridge :
    (type_of% _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.native_polynomial) ↔
      polynomialArena.Law polynomialActual := by
  change (_ = factor ∧ _) ↔ (decide (_ = factor) = true ∧ _)
  simp only [decide_eq_true_eq]

private theorem polynomial_rejected_law : ¬ polynomialArena.Law polynomialRejected := by
  intro h
  exact Bool.false_ne_true h.1

private theorem polynomial_dependence : ObservationalDependence polynomialSignature polynomialActual := by
  intro i
  refine ⟨(), factor, 0, ?_⟩
  have hf : (0 : Polynomial ℤ) ≠ factor := by
    intro h
    have hh := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
    norm_num [factor, Polynomial.coeff_one, Polynomial.coeff_X] at hh
  simp [polynomialActual, realize, hf]

def polynomialFamily : Registration polynomialArena
    (type_of% _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.native_polynomial) where
  actual := polynomialActual
  bridge := polynomial_bridge
  variation := ⟨polynomial_bridge.mp
    _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.native_polynomial,
    polynomialRejected, polynomial_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨polynomialRejected, ?_, rfl, polynomial_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := polynomial_dependence

def polynomialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    _root_.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.native_polynomial
    (Realization polynomialSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.polynomialUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot.polynomialFamily
  realizationSource := none
  generated := false
  arena := .source ⟨polynomialArena⟩
  objectArena := .source ⟨polynomialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source polynomialArena ⟨polynomialFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize polynomialSignature polynomialActual.readout polynomialActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms polynomialFamily
#print axioms polynomialRegistration

end Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
