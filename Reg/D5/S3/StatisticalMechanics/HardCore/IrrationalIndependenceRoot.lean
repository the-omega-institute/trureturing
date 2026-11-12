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

end Reg.D5.S3.StatisticalMechanics.HardCore.IrrationalIndependenceRoot
