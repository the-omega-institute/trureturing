import D5.S3.VertexAlgebra.CollisionAnalytic.FinalLaurentEvaluation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The source-bound audit retains the full polynomial, pole-order and signed
index families. Native source serialization and current binding certification
are separate from the kernel-checked realization obligations. They remain
unresolved under https://github.com/the-omega-institute/trureturing/issues/23249;
no validated binding status is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CollisionAnalytic.FinalLaurentEvaluation
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ThreeFieldFinalLaurentFiber
open _root_.D5.S3.VertexAlgebra.FinalLaurentEvaluation
open UngradedLocalWordSeries StateFieldResidueReconstruction
open LeanInformationAudit

abbrev Source := type_of% (@final_laurent_absolute_evaluation)

structure Parameters where
  k : ℕ
  a : Fin 3 → ℕ
  x : ℂ
  y : ℂ
  z : ℂ

abbrev signature : Signature where
  Params := Parameters
  State _ := MvPolynomial (Fin 3) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (((Fin 3 → ℤ) × LaurentIndex) → ℂ) × ((Fin 3 → ℤ) → ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p Q =>
    (fun i => laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) p.k p.a i.1 i.2 *
      (p.x^i.1 0 * p.y^i.1 1 * p.z^i.1 2),
     fun e => laurentCoefficient (Q : MvPowerSeries (Fin 3) ℂ) p.k p.a e *
      (p.x^e 0 * p.y^e 1 * p.z^e 2))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ) (a : Fin 3 → ℕ)
    (x y z : ℂ), x ≠ 0 → y ≠ 0 → z ≠ 0 →
    ‖x‖ < ‖y‖ → ‖x‖+‖y‖ < ‖z‖ →
    Summable (fun i => ‖(R.readout () ⟨k,a,x,y,z⟩ Q).1 i‖) ∧
    Summable (fun e => ‖(R.readout () ⟨k,a,x,y,z⟩ Q).2 e‖) ∧
    HasSum (R.readout () ⟨k,a,x,y,z⟩ Q).2
      (MvPolynomial.eval ![x,y,z] Q /
        (x^k * y^k * (x+y)^k * (x+y+z)^(a 0) * (y+z)^(a 1) * z^(a 2)))

private theorem positive : arena.Law actual := @final_laurent_absolute_evaluation

private def bad : Realization signature := realize signature
  (fun _ _ _ => (fun _ => 1, fun _ => 1)) (fun e => nomatch e)

private theorem negative : ¬ arena.Law bad := by
  intro h
  have hraw := (h 0 0 (fun _ => 0) 1 2 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1
  have hc : Summable (fun _ : (Fin 3 → ℤ) × LaurentIndex => (1 : ℝ)) := by
    simpa [bad, realize] using hraw
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hc)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, fun _ => 0, 1, 2, 4⟩, (0 : MvPolynomial (Fin 3) ℂ), (1 : MvPolynomial (Fin 3) ℂ), ?_⟩
  intro he
  have hh := congrFun (congrArg Prod.fst he) ((fun _ => 0), ((0,0),(0,0)))
  norm_num [actual, realize, laurentTerm, laurentInput, laurentWeight,
    integerBinomial] at hh
  have hv : (![0, 0, 0] : Fin 3 → ℤ) = 0 := by
    funext c
    fin_cases c <;> rfl
  have hi : signedIndex (0 : Fin 3 → ℤ) = 0 := by
    ext c
    simp [signedIndex]
  have hn : ∀ c : Fin 3, 0 ≤ (0 : Fin 3 → ℤ) c := fun _ => le_rfl
  have hz : signedExtend (0 : MvPowerSeries (Fin 3) ℂ) (0 : Fin 3 → ℤ) = 0 := by
    change (if ∀ c : Fin 3, 0 ≤ (0 : Fin 3 → ℤ) c then
      MvPowerSeries.coeff (signedIndex 0) (0 : MvPowerSeries (Fin 3) ℂ) else 0) = 0
    rw [if_pos hn, MvPowerSeries.coeff_zero]
  have ho : signedExtend (1 : MvPowerSeries (Fin 3) ℂ) (0 : Fin 3 → ℤ) = 1 := by
    change (if ∀ c : Fin 3, 0 ≤ (0 : Fin 3 → ℤ) c then
      MvPowerSeries.coeff (signedIndex 0) (1 : MvPowerSeries (Fin 3) ℂ) else 0) = 1
    rw [if_pos hn, hi, MvPowerSeries.coeff_zero_one]
  rw [hv, hz, ho] at hh
  exact zero_ne_one hh

def family : Registration arena Source where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, bad, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, negative⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@final_laurent_absolute_evaluation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.FinalLaurentEvaluation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.FinalLaurentEvaluation.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.VertexAlgebra.CollisionAnalytic.FinalLaurentEvaluation
