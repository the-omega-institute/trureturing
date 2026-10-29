import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.TraceFibers.StrictExteriorSecants
import Reg.Support.DependentFamily

/-! Source-bound registration of the whole-fiber quantitative estimate. -/

noncomputable section
open scoped Matrix
open LeanInformationAudit
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus (maxEntry)
open _root_.D5.S3.Observer.TraceFibers.StrictExteriorSecants
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Observer.TraceFibers.StrictExteriorSecants

abbrev signature : Signature where
  Params := Unit
  State _ := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ P => maxEntry P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (θ : ℚ) (_hθ : 0 < θ) (b : ℝ) (_hb : 0 < b)
    (_hout : b < min (1 / (θ : ℝ)) (1 + (θ : ℝ)) ∨
      max (1 / (θ : ℝ)) (1 + (θ : ℝ)) < b),
    ∃ L : ℝ, 0 ≤ L ∧ ∀ P Q : Mat, LegalSource P → LegalSource Q →
      Matrix.trace (action false * P) = b → Matrix.trace (action false * Q) = b →
      R.readout () () (P - Q) ≤ L *
        |(P 1 0 - (θ : ℝ) * P 1 1) - (Q 1 0 - (θ : ℝ) * Q 1 1)|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨L, _, hL⟩ := h 1 (by norm_num) 3 (by norm_num) (by norm_num)
  let P := sourceChart (1 / 4) (11 / 2)
  have hP : LegalSource P := source_chart_legal _ _ (by norm_num) (by norm_num)
  have hb : Matrix.trace (action false * P) = 3 := by
    norm_num [P, sourceChart, action_m_shape, Matrix.trace_fin_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hh := hL P P hP hP hb hb
  change (1 : ℝ) ≤ _ at hh
  simp only [sub_self, abs_zero, mul_zero] at hh
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hh

def family : Registration arena (type_of% @strict_exterior_uniform_secant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_exterior_uniform_secant, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : Mat), (1 : Mat), ?_⟩
    change maxEntry (0 : Mat) ≠ maxEntry (1 : Mat)
    norm_num [maxEntry, Matrix.one_apply]

def entry : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@strict_exterior_uniform_secant)
    (type_of% (realize signature (fun _ _ P => maxEntry P) (fun e => nomatch e)))
    Unit Unit := {
  unitName :=
    `Reg.D5.S3.Observer.TraceFibers.StrictExteriorSecants.informationUnit
  realizationName := `Reg.D5.S3.Observer.TraceFibers.StrictExteriorSecants.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => maxEntry P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.TraceFibers.StrictExteriorSecants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Reg.D5.S3.Observer.TraceFibers.StrictExteriorSecants
