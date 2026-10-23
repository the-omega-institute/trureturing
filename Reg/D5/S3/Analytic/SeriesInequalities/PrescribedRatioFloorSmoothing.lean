import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.PSeries

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
open LeanInformationAudit Filter Set
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing

abbrev seqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ) (fun _ => ℕ → ℝ)
abbrev growthSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def seqActual : Realization seqSignature :=
  realize seqSignature (fun _ _ x => x) (fun e => nomatch e)
def growthActual : Realization growthSignature :=
  realize growthSignature (fun _ _ x => x) (fun e => nomatch e)
def seqNeg : Realization seqSignature :=
  realize seqSignature (fun _ _ _ _ => -1) (fun e => nomatch e)
def growthNeg : Realization growthSignature :=
  realize growthSignature (fun _ _ _ _ => -1) (fun e => nomatch e)
def growthSquare : Realization growthSignature :=
  realize growthSignature (fun _ _ _ t => t ^ 2) (fun e => nomatch e)
private theorem seqDependence : ObservationalDependence seqSignature seqActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (fun _ : ℕ => (0 : ℝ)) ≠ (fun _ : ℕ => (1 : ℝ))
  intro h
  have h0 := congrFun h 0
  norm_num at h0
private theorem growthDependence : ObservationalDependence growthSignature growthActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (fun _ : ℝ => (0 : ℝ)) ≠ (fun _ : ℝ => (1 : ℝ))
  intro h
  have h0 := congrFun h 0
  norm_num at h0

private def testGrowth (t : ℝ) : ℝ := t ^ 2
private theorem testGrowth_ge (t : ℝ) (ht : 2 ≤ t) : 1 ≤ testGrowth t := by
  dsimp [testGrowth]
  nlinarith
private theorem testGrowth_mono : MonotoneOn testGrowth (Ici 2) := by
  intro s hs t ht hst
  dsimp [testGrowth]
  change 2 ≤ s at hs
  change 2 ≤ t at ht
  nlinarith
private theorem testGrowth_double (t : ℝ) (_ht : 2 ≤ t) : testGrowth (2 * t) ≤ 4 * testGrowth t := by
  dsimp [testGrowth]
  nlinarith [sq_nonneg t]
private theorem testGrowth_summable : Summable (doublingFloor testGrowth 1) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 2).2 hs
  exact hshift.congr (fun k => by
    simp only [doublingFloor, testGrowth, one_div_one, Real.rpow_one, Nat.cast_add, Nat.cast_ofNat]
    congr 1
    ring)


def arena_1 : Arena where
  signature := seqSignature
  Law F := ∀ {q C c d : ℝ} {ω : ℕ → ℝ}
    (hq : 0 < q) (hqone : q < 1) (hpos : ∀ k, 0 < ω k)
    (hanti : Antitone ω) (hC : 1 ≤ C) (hc : 0 < c) (hd : 0 ≤ d)
    (hhalf : ∀ j k : ℕ, j ≤ k → k + 2 ≤ 2 * (j + 2) → ω j ≤ C * ω k)
    (hlower : ∀ k : ℕ, c ≤ ω k * ((k : ℝ) + 2) ^ d),
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k, ω k ≤ smooth q ω k ∧ smooth q ω k ≤ B * (F.readout () () ω) k

private theorem rejected_law_1 : ¬ arena_1.Law seqNeg := by
  intro h
  obtain ⟨B, hB, hbound⟩ := @h (1/2) 1 1 0 (fun _ => 1)
    (by norm_num) (by norm_num) (by intro k; norm_num)
    (by intro j k hjk; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro j k hjk hscale; norm_num) (by intro k; norm_num)
  have hbad := (hbound 0).2
  change (1 : ℝ) ≤ B * (-1) at hbad
  nlinarith

def family_1 : Registration arena_1 (type_of% (@uniform_smoothing_equivalence)) where
  actual := seqActual
  bridge := Iff.rfl
  variation := ⟨@uniform_smoothing_equivalence, seqNeg, rejected_law_1⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_1.Law seqActual seqNeg rejected_law_1
  dependence := seqDependence

noncomputable def audit_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@uniform_smoothing_equivalence) (Realization seqSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.uniform_smoothing_equivalence_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.family_1
  realizationSource := none
  generated := false
  arena := .source ⟨arena_1⟩
  objectArena := .source ⟨arena_1⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_1 ⟨family_1⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seqSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms uniform_smoothing_equivalence
#print axioms family_1
#print axioms audit_1

def arena_2 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {D : ℝ}
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (j : ℕ) (t : ℝ) (ht : 2 ≤ t),
    (F.readout () () g) ((2 : ℝ) ^ j * t) ≤ D ^ j * g t

private theorem rejected_law_2 : ¬ arena_2.Law growthSquare := by
  intro h
  have hbad := @h (fun _ => 1) 1 (by norm_num) (by intro t ht; norm_num)
    0 2 (by norm_num)
  norm_num [growthSquare, realize] at hbad

def family_2 : Registration arena_2 (type_of% (@doubling_iterate)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@doubling_iterate, growthSquare, rejected_law_2⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_2.Law growthActual growthSquare rejected_law_2
  dependence := growthDependence

noncomputable def audit_2 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@doubling_iterate) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.doubling_iterate_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.family_2
  realizationSource := none
  generated := false
  arena := .source ⟨arena_2⟩
  objectArena := .source ⟨arena_2⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_2 ⟨family_2⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms doubling_iterate
#print axioms family_2
#print axioms audit_2

def arena_3 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {D : ℝ}
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t),
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
      (F.readout () () g) t ≤ C * t ^ (Real.log D / Real.log 2)

private theorem rejected_law_3 : ¬ arena_3.Law growthSquare := by
  intro h
  obtain ⟨C, hC, hbound⟩ := @h (fun _ => 1) 1 (by intro t ht; norm_num)
    (by intro s hs t ht hst; norm_num) (by norm_num) (by intro t ht; norm_num)
  have hbad := hbound (C + 2) (by linarith)
  change (C + 2) ^ 2 ≤ C * (C + 2) ^ (Real.log 1 / Real.log 2) at hbad
  simp only [Real.log_one, zero_div, Real.rpow_zero, mul_one] at hbad
  nlinarith

def family_3 : Registration arena_3 (type_of% (@doubling_polynomial)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@doubling_polynomial, growthSquare, rejected_law_3⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_3.Law growthActual growthSquare rejected_law_3
  dependence := growthDependence

noncomputable def audit_3 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@doubling_polynomial) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.doubling_polynomial_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.family_3
  realizationSource := none
  generated := false
  arena := .source ⟨arena_3⟩
  objectArena := .source ⟨arena_3⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_3 ⟨family_3⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms doubling_polynomial
#print axioms family_3
#print axioms audit_3

def arena_4 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {a D q : ℝ}
    (ha : 0 < a) (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t)
    (hmono : MonotoneOn g (Ici 2)) (hD : 1 ≤ D)
    (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hq : 0 < q) (hqone : q < 1),
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ k, doublingFloor g a k ≤ smooth q (doublingFloor g a) k ∧
        smooth q (doublingFloor g a) k ≤ B * doublingFloor g a k) ∧
      (∀ k, 0 < smooth q (doublingFloor (F.readout () () g) a) k) ∧
      Antitone (smooth q (doublingFloor g a)) ∧
      (∀ k, q * smooth q (doublingFloor g a) k ≤ smooth q (doublingFloor g a) (k + 1)) ∧
      (Summable (doublingFloor g a) → Summable (smooth q (doublingFloor g a)) ∧
        (∑' k, smooth q (doublingFloor g a) k) =
          doublingFloor g a 0 / (1 - q) + ∑' k, doublingFloor g a (k + 1))

private theorem rejected_law_4 : ¬ arena_4.Law growthNeg := by
  intro h
  obtain ⟨B, hB, hbounds, hpos, _⟩ := @h (fun _ => 1) 1 1 (1/2)
    (by norm_num) (by intro t ht; norm_num) (by intro s hs t ht hst; norm_num)
    (by norm_num) (by intro t ht; norm_num) (by norm_num) (by norm_num)
  have hbad := hpos 0
  change (0 : ℝ) < smooth (1/2) (doublingFloor (fun _ => -1) 1) 0 at hbad
  norm_num [smooth, doublingFloor] at hbad

def family_4 : Registration arena_4 (type_of% (@doubling_floor_smoothing)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@doubling_floor_smoothing, growthNeg, rejected_law_4⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_4.Law growthActual growthNeg rejected_law_4
  dependence := growthDependence

noncomputable def audit_4 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@doubling_floor_smoothing) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.doubling_floor_smoothing_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.family_4
  realizationSource := none
  generated := false
  arena := .source ⟨arena_4⟩
  objectArena := .source ⟨arena_4⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_4 ⟨family_4⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms doubling_floor_smoothing
#print axioms family_4
#print axioms audit_4

def arena_5 : Arena where
  signature := growthSignature
  Law F := ∀ {R : ℝ} (hR : 1 < R),
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧ 1 / R ≤ (q : ℝ) ∧
      ∀ (g : ℝ → ℝ) (a D K : ℝ), 0 < a → 0 < K →
        (∀ t : ℝ, 2 ≤ t → 1 ≤ g t) → MonotoneOn g (Ici 2) → 1 ≤ D →
        (∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) → Summable (doublingFloor g a) →
        ∃ c : ℚ, 0 < (c : ℝ) ∧ (c : ℝ) ≤ 1 ∧
          let η := fun k => (c : ℝ) * smooth (q : ℝ) (doublingFloor (F.readout () () g) a) k
          (∀ k, 0 < η k ∧ η k ≤ 1) ∧ Antitone η ∧ Summable η ∧
          (∑' k, η k) ≤ K ∧ (∀ k, η k ≤ R * η (k + 1)) ∧
          ∃ B : ℝ, 1 ≤ B ∧ ∀ k,
            (c : ℝ) * doublingFloor g a k ≤ η k ∧
              η k ≤ B * ((c : ℝ) * doublingFloor g a k)

private theorem rejected_law_5 : ¬ arena_5.Law growthNeg := by
  intro h
  obtain ⟨q, hqpos, hqone, hqR, hq⟩ := @h 2 (by norm_num)
  obtain ⟨c, hc, hcone, hpos, _⟩ := hq testGrowth 1 4 1
    (by norm_num) (by norm_num) testGrowth_ge testGrowth_mono
    (by norm_num) testGrowth_double testGrowth_summable
  have hbad := (hpos 0).1
  change (0 : ℝ) < (c : ℝ) * smooth (q : ℝ) (doublingFloor (fun _ => -1) 1) 0 at hbad
  norm_num [smooth, doublingFloor] at hbad
  nlinarith

def family_5 : Registration arena_5 (type_of% (@prescribed_ratio_floor)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@prescribed_ratio_floor, growthNeg, rejected_law_5⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_5.Law growthActual growthNeg rejected_law_5
  dependence := growthDependence

noncomputable def audit_5 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@prescribed_ratio_floor) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.prescribed_ratio_floor_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing.family_5
  realizationSource := none
  generated := false
  arena := .source ⟨arena_5⟩
  objectArena := .source ⟨arena_5⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_5 ⟨family_5⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "value", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms prescribed_ratio_floor
#print axioms family_5
#print axioms audit_5

end Reg.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
