import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.PSeries

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
open _root_.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
open LeanInformationAudit Filter Set
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope

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
def growthOne : Realization growthSignature :=
  realize growthSignature (fun _ _ _ _ => 1) (fun e => nomatch e)

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

private theorem testFloor_not_summable : ¬ Summable (doublingFloor (fun _ => 1) 1) := by
  intro h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).1
  exact h.congr (fun k => by simp [doublingFloor, Nat.cast_add])

private theorem testIntegral_not_summable : ¬ Summable (integralTestTerm (fun _ => 1) 1) := by
  intro h
  have hshift := (summable_nat_add_iff 2).2 h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).1
  exact hshift.congr (fun k => by simp [integralTestTerm, Nat.cast_add])

def arena_1 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {a c N b D : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hcone : c ≤ 1) (hN : 1 ≤ N) (hb : 1 < b)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t),
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤
        profile (fun k => c * doublingFloor g a k) N b a u ∧
      profile (fun k => c * doublingFloor g a k) N b a u ≤
        ENNReal.ofReal (C₁ * (u ^ (-a) * (F.readout () () g) (1 / u)))

private theorem rejected_law_1 : ¬ arena_1.Law growthNeg := by
  intro h
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound⟩ := @h (fun _ => 1) 1 1 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; norm_num) (by intro s hs t ht hst; norm_num)
    (by norm_num) (by intro t ht; norm_num)
  have hbad := (hbound (1/2) (by norm_num) (by norm_num)).1.trans
    (hbound (1/2) (by norm_num) (by norm_num)).2
  change ENNReal.ofReal (c₁ * (((1/2 : ℝ) ^ (-(1 : ℝ))) * 1)) ≤
    ENNReal.ofReal (C₁ * (((1/2 : ℝ) ^ (-(1 : ℝ))) * (-1))) at hbad
  have hp : 0 < (1/2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hz : ENNReal.ofReal (C₁ * (((1/2 : ℝ) ^ (-(1 : ℝ))) * (-1))) = 0 := by
    apply ENNReal.ofReal_eq_zero.mpr
    nlinarith
  rw [hz] at hbad
  have hpositive : 0 < ENNReal.ofReal (c₁ * (((1/2 : ℝ) ^ (-(1 : ℝ))) * 1)) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  exact (not_le_of_gt hpositive) hbad

def family_1 : Registration arena_1 (type_of% (@raw_profile_two_sided)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@raw_profile_two_sided, growthNeg, rejected_law_1⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_1.Law growthActual growthNeg rejected_law_1
  dependence := growthDependence

noncomputable def audit_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@raw_profile_two_sided) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.raw_profile_two_sided_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.family_1
  realizationSource := none
  generated := false
  arena := .source ⟨arena_1⟩
  objectArena := .source ⟨arena_1⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_1 ⟨family_1⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms raw_profile_two_sided
#print axioms family_1
#print axioms audit_1

def arena_2 : Arena where
  signature := seqSignature
  Law F := ∀ {g : ℝ → ℝ} {a D N b R K : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hR : 1 < R) (hK : 0 < K)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hs : Summable (doublingFloor g a)),
    ∃ η : ℕ → ℝ, (∀ k, 0 < (F.readout () () η) k ∧ η k ≤ 1) ∧ Antitone η ∧ Summable η ∧
      (∑' k, η k) ≤ K ∧ (∀ k, η k ≤ R * η (k + 1)) ∧
      ∃ c₁ C₁ ε : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
        ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤ profile η N b a u ∧
        profile η N b a u ≤ ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u)))

private theorem rejected_law_2 : ¬ arena_2.Law seqNeg := by
  intro h
  obtain ⟨η, hpos, _⟩ := @h testGrowth 1 4 1 2 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    testGrowth_ge testGrowth_mono (by norm_num) testGrowth_double testGrowth_summable
  have hbad := (hpos 0).1
  change (0 : ℝ) < -1 at hbad
  norm_num at hbad

def family_2 : Registration arena_2 (type_of% (@prescribed_ratio_matching_profile)) where
  actual := seqActual
  bridge := Iff.rfl
  variation := ⟨@prescribed_ratio_matching_profile, seqNeg, rejected_law_2⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_2.Law seqActual seqNeg rejected_law_2
  dependence := seqDependence

noncomputable def audit_2 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@prescribed_ratio_matching_profile) (Realization seqSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.prescribed_ratio_matching_profile_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.family_2
  realizationSource := none
  generated := false
  arena := .source ⟨arena_2⟩
  objectArena := .source ⟨arena_2⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_2 ⟨family_2⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seqSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms prescribed_ratio_matching_profile
#print axioms family_2
#print axioms audit_2

def arena_3 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {η : ℕ → ℝ} {a D N b C ε : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hC : 0 < C) (hε : 0 < ε)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hη : ∀ k, 0 < η k) (hsη : Summable η)
    (hbound : ∀ u : ℝ, 0 < u → u ≤ ε →
      profile η N b a u ≤ ENNReal.ofReal (C * (u ^ (-a) * g (1 / u)))),
    Summable (doublingFloor (F.readout () () g) a)

private theorem rejected_law_3 : ¬ arena_3.Law growthOne := by
  intro h
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound⟩ := raw_profile_two_sided
    (g := testGrowth) (a := 1) (c := 1) (N := 1) (b := 2) (D := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    testGrowth_ge testGrowth_mono (by norm_num) testGrowth_double
  have hpos (k : ℕ) : 0 < doublingFloor testGrowth 1 k := by
    have hge := testGrowth_ge ((k : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    unfold doublingFloor
    positivity
  have hbad := @h testGrowth (doublingFloor testGrowth 1) 1 4 1 2 C₁ (1/2)
    (by norm_num) (by norm_num) (by norm_num) hC₁ (by norm_num)
    testGrowth_ge testGrowth_mono (by norm_num) testGrowth_double hpos testGrowth_summable
    (fun u hu hue => by simpa only [one_mul] using (hbound u hu hue).2)
  exact testFloor_not_summable hbad

def family_3 : Registration arena_3 (type_of% (@summable_floor_of_profile_bound)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@summable_floor_of_profile_bound, growthOne, rejected_law_3⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_3.Law growthActual growthOne rejected_law_3
  dependence := growthDependence

noncomputable def audit_3 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@summable_floor_of_profile_bound) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.summable_floor_of_profile_bound_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.family_3
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
    owner := `D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms summable_floor_of_profile_bound
#print axioms family_3
#print axioms audit_3

def arena_4 : Arena where
  signature := growthSignature
  Law F := ∀ {g : ℝ → ℝ} {a D N b R K : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hR : 1 < R) (hK : 0 < K)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t),
    (Summable (integralTestTerm (F.readout () () g) a) ↔
      ∃ η : ℕ → ℝ, AdmissibleFloor R K η ∧
        ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
          profile η N b a u ≤ ENNReal.ofReal (C * (u ^ (-a) * g (1 / u)))) ∧
      (Summable (integralTestTerm g a) →
        ∃ η : ℕ → ℝ, AdmissibleFloor R K η ∧
          ∃ c₁ C₁ ε : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
            ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤ profile η N b a u ∧
              profile η N b a u ≤ ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u))))

private theorem rejected_law_4 : ¬ arena_4.Law growthOne := by
  intro h
  have hseries : Summable (integralTestTerm testGrowth 1) := by
    rw [← summable_nat_add_iff 2]
    have he : (fun k => integralTestTerm testGrowth 1 (k + 2)) = doublingFloor testGrowth 1 := by
      funext k
      simp [integralTestTerm, doublingFloor, Nat.cast_add]
    rw [he]
    exact testGrowth_summable
  have hgood := fixed_floor_growth_criterion (g := testGrowth)
    (a := 1) (D := 4) (N := 1) (b := 2) (R := 2) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    testGrowth_ge testGrowth_mono (by norm_num) testGrowth_double
  have hbad := @h testGrowth 1 4 1 2 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    testGrowth_ge testGrowth_mono (by norm_num) testGrowth_double
  exact testIntegral_not_summable (hbad.1.mpr (hgood.1.mp hseries))

def family_4 : Registration arena_4 (type_of% (@fixed_floor_growth_criterion)) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨@fixed_floor_growth_criterion, growthOne, rejected_law_4⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena_4.Law growthActual growthOne rejected_law_4
  dependence := growthDependence

noncomputable def audit_4 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixed_floor_growth_criterion) (Realization growthSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.fixed_floor_growth_criterion_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope.family_4
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
    owner := `D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms fixed_floor_growth_criterion
#print axioms family_4
#print axioms audit_4

end Reg.D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope
