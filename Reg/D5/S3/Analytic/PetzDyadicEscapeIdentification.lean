import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzDyadicEscapeIdentification
import Reg.Support.DependentFamily

/-! Source-bound audits of finite rate law identification and its sharp sample count. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.PetzDyadicEscapeIdentification

open LeanInformationAudit
open _root_.D5.S3.Analytic.PetzDyadicEscapeIdentification
open _root_.D5.S3.Analytic.PetzDyadicEscapeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

abbrev profileSignature : Signature where
  Params := Σ n : ℕ, Σ _ : Fin n → ℝ, Σ _ : Fin n → ℝ, Fin n → ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization profileSignature :=
  realize profileSignature
    (fun i p s => rateProfile p.2.1 (bif i then p.2.2.1 else p.2.2.2) s)
    (fun e => nomatch e)

private def constant : Realization profileSignature :=
  realize profileSignature (fun _ _ _ => 0) (fun e => nomatch e)

private def copiedAt (i : Bool) : Realization profileSignature :=
  realize profileSignature
    (fun j p s => if j = i then actual.readout (!j) p s
      else actual.readout j p s)
    (fun e => nomatch e)

abbrev profileArena : Arena where
  signature := profileSignature
  Law R := ∀ {m n : ℕ} (hm : 1 ≤ m)
    (rates w v : Fin n → ℝ) (hr : StrictMono rates)
    (scales : Finset ℝ) (hcount : 2 * m - 2 ≤ scales.card)
    (hpos : ∀ s ∈ scales, 0 < s)
    (hw : (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ m)
    (hv : (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ m)
    (hmass : rateMoment rates w 0 = rateMoment rates v 0)
    (hmean : rateMoment rates w 1 = rateMoment rates v 1)
    (hobs : ∀ s ∈ scales,
      R.readout true ⟨n, rates, w, v⟩ s = R.readout false ⟨n, rates, w, v⟩ s),
    w = v

private def witnessRates : Fin 4 → ℝ := binomialRate 3 1 1

private theorem witnessRates_strictMono : StrictMono witnessRates := by
  intro i j hij
  simpa only [witnessRates, binomialRate, mul_one, add_lt_add_iff_left] using
    (Nat.cast_lt.mpr hij : (i.val : ℝ) < j.val)

private def witnessScales : Finset ℝ := {1, 2}

private theorem witnessProfiles_ne :
    rateProfile witnessRates (evenBinomial 3) 1 ≠ rateProfile witnessRates (oddBinomial 3) 1 := by
  apply ne_of_gt
  apply sub_pos.mp
  change 0 < rateProfile (binomialRate 3 1 1) (evenBinomial 3) 1 -
    rateProfile (binomialRate 3 1 1) (oddBinomial 3) 1
  rw [binomial_profile_difference 3 (by decide)]
  have hstep : 0 < 1 - Real.exp (-(1 * 1 : ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  exact div_pos (mul_pos (Real.exp_pos _) (pow_pos hstep _)) (by positivity)

private theorem witnessRejects (R : Realization profileSignature)
    (hobs : ∀ s ∈ witnessScales,
      R.readout true ⟨4, witnessRates, evenBinomial 3, oddBinomial 3⟩ s =
        R.readout false ⟨4, witnessRates, evenBinomial 3, oddBinomial 3⟩ s) :
    ¬ profileArena.Law R := by
  intro law
  have hcount : 2 * 2 - 2 ≤ witnessScales.card := by
    have hc : witnessScales.card = 2 := Finset.card_pair (by norm_num : (1 : ℝ) ≠ 2)
    exact hc.ge
  have hpos : ∀ s ∈ witnessScales, 0 < s := by
    intro s hs
    simp only [witnessScales, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> norm_num
  obtain ⟨hw, hv⟩ := binomial_laws_support_card 2 (by decide)
  obtain ⟨_, _, hmassW, hmassV⟩ := binomial_laws_normalized 3 (by decide)
  have hmass : rateMoment witnessRates (evenBinomial 3) 0 =
      rateMoment witnessRates (oddBinomial 3) 0 := by
    simp only [rateMoment_eq_sum, pow_zero, mul_one, hmassW, hmassV]
  have heq := @law 2 4 (by decide) witnessRates (evenBinomial 3) (oddBinomial 3)
    witnessRates_strictMono witnessScales hcount hpos hw.le hv.le hmass
    (binomial_laws_equal_mean 3 (by decide) 1 1) hobs
  exact witnessProfiles_ne (congrArg (fun w => rateProfile witnessRates w 1) heq)

private theorem profileDependence : ObservationalDependence profileSignature actual := by
  intro i
  let one : Fin 1 → ℝ := fun _ => 1
  have hne : rateProfile one one 0 ≠ rateProfile one one 1 := by
    apply ne_of_lt
    simp [one, rateProfile_eq_laplace, rateMoment_eq_sum, tiltedRateMoment, Fin.sum_univ_one,
      sub_add_cancel, Real.exp_pos]
  refine ⟨⟨1, one, one, one⟩, 0, 1, ?_⟩
  cases i <;> exact hne

def profileFamily : Registration profileArena (type_of% @rateProfile_identifies_weights) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rateProfile_identifies_weights, constant, witnessRejects constant (by intros; rfl)⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨copiedAt i, ?_, rfl, witnessRejects (copiedAt i) ?_⟩
      · intro j hj
        funext p s
        simp [copiedAt, realize, hj]
      · intro s _
        cases i <;> rfl
    · intro e
      exact nomatch e
  dependence := profileDependence

def profileAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rateProfile_identifies_weights) (Realization profileSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeIdentification.rateProfile_identifies_weights.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeIdentification.profileFamily
  realizationSource := none
  generated := false
  arena := .source ⟨profileArena⟩
  objectArena := .source ⟨profileArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source profileArena ⟨profileFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize profileSignature
    (fun i p s => rateProfile p.2.1 (bif i then p.2.2.1 else p.2.2.2) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeIdentification
    definition := none
    coordinates := #[1, 3, 4, 5]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms profileAudit

abbrev sharpSignature : Signature where
  Params := Σ m : ℕ, Σ _ : Fin (2 * m) → ℝ, Σ _ : Fin (2 * m) → ℝ, Fin (2 * m) → ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def sharpActual : Realization sharpSignature :=
  realize sharpSignature
    (fun i p s => rateProfile p.2.1 (bif i then p.2.2.1 else p.2.2.2) s)
    (fun e => nomatch e)

private def zeroedAt (i : Bool) : Realization sharpSignature :=
  realize sharpSignature
    (fun j p s => if j = i then 0 else sharpActual.readout j p s)
    (fun e => nomatch e)

abbrev sharpArena : Arena where
  signature := sharpSignature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (rates : Fin (2 * m) → ℝ) (hr : StrictMono rates)
    (scales : Finset ℝ) (hcount : scales.card = 2 * m - 3) (hpos : ∀ s ∈ scales, 0 < s),
    ∃ w v : Fin (2 * m) → ℝ,
      w ≠ v ∧ (∀ i, 0 ≤ w i ∧ 0 ≤ v i ∧ w i * v i = 0) ∧
      (Finset.univ.filter (fun i => w i ≠ 0)).card = m ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card = m ∧
      (∑ i, w i) = 1 ∧ (∑ i, v i) = 1 ∧
      rateMoment rates w 1 = rateMoment rates v 1 ∧
      (∀ s ∈ scales,
        R.readout true ⟨m, rates, w, v⟩ s = R.readout false ⟨m, rates, w, v⟩ s)

private def singleScale : Finset ℝ := {1}

private theorem singleScale_card : singleScale.card = 2 * 2 - 3 := by
  simp [singleScale]

private theorem singleScale_pos : ∀ s ∈ singleScale, 0 < s := by
  simp [singleScale]

private theorem witnessProfile_pos (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : (∑ i, w i) = 1) : 0 < rateProfile witnessRates w 1 := by
  have hkernel (i : Fin 4) : 0 < Real.exp (-witnessRates i) - 1 + witnessRates i := by
    have hr : 0 < witnessRates i := by
      dsimp [witnessRates, binomialRate]
      positivity
    linarith [Real.add_one_lt_exp (neg_ne_zero.mpr hr.ne')]
  have hsome : ∃ i ∈ Finset.univ, 0 < w i :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp (hmass ▸ zero_lt_one)
  obtain ⟨i, hi, hwi⟩ := hsome
  rw [rateProfile_eq_laplace, rateMoment_eq_sum, rateMoment_eq_sum]
  simp only [tiltedRateMoment, pow_zero, pow_one, mul_one, one_mul, div_one,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_pos'
  · intro j _
    simpa only [mul_add, mul_sub, mul_one] using mul_nonneg (hw j) (hkernel j).le
  · refine ⟨i, hi, ?_⟩
    simpa only [mul_add, mul_sub, mul_one] using mul_pos hwi (hkernel i)

private theorem sharpRejects (i : Bool) : ¬ sharpArena.Law (zeroedAt i) := by
  intro law
  obtain ⟨w, v, _, hnonneg, _, _, hw, hv, _, hobs⟩ :=
    @law 2 (by decide) witnessRates witnessRates_strictMono singleScale
      singleScale_card singleScale_pos
  have heq := hobs 1 (by simp [singleScale])
  cases i
  · change rateProfile witnessRates w 1 = 0 at heq
    exact (witnessProfile_pos w (fun j => (hnonneg j).1) hw).ne' heq
  · change 0 = rateProfile witnessRates v 1 at heq
    exact (witnessProfile_pos v (fun j => (hnonneg j).2.1) hv).ne heq

private theorem sharpDependence : ObservationalDependence sharpSignature sharpActual := by
  intro i
  obtain ⟨w, v, _, hnonneg, _, _, hw, _, _, hobs⟩ :=
    rateProfile_query_count_sharp (m := 2) (by decide) witnessRates witnessRates_strictMono
      singleScale singleScale_card singleScale_pos
  have heq := hobs 1 (by simp [singleScale])
  have hwpos := witnessProfile_pos w (fun j => (hnonneg j).1) hw
  have hvpos : 0 < rateProfile witnessRates v 1 := heq ▸ hwpos
  refine ⟨⟨2, witnessRates, w, v⟩, 0, 1, ?_⟩
  cases i
  · change rateProfile witnessRates v 0 ≠ rateProfile witnessRates v 1
    simpa only [rateProfile, div_zero] using hvpos.ne
  · change rateProfile witnessRates w 0 ≠ rateProfile witnessRates w 1
    simpa only [rateProfile, div_zero] using hwpos.ne

def sharpFamily : Registration sharpArena (type_of% @rateProfile_query_count_sharp) where
  actual := sharpActual
  bridge := Iff.rfl
  variation := ⟨@rateProfile_query_count_sharp, zeroedAt true, sharpRejects true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroedAt i, ?_, rfl, sharpRejects i⟩
      intro j hj
      funext p s
      simp [zeroedAt, realize, hj]
    · intro e
      exact nomatch e
  dependence := sharpDependence

def sharpAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rateProfile_query_count_sharp) (Realization sharpSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeIdentification.rateProfile_query_count_sharp.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeIdentification.sharpFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sharpArena⟩
  objectArena := .source ⟨sharpArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sharpArena ⟨sharpFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sharpSignature
    (fun i p s => rateProfile p.2.1 (bif i then p.2.2.1 else p.2.2.2) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeIdentification
    definition := none
    coordinates := #[0, 2, 7, 8]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sharpAudit

end Reg.D5.S3.Analytic.PetzDyadicEscapeIdentification
