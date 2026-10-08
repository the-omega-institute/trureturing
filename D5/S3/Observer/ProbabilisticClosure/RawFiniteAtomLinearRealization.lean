/- GID: D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite tests descend through the exceptional parity quotient. -/

import D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization
import Mathlib.Logic.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.RawFiniteAtomLinearRealization
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open AdaptiveMarkerStoppingTails FiniteAtomLinearRealization

def rawCanonical (alpha q : unitInterval) (eta : Bool × Bool) : Bool × Bool := by
  classical
  exact if (alpha : ℝ) = (1 - (alpha : ℝ)) * (q : ℝ) then
    (false, eta.1.xor eta.2) else eta

private theorem raw_canonical_idempotent (alpha q : unitInterval) (eta : Bool × Bool) :
    rawCanonical alpha q (rawCanonical alpha q eta) = rawCanonical alpha q eta := by
  classical
  unfold rawCanonical
  split_ifs <;> simp

private theorem raw_canonical_flip (alpha q : unitInterval) (eta : Bool × Bool) (j : Side) :
    rawCanonical alpha q (flipParity (rawCanonical alpha q eta) j) =
      rawCanonical alpha q (flipParity eta j) := by
  classical
  rcases eta with ⟨l,r⟩
  cases l <;> cases r <;> cases j <;> unfold rawCanonical <;> split_ifs <;> simp [flipParity]

private theorem raw_canonical_rate (alpha q : unitInterval) (ha : 0 < (alpha : ℝ))
    (eta : Bool × Bool) (j : Side) :
    markerRate alpha q (rawCanonical alpha q eta) j = markerRate alpha q eta j := by
  classical
  have hd := (denominator_pos alpha q ha eta).ne'
  have hc := (denominator_pos alpha q ha (rawCanonical alpha q eta)).ne'
  rcases eta with ⟨l,r⟩
  unfold rawCanonical at hc ⊢
  split_ifs with he
  · have hb : (alpha : ℝ) = (1 - (alpha : ℝ)) * (q : ℝ) := he
    have hb2 := congrArg (fun x : ℝ => x ^ 2) hb
    simp only [if_pos he] at hc
    cases l <;> cases r <;> cases j <;>
      simp [markerRate, rootMass, denominator, selectedParity] at hd hc ⊢ <;>
      field_simp [hd,hc] <;> (apply Or.inl; nlinarith [hb, hb2])
  · rfl

@[reducible] def rawModel {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval) :
    MassModel .raw alpha q := by
  classical
  let enc (p : Fin m × (Bool × Bool)) :
      {p : Fin m × (Bool × Bool) // rawCanonical alpha (q p.1) p.2 = p.2} :=
    ⟨(p.1, rawCanonical alpha (q p.1) p.2), raw_canonical_idempotent alpha (q p.1) p.2⟩
  exact {
    Carrier := {p : Fin m × (Bool × Bool) // rawCanonical alpha (q p.1) p.2 = p.2} ⊕ Unit
    finite := inferInstance
    finiteOutputs := (fullModel .raw alpha q).finiteOutputs
    mode := fun c => match c with | .inl _ => .active | .inr _ => .stopped
    matrix := fun j o d c => match c with
      | .inl p =>
          (if o = .zero then
            if d = .inl (enc (p.1.1, flipParity p.1.2 j)) then
              1 - markerRate alpha (q p.1.1) p.1.2 j else 0
           else 0) +
          (if o = .rawMark then
            if d = .inr () then markerRate alpha (q p.1.1) p.1.2 j else 0
           else 0)
      | .inr _ => if o = .reject then if d = .inr () then 1 else 0 else 0 }

def rawEncode {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval) :
    (fullModel .raw alpha q).Carrier → (rawModel alpha q).Carrier
  | .inl p => .inl ⟨(p.1, rawCanonical alpha (q p.1) p.2),
      raw_canonical_idempotent alpha (q p.1) p.2⟩
  | .inr _ => .inr ()

private theorem raw_terminal_row {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (T : Test) :
    testRow (rawModel alpha q) T (.inr ()) = if terminalAccept .stopped T then 1 else 0 := by
  classical
  letI := (rawModel alpha q).finite
  letI := (rawModel alpha q).finiteOutputs
  induction T with
  | read accept => rfl
  | inspect next ih => exact ih .stopped
  | query j next ih =>
      simp [testRow, rawModel, Finset.univ, Fintype.complete, terminalAccept, ih .reject]
      split_ifs <;> simp_all

private theorem raw_row_descends {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval)
    (ha : 0 < (alpha : ℝ)) (T : Test) (c : (fullModel .raw alpha q).Carrier) :
    testRow (rawModel alpha q) T (rawEncode alpha q c) = testRow (fullModel .raw alpha q) T c := by
  classical
  letI := (rawModel alpha q).finite
  letI := (rawModel alpha q).finiteOutputs
  cases c with
  | inr t => rw [rawEncode, raw_terminal_row, full_terminal_row]; simp [fullModel]
  | inl p =>
      rcases p with ⟨i,eta⟩
      induction T generalizing eta with
      | read accept => rfl
      | inspect next ih => exact ih .active eta
      | query j next ih =>
          rw [full_active_row]
          simp [testRow, rawEncode, rawModel, Finset.univ, Fintype.complete,
            Finset.sum_add_distrib, add_mul]
          rw [raw_terminal_row]
          have hr := raw_canonical_rate alpha (q i) ha eta j
          have hf := raw_canonical_flip alpha (q i) eta j
          rw [hr]
          have he : rawEncode alpha q (.inl (i, flipParity eta j)) =
              .inl ⟨(i, rawCanonical alpha (q i) (flipParity (rawCanonical alpha (q i) eta) j)),
                raw_canonical_idempotent alpha (q i) _⟩ := by
            unfold rawEncode
            apply congrArg Sum.inl
            apply Subtype.ext
            simp [hf]
          rw [← he, ih .zero (flipParity eta j)]
          simp [terminalMode, markerOutput]

def rawFeature {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval)
    (w : Fin m → ℝ) (h : State) : (rawModel alpha q).Carrier → ℝ := by
  classical
  letI := (fullModel .raw alpha q).finite
  exact fun d => ∑ c, if rawEncode alpha q c = d then fullFeature .raw alpha q w h c else 0

private theorem raw_pushforward_sum {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (v : (fullModel .raw alpha q).Carrier → ℝ)
    (f : (rawModel alpha q).Carrier → ℝ) :
    (letI := (fullModel .raw alpha q).finite
     letI := (rawModel alpha q).finite
     ∑ d, (∑ c, if rawEncode alpha q c = d then v c else 0) * f d) =
    (letI := (fullModel .raw alpha q).finite
     ∑ c, v c * f (rawEncode alpha q c)) := by
  classical
  letI := (fullModel .raw alpha q).finite
  letI := (rawModel alpha q).finite
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

private theorem raw_joint_descends {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ)) (j : Side) (o : Output)
    (d : (rawModel alpha q).Carrier) (c : (fullModel .raw alpha q).Carrier) :
    (rawModel alpha q).matrix j o d (rawEncode alpha q c) =
      (letI := (fullModel .raw alpha q).finite
       ∑ e, if rawEncode alpha q e = d then (fullModel .raw alpha q).matrix j o e c else 0) := by
  classical
  letI := (fullModel .raw alpha q).finite
  have hdelta (e0 : (fullModel .raw alpha q).Carrier) (v : ℝ) :
      (∑ e, if rawEncode alpha q e = d then if e = e0 then v else 0 else 0) =
        if rawEncode alpha q e0 = d then v else 0 := by
    rw [Finset.sum_eq_single e0]
    · simp
    · intro e he hne; simp [hne]
    · simp
  have hadd (f g : (fullModel .raw alpha q).Carrier → ℝ) :
      (∑ e, if rawEncode alpha q e = d then f e + g e else 0) =
        (∑ e, if rawEncode alpha q e = d then f e else 0) +
          (∑ e, if rawEncode alpha q e = d then g e else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    rw [ite_add_ite]
    simp
  cases c with
  | inl p =>
      rcases p with ⟨i,eta⟩
      dsimp only [fullModel]
      simp only [markerOutput, if_pos rfl]
      rw [hadd]
      by_cases hz : o = .zero <;> by_cases hm : o = .rawMark <;>
        simp only [hz,hm,ite_true,ite_false,Finset.sum_const_zero,add_zero,zero_add]
      all_goals
        try simp only [hdelta]
        simp [rawModel,rawEncode,raw_canonical_rate alpha (q i) ha,
          raw_canonical_flip,eq_comm,hz,hm]
  | inr t =>
      change (if o = .reject then if d = .inr () then 1 else 0 else 0) =
        ∑ e, if rawEncode alpha q e = d then
          (if o = .reject then if e = .inr t then 1 else 0 else 0) else 0
      by_cases ho : o = .reject <;> simp only [ho,ite_true,ite_false,ite_self,Finset.sum_const_zero]
      rw [hdelta]
      simp [rawEncode,eq_comm]

private theorem raw_transport {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ)) (j : Side) (o : Output)
    (v : (fullModel .raw alpha q).Carrier → ℝ) :
    (letI := (fullModel .raw alpha q).finite
     letI := (rawModel alpha q).finite
     Matrix.mulVec ((rawModel alpha q).matrix j o)
       (fun d => ∑ c, if rawEncode alpha q c = d then v c else 0)) =
      (letI := (fullModel .raw alpha q).finite
       fun d => ∑ e, if rawEncode alpha q e = d then
         Matrix.mulVec ((fullModel .raw alpha q).matrix j o) v e else 0) := by
  classical
  letI := (fullModel .raw alpha q).finite
  letI := (rawModel alpha q).finite
  funext d
  calc
    Matrix.mulVec ((rawModel alpha q).matrix j o)
        (fun d => ∑ c, if rawEncode alpha q c = d then v c else 0) d =
        ∑ c, v c * (rawModel alpha q).matrix j o d (rawEncode alpha q c) := by
      change (∑ c, (rawModel alpha q).matrix j o d c *
        (∑ e, if rawEncode alpha q e = c then v e else 0)) = _
      simp_rw [mul_comm ((rawModel alpha q).matrix j o d _)]
      exact raw_pushforward_sum alpha q v (fun c => (rawModel alpha q).matrix j o d c)
    _ = ∑ c, v c * (∑ e, if rawEncode alpha q e = d then
        (fullModel .raw alpha q).matrix j o e c else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [raw_joint_descends alpha q ha]
    _ = ∑ e, if rawEncode alpha q e = d then
        Matrix.mulVec ((fullModel .raw alpha q).matrix j o) v e else 0 := by
      simp_rw [Finset.mul_sum,mul_ite,mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hd : rawEncode alpha q e = d <;> simp [hd,Matrix.mulVec,dotProduct,mul_comm]

private theorem raw_feature_updates {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    FeatureUpdates (rawModel alpha q) (rawFeature alpha q w) := by
  classical
  letI := (fullModel .raw alpha q).finite
  letI := (rawModel alpha q).finite
  have hu := (FiniteAtomLinearRealization.result .raw alpha q w ha hq hw hsum).2
  intro h j source
  dsimp only
  change (0 < ∑ d, Matrix.mulVec ((rawModel alpha q).matrix j (nativeStep .raw source h j).1)
    (rawFeature alpha q w h) d) → ∀ d, rawFeature alpha q w (nativeStep .raw source h j).2 d = _
  have hvect : Matrix.mulVec ((rawModel alpha q).matrix j (nativeStep .raw source h j).1)
      (rawFeature alpha q w h) =
      fun d => ∑ e, if rawEncode alpha q e = d then
        Matrix.mulVec ((fullModel .raw alpha q).matrix j (nativeStep .raw source h j).1)
          (fullFeature .raw alpha q w h) e else 0 :=
    raw_transport alpha q ha j _ (fullFeature .raw alpha q w h)
  rw [hvect]
  have hmass :
      (∑ d : (rawModel alpha q).Carrier, ∑ e, if rawEncode alpha q e = d then
        Matrix.mulVec ((fullModel .raw alpha q).matrix j (nativeStep .raw source h j).1)
          (fullFeature .raw alpha q w h) e else 0) =
      ∑ e, Matrix.mulVec ((fullModel .raw alpha q).matrix j (nativeStep .raw source h j).1)
        (fullFeature .raw alpha q w h) e := by
    rw [Finset.sum_comm]
    simp
  rw [hmass]
  intro hv d
  have hupdate := hu h j source hv
  change (∑ e : (fullModel .raw alpha q).Carrier,
      if rawEncode alpha q e = d then
        fullFeature .raw alpha q w (nativeStep .raw source h j).2 e else 0) = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hd : rawEncode alpha q e = d
  · rw [if_pos hd, if_pos hd, hupdate e]
  · rw [if_neg hd, if_neg hd, zero_div]

private theorem raw_native_bridge {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) (ha : 0 < (alpha : ℝ))
    (hq : ∀ i, 0 < (q i : ℝ)) (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    FullNativeBridge w (rawModel alpha q) (rawFeature alpha q w) := by
  classical
  letI := (fullModel .raw alpha q).finite
  letI := (rawModel alpha q).finite
  have hb := (native_finite_test_realization .raw alpha q w ha hq hw hsum).2.2.2
  intro Seed inst policy nu prob n h B hB
  dsimp only
  intro hE
  obtain ⟨hn, hp, hm, hr⟩ := hb Seed policy nu n h B hB hE
  refine ⟨?_, ?_, hm, ?_⟩
  · simpa [rawFeature] using
      (raw_pushforward_sum alpha q (fullFeature .raw alpha q w h) (fun _ => 1)).trans
        (by simpa using hn)
  · intro d
    unfold rawFeature
    apply Finset.sum_nonneg
    intro c hc
    split_ifs
    · exact hp c
    · exact le_rfl
  · intro T
    rw [hr T]
    congr 1
    simp only [rawFeature]
    rw [raw_pushforward_sum]
    simp_rw [raw_row_descends alpha q ha]

private theorem raw_component_card (alpha q : unitInterval) :
    Fintype.card {eta : Bool × Bool // rawCanonical alpha q eta = eta} =
      if (alpha : ℝ) = (1 - (alpha : ℝ)) * (q : ℝ) then 2 else 4 := by
  classical
  rw [Fintype.card_subtype]
  by_cases he : (alpha : ℝ) = (1 - (alpha : ℝ)) * (q : ℝ)
  · simp only [rawCanonical, if_pos he]
    decide
  · simp [rawCanonical, he]

private theorem raw_card {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval) :
    (letI := (rawModel alpha q).finite
     Fintype.card (rawModel alpha q).Carrier) = 4 * m - 2 * exceptionalCount alpha q + 1 := by
  classical
  change Fintype.card ({p : Fin m × (Bool × Bool) // rawCanonical alpha (q p.1) p.2 = p.2} ⊕ Unit) = _
  rw [Fintype.card_sum, Fintype.card_unit,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun i eta => rawCanonical alpha (q i) eta = eta)), Fintype.card_sigma]
  simp_rw [raw_component_card]
  have hc : (∑ i : Fin m, if (alpha : ℝ) = (1 - (alpha : ℝ)) * (q i : ℝ) then 2 else 4) +
      2 * exceptionalCount alpha q = 4 * m := by
    rw [exceptionalCount, Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    simp [ite_add_ite, Nat.mul_comm]
  omega

private theorem exceptional_count_le_one {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : (alpha : ℝ) < 1) (hq : Function.Injective q) :
    exceptionalCount alpha q ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  apply hq
  apply Subtype.ext
  have hn : 1 - (alpha : ℝ) ≠ 0 := by linarith
  exact (mul_left_cancel₀ hn (hi.symm.trans hj))
private theorem raw_probability {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ)) :
    (letI := (rawModel alpha q).finite
     letI := (rawModel alpha q).finiteOutputs
     (∀ j c, ∑ o, ∑ d, (rawModel alpha q).matrix j o d c = 1) ∧
       ∀ j o d c, 0 ≤ (rawModel alpha q).matrix j o d c) := by
  classical
  letI := (rawModel alpha q).finite
  letI := (rawModel alpha q).finiteOutputs
  have hp := (full_model_probability .raw alpha q ha).2.2
  constructor
  · intro j c
    cases c with
    | inl p => simp [rawModel, Finset.univ, Fintype.complete, Finset.sum_add_distrib]
    | inr u => simp [rawModel, Finset.univ, Fintype.complete]
  · intro j o d c
    cases c with
    | inl p =>
        have hz := hp j .zero (.inl (p.val.1, flipParity p.val.2 j)) (.inl p.val)
        have hm := hp j .rawMark (.inr (terminalIndex .raw (selectedParity p.val.2 j))) (.inl p.val)
        simp [fullModel, markerOutput] at hz hm
        dsimp [rawModel]
        split_ifs <;> linarith
    | inr u => dsimp [rawModel]; split_ifs <;> norm_num

/-- Original next-output mass is the total mass of the corresponding matrix column. -/
def OutputMassBridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (w : Fin m → ℝ) (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (policy : Policy Seed)
    (nu : Measure Seed) [IsProbabilityMeasure nu] (n : ℕ) (h : State) (B : Set Seed),
    MeasurableSet B →
    let law := nu.prod (sourceMixture alpha q w)
    let E := nativeEvent policy n h B
    0 < law.real E → ∀ (j : Side) (o : Output),
      (letI := R.finite
       law.real (E ∩ {p | (nativeStep task p.2 h j).1 = o}) =
         law.real E * ∑ d, Matrix.mulVec (R.matrix j o) (feature h) d)

private theorem native_output_mass_bridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} {w : Fin m → ℝ} (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) (hb : FullNativeBridge w R feature) :
    OutputMassBridge w R feature := by
  classical
  letI := R.finite
  letI := R.finiteOutputs
  intro Seed inst policy nu prob n h B hB
  dsimp only
  intro hE j o
  let T : Test := .query j fun o' => .read fun _ => decide (o' = o)
  have hr := (hb Seed policy nu n h B hB hE).2.2.2 T
  have he : nativeEvent policy n h B ∩ {p | nativeAccept task p.2 h T = true} =
      nativeEvent policy n h B ∩ {p | (nativeStep task p.2 h j).1 = o} := by
    ext p
    simp [T,nativeAccept]
  rw [he] at hr
  rw [hr]
  congr 1
  simp only [T,testRow]
  simp [mul_ite,Finset.sum_ite_irrel]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Matrix.mulVec,dotProduct,mul_comm]

/-- Scaling the next feature by its actual event mass gives unnormalized transport. -/
def UnnormalizedBridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (w : Fin m → ℝ) (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (policy : Policy Seed)
    (nu : Measure Seed) [IsProbabilityMeasure nu] (n : ℕ) (h : State) (B : Set Seed),
    MeasurableSet B →
    let law := nu.prod (sourceMixture alpha q w)
    let E := nativeEvent policy n h B
    0 < law.real E → ∀ (j : Side) (source : Source),
      (letI := R.finite
       let step := nativeStep task source h j
       let v := Matrix.mulVec (R.matrix j step.1) (feature h)
       0 < (∑ d, v d) → ∀ d,
         law.real (E ∩ {p | (nativeStep task p.2 h j).1 = step.1}) * feature step.2 d =
           law.real E * v d)

private theorem native_unnormalized_bridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} {w : Fin m → ℝ} (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) (hm : OutputMassBridge w R feature)
    (hu : FeatureUpdates R feature) : UnnormalizedBridge w R feature := by
  intro Seed inst policy nu prob n h B hB
  dsimp only
  intro hE j source hv d
  rw [hm Seed policy nu n h B hB hE j _, hu h j source hv d]
  field_simp [hv.ne']

/-- A fresh independent random seed samples a measurable family of finite tests. -/
def RandomNativeBridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (w : Fin m → ℝ) (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) : Prop :=
  ∀ (Seed : Type) [MeasurableSpace Seed] (policy : Policy Seed)
    (nu : Measure Seed) [IsProbabilityMeasure nu] (n : ℕ) (h : State) (B : Set Seed),
    MeasurableSet B →
    let law := nu.prod (sourceMixture alpha q w)
    let E := nativeEvent policy n h B
    0 < law.real E →
    ∀ (Fresh : Type) [MeasurableSpace Fresh] (rho : Measure Fresh) [IsProbabilityMeasure rho]
      (tests : Fresh → Test), Measurable[(inferInstance : MeasurableSpace Fresh), ⊤] tests →
      MeasurableSet {p : Fresh × (Seed × Source) |
        p.2 ∈ E ∧ nativeAccept task p.2.2 h (tests p.1) = true} →
      (letI := R.finite
       (rho.prod law).real {p | p.2 ∈ E ∧ nativeAccept task p.2.2 h (tests p.1) = true} =
         law.real E * ∑ c, feature h c * (∫ u, testRow R (tests u) c ∂rho))

private theorem test_row_bounds {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} (R : MassModel task alpha q)
    (hn : letI := R.finite; letI := R.finiteOutputs; ∀ j c, ∑ o, ∑ d, R.matrix j o d c = 1)
    (hp : ∀ j o d c, 0 ≤ R.matrix j o d c) (T : Test) (c : R.Carrier) :
    0 ≤ testRow R T c ∧ testRow R T c ≤ 1 := by
  classical
  letI := R.finite
  letI := R.finiteOutputs
  induction T generalizing c with
  | read accept => simp only [testRow]; split_ifs <;> norm_num
  | inspect next ih => exact ih (R.mode c) c
  | query j next ih =>
      constructor
      · exact Finset.sum_nonneg fun o _ => Finset.sum_nonneg fun d _ =>
          mul_nonneg (hp j o d c) (ih o d).1
      · calc
          testRow R (.query j next) c ≤ ∑ o, ∑ d, R.matrix j o d c :=
            Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun d _ =>
              mul_le_of_le_one_right (hp j o d c) (ih o d).2
          _ = 1 := hn j c

private theorem random_native_bridge {m : ℕ} {task : Task} {alpha : unitInterval}
    {q : Fin m → unitInterval} {w : Fin m → ℝ} (R : MassModel task alpha q)
    (feature : State → R.Carrier → ℝ) (hb : FullNativeBridge w R feature)
    (hn : letI := R.finite; letI := R.finiteOutputs; ∀ j c, ∑ o, ∑ d, R.matrix j o d c = 1)
    (hp : ∀ j o d c, 0 ≤ R.matrix j o d c) : RandomNativeBridge w R feature := by
  classical
  letI := R.finite
  intro Seed inst policy nu prob n h B hB
  dsimp only
  intro hE Fresh instFresh rho probFresh tests htests hmeas
  letI : IsFiniteMeasure (sourceMixture alpha q w) := by unfold sourceMixture; infer_instance
  have hr := (hb Seed policy nu n h B hB hE).2.2.2
  have hi (c : R.Carrier) : Integrable (fun u => testRow R (tests u) c) rho := by
    have hm : Measurable (fun u => testRow R (tests u) c) :=
      (measurable_from_top (f := fun T : Test => testRow R T c)).comp htests
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun u => ?_)
    have hbound := test_row_bounds R hn hp (tests u) c
    simpa [Real.norm_eq_abs,abs_of_nonneg hbound.1] using hbound.2
  rw [measureReal_def, Measure.prod_apply hmeas]
  rw [← integral_toReal (measurable_measure_prodMk_left hmeas).aemeasurable
    (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
  change (∫ u, (nu.prod (sourceMixture alpha q w)).real
    (nativeEvent policy n h B ∩ {p | nativeAccept task p.2 h (tests u) = true}) ∂rho) = _
  simp_rw [hr]
  rw [integral_const_mul, integral_finsetSum _ (fun c _ => (hi c).const_mul _)]
  simp only [integral_const_mul]

private theorem conditional_source_support (q : unitInterval) (root : Bool) :
    ∀ᵐ source ∂conditionalSourceLaw q root, noAdjacentOnes source := by
  unfold conditionalSourceLaw
  have hmeas : MeasurableSet {s : Source | noAdjacentOnes s} := by
    unfold noAdjacentOnes
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun n => ?_
    cases n <;> cases j <;> simp only [endpoint,arm] <;> measurability
  apply (ae_map_iff (by fun_prop) hmeas).mpr
  filter_upwards [paired_path_support q root] with p hp
  intro j n
  cases n with
  | zero =>
      cases j
      · simpa [endpoint, arm, hp.1.1] using hp.1.2 0
      · simpa [endpoint, arm, hp.2.1] using hp.2.2 0
  | succ n =>
      cases j
      · simpa [endpoint, arm] using hp.1.2 (n + 1)
      · simpa [endpoint, arm] using hp.2.2 (n + 1)

private theorem marker_recovers_root (source : Source) (hn : noAdjacentOnes source)
    (actions : List Side) (replies : List Bool) (j : Side)
    (hp : prefixNoMarker source actions)
    (hm : markerResponse source j (sideCount actions j) = true) :
    recoveredRoot ⟨j :: actions, true :: replies, true⟩ = source.1 := by
  have hx : ∀ i, ¬(endpoint source j i = true ∧ endpoint source j (i + 1) = true) := by
    simpa only [endpoint] using hn j
  have hz : ∀ i < sideCount actions j,
      ¬(endpoint source j i = false ∧ endpoint source j (i + 1) = false) := by
    intro i hi
    have hi' := hp j i hi
    change ¬(endpoint source j i = false ∧ arm source j i = false)
    exact of_decide_eq_false hi'
  have he := (hchar source.1 (endpoint source j) rfl hx (sideCount actions j)).mp hz
    (sideCount actions j) le_rfl
  have hm' := of_decide_eq_true hm
  have hb : alternatingBit source.1 (sideCount actions j) = false := he.symm.trans hm'.1
  have hmod := Nat.mod_two_eq_zero_or_one (sideCount actions j)
  change decide (sideCount actions j % 2 = 1) = source.1
  cases hr : source.1 <;> rcases hmod with hmod | hmod <;>
    simp [alternatingBit,hr,hmod] at hb ⊢

private theorem stopped_root_recovery {Seed : Type} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (source : Source) (hn : noAdjacentOnes source)
    (n : ℕ) : (actualRun policy seed source n).stopped = true →
      recoveredRoot (actualRun policy seed source n) = source.1 := by
  induction n with
  | zero => simp [actualRun]
  | succ n ih =>
      cases hs : (actualRun policy seed source n).stopped with
      | true => simpa [actualRun,hs] using ih hs
      | false =>
          have hb := stopped_execution_replay_bridge policy seed source n
          have hp : prefixNoMarker source (actualRun policy seed source n).actions := by
            rw [(hb.2.2.1 hs).1]
            exact hb.2.1.mp hs
          simp only [actualRun,hs,Bool.false_eq_true,↓reduceIte]
          intro hm
          exact marker_recovers_root source hn (actualRun policy seed source n).actions
            (actualRun policy seed source n).replies (policy.choose seed
              (actualRun policy seed source n).actions (actualRun policy seed source n).replies) hp hm

/-- The recovered terminal bit is coupled to the original root on its source law. -/
def RootCoupling {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval)
    (w : Fin m → ℝ) : Prop :=
  ∀ᵐ source ∂sourceMixture alpha q w,
    ∀ (Seed : Type) [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed) (n : ℕ),
      (actualRun policy seed source n).stopped = true →
        recoveredRoot (actualRun policy seed source n) = source.1

private theorem source_root_coupling {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (w : Fin m → ℝ) : RootCoupling alpha q w := by
  have hn : ∀ᵐ source ∂sourceMixture alpha q w, noAdjacentOnes source := by
    rw [sourceMixture, ae_finsetSum_measure_iff]
    intro i hi
    apply Measure.ae_smul_measure
    rw [sourceLaw, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (conditional_source_support (q i) true) _,
      Measure.ae_smul_measure (conditional_source_support (q i) false) _⟩
  filter_upwards [hn] with source hs
  intro Seed inst policy seed n
  exact stopped_root_recovery policy seed source hs n

/-- The complete finite-atom upper bound includes normalized columns and native tests. -/
def Proposition278 : Prop :=
  ∀ (m : ℕ) (alpha : unitInterval) (q : Fin m → unitInterval) (w : Fin m → ℝ),
    0 < (alpha : ℝ) → (alpha : ℝ) < 1 →
    (∀ i, 0 < (q i : ℝ) ∧ (q i : ℝ) < 1) → Function.Injective q →
    (∀ i, 0 < w i) → (∑ i, w i) = 1 →
    exceptionalCount alpha q ≤ 1 ∧
      ∀ task : Task, ∃ (R : MassModel task alpha q) (feature : State → R.Carrier → ℝ),
        (letI := R.finite
         letI := R.finiteOutputs
         Fintype.card R.Carrier = desiredCard task alpha q ∧
           (∀ j c, ∑ o, ∑ d, R.matrix j o d c = 1) ∧
           (∀ j o d c, 0 ≤ R.matrix j o d c)) ∧ FullNativeBridge w R feature ∧ FeatureUpdates R feature ∧ RandomNativeBridge w R feature ∧
          OutputMassBridge w R feature ∧ UnnormalizedBridge w R feature


/-- Exact finite native-test dimensions for all three interfaces. -/
theorem result : Proposition278 ∧
    (∀ (m : ℕ) (alpha : unitInterval) (q : Fin m → unitInterval) (w : Fin m → ℝ),
      RootCoupling alpha q w) := by
  refine ⟨?_, fun _ alpha q w => source_root_coupling alpha q w⟩
  classical
  intro m alpha q w ha ha' hq hi hw hw'
  refine ⟨exceptional_count_le_one alpha q ha' hi, ?_⟩
  intro task
  cases task with
  | retained =>
      obtain ⟨⟨hc, hn, hp, hb⟩, hu⟩ := FiniteAtomLinearRealization.result .retained alpha q w ha
        (fun i => (hq i).1) hw hw'
      exact ⟨fullModel .retained alpha q, fullFeature .retained alpha q w,
        ⟨by simpa [desiredCard, terminalCount] using hc, hn, hp⟩, hb, hu, random_native_bridge _ _ hb hn hp,
        native_output_mass_bridge _ _ hb,
        native_unnormalized_bridge _ _ (native_output_mass_bridge _ _ hb) hu⟩
  | emitted =>
      obtain ⟨⟨hc, hn, hp, hb⟩, hu⟩ := FiniteAtomLinearRealization.result .emitted alpha q w ha
        (fun i => (hq i).1) hw hw'
      exact ⟨fullModel .emitted alpha q, fullFeature .emitted alpha q w,
        ⟨by simpa [desiredCard, terminalCount] using hc, hn, hp⟩, hb, hu, random_native_bridge _ _ hb hn hp,
        native_output_mass_bridge _ _ hb,
        native_unnormalized_bridge _ _ (native_output_mass_bridge _ _ hb) hu⟩
  | raw =>
      obtain ⟨hn, hp⟩ := raw_probability alpha q ha
      have hb := raw_native_bridge alpha q w ha (fun i => (hq i).1) hw hw'
      exact ⟨rawModel alpha q, rawFeature alpha q w,
        ⟨raw_card alpha q, hn, hp⟩, hb,
        raw_feature_updates alpha q w ha (fun i => (hq i).1) hw hw',
        random_native_bridge (rawModel alpha q) (rawFeature alpha q w) hb hn hp,
        native_output_mass_bridge _ _ hb,
        native_unnormalized_bridge _ _ (native_output_mass_bridge _ _ hb)
          (raw_feature_updates alpha q w ha (fun i => (hq i).1) hw hw')⟩



end D5.S3.Observer.ProbabilisticClosure.RawFiniteAtomLinearRealization
