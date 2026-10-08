/- GID: D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite tests descend through the exceptional parity quotient. -/

import D5.S3.Observer.ProbabilisticClosure.FiniteAtomLinearRealization
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
    cases l <;> cases r <;> cases j <;>
      simp [markerRate, rootMass, denominator, selectedParity] at hd hc ⊢ <;>
      field_simp [hd,hc] <;> nlinarith [hb]
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
def rawSection {m : ℕ} (alpha : unitInterval) (q : Fin m → unitInterval) :
    (rawModel alpha q).Carrier → (fullModel .raw alpha q).Carrier
  | .inl p => .inl p.val
  | .inr _ => .inr ⟨0, by simp [terminalCount]⟩

private theorem raw_matrix_pushforward {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (j : Side) (o : Output)
    (d c : (rawModel alpha q).Carrier) :
    (rawModel alpha q).matrix j o d c =
      (letI := (fullModel .raw alpha q).finite
       ∑ e, if rawEncode alpha q e = d then
         (fullModel .raw alpha q).matrix j o e (rawSection alpha q c) else 0) := by
  classical
  letI := (fullModel .raw alpha q).finite
  cases c with
  | inl p =>
      change _ = ∑ e, if rawEncode alpha q e = d then
        ((if o = .zero then
          if e = .inl (p.val.1, flipParity p.val.2 j) then
            1 - markerRate alpha (q p.val.1) p.val.2 j else 0 else 0) +
         (if o = .rawMark then
          if e = .inr (terminalIndex .raw (selectedParity p.val.2 j)) then
            markerRate alpha (q p.val.1) p.val.2 j else 0 else 0)) else 0
      simp_rw [ite_add]
      rw [Finset.sum_add_distrib]
      by_cases hz : o = .zero <;> by_cases hm : o = .rawMark <;>
        simp only [hz, hm, ite_true, ite_false, Finset.sum_const_zero, add_zero, zero_add]
      all_goals
        simp_rw [ite_comm (rawEncode alpha q _ = d) (_ = _)]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp [rawModel, rawEncode, p.property, eq_comm]
  | inr u =>
      change _ = ∑ e, if rawEncode alpha q e = d then
        (if o = .reject then
          if e = .inr (⟨0, by simp [terminalCount]⟩ : Fin (terminalCount .raw)) then 1 else 0
         else 0) else 0
      by_cases ho : o = .reject
      · simp only [ho, ite_true]
        simp_rw [ite_comm (rawEncode alpha q _ = d) (_ = _)]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        cases u
        simp [rawModel, rawEncode, ho, eq_comm]
      · simp only [ho, ite_false, Finset.sum_const_zero]
        simp [rawModel, ho]

private theorem raw_probability {m : ℕ} (alpha : unitInterval)
    (q : Fin m → unitInterval) (ha : 0 < (alpha : ℝ)) :
    (letI := (rawModel alpha q).finite
     letI := (rawModel alpha q).finiteOutputs
     (∀ j c, ∑ o, ∑ d, (rawModel alpha q).matrix j o d c = 1) ∧
       ∀ j o d c, 0 ≤ (rawModel alpha q).matrix j o d c) := by
  classical
  letI := (fullModel .raw alpha q).finite
  letI := (fullModel .raw alpha q).finiteOutputs
  letI := (rawModel alpha q).finite
  obtain ⟨hc, hn, hp⟩ := full_model_probability .raw alpha q ha
  constructor
  · intro j c
    change (∑ o, ∑ d, (rawModel alpha q).matrix j o d c) = 1
    simp_rw [raw_matrix_pushforward]
    have he (o : Output) :
        (∑ d, ∑ e, if rawEncode alpha q e = d then
          (fullModel .raw alpha q).matrix j o e (rawSection alpha q c) else 0) =
        ∑ e, (fullModel .raw alpha q).matrix j o e (rawSection alpha q c) := by
      rw [Finset.sum_comm]
      simp
    simp_rw [he]
    exact hn j (rawSection alpha q c)
  · intro j o d c
    rw [raw_matrix_pushforward]
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · exact hp j o e (rawSection alpha q c)
    · exact le_rfl

/-- Exact finite deterministic native-test dimensions for all three interfaces. -/
theorem result : Proposition278 := by
  classical
  intro m alpha q w ha ha' hq hi hw hw'
  refine ⟨exceptional_count_le_one alpha q ha' hi, ?_⟩
  intro task
  cases task with
  | retained =>
      obtain ⟨hc, hn, hp, hb⟩ := native_finite_test_realization .retained alpha q w ha
        (fun i => (hq i).1) hw hw'
      exact ⟨fullModel .retained alpha q, fullFeature .retained alpha q w,
        ⟨by simpa [desiredCard, terminalCount] using hc, hn, hp⟩, hb⟩
  | emitted =>
      obtain ⟨hc, hn, hp, hb⟩ := native_finite_test_realization .emitted alpha q w ha
        (fun i => (hq i).1) hw hw'
      exact ⟨fullModel .emitted alpha q, fullFeature .emitted alpha q w,
        ⟨by simpa [desiredCard, terminalCount] using hc, hn, hp⟩, hb⟩
  | raw =>
      obtain ⟨hn, hp⟩ := raw_probability alpha q ha
      exact ⟨rawModel alpha q, rawFeature alpha q w,
        ⟨raw_card alpha q, hn, hp⟩,
        raw_native_bridge alpha q w ha (fun i => (hq i).1) hw hw'⟩


end D5.S3.Observer.ProbabilisticClosure.RawFiniteAtomLinearRealization
