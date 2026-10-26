/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.SignVariations, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.Data.List.Range]
   utility: none
   digest: Ordered cosine bases and sine-product expressions for absolute-cosine Fourier gaps. -/

import D5.S3.Quantum.Matrix.JainAbsCosine.Defs
import Mathlib.Data.List.SignVariations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.List.Range

/-! Ordered trigonometric samples and exact coefficient variation counts. -/

open scoped BigOperators
open SignType
open D5.S3.Quantum.Matrix.JainAbsCosine.Defs

namespace D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges

private lemma angle_pos (m : ℕ) : 0 < angle m := by
  unfold angle
  exact div_pos Real.pi_pos (by positivity)

private lemma sample_phase_bounds {m l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ m) :
    0 < (l : ℝ) * angle m ∧ (l : ℝ) * angle m < Real.pi / 2 := by
  have hd : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hl' : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hlm' : (l : ℝ) ≤ m := by exact_mod_cast hlm
  refine ⟨mul_pos hl' (angle_pos m), ?_⟩
  rw [angle, ← mul_div_assoc, div_lt_iff₀ hd]
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hlm' Real.pi_pos.le]

/-- The cosine bases lie strictly between zero and one in their sampling order. -/
theorem cosine_base_bounds {m l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ m) :
    0 < Real.cos ((l : ℝ) * angle m) ∧ Real.cos ((l : ℝ) * angle m) < 1 := by
  have hb := sample_phase_bounds hl hlm
  constructor
  · apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos], hb.2⟩
  · simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by norm_num : (0 : ℝ) ≤ 0)
        hb.2.le hb.1

/-- Increasing sample indices strictly decrease the positive cosine base. -/
theorem cosine_base_strictAnti {m a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbm : b ≤ m) :
    Real.cos ((b : ℝ) * angle m) < Real.cos ((a : ℝ) * angle m) := by
  have hb := sample_phase_bounds (show 1 ≤ b by omega) hbm
  have ha' := sample_phase_bounds ha (show a ≤ m by omega)
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two ha'.1.le hb.2.le
    (mul_lt_mul_of_pos_right (by exact_mod_cast hab) (angle_pos m))

/-- The logarithms are strictly negative and strictly decrease in sampling order. -/
theorem logarithmic_exponent_order {m a b : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hbm : b ≤ m) :
    Real.log (Real.cos ((b : ℝ) * angle m)) <
      Real.log (Real.cos ((a : ℝ) * angle m)) ∧
    Real.log (Real.cos ((a : ℝ) * angle m)) < 0 := by
  have hb := cosine_base_bounds (show 1 ≤ b by omega) hbm
  have ha' := cosine_base_bounds ha (show a ≤ m by omega)
  exact ⟨Real.log_lt_log hb.1 (cosine_base_strictAnti ha hab hbm),
    Real.log_neg ha'.1 ha'.2⟩

/-- The difference between two Fourier modes is a sine-product sum. -/
theorem modeValue_sub (m j d : ℕ) (r : ℝ) :
    modeValue m j r - modeValue m (j + d) r =
      4 * ∑ l ∈ Finset.Icc 1 m,
        Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m) *
        Real.sin ((d : ℝ) * (l : ℝ) * angle m) *
        Real.cos ((l : ℝ) * angle m) ^ r := by
  unfold modeValue
  rw [show (1 + 2 * ∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r) -
      (1 + 2 * ∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * ((j + d : ℕ) : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r) =
      2 * ((∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r) -
      ∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * ((j + d : ℕ) : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r) by ring,
      ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hc := Real.cos_sub_cos (2 * (j : ℝ) * (l : ℝ) * angle m)
    (2 * ((j + d : ℕ) : ℝ) * (l : ℝ) * angle m)
  have hsum : (2 * (j : ℝ) * (l : ℝ) * angle m +
      2 * ((j + d : ℕ) : ℝ) * (l : ℝ) * angle m) / 2 =
      ((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m := by push_cast; ring
  have hdiff : (2 * (j : ℝ) * (l : ℝ) * angle m -
      2 * ((j + d : ℕ) : ℝ) * (l : ℝ) * angle m) / 2 =
      -((d : ℝ) * (l : ℝ) * angle m) := by push_cast; ring
  rw [hsum, hdiff, Real.sin_neg] at hc
  linear_combination (2 * Real.cos ((l : ℝ) * angle m) ^ r) * hc

/-- The short sine factor in each gap coefficient is positive. -/
theorem gap_short_sine_pos {m d l : ℕ} (hd : d = 1 ∨ d = 2)
    (hl : 1 ≤ l) (hlm : l ≤ m) :
    0 < Real.sin ((d : ℝ) * (l : ℝ) * angle m) := by
  have hb := sample_phase_bounds hl hlm
  apply Real.sin_pos_of_pos_of_lt_pi
  · rcases hd with rfl | rfl <;> norm_num <;> nlinarith
  · rcases hd with rfl | rfl <;> norm_num <;> nlinarith

private theorem alternating_rank_sign_ne (a : ℕ) :
    sign ((-1 : ℝ) ^ a) ≠ sign ((-1 : ℝ) ^ (a + 1)) := by
  rw [pow_succ, mul_neg_one, Left.sign_neg]
  have hn : sign ((-1 : ℝ) ^ a) ≠ 0 :=
    sign_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  generalize hs : sign ((-1 : ℝ) ^ a) = z at *
  cases z <;> simp_all

private theorem signVariations_alternating_ranks (l : List ℕ) (a b : ℕ)
    (hab : a ≤ b) (hsorted : l.Pairwise (· ≤ ·))
    (himage : ∀ k, k ∈ l ↔ a ≤ k ∧ k ≤ b) :
    List.signVariations (l.map fun k => (-1 : ℝ) ^ k) = b - a := by
  induction l generalizing a b with
  | nil =>
      have h := (himage a).2 ⟨le_rfl, hab⟩
      simp at h
  | cons c l ih =>
      have hca : c = a := by
        have hc := (himage c).1 (by simp)
        have ha := (himage a).2 ⟨le_rfl, hab⟩
        rcases List.mem_cons.1 ha with h | h
        · omega
        · have := (List.pairwise_cons.1 hsorted).1 _ h
          omega
      subst c
      cases l with
      | nil =>
          have hb := (himage b).2 ⟨hab, le_rfl⟩
          have hba : b = a := by simpa using hb
          subst b
          simp
      | cons c l =>
          obtain ⟨hfirst, htail⟩ := List.pairwise_cons.1 hsorted
          have hc := (himage c).1 (by simp)
          have hstep : c = a ∨ c = a + 1 := by
            by_cases hca : c = a
            · exact Or.inl hca
            · have hac : a + 1 ≤ c := by omega
              have hamem := (himage (a + 1)).2 ⟨by omega, by omega⟩
              have hamem' : a + 1 ∈ c :: l := by
                rcases List.mem_cons.1 hamem with h | h
                · omega
                · exact h
              have hle : c ≤ a + 1 := by
                rcases List.mem_cons.1 hamem' with h | h
                · omega
                · exact (List.pairwise_cons.1 htail).1 _ h
              exact Or.inr (by omega)
          have himage' : ∀ k, k ∈ c :: l ↔ c ≤ k ∧ k ≤ b := by
            intro k
            constructor
            · intro hk
              have hk' := (himage k).1 (List.mem_cons_of_mem _ hk)
              refine ⟨?_, hk'.2⟩
              rcases List.mem_cons.1 hk with rfl | hk
              · exact le_rfl
              · exact (List.pairwise_cons.1 htail).1 _ hk
            · rintro ⟨hck, hkb⟩
              have hk := (himage k).2 ⟨by omega, hkb⟩
              rcases List.mem_cons.1 hk with h | h
              · have hkc : k = c := by omega
                simp [hkc]
              · exact h
          have hi := ih c b hc.2 htail himage'
          simp only [List.map_cons]
          rw [List.signVariations_cons_cons_of_ne_zero _
            (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))]
          change List.signVariations ((c :: l).map fun k => (-1 : ℝ) ^ k) + _ = _
          rw [hi]
          rcases hstep with rfl | rfl
          · simp
          · rw [if_neg (alternating_rank_sign_ne a)]
            omega


private lemma sine_interval_sign {x : ℝ} {k : ℕ}
    (hx : (k : ℝ) * Real.pi < x) (hx' : x < (k + 1 : ℝ) * Real.pi) :
    SignType.sign (Real.sin x) = SignType.sign ((-1 : ℝ) ^ k) ∧ Real.sin x ≠ 0 := by
  have hp : 0 < Real.sin (x - (k : ℝ) * Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have he : Real.sin x = (-1 : ℝ) ^ k * Real.sin (x - (k : ℝ) * Real.pi) := by
    convert Real.sin_add_nat_mul_pi (x - (k : ℝ) * Real.pi) k using 1 <;> congr 1 <;> ring
  rw [he]
  exact ⟨by rw [sign_mul, sign_eq_one_iff.mpr hp, mul_one],
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hp.ne'⟩

private lemma sine_floor_sign {x : ℝ} (hx : 0 < x) (hn : Real.sin x ≠ 0) :
    SignType.sign (Real.sin x) = SignType.sign ((-1 : ℝ) ^ ⌊x / Real.pi⌋₊) := by
  have hlo : (⌊x / Real.pi⌋₊ : ℝ) * Real.pi ≤ x := by
    exact (le_div_iff₀ Real.pi_pos).mp (Nat.floor_le (div_nonneg hx.le Real.pi_pos.le))
  have hhi : x < (⌊x / Real.pi⌋₊ + 1 : ℝ) * Real.pi := by
    exact (div_lt_iff₀ Real.pi_pos).mp (Nat.lt_floor_add_one (x / Real.pi))
  have hstrict : (⌊x / Real.pi⌋₊ : ℝ) * Real.pi < x := by
    refine lt_of_le_of_ne hlo ?_
    intro he
    apply hn
    rw [← he, Real.sin_nat_mul_pi]
  exact (sine_interval_sign hstrict hhi).1

private lemma sine_rank_image {x α : ℝ} {N j : ℕ}
    (hx : 0 < x) (hxπ : x < Real.pi) (hα : 0 < α) (hαπ : α < Real.pi)
    (hlo : (j : ℝ) * Real.pi < x + (N : ℝ) * α)
    (hhi : x + (N : ℝ) * α < (j + 1 : ℝ) * Real.pi) :
    ∀ k : ℕ, k ∈ ((List.range (N + 1)).filter
      (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α) ≠ 0)).map
      (fun (i : ℕ) => ⌊(x + (i : ℝ) * α) / Real.pi⌋₊) ↔ k ≤ j := by
  classical
  intro k
  constructor
  · intro hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hi, _⟩ := List.mem_filter.mp hi
    have hiN : i ≤ N := by have := List.mem_range.mp hi; omega
    have hipos : 0 ≤ x + (i : ℝ) * α := by positivity
    have hiphase : x + (i : ℝ) * α < (j + 1 : ℝ) * Real.pi := by
      have : (i : ℝ) ≤ N := by exact_mod_cast hiN
      exact lt_of_le_of_lt (by linarith [mul_le_mul_of_nonneg_right this hα.le]) hhi
    have hfloor : ⌊(x + (i : ℝ) * α) / Real.pi⌋₊ < j + 1 :=
      (Nat.floor_lt (div_nonneg hipos Real.pi_pos.le)).mpr
        (by rw [Nat.cast_add, Nat.cast_one]; exact (div_lt_iff₀ Real.pi_pos).mpr hiphase)
    omega
  · intro hkj
    have hex : ∃ i : ℕ, (k : ℝ) * Real.pi < x + (i : ℝ) * α := by
      refine ⟨N, ?_⟩
      have : (k : ℝ) ≤ j := by exact_mod_cast hkj
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right this Real.pi_pos.le) hlo
    let i := Nat.find hex
    have hi : (k : ℝ) * Real.pi < x + (i : ℝ) * α := Nat.find_spec hex
    have hiN : i ≤ N := Nat.find_min' hex (by
      have : (k : ℝ) ≤ j := by exact_mod_cast hkj
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right this Real.pi_pos.le) hlo)
    have hiupper : x + (i : ℝ) * α < (k + 1 : ℝ) * Real.pi := by
      by_cases hiz : i = 0
      · have hkpi := mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le
        simpa only [hiz, Nat.cast_zero, zero_mul, add_zero] using
          (show x < (k + 1 : ℝ) * Real.pi by nlinarith)
      · have hpred : ¬ (k : ℝ) * Real.pi < x + ((i - 1 : ℕ) : ℝ) * α :=
          Nat.find_min hex (show i - 1 < Nat.find hex by dsimp [i] at *; omega)
        have hicast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub (show 1 ≤ i by omega)]; norm_num
        rw [hicast] at hpred
        push_neg at hpred
        nlinarith
    have hisin : Real.sin (x + (i : ℝ) * α) ≠ 0 := (sine_interval_sign hi hiupper).2
    apply List.mem_map.mpr
    refine ⟨i, List.mem_filter.mpr ⟨?_, by simpa using hisin⟩, ?_⟩
    · simp only [List.mem_range]
      omega
    · apply (Nat.floor_eq_iff (by positivity : 0 ≤ (x + (i : ℝ) * α) / Real.pi)).mpr
      constructor
      · exact (le_div_iff₀ Real.pi_pos).mpr hi.le
      · exact (div_lt_iff₀ Real.pi_pos).mpr hiupper

private lemma sampled_sine_signVariations {x α : ℝ} {N j : ℕ}
    (hx : 0 < x) (hxπ : x < Real.pi) (hα : 0 < α) (hαπ : α < Real.pi)
    (hlo : (j : ℝ) * Real.pi < x + (N : ℝ) * α)
    (hhi : x + (N : ℝ) * α < (j + 1 : ℝ) * Real.pi) :
    List.signVariations ((List.range (N + 1)).map (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α))) = j := by
  classical
  let samples : List ℕ := (List.range (N + 1)).filter (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α) ≠ 0)
  let ranks := samples.map (fun (i : ℕ) => ⌊(x + (i : ℝ) * α) / Real.pi⌋₊)
  have himage : ∀ k, k ∈ ranks ↔ 0 ≤ k ∧ k ≤ j := by
    intro k
    simpa only [Nat.zero_le, true_and] using sine_rank_image hx hxπ hα hαπ hlo hhi k
  have hsorted : ranks.Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    apply ((List.pairwise_lt_range (n := N + 1)).filter _).imp
    intro a b hab
    apply Nat.floor_mono
    apply (div_le_div_iff_of_pos_right Real.pi_pos).mpr
    have : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right this hα.le) x
  have heq : List.signVariations (samples.map (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α))) =
      List.signVariations (ranks.map fun k => (-1 : ℝ) ^ k) := by
    apply List.signVariations_congr
    simp only [ranks, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    obtain ⟨_, hsin⟩ := List.mem_filter.mp hi
    exact sine_floor_sign (by positivity) (by simpa using hsin)
  have hfilter : samples.map (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α)) =
      ((List.range (N + 1)).map (fun (i : ℕ) => Real.sin (x + (i : ℝ) * α))).filter
        (fun y => !decide (y = 0)) := by
    simp [samples, List.filter_map, Function.comp_def]
  rw [← List.signVariations_filter_ne_zero, ← hfilter, heq]
  simpa using signVariations_alternating_ranks ranks 0 j (Nat.zero_le _) hsorted himage

/-- Exactly `j` changes occur in the coefficients of a single nonconstant mode. -/
theorem mode_coefficients_signVariations {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    List.signVariations (1 :: ((List.range' 1 m).map
      (fun (l : ℕ) => 2 * Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m)))) = j := by
  have hd : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
  have hα : 0 < 2 * (j : ℝ) * angle m := by exact mul_pos (mul_pos (by norm_num) hjpos) (angle_pos m)
  have hαπ : 2 * (j : ℝ) * angle m < Real.pi := by
    rw [angle, ← mul_div_assoc, div_lt_iff₀ hd]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hjm' Real.pi_pos.le]
  have he : (Real.pi / 2 + (m : ℝ) * (2 * (j : ℝ) * angle m)) *
      (2 * (m : ℝ) + 1) = Real.pi / 2 * (2 * (m : ℝ) + 1) +
      2 * (m : ℝ) * (j : ℝ) * Real.pi := by
    unfold angle
    field_simp [ne_of_gt hd]
    <;> ring
  have hlo : (j : ℝ) * Real.pi < Real.pi / 2 + (m : ℝ) * (2 * (j : ℝ) * angle m) := by
    apply (mul_lt_mul_iff_left₀ hd).mp
    rw [he]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hjm' Real.pi_pos.le]
  have hhi : Real.pi / 2 + (m : ℝ) * (2 * (j : ℝ) * angle m) <
      (j + 1 : ℝ) * Real.pi := by
    apply (mul_lt_mul_iff_left₀ hd).mp
    rw [he]
    nlinarith [Real.pi_pos, mul_pos hjpos Real.pi_pos,
      mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le]
  have hs := sampled_sine_signVariations (N := m) (j := j)
    (show 0 < Real.pi / 2 by positivity) (show Real.pi / 2 < Real.pi by linarith [Real.pi_pos])
    hα hαπ hlo hhi
  have hlist : (List.range (m + 1)).map (fun (i : ℕ) => Real.sin (Real.pi / 2 + (i : ℝ) *
      (2 * (j : ℝ) * angle m))) =
      1 :: ((List.range' 1 m).map (fun (l : ℕ) => Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m))) := by
    rw [List.range_succ_eq_map, List.range'_eq_map_range]
    simp only [List.map_cons, List.map_map, Nat.cast_zero, zero_mul, add_zero, Real.sin_pi_div_two, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    push_cast
    rw [show Real.pi / 2 + ((i : ℝ) + 1) * (2 * (j : ℝ) * angle m) =
      2 * (j : ℝ) * (1 + (i : ℝ)) * angle m + Real.pi / 2 by ring, Real.sin_add_pi_div_two]
  rw [hlist] at hs
  calc
    _ = List.signVariations (1 :: ((List.range' 1 m).map
        (fun (l : ℕ) => Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m)))) := by
      apply List.signVariations_congr
      simp only [List.map_cons, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [sign_mul, sign_eq_one_iff.mpr (by norm_num : (0 : ℝ) < 2), one_mul]
    _ = j := hs

/-- The first long sine phase in either short gap lies strictly between zero and pi. -/
theorem gap_first_phase_bounds {m j d : ℕ} (hj : 1 ≤ j)
    (hd : d = 1 ∨ d = 2) (hjdm : j + d ≤ m) :
    0 < ((2 * j + d : ℕ) : ℝ) * angle m ∧
      ((2 * j + d : ℕ) : ℝ) * angle m < Real.pi := by
  have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hα : 0 < ((2 * j + d : ℕ) : ℝ) * angle m := by
    have : 0 < 2 * j + d := by omega
    exact mul_pos (by exact_mod_cast this) (angle_pos m)
  have hαπ : ((2 * j + d : ℕ) : ℝ) * angle m < Real.pi := by
    rw [angle, ← mul_div_assoc, div_lt_iff₀ hden]
    have : 2 * j + d < 2 * m + 1 := by rcases hd with rfl | rfl <;> omega
    have hc : ((2 * j + d : ℕ) : ℝ) < 2 * (m : ℝ) + 1 := by exact_mod_cast this
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right hc Real.pi_pos]
  exact ⟨hα, hαπ⟩

/-- Both short-gap coefficient sequences have exactly `j` sign changes, with zero entries ignored. -/
theorem gap_coefficients_signVariations {m j d : ℕ} (hj : 1 ≤ j)
    (hd : d = 1 ∨ d = 2) (hjdm : j + d ≤ m) :
    List.signVariations ((List.range' 1 m).map (fun (l : ℕ) =>
      Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m) *
      Real.sin ((d : ℝ) * (l : ℝ) * angle m))) = j := by
  have hm : 1 ≤ m := by rcases hd with rfl | rfl <;> omega
  have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
  obtain ⟨hα, hαπ⟩ := gap_first_phase_bounds hj hd hjdm
  have he : (((2 * j + d : ℕ) : ℝ) * angle m +
      ((m - 1 : ℕ) : ℝ) * (((2 * j + d : ℕ) : ℝ) * angle m)) *
      (2 * (m : ℝ) + 1) = (m : ℝ) * ((2 * j + d : ℕ) : ℝ) * Real.pi := by
    rw [Nat.cast_sub hm, Nat.cast_one]
    unfold angle
    field_simp [ne_of_gt hden]
    <;> ring
  have hlo : (j : ℝ) * Real.pi < ((2 * j + d : ℕ) : ℝ) * angle m +
      ((m - 1 : ℕ) : ℝ) * (((2 * j + d : ℕ) : ℝ) * angle m) := by
    apply (mul_lt_mul_iff_left₀ hden).mp
    rw [he]
    have hjm' : (j : ℝ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m by rcases hd with rfl | rfl <;> omega)
    have hp := mul_le_mul_of_nonneg_right hjm' Real.pi_pos.le
    rcases hd with rfl | rfl <;> push_cast <;>
      nlinarith [Real.pi_pos, mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le]
  have hhi : ((2 * j + d : ℕ) : ℝ) * angle m +
      ((m - 1 : ℕ) : ℝ) * (((2 * j + d : ℕ) : ℝ) * angle m) <
      (j + 1 : ℝ) * Real.pi := by
    apply (mul_lt_mul_iff_left₀ hden).mp
    rw [he]
    rcases hd with rfl | rfl <;> push_cast <;>
      nlinarith [Real.pi_pos, mul_nonneg (Nat.cast_nonneg j) Real.pi_pos.le,
        mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le]
  have hs := sampled_sine_signVariations (N := m - 1) (j := j) hα hαπ hα hαπ hlo hhi
  have hlist : (List.range (m - 1 + 1)).map (fun (i : ℕ) => Real.sin
      (((2 * j + d : ℕ) : ℝ) * angle m + (i : ℝ) *
        (((2 * j + d : ℕ) : ℝ) * angle m))) =
      (List.range' 1 m).map (fun (l : ℕ) => Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m)) := by
    rw [Nat.sub_add_cancel hm, List.range'_eq_map_range]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    push_cast
    congr 1
    ring
  rw [hlist] at hs
  calc
    _ = List.signVariations ((List.range' 1 m).map (fun (l : ℕ) =>
        Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m))) := by
      apply List.signVariations_congr
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro l hl
      have hb : 1 ≤ l ∧ l ≤ m := by
        have hb' := List.mem_range'.mp hl
        constructor <;> omega
      rw [sign_mul, sign_eq_one_iff.mpr (gap_short_sine_pos hd hb.1 hb.2), mul_one]
    _ = j := hs

end D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
