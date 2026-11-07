/- GID: D5/S3/ArithUnits/MercaKernelBins
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaKernelBins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal interval-bin identities for the actual normalized quartic kernel. -/

import D5.S3.ArithUnits.MercaClassNumberCriterion

/-! The checker's bin identities are proved for every stated conductor, with
literal counts in the actual kernel, independently of the finite census. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace D5.S3.ArithUnits.MercaKernelBins
open MercaQuarticCharacter MercaQuarticMoments

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

/-- Count actual kernel units in the literal bin floor(4 val(u)/r)=j. -/
def binCount (j : ℕ) : ℤ :=
  ((Finset.univ : Finset (ZMod r)ˣ).filter
    (fun u => u ∈ kernel r hr ∧ 4 * (u : ZMod r).val / r = j)).card

private def countWhere (P : ℕ → Prop) [DecidablePred P] : ℤ :=
  ((Finset.univ : Finset (ZMod r)ˣ).filter
    (fun u => u ∈ kernel r hr ∧ P (u : ZMod r).val)).card

private lemma count_sum (P : ℕ → Prop) [DecidablePred P] :
    countWhere r hr P = ∑ u : (ZMod r)ˣ,
      if u ∈ kernel r hr ∧ P (u : ZMod r).val then (1 : ℤ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [countWhere]

private lemma real_indicator (u : (ZMod r)ˣ) :
    (character r hr u).re =
      (if u ∈ kernel r hr then (1 : ℝ) else 0) -
        (if -u ∈ kernel r hr then (1 : ℝ) else 0) := by
  classical
  have hu (v : (ZMod r)ˣ) : v ∈ kernel r hr ↔ character r hr v = 1 := by
    simp only [kernel, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
      Units.val_one]
  have hnu : -u ∈ kernel r hr ↔ character r hr u = -1 := by
    rw [hu (-u)]
    rw [Units.val_neg, (kernel_structure r hr).2.2.2.1.eval_neg]
    exact neg_eq_iff_eq_neg
  have hfour : character r hr ^ 4 = 1 :=
    (kernel_structure r hr).1 ▸ pow_orderOf_eq_one _
  have hv : character r hr u ^ 4 = 1 := by
    rw [← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
  rw [hu u, hnu]
  rcases fourth_values _ hv with h | h | h | h <;>
    norm_num [h, Complex.ext_iff]

private lemma interval_units (n : ℕ) (hn : n < r) :
    intervalSum r hr n = ∑ u : (ZMod r)ˣ,
      if (u : ZMod r).val ≤ n then character r hr u else 0 := by
  classical
  rw [intervalSum_eq_zmod r hr n hn]
  let e : (ZMod r)ˣ ↪ ZMod r := ⟨Units.val, Units.val_injective⟩
  symm
  calc
    _ = ∑ a ∈ Finset.univ.map e,
        if a.val ≤ n then character r hr a else 0 := by simp [e]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      have hnu : ¬ IsUnit a := by
        intro hu
        exact ha (Finset.mem_map.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩)
      rw [(character r hr).map_nonunit hnu]
      split_ifs <;> rfl

private lemma interval_count (n : ℕ) (hn : n < r) :
    (intervalSum r hr n).re =
      ((countWhere r hr (fun a => a ≤ n) -
        countWhere r hr (fun a => r - n ≤ a) : ℤ) : ℝ) := by
  classical
  rw [interval_units r hr n hn, Complex.re_sum]
  have hpoint (u : (ZMod r)ˣ) :
      (if (u : ZMod r).val ≤ n then character r hr u else 0).re =
        (if u ∈ kernel r hr ∧ (u : ZMod r).val ≤ n then (1 : ℝ) else 0) -
        (if -u ∈ kernel r hr ∧ (u : ZMod r).val ≤ n then (1 : ℝ) else 0) := by
    by_cases hn : (u : ZMod r).val ≤ n
    · simpa only [hn, ite_true, and_true] using real_indicator r hr u
    · simp only [hn, ite_false, and_false, Complex.zero_re, sub_self]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Int.cast_sub, count_sum, count_sum, Int.cast_sum,
    Int.cast_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> norm_num
  · rw [← Equiv.sum_comp (Equiv.neg (ZMod r)ˣ)]
    apply Finset.sum_congr rfl
    intro u _
    change (if - -u ∈ kernel r hr ∧ ((-u : (ZMod r)ˣ) : ZMod r).val ≤ n
      then (1 : ℝ) else 0) = _
    letI : NeZero (u : ZMod r) := ⟨Units.ne_zero u⟩
    rw [neg_neg, Units.val_neg, ZMod.val_neg_of_ne_zero (u : ZMod r)]
    have hv := ZMod.val_lt (u : ZMod r)
    have he : r - (u : ZMod r).val ≤ n ↔ r - n ≤ (u : ZMod r).val := by omega
    simp only [he]
    split_ifs <;> norm_num

private lemma count_quarter :
    countWhere r hr (fun a => a ≤ (r - 1) / 4) = binCount r hr 0 ∧
    countWhere r hr (fun a => r - (r - 1) / 4 ≤ a) = binCount r hr 3 := by
  classical
  have hrp := (Fact.out : r.Prime).pos
  have hrm : r = 4 * ((r - 1) / 4) + 1 := by omega
  have eqcount (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
      (he : ∀ a, a < r → (P a ↔ Q a)) : countWhere r hr P = countWhere r hr Q := by
    unfold countWhere
    congr 2
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he _ (ZMod.val_lt _)]
  constructor
  · change countWhere r hr _ = countWhere r hr (fun a => 4 * a / r = 0)
    apply eqcount
    intro a ha
    rw [Nat.div_eq_zero_iff]
    omega
  · change countWhere r hr _ = countWhere r hr (fun a => 4 * a / r = 3)
    apply eqcount
    intro a ha
    rw [Nat.div_eq_iff hrp]
    omega

private lemma count_half :
    countWhere r hr (fun a => a ≤ (r - 1) / 2) = binCount r hr 0 + binCount r hr 1 ∧
    countWhere r hr (fun a => r - (r - 1) / 2 ≤ a) =
      binCount r hr 2 + binCount r hr 3 := by
  classical
  have hrp := (Fact.out : r.Prime).pos
  have hrm : r = 4 * ((r - 1) / 4) + 1 := by omega
  have hb (u : (ZMod r)ˣ) := ZMod.val_lt (u : ZMod r)
  have hbin (a : ℕ) (ha : a < r) :
      a ≤ (r - 1) / 2 ↔ 4 * a / r = 0 ∨ 4 * a / r = 1 := by
    have hd : 4 * a / r < 2 ↔ 4 * a < 2 * r := Nat.div_lt_iff_lt_mul hrp
    generalize 4 * a / r = b at *
    omega
  have hbin' (a : ℕ) (ha : a < r) :
      r - (r - 1) / 2 ≤ a ↔ 4 * a / r = 2 ∨ 4 * a / r = 3 := by
    have hd : 2 ≤ 4 * a / r ↔ 2 * r ≤ 4 * a := Nat.le_div_iff_mul_le hrp
    have hlt : 4 * a / r < 4 := (Nat.div_lt_iff_lt_mul hrp).mpr (by omega)
    omega
  change countWhere r hr _ = countWhere r hr (fun a => 4 * a / r = 0) +
      countWhere r hr (fun a => 4 * a / r = 1) ∧
    countWhere r hr _ = countWhere r hr (fun a => 4 * a / r = 2) +
      countWhere r hr (fun a => 4 * a / r = 3)
  constructor <;> simp only [count_sum, ← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;> intro u _
  · simp only [hbin _ (hb u)]
    by_cases hk : u ∈ kernel r hr
    · simp only [hk, true_and]
      have he : ¬ (4 * (u : ZMod r).val / r = 0 ∧ 4 * (u : ZMod r).val / r = 1) := by omega
      split_ifs <;> omega
    · simp [hk]
  · simp only [hbin' _ (hb u)]
    by_cases hk : u ∈ kernel r hr
    · simp only [hk, true_and]
      have he : ¬ (4 * (u : ZMod r).val / r = 2 ∧ 4 * (u : ZMod r).val / r = 3) := by omega
      split_ifs <;> omega
    · simp [hk]

/-- Both source interval-bin formulas hold universally for the actual kernel. -/
theorem bin_identities (hr5 : 5 < r) :
    5 * realCoordinate r hr =
      -3 * (binCount r hr 0 - binCount r hr 3) - (binCount r hr 1 - binCount r hr 2) ∧
    5 * imagCoordinate r hr =
      -(binCount r hr 0 - binCount r hr 3) + 3 * (binCount r hr 1 - binCount r hr 2) := by
  have hrp := (Fact.out : r.Prime).pos
  have hQ := interval_count r hr ((r - 1) / 4) (by omega)
  rw [(count_quarter r hr).1, (count_quarter r hr).2] at hQ
  have hS := interval_count r hr ((r - 1) / 2) (by omega)
  rw [(count_half r hr).1, (count_half r hr).2] at hS
  obtain ⟨_, hSQ, _, hRe, hIm⟩ := interval_identities r hr hr5
  have hs := congrArg Complex.re hSQ
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.I_re,
    Complex.add_im, Complex.one_im, Complex.I_im] at hs
  push_cast at hQ hS
  have hk : (5 : ℝ) * realCoordinate r hr =
      -3 * ((binCount r hr 0 : ℝ) - binCount r hr 3) -
        ((binCount r hr 1 : ℝ) - binCount r hr 2) := by linarith
  have ht : (5 : ℝ) * imagCoordinate r hr =
      -((binCount r hr 0 : ℝ) - binCount r hr 3) +
        3 * ((binCount r hr 1 : ℝ) - binCount r hr 2) := by linarith
  exact ⟨by exact_mod_cast hk, by exact_mod_cast ht⟩

end D5.S3.ArithUnits.MercaKernelBins
