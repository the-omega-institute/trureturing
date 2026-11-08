/- GID: D5/S3/Weil/Mertens/ZeroAbscissaPower
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/ZeroAbscissaPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual integrated zero sums bound the Chebyshev error by weighted differences. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes
import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Weighted finite differences of the complete actual integrated zero formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Arith.Robin.CompleteMertensPeak
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.ZeroAbscissaPower

private def primitiveTerm (s : ℝ) (k : ℕ) : ℂ :=
  actualCoeff k * Complex.exp ((Real.log s : ℂ) * (actualZero k - 1))

private theorem actual_zero (k : ℕ) : IsNontrivialZero (actualZero k) :=
  actualData.zero_isNontrivial (actualOccurrenceEquiv k).1

private theorem actual_zero_ne (k : ℕ) : actualZero k ≠ 0 ∧ actualZero k ≠ 1 := by
  constructor
  · intro e
    have h := (actual_zero k).2.1
    rw [e] at h
    norm_num at h
  · intro e
    have h := (actual_zero k).2.2
    rw [e] at h
    norm_num at h

private theorem primitiveTerm_eq {s : ℝ} (hs : 0 < s) (k : ℕ) :
    primitiveTerm s k =
      (actualCoeff k * Complex.exp ((Real.log s : ℂ) * actualZero k)) / s := by
  dsimp only [primitiveTerm]
  rw [mul_sub, mul_one, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hs]
  ring

private theorem primitiveTerm_summable {s : ℝ} (hs : 0 < s) :
    Summable (primitiveTerm s) := by
  change Summable (fun k => primitiveTerm s k)
  simpa only [primitiveTerm_eq hs] using (actualH_summable (Real.log s)).div_const (s : ℂ)

private theorem primitive_series_eq {s : ℝ} (hs : 0 < s) :
    (∑' k : ℕ, primitiveTerm s k) = actualH (Real.log s) / s := by
  simp only [primitiveTerm_eq hs, tsum_div_const, actualH]

private theorem primitiveTerm_deriv {s : ℝ} (hs : 0 < s) (k : ℕ) :
    HasDerivAt (fun t : ℝ => primitiveTerm t k)
      (-Complex.exp ((Real.log s : ℂ) * (actualZero k - 2)) / actualZero k) s := by
  have hd := ((((Real.hasDerivAt_log hs.ne').ofReal_comp).mul_const
    (actualZero k - 1)).cexp).const_mul (actualCoeff k)
  convert hd using 1
  · ext t
    rfl
  · have he : (Real.log s : ℂ) * (actualZero k - 1) =
        (Real.log s : ℂ) * (actualZero k - 2) + (Real.log s : ℂ) := by ring
    rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hs]
    dsimp only [actualCoeff]
    have h0 := (actual_zero_ne k).1
    have h1 : 1 - actualZero k ≠ 0 := sub_ne_zero.mpr (actual_zero_ne k).2.symm
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    push_cast
    field_simp [h0, h1, hs0]
    <;> ring

private theorem local_power_bound {x s β r : ℝ}
    (hx : 4 ≤ x) (hs : x / 2 ≤ s) (hr : r ≤ β) (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1) (_hr0 : 0 ≤ r) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    s ^ (r - j) ≤ (2 : ℝ) ^ j * x ^ (β - j) := by
  have hx0 : 0 < x := by linarith
  have hhalf : 1 ≤ x / 2 := by linarith
  have hs1 : 1 ≤ s := hhalf.trans hs
  have hj1 : (1 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  calc
    s ^ (r - j) ≤ s ^ (β - j) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
    _ ≤ (x / 2) ^ (β - j) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hs (by linarith)
    _ = x ^ (β - j) * (2 : ℝ) ^ ((j : ℝ) - β) := by
      rw [Real.div_rpow hx0.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring
    _ ≤ x ^ (β - j) * (2 : ℝ) ^ (j : ℝ) := by
      gcongr
      · norm_num
      · linarith
    _ = (2 : ℝ) ^ j * x ^ (β - j) := by rw [Real.rpow_natCast]; ring

private theorem primitiveTerm_norm {x s β : ℝ}
    (hx : 4 ≤ x) (hs : x / 2 ≤ s) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hzero : ∀ k : ℕ, (actualZero k).re ≤ β) (k : ℕ) :
    ‖primitiveTerm s k‖ ≤ 2 * x ^ (β - 1) * ‖actualCoeff k‖ := by
  have hs0 : 0 < s := by linarith
  rw [primitiveTerm, norm_mul, Complex.norm_exp]
  have he : (((Real.log s : ℂ) * (actualZero k - 1))).re =
      Real.log s * ((actualZero k).re - 1) := by simp
  rw [he, ← Real.rpow_def_of_pos hs0]
  have h := local_power_bound hx hs (hzero k) hβ hβ1
    (actual_zero k).2.1.le 1 (Or.inl rfl)
  norm_num only [Nat.cast_one, pow_one] at h
  calc
    _ ≤ ‖actualCoeff k‖ * (2 * x ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

private theorem primitiveTerm_increment {x a b β : ℝ}
    (hx : 4 ≤ x) (ha : x / 2 ≤ a) (hb : x / 2 ≤ b)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hzero : ∀ k : ℕ, (actualZero k).re ≤ β) (k : ℕ) :
    ‖primitiveTerm b k - primitiveTerm a k‖ ≤
      (4 * x ^ (β - 2) / ‖actualZero k‖) * |b - a| := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :=
    primitiveTerm_deriv (s := t) (by
      have hmin : x / 2 ≤ min a b := le_min ha hb
      have := ht.1
      change min a b ≤ t at this
      linarith) k
  have hbound (t : ℝ) (ht : t ∈ uIcc a b) :
      ‖-Complex.exp ((Real.log t : ℂ) * (actualZero k - 2)) / actualZero k‖ ≤
        4 * x ^ (β - 2) / ‖actualZero k‖ := by
    have htlo : x / 2 ≤ t := (le_min ha hb).trans ht.1
    have ht0 : 0 < t := by linarith
    rw [norm_div, norm_neg, Complex.norm_exp]
    have he : (((Real.log t : ℂ) * (actualZero k - 2))).re =
        Real.log t * ((actualZero k).re - 2) := by simp
    rw [he, ← Real.rpow_def_of_pos ht0]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    convert local_power_bound hx htlo (hzero k) hβ hβ1
      (actual_zero k).2.1.le 2 (Or.inr rfl)
      using 1 <;> norm_num
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt) hbound (convex_uIcc a b)
      (left_mem_uIcc) (right_mem_uIcc)

private theorem crypto_zero_iff (ρ : ℂ) :
    ConjectureMachines.Semantics.Riemann.VonMangoldtCount.IsNontrivialZetaZero ρ ↔
      IsNontrivialZero ρ := by
  constructor
  · intro h
    exact ⟨h.1,
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_criticalStrip_of_isNontrivialZetaZero h⟩
  · rintro ⟨hz, h0, h1⟩
    refine ⟨hz, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      norm_num at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro e
      rw [e] at h1
      norm_num at h1

private theorem counting_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 2 ≤ T →
      (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction T : ℝ)
        ≤ A * T * (1 + Real.log T) := by
  classical
  obtain ⟨A, hA, hlocal⟩ :=
    D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt.local_count
  refine ⟨6 * A, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  let n : ℕ := ⌈2 * T + 1⌉₊
  have hnlo : 2 * T + 1 ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) ≤ 2 * T + 2 := by
    have hn := Nat.ceil_lt_add_one (show 0 ≤ 2 * T + 1 by linarith)
    dsimp only [n]
    linarith
  have hcount : ∀ m : ℕ, (m : ℝ) ≤ 2 * T + 2 →
      (Zeta23.Ncount (-T - 1) (-T - 1 + m) : ℝ) ≤
        (m : ℝ) * (2 * A * (1 + Real.log T)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hempty : Zeta23.zerosIn (-T - 1) (-T - 1 + (0 : ℕ)) = ∅ := by
        ext ρ
        simp only [Zeta23.zerosIn, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨_, hlo, hhi⟩
        norm_num at hhi
        linarith
      have hempty' : Zeta23.zerosIn (-T - 1) (-T - 1) = ∅ := by simpa using hempty
      simp [Zeta23.Ncount, hempty']
    | succ m ih =>
      intro hm
      have hm' : (m : ℝ) ≤ 2 * T + 2 := by
        have : (m : ℝ) + 1 ≤ 2 * T + 2 := by simpa using hm
        linarith
      have hml : -T - 1 ≤ -T - 1 + (m : ℝ) := by
        linarith [Nat.cast_nonneg (α := ℝ) m]
      have hmh : -T - 1 + (m : ℝ) ≤ -T - 1 + (m : ℝ) + 1 := by linarith
      have hsplit := Zeta23.Ncount_add hml hmh
      have hloc := hlocal (-T - 1 + (m : ℝ))
      simp only [Zeta23.zetaZeroConfig_N] at hloc
      have habs : |-T - 1 + (m : ℝ)| + 3 ≤ 4 * T := by
        have hm'' : (m : ℝ) + 1 ≤ 2 * T + 2 := by simpa using hm
        have ha : |-T - 1 + (m : ℝ)| ≤ T + 1 :=
          abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) m], by linarith⟩
        linarith
      have hl : Real.log (|-T - 1 + (m : ℝ)| + 3) ≤ 2 * (1 + Real.log T) := by
        calc
          _ ≤ Real.log (4 * T) := Real.log_le_log (by positivity) habs
          _ = Real.log 4 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
          _ ≤ 2 * (1 + Real.log T) := by
            have htwo : Real.log 2 ≤ 1 := by
              linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
            have hfour : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
              norm_num
            linarith
      have hloc' := hloc.trans (mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ A))
      have hi := ih hm'
      have he : -T - 1 + (m : ℝ) + 1 = -T - 1 + ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [he] at hsplit hloc'
      rw [hsplit, Nat.cast_add]
      push_cast at hloc' ⊢
      linarith
  have hsub :
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.nontrivialZetaZerosUpTo T ⊆
        (Zeta23.zerosIn_finite (-T - 1) (-T - 1 + (n : ℝ))).toFinset := by
    intro ρ hρ
    obtain ⟨hz, him⟩ :=
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosUpTo.mp hρ
    rw [Set.Finite.mem_toFinset]
    have hs := (crypto_zero_iff ρ).mp hz
    exact ⟨hs, by linarith [(abs_le.mp him).1], by linarith [(abs_le.mp him).2]⟩
  have hsum := Finset.sum_le_sum_of_subset hsub
    (f := fun ρ => Zeta23.zeroMult ρ)
  have hw :
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction T ≤
        Zeta23.Ncount (-T - 1) (-T - 1 + (n : ℝ)) := by
    rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _
      (Zeta23.zerosIn_finite (-T - 1) (-T - 1 + (n : ℝ)))]
    simpa only [ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction,
      Zeta23.zeroMult, analyticOrderNatAt] using hsum
  have hreal :
      (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction T : ℝ) ≤
        (Zeta23.Ncount (-T - 1) (-T - 1 + (n : ℝ)) : ℝ) := by exact_mod_cast hw
  calc
    _ ≤ (n : ℝ) * (2 * A * (1 + Real.log T)) := hreal.trans (hcount n hnhi)
    _ ≤ (3 * T) * (2 * A * (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (6 * A) * T * (1 + Real.log T) := by ring

private theorem occurrence_finite_sum (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, IsNontrivialZero ρ) (f : ℂ → ℝ) (hf : ∀ ρ, 0 ≤ f ρ) :
    Summable (fun k : ℕ => if actualZero k ∈ S then f (actualZero k) else 0) ∧
      (∑' k : ℕ, if actualZero k ∈ S then f (actualZero k) else 0) =
        ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * f ρ := by
  classical
  let J : Finset ℕ := (S.finite_toSet.preimage
    (fun _ _ _ _ h => actualData.zero_injective h)).toFinset
  have hJ (n : ℕ) : n ∈ J ↔ actualData.zero n ∈ S := by
    simp [J]
  let g : ActualZeroOccurrence → ℝ := fun p =>
    if actualData.zero p.1 ∈ S then f (actualData.zero p.1) else 0
  have hgn : Summable (fun n : ℕ => ∑' i : Fin (actualData.multiplicity n), g ⟨n, i⟩) := by
    apply summable_of_ne_finset_zero (s := J)
    intro n hn
    have hnot : actualData.zero n ∉ S := by simpa only [hJ] using hn
    simp [g, hnot]
  have hg : Summable g := (summable_sigma_of_nonneg (fun p => by
    dsimp only [g]; split_ifs; exact hf _; exact le_rfl)).2
      ⟨fun _ => Summable.of_finite, hgn⟩
  have hnat : Summable (fun k : ℕ => if actualZero k ∈ S then f (actualZero k) else 0) := by
    convert actualOccurrenceEquiv.summable_iff.mpr hg using 1 <;> rfl
  refine ⟨hnat, ?_⟩
  calc
    _ = ∑' p : ActualZeroOccurrence, g p := actualOccurrenceEquiv.tsum_eq g
    _ = ∑' n : ℕ, ∑' i : Fin (actualData.multiplicity n), g ⟨n, i⟩ := hg.tsum_sigma
    _ = ∑ n ∈ J, (actualData.multiplicity n : ℝ) * f (actualData.zero n) := by
      rw [tsum_eq_sum (s := J) (fun n hn => by
        have hnot : actualData.zero n ∉ S := by simpa only [hJ] using hn
        simp [g, hnot])]
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [g, (hJ n).mp hn, tsum_fintype]
    _ = _ := by
      refine Finset.sum_bij (fun n _ => actualData.zero n) ?_ ?_ ?_ ?_
      · intro n hn
        exact (hJ n).mp hn
      · intro n hn m hm he
        exact actualData.zero_injective he
      · intro ρ hρ
        obtain ⟨n, hn⟩ := actualData.zero_exhaustive (hS ρ hρ)
        exact ⟨n, (hJ n).mpr (hn ▸ hρ), hn⟩
      · intro n hn
        rw [D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.multiplicity_eq_zeroMult]
        rfl

private theorem actual_low_weight :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 2 ≤ T →
      Summable (fun k : ℕ => if |(actualZero k).im| ≤ T then 1 / ‖actualZero k‖ else 0) ∧
        (∑' k : ℕ, if |(actualZero k).im| ≤ T then 1 / ‖actualZero k‖ else 0) ≤
          B * (1 + Real.log T) ^ 2 := by
  classical
  obtain ⟨A, hA, hcount⟩ := counting_bound
  have htwo : ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction 2 = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    obtain ⟨hz, hheight⟩ :=
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosUpTo.mp hρ
    have := actual_height_gt_ten ρ ((crypto_zero_iff ρ).mp hz)
    linarith
  let B : ℝ := 4 * A
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro T hT
  have htrans := occurrence_finite_sum
    (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.nontrivialZetaZerosUpTo T)
    (fun ρ hρ => (crypto_zero_iff ρ).mp
      (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosUpTo.mp hρ).1)
    (fun ρ => 1 / ‖ρ‖) (fun ρ => by positivity)
  have heq (k : ℕ) : actualZero k ∈
      ConjectureMachines.Semantics.Riemann.VonMangoldtCount.nontrivialZetaZerosUpTo T ↔
        |(actualZero k).im| ≤ T := by
    rw [ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosUpTo]
    exact and_iff_right ((crypto_zero_iff _).mpr (actual_zero k))
  simp only [heq] at htrans
  refine ⟨htrans.1, ?_⟩
  rw [htrans.2]
  have hbound :=
    ConjectureMachines.Semantics.Riemann.WeightedStieltjes.sum_weighted_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
      (t₀ := 2) (a := A) (C := A) (D := 0) (by norm_num) hT htwo
      (fun t ht => by convert hcount t ht.1 using 1 <;> ring)
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simp only [mul_one_div] at htrans
  calc
    _ ≤ A / 2 * (Real.log T) ^ 2 + (A + A) * Real.log T + A + 0 / 2 -
        A / 2 * (Real.log 2) ^ 2 - A * Real.log 2 := by
      simpa only [mul_one_div] using hbound
    _ ≤ B * (1 + Real.log T) ^ 2 := by
      dsimp only [B]
      nlinarith [sq_nonneg (Real.log T), sq_nonneg (Real.log 2),
        mul_nonneg hA hlog, mul_nonneg hA hlogtwo,
        mul_nonneg hA (sq_nonneg (Real.log T)), mul_nonneg hA (sq_nonneg (Real.log 2))]

private theorem actual_high_weight :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 2 ≤ T →
      (∑' k : ℕ, if T < |(actualZero k).im| then ((actualZero k).im)⁻¹ ^ 2 else 0) ≤
        B * (1 + Real.log T) / T := by
  classical
  obtain ⟨A, hA, hcount⟩ := counting_bound
  refine ⟨4 * A, by positivity, ?_⟩
  intro T hT
  apply Real.tsum_le_of_sum_le (fun k => by split_ifs <;> positivity)
  intro s
  by_cases hs : s.Nonempty
  · let U : ℝ := max T (s.sup' hs (fun k => |(actualZero k).im|))
    have hTU : T ≤ U := le_max_left _ _
    have hU (k : ℕ) (hk : k ∈ s) : |(actualZero k).im| ≤ U :=
      (Finset.le_sup' (fun k => |(actualZero k).im|) hk).trans (le_max_right _ _)
    let S := ConjectureMachines.Semantics.Riemann.VonMangoldtCount.nontrivialZetaZerosBetween T U
    have htrans := occurrence_finite_sum S
      (fun ρ hρ => (crypto_zero_iff ρ).mp
        (ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosBetween.mp hρ).1)
      (fun ρ => ρ.im⁻¹ ^ 2) (fun ρ => by positivity)
    have hsub : (∑ k ∈ s, if T < |(actualZero k).im| then ((actualZero k).im)⁻¹ ^ 2 else 0) ≤
        ∑' k : ℕ, if actualZero k ∈ S then ((actualZero k).im)⁻¹ ^ 2 else 0 := by
      calc
        _ = ∑ k ∈ s, if actualZero k ∈ S then ((actualZero k).im)⁻¹ ^ 2 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have he : actualZero k ∈ S ↔ T < |(actualZero k).im| := by
            simp only [S,
              ConjectureMachines.Semantics.Riemann.VonMangoldtCount.mem_nontrivialZetaZerosBetween]
            exact ⟨fun h => h.2.2, fun h =>
              ⟨(crypto_zero_iff _).mpr (actual_zero k), hU k hk, h⟩⟩
          simp only [he]
        _ ≤ _ := htrans.1.sum_le_tsum s (fun k _ => by split_ifs <;> positivity)
    have hbound :=
      ConjectureMachines.Semantics.Riemann.WeightedStieltjes.sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
        (a := A) (C := A) (D := 0) (by linarith) hTU hA (by norm_num)
        (fun t ht => by convert hcount t (hT.trans ht.1) using 1 <;> ring)
    rw [htrans.2] at hsub
    have hid : (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.im⁻¹ ^ 2)) =
        ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2 := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [sq_abs, div_eq_mul_inv, inv_pow]
    rw [hid] at hsub
    calc
      _ ≤ (2 * A * Real.log T + 2 * A + 2 * A) / T + 2 * 0 / T ^ 2 := hsub.trans hbound
      _ ≤ 4 * A * (1 + Real.log T) / T := by
        have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        simp only [mul_zero, zero_div, add_zero]
        apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
        nlinarith [mul_nonneg hA hl]
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by positivity) (by
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)])) (by linarith)

private theorem coeff_norm_le (k : ℕ) :
    ‖actualCoeff k‖ ≤ ((actualZero k).im)⁻¹ ^ 2 := by
  have hh := actual_height_gt_ten (actualZero k) (actual_zero k)
  have hpos : 0 < |(actualZero k).im| := by linarith
  have hprod : |(actualZero k).im| ^ 2 ≤
      ‖actualZero k‖ * ‖1 - actualZero k‖ := by
    calc
      _ = |(actualZero k).im| * |(actualZero k).im| := by ring
      _ ≤ _ := mul_le_mul (Complex.abs_im_le_norm _)
        (by simpa using Complex.abs_im_le_norm (1 - actualZero k))
        (abs_nonneg _) (norm_nonneg _)
  rw [actualCoeff, norm_div, norm_one, norm_mul]
  have h := one_div_le_one_div_of_le (pow_pos hpos 2) hprod
  simpa only [one_div, sq_abs, inv_pow] using h

/-- A finite low-height derivative estimate and the actual infinite high-height
tail give a uniform difference estimate for the complete integrated zero series.
Every natural index is an analytic occurrence; no zero is discarded. -/
theorem actual_primitive_low_high :
    ∃ C : ℝ, 0 < C ∧ ∀ β x a b T : ℝ,
      0 ≤ β → β ≤ 1 → (∀ k : ℕ, (actualZero k).re ≤ β) →
      4 ≤ x → x / 2 ≤ a → x / 2 ≤ b → 2 ≤ T →
      ‖actualH (Real.log b) / b - actualH (Real.log a) / a‖ ≤
        C * |b - a| * x ^ (β - 2) * (1 + Real.log T) ^ 2 +
          C * x ^ (β - 1) * (1 + Real.log T) / T := by
  classical
  obtain ⟨B₁, hB₁, hlow⟩ := actual_low_weight
  obtain ⟨B₂, hB₂, hhigh⟩ := actual_high_weight
  let C : ℝ := 4 * B₁ + 4 * B₂ + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro β x a b T hβ hβ1 hzero hx ha hb hT
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hR : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      actualOccurrenceEquiv.summable_iff.mpr actual_sigma_inverse_square_summable
  let l : ℕ → ℝ := fun k => if |(actualZero k).im| ≤ T then 1 / ‖actualZero k‖ else 0
  let r : ℕ → ℝ := fun k => if T < |(actualZero k).im| then ((actualZero k).im)⁻¹ ^ 2 else 0
  have hl : Summable l := (hlow T hT).1
  have hr : Summable r := Summable.of_nonneg_of_le (fun k => by
    dsimp only [r]; split_ifs <;> positivity) (fun k => by
    dsimp only [r]; split_ifs
    · exact le_rfl
    · exact sq_nonneg _) hR
  have hpoint (k : ℕ) :
      ‖primitiveTerm b k - primitiveTerm a k‖ ≤
        (4 * |b - a| * x ^ (β - 2)) * l k + (4 * x ^ (β - 1)) * r k := by
    by_cases hk : |(actualZero k).im| ≤ T
    · have hi := primitiveTerm_increment hx ha hb hβ hβ1 hzero k
      simpa only [l, r, ite_eq_left hk, ite_eq_right (not_lt.mpr hk), mul_zero, zero_mul, add_zero,
        div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hi
    · have hk' : T < |(actualZero k).im| := lt_of_not_ge hk
      simp only [l, r, ite_eq_right hk, ite_eq_left hk', mul_zero, zero_add]
      calc
        _ ≤ ‖primitiveTerm b k‖ + ‖primitiveTerm a k‖ := norm_sub_le _ _
        _ ≤ 2 * x ^ (β - 1) * ‖actualCoeff k‖ +
            2 * x ^ (β - 1) * ‖actualCoeff k‖ := add_le_add
          (primitiveTerm_norm hx hb hβ hβ1 hzero k)
          (primitiveTerm_norm hx ha hβ hβ1 hzero k)
        _ ≤ (4 * x ^ (β - 1)) * ((actualZero k).im)⁻¹ ^ 2 := by
          convert mul_le_mul_of_nonneg_left (coeff_norm_le k)
            (show 0 ≤ 4 * x ^ (β - 1) by positivity) using 1 <;> ring
  have hsum := tsum_of_norm_bounded
    (((hl.hasSum.mul_left (4 * |b - a| * x ^ (β - 2))).add
      (hr.hasSum.mul_left (4 * x ^ (β - 1))))) hpoint
  rw [(primitiveTerm_summable hb0).tsum_sub (primitiveTerm_summable ha0),
    primitive_series_eq hb0, primitive_series_eq ha0] at hsum
  calc
    _ ≤ (4 * |b - a| * x ^ (β - 2)) * (∑' k, l k) +
        (4 * x ^ (β - 1)) * (∑' k, r k) := hsum
    _ ≤ (4 * |b - a| * x ^ (β - 2)) * (B₁ * (1 + Real.log T) ^ 2) +
        (4 * x ^ (β - 1)) * (B₂ * (1 + Real.log T) / T) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlow T hT).2 (by positivity))
        (mul_le_mul_of_nonneg_left (hhigh T hT) (by positivity))
    _ ≤ _ := by
      have hC₁ : 4 * B₁ ≤ C := by dsimp only [C]; linarith
      have hC₂ : 4 * B₂ ≤ C := by dsimp only [C]; linarith
      have hlpos : 0 ≤ 1 + Real.log T := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
        linarith
      have hh₁ := mul_le_mul_of_nonneg_right hC₁
        (show 0 ≤ |b - a| * x ^ (β - 2) * (1 + Real.log T) ^ 2 by positivity)
      have hh₂ := mul_le_mul_of_nonneg_right hC₂
        (show 0 ≤ x ^ (β - 1) * (1 + Real.log T) / T by positivity)
      convert add_le_add hh₁ hh₂ using 1 <;> ring

private def elementaryCorrection (s : ℝ) : ℝ :=
  (Real.log (2 * Real.pi) - trivialT (Real.log s)) / s

private theorem correction_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt elementaryCorrection
      ((-Real.log (1 - Real.exp (-(2 * Real.log s))) / 2 -
        Real.log (2 * Real.pi)) / s ^ 2) s := by
  have hlog := Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans hs))
  have ht := ActualKernelLocalPositivity.trivialT_derivative (Real.log_pos hs)
  have hd := ((ht.comp s hlog).const_sub (Real.log (2 * Real.pi))).div
    (hasDerivAt_id s) (ne_of_gt (zero_lt_one.trans hs))
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_def, id_eq]
  field_simp [ne_of_gt (zero_lt_one.trans hs)]
  <;> ring

private theorem correction_deriv_bound {s : ℝ} (hs : 2 ≤ s) :
    |(-Real.log (1 - Real.exp (-(2 * Real.log s))) / 2 -
      Real.log (2 * Real.pi)) / s ^ 2| ≤ (|Real.log (2 * Real.pi)| + 2) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hl : Real.log 2 ≤ Real.log s := Real.log_le_log (by norm_num) hs
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.exp (-(2 * Real.log s)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have harg : 1 / 2 ≤ 1 - Real.exp (-(2 * Real.log s)) := by linarith
  have hlower : -Real.log 2 ≤ Real.log (1 - Real.exp (-(2 * Real.log s))) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) harg
    simpa only [one_div, Real.log_inv] using hh
  have hupper : Real.log (1 - Real.exp (-(2 * Real.log s))) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith [Real.exp_pos (-(2 * Real.log s))])
  have hlogtwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [abs_div, abs_of_nonneg (sq_nonneg s)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg s)
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log (2 * Real.pi)),
    le_abs_self (Real.log (2 * Real.pi))]

private theorem correction_increment {x a b : ℝ}
    (hx : 4 ≤ x) (ha : x / 2 ≤ a) (hb : x / 2 ≤ b) :
    |elementaryCorrection b - elementaryCorrection a| ≤
      (4 * (|Real.log (2 * Real.pi)| + 2) / x ^ 2) * |b - a| := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :=
    correction_deriv (s := t) (by
      have := (le_min ha hb).trans ht.1
      linarith)
  have hbound (t : ℝ) (ht : t ∈ uIcc a b) :
      ‖(-Real.log (1 - Real.exp (-(2 * Real.log t))) / 2 -
        Real.log (2 * Real.pi)) / t ^ 2‖ ≤ 4 * (|Real.log (2 * Real.pi)| + 2) / x ^ 2 := by
    have htlo : x / 2 ≤ t := (le_min ha hb).trans ht.1
    have ht2 : 2 ≤ t := by linarith
    have htpos : 0 < t := by linarith
    rw [Real.norm_eq_abs]
    refine (correction_deriv_bound ht2).trans ?_
    apply (div_le_div_iff₀ (sq_pos_of_pos htpos) (sq_pos_of_pos (by linarith : 0 < x))).mpr
    have hsq : x ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    nlinarith [mul_nonneg (abs_nonneg (Real.log (2 * Real.pi))) (sub_nonneg.mpr hsq)]
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt) hbound (convex_uIcc a b)
      left_mem_uIcc right_mem_uIcc

private theorem complete_primitive_eq {x : ℝ} (hx : 2 ≤ x) :
    ((U x / x : ℝ) : ℂ) = actualH (Real.log x) / x + elementaryCorrection x := by
  have hx0 : 0 < x := by linarith
  have hf := actual_integrated_explicit_formula (Real.log_pos (by linarith : 1 < x))
  rw [Real.exp_log hx0] at hf
  rw [hf]
  simp only [elementaryCorrection, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  ring

private theorem primitive_eq_negative_tail {x : ℝ} (hx : 2 ≤ x) :
    U x / x = -Q x := by
  have h := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  change Q x = _ at h
  dsimp only [U]
  field_simp [ne_of_gt (by linarith : 0 < x)] at h ⊢
  nlinarith

private theorem primitive_increment {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    U b / b - U a / a = ∫ t in a..b, psiErrorKernel t := by
  have hi (t : ℝ) (ht : 2 ≤ t) : IntegrableOn psiErrorKernel (Ioi t) :=
    WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
      (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ t))
  have hh := intervalIntegral.integral_Ioi_sub_Ioi' (hi a ha) (hi b hb)
  rw [primitive_eq_negative_tail ha, primitive_eq_negative_tail hb]
  dsimp only [Q] at *
  linarith

private theorem reciprocal_weight_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, 1 / t ^ 2) = (b - a) / (a * b) := by
  have hn (t : ℝ) (ht : t ∈ uIcc a b) : t ≠ 0 :=
    ne_of_gt ((lt_min ha hb).trans_le ht.1)
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => -t⁻¹) (1 / t ^ 2) t := by
    convert (hasDerivAt_inv (hn t ht)).neg using 1 <;> try rfl
    simp only [one_div, neg_neg]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b :=
    (continuousOn_of_forall_continuousAt (fun t ht =>
      continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 (hn t ht)))).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  field_simp [ha.ne', hb.ne']
  <;> ring

private theorem kernel_interval_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable psiErrorKernel volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
    (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ a))).mono_set Ioc_subset_Ioi_self

private theorem actual_weighted_monotonicity {x h D : ℝ}
    (hx : 4 ≤ x) (hh : 0 < h) (hhx : h ≤ x / 2)
    (hplus : |U (x + h) / (x + h) - U x / x| ≤ D)
    (hminus : |U x / x - U (x - h) / (x - h)| ≤ D) :
    |Chebyshev.psi x - x| ≤ h + 2 * x ^ 2 * D / h := by
  have hx0 : 0 < x := by linarith
  have hxm : 2 ≤ x - h := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hxp : 2 ≤ x + h := by linarith
  have hD : 0 ≤ D := (abs_nonneg _).trans hplus
  have hweight (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b :=
    (continuousOn_of_forall_continuousAt (fun t ht =>
      continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 (ne_of_gt ((lt_min ha hb).trans_le ht.1))))).intervalIntegrable
  have hp : (Chebyshev.psi x - x - h) * (h / (x * (x + h))) ≤
      U (x + h) / (x + h) - U x / x := by
    rw [primitive_increment hx2 hxp,
      ← show (∫ t in x..x + h, 1 / t ^ 2) = h / (x * (x + h)) by
        simpa using reciprocal_weight_integral hx0 (by linarith : 0 < x + h),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((hweight x (x + h) hx0 (by linarith)).const_mul _)
      (kernel_interval_integrable hx2 (by linarith))
    intro t ht
    dsimp only [psiErrorKernel]
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    linarith [Chebyshev.psi_mono ht.1, ht.2]
  have hm : U x / x - U (x - h) / (x - h) ≤
      (Chebyshev.psi x - x + h) * (h / (x * (x - h))) := by
    rw [primitive_increment hxm hx2,
      ← show (∫ t in x - h..x, 1 / t ^ 2) = h / (x * (x - h)) by
        have hi := reciprocal_weight_integral (by linarith : 0 < x - h) hx0
        convert hi using 1 <;> ring,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      (kernel_interval_integrable hxm (by linarith))
      ((hweight (x - h) x (by linarith) hx0).const_mul _)
    intro t ht
    dsimp only [psiErrorKernel]
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    linarith [Chebyshev.psi_mono ht.2, ht.1]
  have hp' : (Chebyshev.psi x - x - h) * h ≤ D * (x * (x + h)) := by
    have hz := hp.trans (le_trans (le_abs_self _) hplus)
    have hw : 0 < x * (x + h) := by positivity
    have he : (Chebyshev.psi x - x - h) * (h / (x * (x + h))) =
        ((Chebyshev.psi x - x - h) * h) / (x * (x + h)) := by ring
    rw [he] at hz
    exact (div_le_iff₀ hw).mp hz
  have hm' : -D * (x * (x - h)) ≤ (Chebyshev.psi x - x + h) * h := by
    have hz : -D ≤ (Chebyshev.psi x - x + h) * (h / (x * (x - h))) :=
      (le_trans (by linarith [(neg_abs_le (U x / x - U (x - h) / (x - h))), hminus]) hm)
    have hw : 0 < x * (x - h) := by positivity
    rw [show (Chebyshev.psi x - x + h) * (h / (x * (x - h))) =
      ((Chebyshev.psi x - x + h) * h) / (x * (x - h)) by ring] at hz
    exact (le_div_iff₀ hw).mp hz
  have hxph : x * (x + h) ≤ 2 * x ^ 2 := by nlinarith
  have hxmh : x * (x - h) ≤ 2 * x ^ 2 := by nlinarith
  apply abs_le.mpr
  constructor
  · apply (le_of_mul_le_mul_right ?_ hh)
    have hhD := mul_le_mul_of_nonneg_left hxmh hD
    field_simp [hh.ne']
    nlinarith
  · apply (le_of_mul_le_mul_right ?_ hh)
    have hhD := mul_le_mul_of_nonneg_left hxph hD
    field_simp [hh.ne']
    nlinarith

/-- The complete actual weighted finite-difference bound, uniform in the
abscissa parameter, both endpoints, and the height cutoff. -/
theorem actual_psi_low_high :
    ∃ C : ℝ, 0 < C ∧ ∀ β x h T : ℝ,
      0 ≤ β → β ≤ 1 → (∀ k : ℕ, (actualZero k).re ≤ β) →
      4 ≤ x → 1 ≤ h → h ≤ x / 2 → 2 ≤ T →
      |Chebyshev.psi x - x| ≤ h +
        C * x ^ β * (1 + Real.log T) ^ 2 +
          C * x ^ (β + 1) * (1 + Real.log T) / (h * T) := by
  obtain ⟨C, hC, hzeroDiff⟩ := actual_primitive_low_high
  let D₀ : ℝ := |Real.log (2 * Real.pi)| + 2
  let B : ℝ := 2 * C + 8 * D₀ + 1
  refine ⟨B, by dsimp only [B, D₀]; positivity, ?_⟩
  intro β x h T hβ hβ1 hzero hx hh hhx hT
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hL : 1 ≤ 1 + Real.log T := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
    linarith
  let D : ℝ := C * h * x ^ (β - 2) * (1 + Real.log T) ^ 2 +
    C * x ^ (β - 1) * (1 + Real.log T) / T + 4 * D₀ / x ^ 2 * h
  have hdiff (a b : ℝ) (ha : x / 2 ≤ a) (hb : x / 2 ≤ b) (hab : |b - a| = h) :
      |U b / b - U a / a| ≤ D := by
    have ha2 : 2 ≤ a := by linarith
    have hb2 : 2 ≤ b := by linarith
    have hz := hzeroDiff β x a b T hβ hβ1 hzero hx ha hb hT
    have hg := correction_increment hx ha hb
    have he : ((U b / b - U a / a : ℝ) : ℂ) =
        (actualH (Real.log b) / b - actualH (Real.log a) / a) +
          ((elementaryCorrection b - elementaryCorrection a : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, complete_primitive_eq ha2, complete_primitive_eq hb2,
        Complex.ofReal_sub]
      ring
    have hn := norm_add_le (actualH (Real.log b) / b - actualH (Real.log a) / a)
      ((elementaryCorrection b - elementaryCorrection a : ℝ) : ℂ)
    rw [← he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hab] at hz hg
    exact hn.trans (add_le_add hz hg)
  have hp := hdiff x (x + h) (by linarith) (by linarith)
    (by rw [add_sub_cancel_left, abs_of_pos hh0])
  have hm := hdiff (x - h) x (by linarith) (by linarith)
    (by rw [sub_sub_cancel, abs_of_pos hh0])
  have hmain := actual_weighted_monotonicity hx hh0 hhx hp hm
  have hp₂ : x ^ (2 : ℕ) * x ^ (β - 2) = x ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    ring
  have hp₁ : x ^ (2 : ℕ) * x ^ (β - 1) = x ^ (β + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    ring
  have hscale : h + 2 * x ^ 2 * D / h = h +
      2 * C * x ^ β * (1 + Real.log T) ^ 2 +
        2 * C * x ^ (β + 1) * (1 + Real.log T) / (h * T) + 8 * D₀ := by
    have ht0 : T ≠ 0 := ne_of_gt (by linarith : 0 < T)
    have hlow : 2 * x ^ 2 * (C * h * x ^ (β - 2) * (1 + Real.log T) ^ 2) / h =
        2 * C * x ^ β * (1 + Real.log T) ^ 2 := by
      calc
        _ = 2 * C * (x ^ 2 * x ^ (β - 2)) * (1 + Real.log T) ^ 2 := by
          field_simp [hh0.ne']
          <;> ring
        _ = _ := by rw [hp₂]
    have hhigh : 2 * x ^ 2 * (C * x ^ (β - 1) * (1 + Real.log T) / T) / h =
        2 * C * x ^ (β + 1) * (1 + Real.log T) / (h * T) := by
      calc
        _ = 2 * C * (x ^ 2 * x ^ (β - 1)) * (1 + Real.log T) / (h * T) := by
          field_simp [hh0.ne', ht0]
          <;> ring
        _ = _ := by rw [hp₁]
    have hcor : 2 * x ^ 2 * (4 * D₀ / x ^ 2 * h) / h = 8 * D₀ := by
      field_simp [hx0.ne', hh0.ne']
      <;> ring
    dsimp only [D]
    rw [mul_add, mul_add, add_div, add_div, hlow, hhigh, hcor]
    ring
  rw [hscale] at hmain
  have hpow : 1 ≤ x ^ β := Real.one_le_rpow (by linarith) hβ
  have hLsq : 1 ≤ (1 + Real.log T) ^ 2 := by nlinarith
  have hproduct : 1 ≤ x ^ β * (1 + Real.log T) ^ 2 := by nlinarith
  have hconst := mul_le_mul_of_nonneg_left hproduct
    (show 0 ≤ 8 * D₀ by dsimp only [D₀]; positivity)
  have hB₁ : 2 * C + 8 * D₀ ≤ B := by dsimp only [B]; linarith
  have hB₂ : 2 * C ≤ B := by dsimp only [B, D₀]; linarith [abs_nonneg (Real.log (2 * Real.pi))]
  have hfirst := mul_le_mul_of_nonneg_right hB₁
    (show 0 ≤ x ^ β * (1 + Real.log T) ^ 2 by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hB₂
    (show 0 ≤ x ^ (β + 1) * (1 + Real.log T) / (h * T) by positivity)
  have hlow : 2 * C * x ^ β * (1 + Real.log T) ^ 2 + 8 * D₀ ≤
      B * x ^ β * (1 + Real.log T) ^ 2 := by nlinarith
  have hhigh : 2 * C * x ^ (β + 1) * (1 + Real.log T) / (h * T) ≤
      B * x ^ (β + 1) * (1 + Real.log T) / (h * T) := by
    convert hsecond using 1 <;> ring
  linarith

private theorem psi_linear_error {x : ℝ} (hx : 2 ≤ x) :
    |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hp := Chebyshev.psi_le_const_mul_self (by linarith : 0 ≤ x)
  apply abs_le.mpr
  constructor <;> nlinarith [Chebyshev.psi_nonneg x]

/-- The full unconditional Chebyshev power estimate at the actual supremum
of real parts of nontrivial zeta zeros, for every real endpoint at least two. -/
theorem actual_zero_abscissa_power_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^
        (D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa + ε) := by
  let Θ := D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa
  have hΘ0 : 0 ≤ Θ :=
    D5.S3.Arith.Robin.ForwardKernel.KappaGap.zeroAbscissa_nonnegative
  have hΘ1 : Θ ≤ 1 := by
    apply csSup_le (show (Complex.re '' {ρ : ℂ | IsNontrivialZero ρ}).Nonempty from
      ⟨(actualZero 0).re, actualZero 0, actual_zero 0, rfl⟩)
    rintro r ⟨ρ, hρ, rfl⟩
    exact hρ.2.2.le
  have hzero (k : ℕ) : (actualZero k).re ≤ Θ :=
    D5.S3.Arith.Robin.ForwardKernel.KappaGap.zero_re_le_abscissa (actual_zero k)
  intro ε hε
  have hεΘ : 0 ≤ Θ + ε := by linarith
  by_cases hΘ : Θ < 1
  · obtain ⟨C, hC, hquant⟩ := actual_psi_low_high
    have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - Θ)) ≤ 1 / 2 := by
      exact ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - Θ)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun x hx => hx.le)
    have hlog : ∀ᶠ x : ℝ in atTop, |Real.log x| ≤ x ^ (ε / 2) := by
      have hh := (isLittleO_log_rpow_atTop (by linarith : 0 < ε / 2)).bound
        (by norm_num : (0 : ℝ) < 1)
      filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with x hx hx0
      simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx
    have hevent : ∀ᶠ x : ℝ in atTop,
        |Chebyshev.psi x - x| ≤ (4 * (1 + 2 * C)) * x ^ (Θ + ε) := by
      filter_upwards [eventually_ge_atTop (4 : ℝ), hsmall, hlog] with x hx hhs hls
      have hx0 : 0 < x := by linarith
      have hx1 : 1 ≤ x := by linarith
      have hp : 1 ≤ x ^ Θ := Real.one_le_rpow hx1 hΘ0
      have hpow : x * x ^ (-(1 - Θ)) = x ^ Θ := by
        conv_lhs => lhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hhalf : x ^ Θ ≤ x / 2 := by
        rw [← hpow]
        nlinarith [mul_le_mul_of_nonneg_left hhs hx0.le]
      have hq := hquant Θ x (x ^ Θ) x hΘ0 hΘ1 hzero hx hp hhalf (by linarith)
      have hp1 : x ^ (Θ + 1) = x ^ Θ * x := by
        rw [Real.rpow_add hx0, Real.rpow_one]
      have htail : C * (x ^ Θ * x) * (1 + Real.log x) / (x ^ Θ * x) =
          C * (1 + Real.log x) := by
        field_simp [(Real.rpow_pos_of_pos hx0 Θ).ne', hx0.ne']
      rw [hp1, htail] at hq
      have hl0 : 1 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx1]
      have hlogpow : (1 + Real.log x) ^ 2 ≤ 4 * x ^ ε := by
        have hroot : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
        have hsquare : (x ^ (ε / 2)) ^ 2 = x ^ ε := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
          congr 1
          norm_num
        have hlx : Real.log x ≤ x ^ (ε / 2) := (le_abs_self _).trans hls
        have hsum : 1 + Real.log x ≤ 2 * x ^ (ε / 2) := by linarith
        have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log x) hsum 2
        nlinarith
      have hlogsquare : 1 + Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
      have hbase : |Chebyshev.psi x - x| ≤
          (1 + 2 * C) * x ^ Θ * (1 + Real.log x) ^ 2 := by
        have hprod := mul_le_mul_of_nonneg_left hlogsquare
          (show 0 ≤ C by linarith)
        have h1 := mul_le_mul_of_nonneg_right hp
          (show 0 ≤ C * (1 + Real.log x) ^ 2 by positivity)
        have h2 : x ^ Θ ≤ x ^ Θ * (1 + Real.log x) ^ 2 := by
          have hs : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hx0.le Θ)
        nlinarith
      calc
        _ ≤ (1 + 2 * C) * x ^ Θ * (1 + Real.log x) ^ 2 := hbase
        _ ≤ (1 + 2 * C) * x ^ Θ * (4 * x ^ ε) := by gcongr
        _ = (4 * (1 + 2 * C)) * x ^ (Θ + ε) := by rw [Real.rpow_add hx0]; ring
    obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
    let A : ℝ := Real.log 4 + 5
    let B : ℝ := 4 * (1 + 2 * C) + A * max X 4
    have hA : 0 < A := by dsimp only [A]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨B, ?_⟩
    intro x hx
    change |Chebyshev.psi x - x| ≤ B * x ^ (Θ + ε)
    have hx0 : 0 < x := by linarith
    by_cases hxX : X ≤ x
    · have hbC : 4 * (1 + 2 * C) ≤ B := by
        dsimp only [B]
        have hmax : 0 ≤ max X 4 := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_right _ _)
        nlinarith
      exact (hX x hxX).trans (mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hx0.le _))
    · have hxmax : x ≤ max X 4 := (le_of_not_ge hxX).trans (le_max_left _ _)
      have hinit : |Chebyshev.psi x - x| ≤ A * max X 4 :=
        (psi_linear_error hx).trans (mul_le_mul_of_nonneg_left hxmax hA.le)
      have hpow1 : 1 ≤ x ^ (Θ + ε) := Real.one_le_rpow (by linarith) hεΘ
      have hbA : A * max X 4 ≤ B := by dsimp only [B]; linarith
      exact hinit.trans (hbA.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow1 hB))
  · refine ⟨Real.log 4 + 5, ?_⟩
    intro x hx
    have hlin := psi_linear_error hx
    have hpow : x ≤ x ^ (Θ + ε) := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x)
        (show (1 : ℝ) ≤ Θ + ε by linarith)
      simpa only [Real.rpow_one] using hh
    exact hlin.trans (mul_le_mul_of_nonneg_left hpow
      (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]))

#print axioms actual_primitive_low_high
#print axioms actual_psi_low_high
#print axioms actual_zero_abscissa_power_bound

end D5.S3.Weil.Mertens.ZeroAbscissaPower
end
