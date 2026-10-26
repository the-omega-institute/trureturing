/- GID: D5/S3/Combinatorics/Circle/M5FullWordConsumer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5FullWordConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Original centered source rows and the five-pair physical word construction. -/
module
import all D5.S3.Combinatorics.Circle.M5RetainedTail
public import D5.S3.Combinatorics.Circle.M5SourceRows
public import D5.S3.Combinatorics.Circle.SourceWidth
/-! # M5FullWordConsumer -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth SourcePrefixInventory
open Fin.NatCast
open scoped BigOperators

private def sourceArithmetic {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : Arithmetic := by
  let N := modulus k
  let Q := quarter k
  let C := halfCapacity k
  let q := (2 : ℤ) ^ L
  let H := (2 : ℤ) ^ (L + 1)
  let z := sourceSeed t x 0
  let n := sourceSeed t x 2
  let Δ := b - z
  let b1 := sourceSeed t x 3
  let r := (2 : ℤ) ^ sourceLength t x 3
  let w := sourceSeed t x 4
  let v := sourceSeed t x 5
  let e := (2 : ℤ) ^ sourceLength t x 5
  let u := sourceSeed t x 6
  let F := (2 : ℤ) ^ (sourceLength t x 6 + 1)
  let y := sourceSeed t x 7
  let a0 := sourceSeed t x 8
  have hk := (source_ten h).1
  obtain ⟨hH8, hL2, hΔ2, hΔeven, hNz, hNb, hzn, hbn, hb1n, hna, hnz, hzb, hΔn⟩ :=
    source_core h
  have hNQ : N = 4 * Q - 1 := (modulus_quarter k hk).1
  have hCQ : C = 2 * Q - 1 := (modulus_quarter k hk).2.1
  have hQ : 0 < Q := (modulus_quarter k hk).2.2.2
  have hHq : H = 2 * q := by dsimp only [H, q]; rw [pow_succ]; ring
  have hHpow : H = 4 * (2 : ℤ) ^ (L - 1) := by
    dsimp only [H]
    rw [show L + 1 = (L - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hHdiv : H / 4 = (2 : ℤ) ^ (L - 1) := by omega
  have hHcases : H = 8 ∨ H = 16 ∨ 32 ≤ H := by
    by_cases hL : L = 2
    · left; simp [H, hL]
    · by_cases hL3 : L = 3
      · right; left; simp [H, hL3]
      · right; right
        have hh := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2)
          (show 5 ≤ L + 1 by omega)
        norm_num at hh
        exact hh
  have hzraw : z = N - 2 * actualSource k t x := by
    simpa only [z, Nat.zero_mod, ite_true, source_parent_zero h] using
      source_seed_formula h 0 (by decide)
  have hwraw : w = N - 2 * actualSource k t (sourceParent t x 4) := by
    simpa only [w, Nat.reduceMod, ite_true] using source_seed_formula h 4 (by decide)
  have huraw : u = N - 2 * actualSource k t (sourceParent t x 6) := by
    simpa only [u, Nat.reduceMod, ite_true] using source_seed_formula h 6 (by decide)
  have hwsource : w = N - 2 * r * b1 := by
    have hh := source_seed_recurrence h 3 (by decide)
    rw [pow_succ] at hh
    change w = N - (r * 2) * b1 at hh
    nlinarith only [hh]
  have hvsource : v = N - q * w := by
    have hh := source_seed_recurrence h 4 (by decide)
    rw [h.w_row_length, Nat.sub_add_cancel (show 1 ≤ L by omega)] at hh
    exact hh
  have husource : u = N - 2 * e * v := by
    have hh := source_seed_recurrence h 5 (by decide)
    rw [pow_succ] at hh
    change u = N - (e * 2) * v at hh
    nlinarith only [hh]
  have hysource : y = N - F * u := source_seed_recurrence h 6 (by decide)
  have hr1 : 1 ≤ r := one_le_pow₀ (by decide)
  have hrH : r ≤ H / 4 := by
    rw [hHdiv]
    exact pow_le_pow_right₀ (by decide) (show sourceLength t x 3 ≤ L - 1 by
      have hh := h.gamma_row_short
      omega)
  have he1 : 1 ≤ e := one_le_pow₀ (by decide)
  have hF2 : 2 ≤ F := by
    dsimp only [F]
    rw [pow_succ]
    have hh : (1 : ℤ) ≤ 2 ^ sourceLength t x 6 := one_le_pow₀ (by decide)
    omega
  have hext := source_extrema k t hk a b h.a_positive
    (lt_trans h.a_positive h.minimum_inequalities.1) h.negative_minimum
    h.positive_minimum h.negative_attained h.positive_attained p d
    h.p_maximum h.d_minimum
  have ht : actualSource k t (sourceParent t x 6) = e * v := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_terminal_formula h 5 (by decide)
  have hTmax : 2 * e * v ≤ N - a := by
    have hh := h.p_maximum (sourceParent t x 6)
    rw [ht] at hh
    nlinarith only [hh, hext.2.2.1]
  have hUvalue : F * u = -2 * actualSource k t (sourceParent t x 7) := by
    have hh := source_terminal_formula h 6 (by decide)
    norm_num only [Nat.reduceMod, ite_true] at hh
    dsimp only [F]
    rw [pow_succ]
    nlinarith only [hh]
  have hUneg : actualSource k t (sourceParent t x 7) < 0 := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_parent_sign h 7 (by decide)
  have hUthreshold : N + 1 ≤ 2 * F * u := by
    have hh := source_parent_large h 7 (by decide)
    rw [abs_of_neg hUneg] at hh
    nlinarith only [hh, hUvalue, hNQ]
  have hUmax : F * u ≤ H * z := by
    have hh := h.d_minimum (sourceParent t x 7)
    nlinarith only [hh, hUvalue, hext.2.2.2, hNz]
  have hubound : u ≤ C := by
    exact abs_le.mpr (source_bounds k t hk (advance (sourceParent t x 6) 1))
  have hvb : b ≤ v := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_seed_minimum h 5 (by decide)
  have hyb : b ≤ y := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_seed_minimum h 7 (by decide)
  have ha0a : a ≤ a0 := by
    simpa only [Nat.reduceMod, ite_true] using source_seed_minimum h 8 (by decide)
  have hwb := h.w_bounds
  have hwh := h.w_hard
  have hua := h.u_above_z
  have ha0 := h.a0_bound
  have hδhard := h.delta_hard
  rw [← hwraw] at hwb
  rw [← hzraw, ← hwraw] at hwh
  rw [← hzraw, ← huraw] at hua
  rw [← hzraw] at ha0 hδhard
  exact {
    N := N, Q := Q, C := C, a := a, b := b, q := q, H := H,
    z := z, n := n, Δ := Δ, b1 := b1, r := r, w := w, v := v, e := e,
    u := u, F := F, y := y, a0 := a0,
    N_quarter := hNQ, C_quarter := hCQ, Q_positive := hQ,
    H_q := hHq, H_four := by omega, H_eight := hH8, H_cases := hHcases,
    a_positive := h.a_positive, ab := h.minimum_inequalities,
    n_minimum := hna, nzb := ⟨hnz, hzb⟩,
    delta_two := hΔ2, delta_even := hΔeven, delta_n := hΔn,
    N_z := hNz, N_b := hNb, z_n := hzn, b_n := hbn, b1_n := hb1n,
    c0_hard := h.c0_hard, delta_hard := hδhard, b1_hard := h.b1_hard,
    w_bounds := hwb, w_hard := hwh, r_bounds := ⟨hr1, hrH⟩,
    w_source := hwsource, v_source := hvsource, v_minimum := hvb,
    e_one := he1, u_source := husource, T_maximum := hTmax,
    F_two := hF2, U_threshold := hUthreshold, U_maximum := hUmax,
    u_above := hua, u_bound := hubound, branch := h.power_branch,
    y_source := hysource, y_minimum := hyb, a0_bounds := ⟨ha0a, ha0⟩,
    odd_z := source_seed_odd h 0 (by decide),
    odd_n := source_seed_odd h 2 (by decide),
    odd_b := by simpa only [source_seed_one h] using source_seed_odd h 1 (by decide),
    odd_w := source_seed_odd h 4 (by decide),
    odd_u := source_seed_odd h 6 (by decide),
    odd_a0 := source_seed_odd h 8 (by decide) }


private def sourceData {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : RowData (sourceArithmetic h) := by
  classical
  let len := fun i : Fin 10 => sourceLength t x i.val
  let f := fun o : Occ len => actualSource k t (physical x o)
  let base := fun i : Fin 10 => actualSource k t (advance (sourceParent t x i.val) 1)
  have hk := (source_ten h).1
  have hbase (i : Fin 10) : base i =
      if i.val % 2 = 0 then -sourceSeed t x i.val else sourceSeed t x i.val := by
    have hs := source_parent_sign h i.val (by omega)
    have hl := source_parent_large h i.val (by omega)
    by_cases hi : i.val % 2 = 0
    · simp only [hi, ite_true] at hs ⊢
      rw [abs_of_pos hs] at hl
      have hn := (source_positive_step k t hk _ hl).2
      dsimp only [base, sourceSeed]
      rw [abs_of_neg hn, neg_neg]
    · simp only [hi, ite_false] at hs ⊢
      rw [abs_of_neg hs] at hl
      have hn := (source_negative_step k t hk (sourceParent t x i.val) (by omega)).2
      dsimp only [base, sourceSeed]
      rw [abs_of_pos hn]
  have hp4 : (2 : ℤ) ^ len 4 = (sourceArithmetic h).H / 4 := by
    have hL := (source_core h).2.1
    change (2 : ℤ) ^ sourceLength t x 4 = (2 : ℤ) ^ (L + 1) / 4
    rw [h.w_row_length, show L + 1 = (L - 1) + 2 by omega, pow_add]
    norm_num
  have hsurj : Function.Surjective (physical (t := t) x) := by
    intro j
    obtain ⟨o, ho, he⟩ := List.mem_map.mp
      ((physical_inventory h).mem_iff.mpr (List.mem_finRange j))
    exact ⟨o, he⟩
  refine {
    len := len, f := f, base := base,
    values := ?_, small := ?_, bound := ?_,
    base0 := ?_, base1 := ?_, base2 := ?_, base3 := ?_,
    base4 := ?_, base5 := ?_, base6 := ?_, base7 := ?_,
    pow0 := ?_, pow1 := ?_, pow2 := ?_, pow3 := rfl, pow4 := hp4,
    pow5 := rfl, pow6 := ?_,
    large0 := ?_, large1 := ?_, large2 := ?_, large3 := ?_,
    large4 := ?_, large5 := ?_, large6 := ?_, large7 := ?_, large8 := ?_,
    last_negative := ?_, next7 := ?_, total := ?_ }
  · intro i j
    exact row_value hk (source_own_row h i.val i.isLt) j.val (Nat.le_of_lt j.isLt)
  · intro i j
    exact Int.le_sub_one_of_lt ((source_own_row h i.val i.isLt).small j.val j.isLt)
  · intro i
    exact abs_le.mpr (source_bounds k t hk (sourceParent t x i.val))
  · change base 0 = -sourceSeed t x 0
    simpa only [Fin.val_zero, Nat.zero_mod, ite_true] using hbase 0
  · change base 1 = b
    have hb := hbase 1
    norm_num only [Fin.val_one, Nat.reduceMod, one_ne_zero, ite_false] at hb
    rw [hb, source_seed_one h]
  · change base 2 = -sourceSeed t x 2
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, ite_true] using hbase 2
  · change base 3 = sourceSeed t x 3
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, one_ne_zero, ite_false] using hbase 3
  · change base 4 = -sourceSeed t x 4
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, ite_true] using hbase 4
  · change base 5 = sourceSeed t x 5
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, one_ne_zero, ite_false] using hbase 5
  · change base 6 = -sourceSeed t x 6
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, ite_true] using hbase 6
  · change (2 : ℤ) ^ sourceLength t x 0 = (2 : ℤ) ^ L
    rw [h.x_row_length]
  · change (2 : ℤ) ^ sourceLength t x 1 = (2 : ℤ) ^ L
    rw [h.d_row_length]
  · change (2 : ℤ) ^ sourceLength t x 2 = (2 : ℤ) ^ L
    rw [h.beta_row_length]
  · change 2 * (2 : ℤ) ^ sourceLength t x 6 = (2 : ℤ) ^ (sourceLength t x 6 + 1)
    rw [pow_succ]; ring
  · change 2 * actualSource k t (sourceParent t x 0) = modulus k - sourceSeed t x 0
    have hh := source_seed_formula h 0 (by decide)
    norm_num only [Nat.zero_mod, ite_true] at hh
    omega
  · change actualSource k t (sourceParent t x 1) = -(2 : ℤ) ^ L * sourceSeed t x 0
    simpa only [Nat.zero_mod, ite_true, h.x_row_length, neg_mul] using
      source_terminal_formula h 0 (by decide)
  · change actualSource k t (sourceParent t x 2) = (2 : ℤ) ^ L * b
    simpa only [Nat.one_mod, one_ne_zero, ite_false, h.d_row_length, source_seed_one h] using
      source_terminal_formula h 1 (by decide)
  · change actualSource k t (sourceParent t x 3) = -(2 : ℤ) ^ L * sourceSeed t x 2
    simpa only [Nat.reduceMod, ite_true, h.beta_row_length, neg_mul] using
      source_terminal_formula h 2 (by decide)
  · change actualSource k t (sourceParent t x 4) =
      (2 : ℤ) ^ sourceLength t x 3 * sourceSeed t x 3
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using
      source_terminal_formula h 3 (by decide)
  · change actualSource k t (sourceParent t x 5) =
      -((sourceArithmetic h).H / 4) * sourceSeed t x 4
    rw [← hp4]
    change actualSource k t (sourceParent t x 5) =
      -(2 : ℤ) ^ sourceLength t x 4 * sourceSeed t x 4
    simpa only [Nat.reduceMod, ite_true, neg_mul] using
      source_terminal_formula h 4 (by decide)
  · change 2 * actualSource k t (sourceParent t x 6) = modulus k - sourceSeed t x 6
    have hh := source_seed_formula h 6 (by decide)
    norm_num only [Nat.reduceMod, ite_true] at hh
    omega
  · change base 7 = sourceSeed t x 7
    simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, one_ne_zero, ite_false] using hbase 7
  · change 2 * actualSource k t (sourceParent t x 7) =
      -(2 : ℤ) ^ (sourceLength t x 6 + 1) * sourceSeed t x 6
    have hh := source_terminal_formula h 6 (by decide)
    norm_num only [Nat.reduceMod, ite_true] at hh
    rw [pow_succ]
    nlinarith only [hh]
  · change 2 * actualSource k t (sourceParent t x 8) = modulus k - sourceSeed t x 8
    have hh := source_seed_formula h 8 (by decide)
    norm_num only [Nat.reduceMod, ite_true] at hh
    omega
  · change actualSource k t (sourceParent t x 9) < 0
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using
      source_parent_sign h 9 (by decide)
  · change sourceSeed t x 8 = modulus k - 2 * (2 : ℤ) ^ sourceLength t x 7 * sourceSeed t x 7
    have hh := source_seed_recurrence h 7 (by decide)
    rw [pow_succ] at hh
    nlinarith only [hh]
  · change (∑ o, actualSource k t (physical x o)) = 0
    rw [(show Function.Bijective (physical (t := t) x) from ⟨physical_injective h, hsurj⟩).sum_comp]
    exact (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.1

/-- The covered original M5 source has a complete physical-label word.  No
assumption about a chosen word, a normalized arithmetic certificate or a free
source orbit is used.  All natural take lengths use the original capacity. -/
theorem exists_full_word {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    let s := actualSource k t
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      word.head? = some x ∧ (word.map s).sum = 0 ∧
      ∀ j : ℕ, 0 ≤ ((word.take j).map s).sum ∧
        ((word.take j).map s).sum ≤ halfCapacity k := by
  classical
  let D := sourceArithmetic h
  let R := sourceData h
  obtain ⟨A, f, hA, hAP, hf, hfg, heq, hprev, hnext⟩ := canonical_mask_height D.toPrefixArithmetic
  obtain ⟨Sn, hSn⟩ := mask_exists (R.len 2) A (by omega)
    (by rw [(show (2 : ℤ) ^ R.len 2 = D.q from R.pow2)]; change A < D.q
        have hq := (arithmetic_geometry D.toPrefixArithmetic).2.2.2.2.2.2.2.1
        have hP := (arithmetic_geometry D.toPrefixArithmetic).2.2.2.2.2.2.1; omega)
  obtain ⟨Sw, hSw⟩ := mask_exists (R.len 4) (D.H / 4 - A) (by omega)
    (by rw [(show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)]; change D.H / 4 - A < D.H / 4; omega)
  obtain ⟨⟨preJ⟩, hZ0, hZv⟩ := wj_prefix R.toRowData A f hA hAP hf hfg heq Sn Sw hSn hSw
  obtain ⟨K⟩ := select_T R A hA hAP hprev hnext Sn Sw hSn hSw
  obtain ⟨preT⟩ := t_extension R.toRowData A f heq Sn Sw hSn hSw preJ K
  obtain ⟨preV⟩ := uv_extension R K preT
  obtain ⟨pre⟩ := complete_occurrences R K preV
  let phi : Occ R.len → Fin k := physical (t := t) x
  let word := pre.word.map phi
  have hinj : Function.Injective phi := physical_injective h
  have hsurj : Function.Surjective phi := by
    change Function.Surjective (physical (t := t) x)
    intro j
    obtain ⟨o, ho, he⟩ := List.mem_map.mp
      ((physical_inventory h).mem_iff.mpr (List.mem_finRange j))
    exact ⟨o, he⟩
  have hnd := (pre.perm.nodup_iff.mpr Finset.univ.nodup_toList).map hinj
  have hp : word.Perm (List.finRange k) := by
    rw [List.perm_ext_iff_of_nodup hnd (List.nodup_finRange k)]
    intro j
    have ⟨o, ho⟩ := hsurj j
    have hom : o ∈ pre.word := pre.perm.mem_iff.mpr (by simp)
    exact ⟨fun _ => List.mem_finRange j, fun _ => List.mem_map.mpr ⟨o, hom, ho⟩⟩
  have hlegal : InStrip (actualSource k t) (halfCapacity k) 0 word := by
    apply (inStrip_map phi (actualSource k t) (halfCapacity k) 0 pre.word).mpr
    exact pre.legal
  refine ⟨word, hp, ?_, ?_, ?_⟩
  · change (pre.word.map phi).head? = some x
    rw [List.head?_map, pre.head]
    change some (sourceParent t x 0) = some x
    rw [source_parent_zero h]
  · change ((pre.word.map phi).map (actualSource k t)).sum = 0
    rw [List.map_map]
    exact pre.height
  · intro j
    simpa only [zero_add] using inStrip_prefix hlegal j

end D5.S3.Combinatorics.Circle.M5FullWordConsumer
