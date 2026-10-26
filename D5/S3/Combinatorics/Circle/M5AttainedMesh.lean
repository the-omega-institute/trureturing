/- GID: D5/S3/Combinatorics/Circle/M5AttainedMesh
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5AttainedMesh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Finite supported masks and both source-attained T branches. -/
module
import all D5.S3.Combinatorics.Circle.M5SourceArithmetic
public import D5.S3.Combinatorics.Circle.DyadicPrefix
/-! # M5AttainedMesh -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth
open Fin.NatCast
open scoped BigOperators

/- Selecting a full dyadic mask and removing unavailable indices loses no
more than the total missing weight. The resulting mask is literal support. -/
private theorem supported_round_up (u : ℕ) (S : Finset (Fin u)) (d : ℕ)
    (hd : d ≤ ∑ i ∈ S, 2 ^ i.val) :
    ∃ J : Finset (Fin u), J ⊆ S ∧ d ≤ ∑ i ∈ J, 2 ^ i.val ∧
      (∑ i ∈ J, 2 ^ i.val) ≤ d + ∑ i ∈ Sᶜ, 2 ^ i.val := by
  classical
  let missing := ∑ i ∈ Sᶜ, 2 ^ i.val
  have hfull : (∑ i : Fin u, 2 ^ i.val) = 2 ^ u - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [Nat.reduceSub, mul_one] using
      geom_sum_mul_of_one_le (by decide : 1 ≤ (2 : ℕ)) u
  have htotal := Finset.sum_compl_add_sum S (fun i : Fin u => 2 ^ i.val)
  have hpow : 0 < 2 ^ u := by positivity
  have hbound : d + missing < 2 ^ u := by
    dsimp only [missing]
    omega
  let R := DyadicPrefix.bitSubset u (d + missing) hbound
  let J := R ∩ S
  have hR : (∑ i ∈ R, 2 ^ i.val) = d + missing := DyadicPrefix.bit_subset_sum hbound
  have hsplit := Finset.sum_inter_add_sum_sdiff R S (fun i : Fin u => 2 ^ i.val)
  have hsub : R \ S ⊆ Sᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
  have hlost : (∑ i ∈ R \ S, 2 ^ i.val) ≤ missing :=
    Finset.sum_le_sum_of_subset hsub
  refine ⟨J, Finset.inter_subset_right, ?_, ?_⟩ <;> dsimp only [J] <;> omega

private theorem two_step_crossing (n ell hi W a b : ℤ) (M : ℕ)
    (hell : ell ≤ n) (hwidth : hi = ell + W)
    (ha : 0 < a ∧ a ≤ W) (hb : 0 < b ∧ b ≤ W)
    (hend : n - (M : ℤ) * (a + b) ≤ hi) :
    ∃ c f : ℕ, c ≤ M ∧ f ≤ c ∧ c ≤ f + 1 ∧
      ell ≤ n - (c : ℤ) * a - (f : ℤ) * b ∧
      n - (c : ℤ) * a - (f : ℤ) * b ≤ hi := by
  have hex : ∃ j : ℕ, n - (j : ℤ) * (a + b) ≤ hi := ⟨M, hend⟩
  let j := Nat.find hex
  have hj : n - (j : ℤ) * (a + b) ≤ hi := Nat.find_spec hex
  have hjM : j ≤ M := Nat.find_min' hex hend
  by_cases hj0 : j = 0
  · refine ⟨0, 0, by omega, by omega, by omega, ?_, ?_⟩ <;> simp_all
  · have hcast : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
    have hprev : hi < n - ((j - 1 : ℕ) : ℤ) * (a + b) :=
      lt_of_not_ge (Nat.find_min hex (show j - 1 < Nat.find hex by change j - 1 < j; omega))
    rw [hcast] at hprev
    by_cases hmid : n - (j : ℤ) * a - ((j : ℤ) - 1) * b ≤ hi
    · refine ⟨j, j - 1, hjM, by omega, by omega, ?_, ?_⟩
      · rw [hcast]; nlinarith only [hprev, hwidth, ha.2]
      · simpa only [hcast] using hmid
    · refine ⟨j, j, hjM, by omega, by omega, ?_, ?_⟩
      · push Not at hmid
        nlinarith only [hmid, hwidth, hb.2]
      · nlinarith only [hj]

private theorem half_many_T_coefficients (D : Arithmetic) (hF : D.F = D.H / 2)
    (he : 2 ≤ D.e) (A : ℤ)
    (hA : 1 ≤ A) (hcanonical : 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1) :
    A = 1 ∧ ∃ c f : ℕ, (c : ℤ) ≤ D.H / 4 - 1 ∧ f ≤ c ∧ c ≤ f + 1 ∧
      (D.u - D.z) / 2 ≤ D.n - (c : ℤ) * (2 * D.b - D.w) - (f : ℤ) * (D.u - D.b) ∧
      D.n - (c : ℤ) * (2 * D.b - D.w) - (f : ℤ) * (D.u - D.b) ≤
        D.u - (D.z + 1) / 2 := by
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, _, hwb, hzmax⟩ := arithmetic_geometry D.toPrefixArithmetic
  obtain ⟨huz, hHu, hnδ, hnH, hb1n, hbu, hBu, hBuW⟩ := half_source_bounds D hF
  obtain ⟨hell0, hW0, hell, hhi, hW, hhiW⟩ := gate_limits D.toPrefixArithmetic
  have hH := D.H_eight
  have hH4 := D.H_four
  have hδ := D.delta_two
  have h4v : 4 * D.v ≤ 2 * D.e * D.v := by
    have hm := mul_nonneg (show 0 ≤ D.e - 2 by omega) (le_of_lt hv0)
    nlinarith only [hm]
  have h3b : 3 * D.b < 2 * D.w := by
    have hmul := congrArg (fun q : ℤ => 2 * q * D.w) D.H_q
    have hdiff : 0 < D.H * (2 * D.w - 3 * D.b) := by
      nlinarith only [h4v, D.u_source, D.v_source, hmul, D.N_b, hn0, hu0]
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ D.H)
      (show 2 * D.w - 3 * D.b ≤ 0 by omega)
    omega
  have hK : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) := by
    have hm := mul_nonneg (show 0 ≤ 3 * D.H - 1 by omega) (show 0 ≤ D.Δ by omega)
    nlinarith only [h3b, D.b_n, hδ, hH]
  have hAone : A = 1 := by
    by_contra hh
    have hm := mul_nonneg (show 0 ≤ 2 * (D.w - D.n) by omega) (show 0 ≤ A - 2 by omega)
    nlinarith only [hm, hK, hcanonical]
  refine ⟨hAone, ?_⟩
  let As := 2 * D.b - D.w
  let Bu := D.u - D.b
  let P := D.H / 4
  have hwmax : D.w ≤ 2 * D.n - 3 := by have hh := D.w_bounds.2; have hh' := D.n_minimum; omega
  have hAs : 0 < As ∧ 2 * As ≤ D.u - 1 := by
    dsimp only [As]
    constructor
    · nlinarith only [hwmax, D.b_n, hδ, hH]
    · omega
  have hAsH : 2 * D.n < D.H * As := by
    have hm := mul_le_mul_of_nonneg_left hwmax (by omega : 0 ≤ D.H)
    have hbmul := congrArg (fun b : ℤ => D.H * b) D.b_n
    dsimp only [As]
    nlinarith only [hm, hbmul, hnδ, hH]
  have hsum : 3 * D.n < D.H * (As + Bu) := by
    dsimp only [Bu]
    nlinarith only [hAsH, hBu]
  have hhiH : 3 * D.n < D.H * (2 * (D.u - (D.z + 1) / 2) - D.n) := by
    have hzm := congrArg (fun z : ℤ => D.H * z) D.z_n
    have hbmul := congrArg (fun b : ℤ => D.H * b) D.b_n
    have hm : 2 * D.H ≤ D.H * D.Δ := by nlinarith only [mul_nonneg (by omega : 0 ≤ D.H) (show 0 ≤ D.Δ - 2 by omega)]
    nlinarith only [hHu, D.N_b, hzm, hbmul, hhi, hnδ, hm, hH]
  have hend : D.n - (P - 1) * (As + Bu) ≤ D.u - (D.z + 1) / 2 := by
    have hsp := mul_nonneg (show 0 ≤ P - 1 by dsimp only [P]; omega)
      (show 0 ≤ D.H * (As + Bu) - 3 * D.n by omega)
    have hp : 4 * P = D.H := hH4
    have hpn := congrArg (fun v : ℤ => v * D.n) hp
    have hnprod := mul_nonneg (show 0 ≤ 2 * P - 3 by dsimp only [P]; omega) (le_of_lt hn0)
    have hout : 0 < D.H * ((D.u - (D.z + 1) / 2) - D.n + (P - 1) * (As + Bu)) := by
      nlinarith only [hsp, hhiH, hnprod, hpn]
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ D.H)
      (show (D.u - (D.z + 1) / 2) - D.n + (P - 1) * (As + Bu) ≤ 0 by omega)
    omega
  have hcast : (((P - 1).toNat : ℕ) : ℤ) = P - 1 := Int.toNat_of_nonneg (by dsimp only [P]; omega)
  have helln : (D.u - D.z) / 2 ≤ D.n := by have hn := D.n_minimum; omega
  obtain ⟨c, f, hc, hfc, hcf, hlo, hhi'⟩ := two_step_crossing D.n ((D.u - D.z) / 2)
    (D.u - (D.z + 1) / 2) ((D.u - 1) / 2) As Bu (P - 1).toNat
    helln hhiW ⟨hAs.1, by omega⟩ ⟨by dsimp only [Bu]; omega, by dsimp only [Bu]; omega⟩
    (by simpa only [hcast] using hend)
  refine ⟨c, f, ?_, hfc, hcf, hlo, hhi'⟩
  have hc' : (c : ℤ) ≤ ((P - 1).toNat : ℤ) := by exact_mod_cast hc
  dsimp only [P] at *
  omega

private theorem half_one_geometry (D : Arithmetic) (hF : D.F = D.H / 2)
    (he : D.e = 1) :
    D.H * (D.w - D.b) = D.n + D.u ∧
      D.H * (D.w - D.n) = D.H ^ 2 * D.Δ + D.n + D.u ∧
      2 * D.n < D.H * (D.w - D.b) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := arithmetic_geometry D.toPrefixArithmetic
  have hq := congrArg (fun q : ℤ => q * D.w) D.H_q
  have hn := D.N_b
  have hs := D.u_source
  rw [he] at hs
  have hB : D.H * (D.w - D.b) = D.n + D.u := by
    nlinarith only [hq, hs, D.v_source, hn]
  have hK : D.H * (D.w - D.n) = D.H ^ 2 * D.Δ + D.n + D.u := by
    have hh := congrArg (fun b : ℤ => D.H * b) D.b_n
    nlinarith only [hB, hh]
  have hu := (half_source_bounds D hF).2.2.2.2.2.1
  have hbn := D.b_n
  have hδ := mul_pos (by have hh := D.H_eight; omega : 0 < D.H)
    (by have hh := D.delta_two; omega : 0 < D.Δ)
  exact ⟨hB, hK, by nlinarith only [hB, hu, hbn, hδ]⟩

private theorem half_one_canonical_bounds (D : Arithmetic) (hF : D.F = D.H / 2)
    (he : D.e = 1) (A : ℤ) (hA : 1 ≤ A)
    (hprev : 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1)
    (hnext : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A) :
    6 * (A - 1) < D.H ∧ A ≤ D.r ∧
      D.z < 2 * (D.z - A * D.H * D.Δ) := by
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D.toPrefixArithmetic
  obtain ⟨huz, hHu, hnδ, hnH, hb1n, hbu, hBu, hBuW⟩ := half_source_bounds D hF
  obtain ⟨hB, hK, hBn⟩ := half_one_geometry D hF he
  have hH := D.H_eight
  have hH4 := D.H_four
  have hδ := D.delta_two
  have hK0 : 0 < D.w - D.n := by have hh := D.w_hard; omega
  have hB0 : 0 < D.w - D.b := by omega
  have hHK : 3 * (D.n + D.Δ + 1) < D.H * (D.w - D.n) := by
    have hm := mul_nonneg (show 0 ≤ D.H - 3 by omega) (show 0 ≤ D.Δ - 2 by omega)
    nlinarith only [hm, hnδ, hK, D.b_n, hbu, hH]
  have hAsmall : 6 * (A - 1) < D.H := by
    have hp : (D.w - D.n) * (6 * (A - 1) - D.H) < 0 := by
      nlinarith only [hHK, hprev]
    by_contra hh
    have hm := mul_nonneg (le_of_lt hK0) (show 0 ≤ 6 * (A - 1) - D.H by omega)
    omega
  let Dr := D.H * (2 * D.r - 1) + 1
  have hr := D.r_bounds
  have hDr0 : 0 < Dr := by
    dsimp only [Dr]
    have hm := mul_nonneg (show 0 ≤ D.H by omega) (show 0 ≤ 2 * D.r - 1 by omega)
    omega
  have hid : Dr * (D.H * D.Δ) = (D.H - 2 * D.r) * D.n - (D.w - D.b) := by
    rw [D.w_source, D.N_b, D.b_n, D.b1_n]
    dsimp only [Dr]
    ring
  have hDrD : Dr * D.Δ < D.n := by
    have hid' : D.H * (Dr * D.Δ - D.n) < 0 := by
      have hm := mul_pos (show 0 < D.r by omega) hn0
      nlinarith only [hid, hm, hB0]
    by_contra hh
    have hm := mul_nonneg (show 0 ≤ D.H by omega) (show 0 ≤ Dr * D.Δ - D.n by omega)
    omega
  have hDrmax : 2 * Dr ≤ D.H ^ 2 := by
    have hm := mul_nonneg (show 0 ≤ D.H by omega) (show 0 ≤ D.H - 4 * D.r by omega)
    dsimp only [Dr]
    nlinarith only [hm, hH]
  have hDrK : Dr * (D.w - D.n) = (D.H - 2 * D.r) * D.n +
      D.H * (2 * D.r - 1) * (D.w - D.b) := by
    have heq : D.w - D.n = D.H * D.Δ + (D.w - D.b) := by nlinarith only [D.b_n]
    rw [heq, mul_add, hid]
    dsimp only [Dr]
    ring
  have hDrKn : (D.H + 2 * D.r - 2) * D.n < Dr * (D.w - D.n) := by
    have hm := mul_pos (show 0 < 2 * D.r - 1 by omega)
      (show 0 < D.H * (D.w - D.b) - 2 * D.n by omega)
    nlinarith only [hm, hDrK]
  have hterm : Dr < (D.H - 2) * D.n := by
    have hm := mul_pos (show 0 < D.H - 2 by omega) (show 0 < D.n - 2 * D.H by omega)
    nlinarith only [hm, hDrmax, sq_nonneg (D.H - 2), hH]
  have hrK : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * D.r := by
    have hm := mul_pos (show 0 < 2 * D.r by omega)
      (show 0 < Dr * (D.w - D.n) - (D.H + 2 * D.r - 2) * D.n by omega)
    have hm2 := mul_nonneg (show 0 ≤ 4 * D.r * (D.r - 1) by
      exact mul_nonneg (by omega) (by omega)) (le_of_lt hn0)
    have hpoly : 0 < Dr * (2 * (D.w - D.n) * D.r - D.n - D.Δ - 1) := by
      dsimp only [Dr] at hm2 ⊢
      dsimp only [Dr] at hDrD hterm
      nlinarith only [hm, hm2, hDrD, hterm]
    by_contra hh
    have hm3 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hDr0)
      (show 2 * (D.w - D.n) * D.r - D.n - D.Δ - 1 ≤ 0 by omega)
    omega
  have hAr : A ≤ D.r := by
    by_contra hh
    have hm := mul_nonneg (le_of_lt hK0) (show 0 ≤ A - 1 - D.r by omega)
    nlinarith only [hm, hprev, hrK]
  have hlower : D.z < 2 * (D.z - A * D.H * D.Δ) := by
    have hm := mul_nonneg (show 0 ≤ D.r - A by omega)
      (show 0 ≤ D.H * D.Δ by positivity)
    have hDrD' : (D.H * (2 * D.r - 1) + 1) * D.Δ < D.n := hDrD
    nlinarith only [hm, hDrD', D.z_n]
  exact ⟨hAsmall, hAr, hlower⟩

private theorem endpoint_polynomial (H A : ℤ) (hH : H = 8 ∨ H = 16 ∨ 32 ≤ H)
    (hA : 1 ≤ A) (hsmall : 6 * (A - 1) < H)
    (h8 : H = 8 → A = 1) :
    2 * H ≤ 4 * H * A + 3 * H - 16 * A ^ 2 - 20 * A := by
  rcases hH with hH | hH | hH
  · have hA1 := h8 hH
    subst H; subst A; norm_num
  · subst H
    have hA3 : A ≤ 3 := by omega
    have hm := mul_nonneg (show 0 ≤ A - 1 by omega) (show 0 ≤ 3 - A by omega)
    nlinarith only [hm, hA3]
  · have he : 0 ≤ 4 * H ^ 2 - 66 * H - 648 := by
      have hm := mul_nonneg (show 0 ≤ H - 32 by omega) (show 0 ≤ 4 * H + 62 by omega)
      nlinarith only [hm]
    have hq1 : 0 ≤ 5 * H - 36 := by omega
    have hc : 0 ≤ H + 6 - 6 * A := by omega
    have h1 := mul_nonneg (show 0 ≤ A - 1 by omega) he
    have h2 := mul_nonneg hc hq1
    have h3 := mul_nonneg (show 0 ≤ H by omega)
      (mul_nonneg (show 0 ≤ A - 1 by omega) hc)
    have hid : 3 * H * ((4 * H * A + 3 * H - 16 * A ^ 2 - 20 * A) - 2 * H) =
        (A - 1) * (4 * H ^ 2 - 66 * H - 648) +
        3 * (H + 6 - 6 * A) * (5 * H - 36) +
        8 * H * (A - 1) * (H + 6 - 6 * A) := by ring
    have hmul : 0 ≤ 3 * H * ((4 * H * A + 3 * H - 16 * A ^ 2 - 20 * A) - 2 * H) := by
      nlinarith only [hid, h1, h2, h3]
    by_contra hh
    have hm := mul_neg_of_pos_of_neg (show 0 < 3 * H by omega)
      (show (4 * H * A + 3 * H - 16 * A ^ 2 - 20 * A) - 2 * H < 0 by omega)
    omega

private theorem half_one_borrow_endpoint (D : Arithmetic) (hF : D.F = D.H / 2)
    (he : D.e = 1) (A : ℤ) (hA : 1 ≤ A) (hAP : A ≤ D.H / 4)
    (hprev : 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1)
    (hnext : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A)
    (hspan : (D.H / 4 - A) * (D.w - D.b) < (D.u - D.z) / 2) :
    D.z - A * D.H * D.Δ - min A (D.H / 4 - 1) * (D.u - D.b) ≤
      D.u - (D.z + 1) / 2 := by
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D.toPrefixArithmetic
  obtain ⟨huz, hHu, hnδ, hnH, hb1n, hbu, hBu, hBuW⟩ := half_source_bounds D hF
  obtain ⟨hB, hK, hBn⟩ := half_one_geometry D hF he
  obtain ⟨hsmall, hAr, hlow⟩ := half_one_canonical_bounds D hF he A hA hprev hnext
  obtain ⟨hell0, hW0, hell, hhi, hW, hhiW⟩ := gate_limits D.toPrefixArithmetic
  have hH := D.H_eight
  have hH4 := D.H_four
  have hδ := D.delta_two
  by_cases hexception : D.H = 8 ∧ A = 2
  · obtain ⟨hH8, hA2⟩ := hexception
    have hr2 : D.r = 2 := by have hh := D.r_bounds.2; omega
    have hw : D.w = 5 * D.n - 192 * D.Δ := by
      rw [D.w_source, D.N_b, D.b_n, D.b1_n, hH8, hr2]
      ring
    have hu : D.u = 31 * D.n - 1600 * D.Δ := by
      rw [hH8, hw, D.b_n, hH8] at hB
      linarith only [hB]
    have hU : 1 ≤ 239 * D.n - 12864 * D.Δ := by
      rw [hH8, hu, D.N_b, D.b_n, hH8] at hHu
      linarith only [hHu]
    have hnum : 1 ≤ 119 * D.n - 6405 * D.Δ := by
      by_cases hn : D.n ≤ 54 * D.Δ - 1
      · omega
      · omega
    have hmin : min A (D.H / 4 - 1) = 1 := by rw [hH8, hA2]; norm_num
    rw [hmin]
    rw [hA2, hH8]
    have hz8 := D.z_n
    have hb8 := D.b_n
    rw [hH8] at hz8 hb8
    linarith only [hnum, hhi, hz8, hb8, hu]
  · have h8 : D.H = 8 → A = 1 := by intro hh; omega
    have hAP' : A ≤ D.H / 4 - 1 := by
      rcases D.H_cases with hh | hh | hh
      · have ha := h8 hh; omega
      · omega
      · omega
    rw [min_eq_left hAP']
    have hp := endpoint_polynomial D.H A D.H_cases hA hsmall h8
    have hspan' : (3 * D.H - 4 * A) * D.n + 2 * D.H * (D.H - 1) * D.Δ <
        (D.H + 4 * A) * D.u := by
      have hm := mul_pos (show 0 < 8 * D.H by omega)
        (show 0 < (D.u - D.z) / 2 - (D.H / 4 - A) * (D.w - D.b) by omega)
      have h1 := congrArg (fun z : ℤ => 4 * D.H * z) hell
      have h2 := congrArg (fun z : ℤ => 8 * (D.H / 4 - A) * z) hB
      have h3 := congrArg (fun z : ℤ => 4 * D.H * z) D.z_n
      have h4 := congrArg (fun z : ℤ => 2 * z * (D.n + D.u)) hH4
      nlinarith only [hm, h1, h2, h3, h4]
    by_contra hbad
    have huupper : 2 * (A + 1) * D.u <
        (2 * A + 3) * D.n + 3 * (D.H - 1) * D.Δ + 1 := by
      have hbA := congrArg (fun b : ℤ => A * b) D.b_n
      nlinarith only [hbad, hbA, D.z_n, hhi]
    have hmul1 := mul_pos (show 0 < 2 * (A + 1) by omega)
      (sub_pos.mpr hspan')
    have hmul2 := mul_pos (show 0 < D.H + 4 * A by omega)
      (sub_pos.mpr huupper)
    have hdelta : 0 ≤ (D.H - 1) * (4 * D.H * A + D.H - 12 * A) * D.Δ := by
      have hid : 4 * D.H * A + D.H - 12 * A = 4 * (D.H - 3) * A + D.H := by ring
      rw [hid]
      have hm : 0 ≤ 4 * (D.H - 3) * A := mul_nonneg (by omega) (by omega)
      exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
    have hpn := mul_nonneg (sub_nonneg.mpr hp) (le_of_lt hn0)
    have hcontr : 2 * D.H * D.n < D.H + 4 * A := by
      nlinarith only [hmul1, hmul2, hdelta, hpn]
    have hn1 : 1 ≤ D.n := by omega
    have hm := mul_nonneg (show 0 ≤ D.H by omega) (show 0 ≤ D.n - 1 by omega)
    have hfour : 4 * A ≤ D.H := by omega
    nlinarith only [hcontr, hm, hfour]

private theorem one_step_crossing (n ell hi W step : ℤ) (M : ℕ)
    (hell : ell ≤ n) (hwidth : hi = ell + W) (hs : 0 < step ∧ step ≤ W)
    (hend : n - (M : ℤ) * step ≤ hi) :
    ∃ f : ℕ, f ≤ M ∧ ell ≤ n - (f : ℤ) * step ∧ n - (f : ℤ) * step ≤ hi := by
  have hex : ∃ f : ℕ, n - (f : ℤ) * step ≤ hi := ⟨M, hend⟩
  let f := Nat.find hex
  have hf : n - (f : ℤ) * step ≤ hi := Nat.find_spec hex
  have hfM : f ≤ M := Nat.find_min' hex hend
  refine ⟨f, hfM, ?_, hf⟩
  by_cases hf0 : f = 0
  · simpa only [hf0, Nat.cast_zero, zero_mul, sub_zero] using hell
  · have hprev := Nat.find_min hex (show f - 1 < Nat.find hex by change f - 1 < f; omega)
    have hcast : ((f - 1 : ℕ) : ℤ) = (f : ℤ) - 1 := by omega
    rw [hcast] at hprev
    push Not at hprev
    nlinarith only [hprev, hwidth, hs.2]

private theorem supported_multiple_crossing (u : ℕ) (S : Finset (Fin u))
    (ell hi W B A : ℤ) (hell : 0 < ell) (hB : 0 < B) (hA : 1 ≤ A)
    (hwidth : hi = ell + W) (hspan : ell ≤ (∑ j ∈ S, (2 : ℕ) ^ j.val : ℕ) * B)
    (hmissing : ((∑ j ∈ Sᶜ, (2 : ℕ) ^ j.val : ℕ) : ℤ) ≤ A - 1)
    (hgap : A * B ≤ W) :
    ∃ J : Finset (Fin u), J ⊆ S ∧
      ell ≤ ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) * B ∧
      ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) * B ≤ hi := by
  have hex : ∃ d : ℕ, ell ≤ (d : ℤ) * B :=
    ⟨∑ j ∈ S, (2 : ℕ) ^ j.val, hspan⟩
  let d := Nat.find hex
  have hd : ell ≤ (d : ℤ) * B := Nat.find_spec hex
  have hdmax : d ≤ ∑ j ∈ S, (2 : ℕ) ^ j.val := Nat.find_min' hex hspan
  have hd0 : d ≠ 0 := by intro hh; simp only [hh, Nat.cast_zero, zero_mul] at hd; omega
  have hprev := Nat.find_min hex (show d - 1 < Nat.find hex by change d - 1 < d; omega)
  have hcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [hcast] at hprev
  push Not at hprev
  obtain ⟨J, hJS, hlo, hhi⟩ := supported_round_up u S d hdmax
  refine ⟨J, hJS, ?_, ?_⟩
  · have hc : (d : ℤ) ≤ ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) := by exact_mod_cast hlo
    nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hB)]
  · have hc : ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) ≤
        (d : ℤ) + ((∑ j ∈ Sᶜ, (2 : ℕ) ^ j.val : ℕ) : ℤ) := by exact_mod_cast hhi
    have hc' : ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) ≤ (d : ℤ) + A - 1 := by omega
    have hm := mul_nonneg (show 0 ≤ (d : ℤ) + A - 1 -
      ((∑ j ∈ J, (2 : ℕ) ^ j.val : ℕ) : ℤ) by omega) (le_of_lt hB)
    nlinarith only [hm, hprev, hgap, hwidth]

def weight {u : ℕ} (S : Finset (Fin u)) : ℤ := ∑ j ∈ S, (2 : ℤ) ^ j.val

theorem weight_nat {u : ℕ} (S : Finset (Fin u)) :
    weight S = ((∑ j ∈ S, (2 : ℕ) ^ j.val : ℕ) : ℤ) := by
  simp only [weight, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

theorem weight_full (u : ℕ) : weight (Finset.univ : Finset (Fin u)) = (2 : ℤ) ^ u - 1 := by
  simp only [weight, Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul (2 : ℤ) u
  norm_num at h
  linarith only [h]

theorem weight_compl {u : ℕ} (S : Finset (Fin u)) :
    weight Sᶜ = (2 : ℤ) ^ u - 1 - weight S := by
  have hh := Finset.sum_compl_add_sum S (fun j : Fin u => (2 : ℤ) ^ j.val)
  have hf := weight_full u
  dsimp only [weight] at hf ⊢
  omega

theorem weight_nonneg {u : ℕ} (S : Finset (Fin u)) : 0 ≤ weight S := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem weight_mono {u : ℕ} {S T : Finset (Fin u)} (h : S ⊆ T) : weight S ≤ weight T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)

theorem mask_exists (u : ℕ) (c : ℤ) (hc : 0 ≤ c) (hcu : c < (2 : ℤ) ^ u) :
    ∃ S : Finset (Fin u), weight S = c := by
  have hcast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc
  have hnat : c.toNat < (2 : ℕ) ^ u := by
    have hc' : (c.toNat : ℤ) < (2 : ℤ) ^ u := by simpa only [hcast] using hcu
    exact_mod_cast hc'
  refine ⟨DyadicPrefix.bitSubset u c.toNat hnat, ?_⟩
  rw [weight_nat, DyadicPrefix.bit_subset_sum hnat, hcast]

private theorem supported_mask_exists {u : ℕ} (S : Finset (Fin u))
    (hmissing : weight Sᶜ = 0) (c : ℤ) (hc : 0 ≤ c) (hcu : c ≤ weight S) :
    ∃ J : Finset (Fin u), J ⊆ S ∧ weight J = c := by
  have hcast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc
  have hn : c.toNat ≤ ∑ j ∈ S, (2 : ℕ) ^ j.val := by
    rw [weight_nat] at hcu
    have hc' : (c.toNat : ℤ) ≤ ((∑ j ∈ S, (2 : ℕ) ^ j.val : ℕ) : ℤ) := by
      simpa only [hcast] using hcu
    exact_mod_cast hc'
  obtain ⟨J, hJS, hlo, hhi⟩ := supported_round_up u S c.toNat hn
  refine ⟨J, hJS, ?_⟩
  rw [weight_nat] at hmissing ⊢
  have hzero : (∑ j ∈ Sᶜ, (2 : ℕ) ^ j.val) = 0 := by exact_mod_cast hmissing
  have he : (∑ j ∈ J, (2 : ℕ) ^ j.val) = c.toNat := by omega
  rw [he, hcast]


end D5.S3.Combinatorics.Circle.M5FullWordConsumer
