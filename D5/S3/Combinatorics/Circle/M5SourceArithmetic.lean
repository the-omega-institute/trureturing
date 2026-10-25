/- GID: D5/S3/Combinatorics/Circle/M5SourceArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5SourceArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Source-derived hard geometry and canonical mask bounds. -/
module
import all D5.S3.Combinatorics.Circle.M5SourceRows
/-! # M5SourceArithmetic -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth
open Fin.NatCast
open scoped BigOperators

structure PrefixArithmetic where
  N : ℤ
  Q : ℤ
  C : ℤ
  a : ℤ
  b : ℤ
  q : ℤ
  H : ℤ
  z : ℤ
  n : ℤ
  Δ : ℤ
  b1 : ℤ
  r : ℤ
  w : ℤ
  v : ℤ
  e : ℤ
  u : ℤ
  F : ℤ
  y : ℤ
  N_quarter : N = 4 * Q - 1
  C_quarter : C = 2 * Q - 1
  Q_positive : 0 < Q
  H_q : H = 2 * q
  H_four : 4 * (H / 4) = H
  H_eight : 8 ≤ H
  H_cases : H = 8 ∨ H = 16 ∨ 32 ≤ H
  a_positive : 0 < a
  ab : a < b ∧ b < 2 * a
  n_minimum : a ≤ n
  nzb : n < z ∧ z < b
  delta_two : 2 ≤ Δ
  delta_even : Δ % 2 = 0
  delta_n : H * Δ < n
  N_z : N = H * z + b
  N_b : N = H * b + n
  z_n : z = n + (H - 1) * Δ
  b_n : b = n + H * Δ
  b1_n : b1 = n + H ^ 2 * Δ
  c0_hard : 2 * a < N - H * a
  delta_hard : a - 1 < (H ^ 2 + 1) * Δ
  b1_hard : 2 * a - 1 ≤ b1
  w_bounds : a ≤ w ∧ w ≤ 2 * a - 3
  w_hard : n + Δ < w
  r_bounds : 1 ≤ r ∧ r ≤ H / 4
  w_source : w = N - 2 * r * b1
  v_source : v = N - q * w
  v_minimum : b ≤ v
  e_one : 1 ≤ e
  u_source : u = N - 2 * e * v
  T_maximum : 2 * e * v ≤ N - a
  F_two : 2 ≤ F
  U_threshold : N + 1 ≤ 2 * F * u
  U_maximum : F * u ≤ H * z
  u_above : z < u
  u_bound : u ≤ C
  branch : (F = H / 2 ∧ 4 ≤ H / 2) ∨ F ≤ H / 4
  y_source : y = N - F * u
  y_minimum : b ≤ y
  odd_z : z % 2 = 1
  odd_n : n % 2 = 1
  odd_b : b % 2 = 1
  odd_w : w % 2 = 1
  odd_u : u % 2 = 1

private structure Arithmetic extends PrefixArithmetic where
  a0 : ℤ
  a0_bounds : a ≤ a0 ∧ a0 ≤ z
  odd_a0 : a0 % 2 = 1

theorem arithmetic_geometry (D : PrefixArithmetic) :
    0 < D.n ∧ 0 < D.z ∧ 0 < D.b ∧ 0 < D.w ∧ 0 < D.v ∧ 0 < D.u ∧
      2 ≤ D.H / 4 ∧ D.q = 2 * (D.H / 4) ∧
      D.N + D.a ≤ D.H * D.w ∧ D.b < D.w ∧ D.z ≤ 2 * D.a - 3 := by
  have ha := D.a_positive
  have hn := D.n_minimum
  have hnb := D.nzb
  have hab := D.ab
  have hwa := D.w_bounds
  have hvb := D.v_minimum
  have huz := D.u_above
  have hH := D.H_eight
  have hH4 := D.H_four
  have hHq := D.H_q
  have hn0 : 0 < D.n := by omega
  have hz0 : 0 < D.z := by omega
  have hb0 : 0 < D.b := by omega
  have hw0 : 0 < D.w := by omega
  have hv0 : 0 < D.v := by omega
  have hu0 : 0 < D.u := by omega
  have hP0 : 2 ≤ D.H / 4 := by omega
  have hq : D.q = 2 * (D.H / 4) := by omega
  have hev : 2 * D.v ≤ 2 * D.e * D.v := by
    have hh := mul_nonneg (sub_nonneg.mpr D.e_one) (le_of_lt hv0)
    nlinarith only [hh]
  have hHw : D.N + D.a ≤ D.H * D.w := by
    have hh := congrArg (fun h : ℤ => h * D.w) D.H_q
    nlinarith only [D.v_source, D.T_maximum, hev, hh]
  have hwb : D.b < D.w := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by omega : 0 ≤ D.H)
    nlinarith only [hmul, hHw, D.N_b, hn0, ha]
  exact ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP0, hq, hHw, hwb, by omega⟩

theorem canonical_mask_height (D : PrefixArithmetic) :
    let P0 := D.H / 4
    let K := D.w - D.n
    let g := (D.w - 1) / 2
    ∃ A f : ℤ, 1 ≤ A ∧ A ≤ P0 ∧ 0 ≤ f ∧ f ≤ g ∧
      2 * f = D.n + D.w + D.Δ - 2 * A * K ∧
      2 * K * (A - 1) < D.n + D.Δ + 1 ∧
      D.n + D.Δ + 1 ≤ 2 * K * A := by
  let P0 := D.H / 4
  let K := D.w - D.n
  let g := (D.w - 1) / 2
  let f0 := D.n - (K - D.Δ) / 2
  obtain ⟨hn0, _, _, _, _, _, hP0, _, hHw, _, _⟩ := arithmetic_geometry D
  have hδ2 := D.delta_two
  have hδeven := D.delta_even
  have hoddw := D.odd_w
  have hoddn := D.odd_n
  have hnmin := D.n_minimum
  have hwmax := D.w_bounds.2
  have hwhard := D.w_hard
  have hH8 := D.H_eight
  have hK : 0 < K := by dsimp only [K]; omega
  have hwe : D.w ≤ 2 * D.n - 3 := by omega
  have hgeq : 2 * g = D.w - 1 := by dsimp only [g]; omega
  have hf0eq : 2 * f0 = 2 * D.n - K + D.Δ := by dsimp only [f0, K]; omega
  have hKsmall : K ≤ g := by dsimp only [K]; omega
  have hf0 : 0 < f0 := by dsimp only [K] at hf0eq; omega
  have hHK : D.n + D.a + D.H ^ 2 * D.Δ ≤ D.H * K := by
    have hh := congrArg (fun v : ℤ => D.H * v) D.b_n
    dsimp only [K]
    nlinarith only [hHw, D.N_b, hh]
  have haM : D.a ≤ (D.H ^ 2 + 1) * D.Δ := by
    have hh := D.delta_hard
    omega
  have hbM : D.b ≤ 2 * D.a - 1 := by
    have hh := D.ab.2
    omega
  have hnma : D.n - D.a ≤ (D.H ^ 2 - D.H + 1) * D.Δ - 1 := by
    nlinarith only [D.b_n, haM, hbM]
  let fend := f0 - (P0 - 1) * K
  have hfour : 4 * (fend - g) = 2 * D.Δ - D.H * K + 2 * D.n + 2 := by
    have hh := congrArg (fun p : ℤ => p * K) D.H_four
    change 4 * P0 * K = D.H * K at hh
    dsimp only [fend]
    dsimp only [K] at hf0eq ⊢
    dsimp only [K] at hh
    nlinarith only [hh, hf0eq, hgeq]
  have hprod : 10 ≤ (D.H - 3) * D.Δ := by
    have hh := mul_nonneg (show 0 ≤ D.H - 8 by omega) (show 0 ≤ D.Δ - 2 by omega)
    nlinarith only [hh, hH8, hδ2]
  have hend : fend ≤ g := by nlinarith only [hfour, hHK, hnma, hprod]
  have hmax : ((P0 - 1).toNat : ℤ) = P0 - 1 := Int.toNat_of_nonneg (by omega)
  have hex : ∃ j : ℕ, (j : ℤ) ≤ P0 - 1 ∧ f0 - (j : ℤ) * K ≤ g := by
    refine ⟨(P0 - 1).toNat, ?_⟩
    rw [hmax]
    exact ⟨le_refl _, hend⟩
  let j := Nat.find hex
  have hj : (j : ℤ) ≤ P0 - 1 ∧ f0 - (j : ℤ) * K ≤ g := Nat.find_spec hex
  have hprevious : j ≠ 0 → g < f0 - ((j - 1 : ℕ) : ℤ) * K := by
    intro hj0
    have hless : j - 1 < Nat.find hex := by change j - 1 < j; omega
    have hh := Nat.find_min hex hless
    by_contra hn
    apply hh
    exact ⟨by omega, by omega⟩
  let A := (j : ℤ) + 1
  let f := f0 - (j : ℤ) * K
  have hf : 0 ≤ f := by
    by_cases hj0 : j = 0
    · simpa only [f, hj0, Nat.cast_zero, zero_mul, sub_zero] using le_of_lt hf0
    · have hh := hprevious hj0
      have he : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
      rw [he] at hh
      dsimp only [f]
      nlinarith only [hh, hKsmall]
  have hfeq : 2 * f = D.n + D.w + D.Δ - 2 * A * K := by
    dsimp only [f, A]
    dsimp only [K] at hf0eq ⊢
    nlinarith only [hf0eq]
  refine ⟨A, f, by dsimp only [A]; omega, by dsimp only [A]; omega,
    hf, hj.2, hfeq, ?_, ?_⟩
  · by_cases hj0 : j = 0
    · simp only [A, hj0, Nat.cast_zero, zero_add, sub_self, mul_zero]
      omega
    · have hh := hprevious hj0
      have he : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
      rw [he] at hh
      dsimp only [A]
      dsimp only [K] at hf0eq ⊢
      dsimp only [K] at hh
      nlinarith only [hh, hf0eq, hgeq]
  · dsimp only [K] at hfeq ⊢
    nlinarith only [hfeq, hgeq, hj.2]

private theorem half_source_bounds (D : Arithmetic) (hF : D.F = D.H / 2) :
    D.u < 2 * D.z ∧ D.N + 1 ≤ D.H * D.u ∧ D.n < D.H ^ 2 * D.Δ ∧
      2 * D.H < D.n ∧ 2 * D.n < D.b1 ∧ D.b < D.u ∧
      D.n < D.H * (D.u - D.b) ∧ 2 * (D.u - D.b) ≤ D.u - 1 := by
  obtain ⟨hn0, hz0, hb0, _, _, _, _, _, _, _, _⟩ := arithmetic_geometry D.toPrefixArithmetic
  have hH8 := D.H_eight
  have hH4 := D.H_four
  have hδ2 := D.delta_two
  have h2F : 2 * D.F = D.H := by omega
  have h2Fu := congrArg (fun F : ℤ => F * D.u) h2F
  have hHu : D.N + 1 ≤ D.H * D.u := by
    nlinarith only [D.U_threshold, h2Fu]
  have huzle : D.u ≤ 2 * D.z := by
    by_contra hh
    have hm := mul_pos (by omega : 0 < D.H) (show 0 < D.u - 2 * D.z by omega)
    nlinarith only [D.U_maximum, h2Fu, hm]
  have huz : D.u < 2 * D.z := by
    have hh := D.odd_u
    omega
  have hb1pos : 0 < D.b1 := by
    have hh := D.b1_hard
    have ha := D.a_positive
    omega
  have hr4 : 4 * D.r ≤ D.H := by
    have hh := D.r_bounds.2
    omega
  have hmul := mul_le_mul_of_nonneg_right hr4 (le_of_lt hb1pos)
  have hwmax : D.w ≤ 2 * D.n - 3 := by
    have hw := D.w_bounds.2
    have hn := D.n_minimum
    omega
  have hpoly : 6 ≤ (D.H - 2) * (D.H ^ 2 * D.Δ - D.n) := by
    have hbmul := congrArg (fun b : ℤ => D.H * b) D.b_n
    have hb1mul := congrArg (fun b : ℤ => D.H * b) D.b1_n
    nlinarith only [hmul, D.w_source, hwmax, D.N_b, hbmul, hb1mul]
  have hnδ : D.n < D.H ^ 2 * D.Δ := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ D.H - 2)
      (show D.H ^ 2 * D.Δ - D.n ≤ 0 by omega)
    omega
  have hnH : 2 * D.H < D.n := by
    have hm := mul_nonneg (by omega : 0 ≤ D.H) (show 0 ≤ D.Δ - 2 by omega)
    nlinarith only [hm, D.delta_n]
  have hnB1 : 2 * D.n < D.b1 := by nlinarith only [hnδ, D.b1_n]
  have hBu : D.n < D.H * (D.u - D.b) := by nlinarith only [hHu, D.N_b]
  have hbu : D.b < D.u := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ D.H)
      (show D.u - D.b ≤ 0 by omega)
    nlinarith only [hm, hBu, hn0]
  have hwidth : 2 * (D.u - D.b) ≤ D.u - 1 := by
    have hzb := D.nzb.2
    omega
  exact ⟨huz, hHu, hnδ, hnH, hnB1, hbu, hBu, hwidth⟩

theorem gate_limits (D : PrefixArithmetic) :
    let ell := (D.u - D.z) / 2
    let hi := D.u - (D.z + 1) / 2
    let W := (D.u - 1) / 2
    0 < ell ∧ 0 ≤ W ∧ 2 * ell = D.u - D.z ∧
      2 * hi = 2 * D.u - D.z - 1 ∧ 2 * W = D.u - 1 ∧ hi = ell + W := by
  obtain ⟨_, hz, _, _, _, hu, _, _, _, _, _⟩ := arithmetic_geometry D
  have hou := D.odd_u
  have hoz := D.odd_z
  have huz := D.u_above
  dsimp only
  omega

private theorem lower_T_coefficient (D : Arithmetic) (hF : D.F ≤ D.H / 4) :
    D.u > 2 * D.z ∧ ∃ c : ℕ, (c : ℤ) ≤ D.q - 1 ∧
      (D.u - D.z) / 2 ≤ (c : ℤ) * D.z ∧
      (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 := by
  obtain ⟨hn0, hz0, hb0, _, _, hu0, _, _, _, _, _⟩ := arithmetic_geometry D.toPrefixArithmetic
  have hH := D.H_eight
  have hH4 := D.H_four
  have hHq := D.H_q
  have hF4 : 4 * D.F ≤ D.H := by omega
  have hFu := mul_le_mul_of_nonneg_right hF4 (le_of_lt hu0)
  have huz : 2 * D.z < D.u := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by omega : 0 ≤ D.H)
    nlinarith only [hm, hFu, D.U_threshold, D.N_z, hb0]
  let ell := (D.u - D.z) / 2
  let hi := D.u - (D.z + 1) / 2
  let W := (D.u - 1) / 2
  obtain ⟨hell0, hW0, hell, hhi, hW, hhiW⟩ := gate_limits D.toPrefixArithmetic
  have hzW : D.z ≤ W := by
    have hou := D.odd_u
    dsimp only [W]
    omega
  have hb2z : D.b < 2 * D.z := by
    have hh := D.ab.2
    have hn := D.n_minimum
    have hnz := D.nzb.1
    omega
  have hC : 2 * D.C = D.H * D.z + D.b - 1 := by
    nlinarith only [D.C_quarter, D.N_quarter, D.N_z]
  have humm : D.u ≤ (D.H - 1) * D.z := by
    have hm := mul_nonneg (show 0 ≤ D.H - 4 by omega) (le_of_lt hz0)
    nlinarith only [hm, D.u_bound, hC, hb2z]
  have hmax : ell ≤ (D.q - 1) * D.z := by
    have hh := congrArg (fun H : ℤ => H * D.z) hHq
    nlinarith only [humm, hell, hh]
  have hq0 : 0 ≤ D.q - 1 := by omega
  have hqcast : (((D.q - 1).toNat : ℕ) : ℤ) = D.q - 1 := Int.toNat_of_nonneg hq0
  have hex : ∃ c : ℕ, ell ≤ (c : ℤ) * D.z := by
    refine ⟨(D.q - 1).toNat, ?_⟩
    rw [hqcast]
    exact hmax
  let c := Nat.find hex
  have hc : ell ≤ (c : ℤ) * D.z := Nat.find_spec hex
  have hcmax : (c : ℤ) ≤ D.q - 1 := by
    have hh := Nat.find_min' hex (show ell ≤ ((D.q - 1).toNat : ℤ) * D.z by
      rw [hqcast]; exact hmax)
    have hh' : (c : ℤ) ≤ ((D.q - 1).toNat : ℤ) := by exact_mod_cast hh
    omega
  have hc0 : c ≠ 0 := by intro hh; rw [hh] at hc; simp only [Nat.cast_zero, zero_mul] at hc; omega
  have hprev : ((c - 1 : ℕ) : ℤ) * D.z < ell := by
    have hh := Nat.find_min hex (show c - 1 < Nat.find hex by change c - 1 < c; omega)
    exact lt_of_not_ge hh
  have hcast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
  rw [hcast] at hprev
  have hupper : (c : ℤ) * D.z ≤ hi := by nlinarith only [hprev, hzW, hhiW]
  exact ⟨huz, c, hcmax, hc, hupper⟩


theorem wj_geometry (D : PrefixArithmetic) (f : ℤ) (hf : 0 ≤ f)
    (hfg : f ≤ (D.w - 1) / 2) :
    2 * D.C = D.N - 1 ∧ D.N = D.H * D.n + D.b1 ∧ D.b - D.z = D.Δ ∧
      D.w < D.b1 ∧ 0 < D.N - (D.q + 1) * D.w ∧
      0 ≤ D.q * D.n + f ∧ D.q * D.n + f ≤ D.C ∧
      2 * f + D.N - D.w ≤ 2 * D.C ∧
      0 < 2 * f + D.N - (D.q + 1) * D.w ∧
      2 * f + D.N - (D.q + 1) * D.w ≤ D.v - 1 := by
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D
  have hH := D.H_eight
  have hHq := D.H_q
  have hqn0 : 0 ≤ D.q * D.n := mul_nonneg (by omega) (le_of_lt hn0)
  have h2C : 2 * D.C = D.N - 1 := by nlinarith only [D.C_quarter, D.N_quarter]
  have hNb1 : D.N = D.H * D.n + D.b1 := by
    have hh := congrArg (fun b : ℤ => D.H * b) D.b_n
    nlinarith only [D.N_b, D.b1_n, hh]
  have hbz : D.b - D.z = D.Δ := by nlinarith only [D.b_n, D.z_n]
  have hwB1 : D.w < D.b1 := by have hh := D.w_bounds.2; have hh' := D.b1_hard; omega
  have hfg' : 2 * f ≤ D.w - 1 := by have hh := D.odd_w; omega
  have hNw : 0 < D.N - (D.q + 1) * D.w := by
    have hq1 : 0 < D.q + 1 := by omega
    have hw2a : D.w < 2 * D.a := by have hh := D.w_bounds.2; omega
    have hm := mul_pos hq1 (sub_pos.mpr hw2a)
    have hHa := congrArg (fun H : ℤ => H * D.a) hHq
    nlinarith only [hm, hHa, D.c0_hard]
  have hqN := congrArg (fun H : ℤ => H * D.n) hHq
  refine ⟨h2C, hNb1, hbz, hwB1, hNw, by omega, ?_, by omega, by omega, ?_⟩
  · nlinarith only [hfg', hNb1, hwB1, hqN, h2C]
  · nlinarith only [hfg', D.v_source]

end D5.S3.Combinatorics.Circle.M5FullWordConsumer
