/- GID: D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.claim; result=D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.result; claim=D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.claim
   digest: The homogeneous N=3 lowest quasienergy cannot have the predicted conformal limit. -/

/-
result:
  proof_shape: content (the polynomial coefficient induction remains after inlining auxiliaries).
  escape_witness: none
  admission_basis: open-problem-resolution (#19220; Refuted)
  Direct frozen dependencies: none (all imported mathematical declarations are from pinned Mathlib).
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The public definitions retain the polynomial, positive-root ordering and limit statement of
Eqs. (3.11)–(3.12) and (4.7)–(4.10); indices of poly are shifted by two.
The proof uses only i = 1. It does not prove existence or the exact value of the actual limit.
Auxiliary declarations below have no escape-witness role; their consumers are listed here.
poly: proof_shape: bind-only (definition); escape_witness: none; consumers: P, poly_coeff; Direct frozen dependencies: none.
P: proof_shape: bind-only (definition); escape_witness: none; consumers: P_closed, P_eval_closed, quasienergy_root, quasienergy_eval_zero, scaling_identity; Direct frozen dependencies: none.
quasienergy: proof_shape: bind-only (definition); escape_witness: none; consumers: claim, quasienergy_root, quasienergy_eval_zero, result; Direct frozen dependencies: none.
claim: proof_shape: bind-only (definition); escape_witness: none; consumers: result; Direct frozen dependencies: none.
Q: proof_shape: bind-only (definition); escape_witness: none; consumers: scaling_identity, Q_eq_tsum, Q_moving_limit, result; Direct frozen dependencies: none.
Fseries: proof_shape: bind-only (definition); escape_witness: none; consumers: six_terms_lower, interval_series_positive, predicted_series_positive, Q_moving_limit; Direct frozen dependencies: none.
predictedU: proof_shape: bind-only (definition); escape_witness: none; consumers: predicted_interval, predicted_series_positive, predicted_constant_div_three, result; Direct frozen dependencies: none.
qterm: proof_shape: bind-only (definition); escape_witness: none; consumers: Q_eq_tsum, qterm_bound, Q_moving_limit; Direct frozen dependencies: none.
majorant: proof_shape: bind-only (definition); escape_witness: none; consumers: majorant_summable, qterm_bound, Q_moving_limit; Direct frozen dependencies: none.
poly_coeff: proof_shape: content; escape_witness: none; consumers: P_closed; Direct frozen dependencies: none.
P_closed: proof_shape: content; escape_witness: none; consumers: P_eval_closed; Direct frozen dependencies: none.
P_eval_closed: proof_shape: content; escape_witness: none; consumers: scaling_identity; Direct frozen dependencies: none.
reverse_sign: proof_shape: bind-only; escape_witness: none; consumers: scaling_identity; Direct frozen dependencies: none.
reverse_power: proof_shape: bind-only; escape_witness: none; consumers: scaling_identity; Direct frozen dependencies: none.
reversed_choose: proof_shape: bind-only; escape_witness: none; consumers: scaling_identity; Direct frozen dependencies: none.
scaling_identity: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: none.
shifted_choose_limit: proof_shape: bind-only; escape_witness: none; consumers: Q_moving_limit; Direct frozen dependencies: none.
factorial_subseries_summable: proof_shape: bind-only; escape_witness: none; consumers: alternating_summable, six_terms_lower, majorant_summable; Direct frozen dependencies: none.
alternating_summable: proof_shape: bind-only; escape_witness: none; consumers: six_terms_lower; Direct frozen dependencies: none.
term_decreases: proof_shape: bind-only; escape_witness: none; consumers: six_terms_lower; Direct frozen dependencies: none.
six_terms_lower: proof_shape: bind-only; escape_witness: none; consumers: interval_series_positive; Direct frozen dependencies: none.
interval_series_positive: proof_shape: bind-only; escape_witness: none; consumers: predicted_series_positive; Direct frozen dependencies: none.
predicted_interval: proof_shape: bind-only; escape_witness: none; consumers: predicted_series_positive, result; Direct frozen dependencies: none.
predicted_series_positive: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
quasienergy_root: proof_shape: bind-only; escape_witness: none; consumers: quasienergy_eval_zero; Direct frozen dependencies: none.
inverse_cube_rpow: proof_shape: bind-only; escape_witness: none; consumers: quasienergy_eval_zero; Direct frozen dependencies: none.
quasienergy_eval_zero: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
Q_eq_tsum: proof_shape: bind-only; escape_witness: none; consumers: Q_moving_limit; Direct frozen dependencies: none.
coefficient_bound: proof_shape: bind-only; escape_witness: none; consumers: qterm_bound; Direct frozen dependencies: none.
majorant_summable: proof_shape: bind-only; escape_witness: none; consumers: Q_moving_limit; Direct frozen dependencies: none.
qterm_bound: proof_shape: bind-only; escape_witness: none; consumers: Q_moving_limit; Direct frozen dependencies: none.
Q_moving_limit: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
predicted_constant_div_three: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Field


namespace D5.S3.Quantum.SpinChains.AlcarazRamosConformalTowerRefutation

open Filter Topology

/-- Eqs. (3.11)–(3.12) with `N = 3` and `λ_j = 1`: `P_M(z) = P_{M−1}(z) − z P_{M−3}(z)`, and `P_M = 1` for `M ≤ 0`
(indices shifted by two: `poly n = P_{n−2}`). -/
noncomputable def poly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => poly (n + 2) - Polynomial.X * poly n

/-- `P_M(z)` for `M ≥ 0`. -/
noncomputable def P (M : ℕ) : Polynomial ℝ := poly (M + 2)

/-- The quasienergies `ε_1 ≤ ε_2 ≤ ⋯`: `ε = 1/z^{1/3}` over the positive roots `z` of `P_M`, counted with multiplicity,
in increasing order (`ε_i` is attached to the `i`-th largest positive root). Unattained indices give `0`. -/
noncomputable def quasienergy (M i : ℕ) : ℝ :=
  let roots := ((P M).roots.filter (fun z => 0 < z)).sort (· ≥ ·)
  (roots.getD (i - 1) 0) ^ (-(1 / 3 : ℝ))

/-- Prediction (4.7), "ε_i = π A^{(N)}/M (x_s^{(N)} + i − 1), for i = 1, 2, …" as the leading behaviour, with the
conjectured exact values `A^{(3)} = 2√3` (4.8) and `x_s^{(3)} = 7/6` for `mod(M, 3) = 0` (4.10): for every fixed `i ≥ 1`,
`M ε_i(M) → π · 2√3 · (7/6 + i − 1)` along `M = 3m`. -/
def claim : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    Tendsto (fun m : ℕ => ((3 * m : ℕ) : ℝ) * quasienergy (3 * m) i) atTop
      (𝓝 (Real.pi * (2 * Real.sqrt 3) * (7 / 6 + (i : ℝ) - 1)))

open Finset Polynomial
open scoped BigOperators

private theorem poly_coeff (n j : ℕ) : (poly n).coeff j = (-1 : ℝ)^j * ((n - 2*j).choose j : ℝ) := by
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · cases j <;> simp [poly, Polynomial.coeff_one]
    · cases j with
      | zero => simp [poly, Polynomial.coeff_one]
      | succ j => simp [poly, Polynomial.coeff_one, Nat.choose_eq_zero_of_lt (show 1 - 2*(j+1) < j+1 by omega)]
    · cases j with
      | zero => simp [poly, Polynomial.coeff_one]
      | succ j => simp [poly, Polynomial.coeff_one, Nat.choose_eq_zero_of_lt (show 2 - 2*(j+1) < j+1 by omega)]
    · cases j with
      | zero => simp [poly, ih (n+2) (by omega) 0, ih n (by omega) 0]
      | succ j =>
        rw [poly, coeff_sub, coeff_X_mul,
          ih (n+2) (by omega) (j+1), ih n (by omega) j]
        by_cases hj : j = 0
        · subst j
          simp only [pow_zero, pow_one, Nat.choose_zero_right, Nat.cast_one, mul_one]
          simp only [show n+2-2*(0+1)=n by omega,
            show n+3-2*(0+1)=n+1 by omega]
          simp
          <;> ring
        · by_cases hn : 2*(j+1) ≤ n+2
          · have hA : n+3-2*(j+1) = (n+2-2*(j+1))+1 := Nat.succ_sub hn
            have hB : n-2*j = n+2-2*(j+1) := by omega
            rw [hA, hB, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
            ring
          · have h0 : n+2-2*(j+1) = 0 := by omega
            have h1 : n-2*j = 0 := by omega
            have hlt : n+3-2*(j+1) < j+1 := by omega
            simp [h0, h1, Nat.choose_eq_zero_of_lt (show 0 < j by omega), hj, Nat.choose_eq_zero_of_lt hlt]

open Polynomial Finset
open scoped BigOperators

private theorem P_closed (m : ℕ) : P (3*m) =
    ∑ j ∈ range (m+1), monomial j ((-1:ℝ)^j * ((3*m+2-2*j).choose j : ℝ)) := by
  ext j
  rw [P, poly_coeff]
  simp only [finsetSum_coeff, coeff_monomial, sum_ite_eq', mem_range]
  split_ifs with hj
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

private theorem P_eval_closed (m : ℕ) (z : ℝ) : (P (3*m)).eval z =
    ∑ j ∈ range (m+1), (-1:ℝ)^j * ((3*m+2-2*j).choose j : ℝ) * z^j := by
  simp [P_closed, eval_finsetSum, eval_monomial]

open Polynomial Finset
open scoped BigOperators
private noncomputable def Q (m : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range (m+1), (-1:ℝ)^k * u^(3*k) * ((m+2+2*k).choose (3*k+2):ℝ) /
    (m:ℝ)^(3*k+2)

private lemma reverse_sign (m k : ℕ) (hk : k ≤ m) :
    (-1:ℝ)^m * (-1:ℝ)^(m-k) = (-1:ℝ)^k := by
  have hm := congrArg (fun t : ℕ => (-1:ℝ)^t) (show m=k+(m-k) by omega)
  rw [pow_add] at hm
  rw [hm, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

private lemma reverse_power (m k : ℕ) (hk : k ≤ m) (e : ℝ) (he : e ≠ 0) :
    e^(3*m) * ((e^3)⁻¹)^(m-k) = e^(3*k) := by
  rw [← inv_pow, ← pow_mul]
  rw [show 3*m = 3*k + 3*(m-k) by omega, pow_add]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ he, one_pow, mul_one]

private lemma reversed_choose (m k : ℕ) (hk : k ≤ m) :
    (3*m+2-2*(m-k)).choose (m-k) = (m+2+2*k).choose (3*k+2) := by
  rw [show 3*m+2-2*(m-k) = m+2+2*k by omega]
  have h := Nat.choose_symm (show m-k ≤ m+2+2*k by omega)
  simpa only [show m+2+2*k-(m-k)=3*k+2 by omega] using h.symm

private theorem scaling_identity (m : ℕ) (hm : 0 < m) (e : ℝ) (he : 0 < e) :
    Q m ((m:ℝ)*e) = (-1:ℝ)^m * e^(3*m) * (P (3*m)).eval ((e^3)⁻¹) / (m:ℝ)^2 := by
  rw [Q, P_eval_closed, mul_sum, sum_div]
  rw [← sum_range_reflect (fun j =>
    (-1:ℝ)^m * e^(3*m) * ((-1:ℝ)^j * ((3*m+2-2*j).choose j:ℝ) * ((e^3)⁻¹)^j) / (m:ℝ)^2) (m+1)]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := mem_range_succ_iff.mp hk
  simp only [Nat.add_sub_cancel, reversed_choose m k hkm]
  have hs := reverse_sign m k hkm
  have hp := reverse_power m k hkm e he.ne'
  have hn : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc
    _ = (-1:ℝ)^k * e^(3*k) * ((m+2+2*k).choose (3*k+2):ℝ) / (m:ℝ)^2 := by
      rw [mul_pow, pow_add]
      field_simp [hn]
    _ = _ := by rw [← hs, ← hp]; ring

open Filter Topology

private theorem shifted_choose_limit (c k : ℕ) :
    Tendsto (fun m : ℕ => ((m+c).choose k : ℝ) / (m:ℝ)^k) atTop (𝓝 (1/(k.factorial:ℝ))) := by
  have hshift : Tendsto (fun m : ℕ => m+c) atTop atTop := tendsto_add_atTop_nat c
  have hbase := (isEquivalent_choose k).comp_tendsto hshift
  have he := hbase.div (Asymptotics.IsEquivalent.refl (u := fun m : ℕ => (m:ℝ)^k))
  apply (Asymptotics.IsEquivalent.tendsto_nhds_iff he).mpr
  have hratio : Tendsto (fun m : ℕ => ((m+c : ℕ):ℝ)/(m:ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, one_mul, zero_add, add_zero, div_one, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c:ℝ) 0 1 (d:=1) (by norm_num : (1:ℝ) ≠ 0))
  have htarget : Tendsto (fun m : ℕ => (((m+c:ℕ):ℝ)/(m:ℝ))^k/(k.factorial:ℝ))
      atTop (𝓝 (1/(k.factorial:ℝ))) := by
    simpa only [one_pow] using (hratio.pow k).div_const (k.factorial:ℝ)
  convert htarget using 1
  funext m
  change (((m+c:ℕ):ℝ)^k/(k.factorial:ℝ))/(m:ℝ)^k = (((m+c:ℕ):ℝ)/(m:ℝ))^k/(k.factorial:ℝ)
  simp only [div_pow]
  ring

open Filter Topology Finset
open scoped BigOperators
private noncomputable def Fseries (u : ℝ) : ℝ := ∑' k : ℕ, (-1:ℝ)^k * u^(3*k) / ((3*k+2).factorial:ℝ)

private lemma factorial_subseries_summable (u : ℝ) (hu : u ≠ 0) :
    Summable (fun k : ℕ => u^(3*k) / ((3*k+2).factorial:ℝ)) := by
  have h := (Real.summable_pow_div_factorial u).comp_injective
    (show Function.Injective (fun k : ℕ => 3*k+2) by intro a b h; dsimp at h; omega)
  convert h.mul_left (u^2)⁻¹ using 1
  ext k
  dsimp only [Function.comp_apply]
  rw [pow_add]
  field_simp [hu]

private lemma alternating_summable (u : ℝ) (hu : u ≠ 0) :
    Summable (fun k : ℕ => (-1:ℝ)^k * u^(3*k) / ((3*k+2).factorial:ℝ)) := by
  simpa only [mul_div_assoc] using (factorial_subseries_summable u hu).alternating

private lemma term_decreases (u : ℝ) (hu : 0 ≤ u) (hu5 : u ≤ 5) (k : ℕ) (hk : 1 ≤ k) :
    u^(3*(k+1)) / ((3*(k+1)+2).factorial:ℝ) ≤
      u^(3*k) / ((3*k+2).factorial:ℝ) := by
  have hfact : (0:ℝ) < ((3*k+2).factorial:ℝ) := by positivity
  have hc : (u^3:ℝ) ≤ 125 := by
    have hh := pow_le_pow_left₀ hu hu5 3
    norm_num at hh
    exact hh
  have hk' : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
  let D : ℝ := (3*k+5:ℝ)*(3*k+4)*(3*k+3)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hp : (125:ℝ) ≤ D := by
    dsimp [D]
    calc
      (125:ℝ) ≤ 8*7*6 := by norm_num
      _ ≤ (3*k+5:ℝ)*(3*k+4)*(3*k+3) := by gcongr <;> linarith
  have hnum : 3*(k+1)+2 = (3*k+2)+1+1+1 := Nat.add_left_inj.mpr rfl
  have hfac : ((3*(k+1)+2).factorial:ℝ) = D*((3*k+2).factorial:ℝ) := by
    rw [hnum, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    dsimp [D]
    ring
  rw [hfac, show 3*(k+1)=3*k+3 by omega, pow_add]
  calc
    _ ≤ (u^(3*k)*D)/(D*((3*k+2).factorial:ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hc.trans hp) (pow_nonneg hu _)) (by positivity)
    _ = _ := by field_simp [hDpos.ne']

private lemma six_terms_lower (u : ℝ) (hu : 0 < u) (hu5 : u ≤ 5) :
    (∑ k ∈ range 6, (-1:ℝ)^k*u^(3*k)/((3*k+2).factorial:ℝ)) ≤ Fseries u := by
  let a : ℕ → ℝ := fun k => u^(3*(k+6))/((3*(k+6)+2).factorial:ℝ)
  have ha : Summable a := by
    exact (summable_nat_add_iff (f := fun k : ℕ => u^(3*k)/((3*k+2).factorial:ℝ)) 6).2
      (factorial_subseries_summable u hu.ne')
  have hmono : Antitone a := antitone_nat_of_succ_le (fun k => by
    change u^(3*(k+1+6))/((3*(k+1+6)+2).factorial:ℝ) ≤
      u^(3*(k+6))/((3*(k+6)+2).factorial:ℝ)
    rw [show k+1+6 = (k+6)+1 by omega]
    exact term_decreases u hu.le hu5 (k+6) (by omega))
  have htail := hmono.alternating_series_le_tendsto ha.tendsto_alternating_series_tsum 0
  have hs := (alternating_summable u hu.ne').sum_add_tsum_nat_add 6
  have hshift : (∑' k : ℕ, (-1:ℝ)^k * a k) =
      ∑' k : ℕ, (-1:ℝ)^(k+6)*u^(3*(k+6))/((3*(k+6)+2).factorial:ℝ) := by
    apply tsum_congr
    intro k
    simp only [a, pow_add, show (-1:ℝ)^6 = 1 by norm_num, mul_one, mul_div_assoc]
  rw [hshift] at htail
  unfold Fseries
  rw [← hs]
  exact le_add_of_nonneg_right (by simpa only [Nat.mul_zero, sum_range_zero] using htail)

private lemma interval_series_positive (u : ℝ) (hl : (42321:ℝ)/10000 ≤ u)
    (hr : u ≤ (42323:ℝ)/10000) : 0 < Fseries u := by
  have hu : 0 < u := by linarith
  have h := six_terms_lower u hu (by linarith)
  have h3 := pow_le_pow_left₀ hu.le hr 3
  have h6 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 42321/10000) hl 6
  have h9 := pow_le_pow_left₀ hu.le hr 9
  have h12 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 42321/10000) hl 12
  have h15 := pow_le_pow_left₀ hu.le hr 15
  norm_num [sum_range_succ, Nat.factorial] at h
  norm_num at h3 h6 h9 h12 h15
  linarith

private noncomputable def predictedU : ℝ := 7*Real.pi/(3*Real.sqrt 3)

private lemma predicted_interval : (42321:ℝ)/10000 ≤ predictedU ∧ predictedU ≤ (42323:ℝ)/10000 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  have hsl : (173205:ℝ)/100000 ≤ Real.sqrt 3 := by nlinarith
  have hsr : Real.sqrt 3 ≤ (173206:ℝ)/100000 := by nlinarith
  have hp : (0:ℝ) < 3*Real.sqrt 3 := by positivity
  unfold predictedU
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [Real.pi_gt_d6]
  · apply (div_le_iff₀ hp).2
    linarith [Real.pi_lt_d6]

private lemma predicted_series_positive : 0 < Fseries predictedU := by
  exact interval_series_positive predictedU predicted_interval.1 predicted_interval.2

open Polynomial

private theorem quasienergy_root (M : ℕ) (h : 0 < quasienergy M 1) :
    ∃ z : ℝ, 0 < z ∧ (P M).eval z = 0 ∧ quasienergy M 1 = z^(-(1/3:ℝ)) := by
  generalize hr : (((P M).roots.filter (fun z => 0 < z)).sort (· ≥ ·)) = l
  cases l with
  | nil =>
    norm_num [quasienergy, hr] at h
  | cons z zs =>
    have hmem : z ∈ (((P M).roots.filter (fun z => 0 < z)).sort (· ≥ ·)) := by
      rw [hr]
      exact List.mem_cons_self
    simp only [Multiset.mem_sort, Multiset.mem_filter] at hmem
    refine ⟨z, hmem.2, isRoot_of_mem_roots hmem.1, ?_⟩
    simp [quasienergy, hr]

private lemma inverse_cube_rpow (z : ℝ) (hz : 0 < z) : (z^(-(1/3:ℝ)))^3 = z⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
  norm_num
  exact Real.rpow_neg_one z

private theorem quasienergy_eval_zero (M : ℕ) (h : 0 < quasienergy M 1) :
    (P M).eval (((quasienergy M 1)^3)⁻¹) = 0 := by
  obtain ⟨z, hz, he, hq⟩ := quasienergy_root M h
  rw [hq, inverse_cube_rpow z hz, inv_inv]
  exact he

open Finset
open scoped BigOperators
private noncomputable def qterm (m : ℕ) (u : ℝ) (k : ℕ) : ℝ :=
  (-1:ℝ)^k * u^(3*k) * (((m+2+2*k).choose (3*k+2):ℝ) / (m:ℝ)^(3*k+2))

private lemma Q_eq_tsum (m : ℕ) (u : ℝ) : Q m u = ∑' k : ℕ, qterm m u k := by
  symm
  rw [tsum_eq_sum (s := range (m+1)) (fun k hk => ?_)]
  · unfold Q
    apply sum_congr rfl
    intro k hk
    simp only [qterm, mul_div_assoc]
  · have hkm : m < k := by simp only [mem_range] at hk; omega
    simp only [qterm, Nat.choose_eq_zero_of_lt (show m+2+2*k < 3*k+2 by omega),
      Nat.cast_zero, zero_div, mul_zero]

private lemma coefficient_bound (m k : ℕ) (hm : 0 < m) :
    ((m+2+2*k).choose (3*k+2):ℝ) / (m:ℝ)^(3*k+2) ≤
      5^(3*k+2) / ((3*k+2).factorial:ℝ) := by
  by_cases hk : k ≤ m
  · have hn : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hnpos : (0:ℝ) < m := Nat.cast_pos'.mpr hm
    have htop : ((m+2+2*k:ℕ):ℝ) ≤ 5*(m:ℝ) := by exact_mod_cast (show m+2+2*k ≤ 5*m by omega)
    calc
      _ ≤ (((m+2+2*k:ℕ):ℝ)^(3*k+2) / ((3*k+2).factorial:ℝ)) / (m:ℝ)^(3*k+2) :=
        div_le_div_of_nonneg_right (Nat.choose_le_pow_div (3*k+2) (m+2+2*k)) (by positivity)
      _ ≤ ((5*(m:ℝ))^(3*k+2) / ((3*k+2).factorial:ℝ)) / (m:ℝ)^(3*k+2) := by gcongr
      _ = _ := by rw [mul_pow]; field_simp [hn]
  · rw [Nat.choose_eq_zero_of_lt (show m+2+2*k < 3*k+2 by omega)]
    simp only [Nat.cast_zero, zero_div]
    positivity

private noncomputable def majorant (k : ℕ) : ℝ :=
  5^(3*k+2)*5^(3*k)/((3*k+2).factorial:ℝ)

private lemma majorant_summable : Summable majorant := by
  have h := factorial_subseries_summable 25 (by norm_num)
  convert h.mul_left 25 using 1
  ext k
  have hp : (25:ℝ)^(3*k) = 5^(3*k)*5^(3*k) := by rw [← mul_pow]; norm_num
  rw [hp]
  simp only [majorant, pow_add]
  norm_num
  ring

private lemma qterm_bound (m k : ℕ) (hm : 0 < m) (u : ℝ) (hu : |u| ≤ 5) :
    ‖qterm m u k‖ ≤ majorant k := by
  have hc : (0:ℝ) ≤ ((m+2+2*k).choose (3*k+2):ℝ)/(m:ℝ)^(3*k+2) := by positivity
  calc
    _ = |u|^(3*k) * (((m+2+2*k).choose (3*k+2):ℝ)/(m:ℝ)^(3*k+2)) := by
      simp only [qterm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ 5^(3*k) * (5^(3*k+2)/((3*k+2).factorial:ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu _) (coefficient_bound m k hm) hc (by positivity)
    _ = _ := by unfold majorant; ring

private theorem Q_moving_limit (v : ℕ → ℝ) (u : ℝ) (hv : Tendsto v atTop (𝓝 u))
    (hbound : ∀ᶠ m in atTop, |v m| ≤ 5) :
    Tendsto (fun m : ℕ => Q m (v m)) atTop (𝓝 (Fseries u)) := by
  have hp (k : ℕ) : Tendsto (fun m => qterm m (v m) k) atTop
      (𝓝 ((-1:ℝ)^k*u^(3*k)/((3*k+2).factorial:ℝ))) := by
    have hc := shifted_choose_limit (2+2*k) (3*k+2)
    have h := ((hv.pow (3*k)).const_mul ((-1:ℝ)^k)).mul hc
    simpa only [qterm, Nat.add_assoc, div_eq_mul_inv, mul_assoc, one_mul] using h
  have hb : ∀ᶠ m in atTop, ∀ k, ‖qterm m (v m) k‖ ≤ majorant k := by
    filter_upwards [hbound, eventually_ge_atTop 1] with m hm hn k
    exact qterm_bound m k (by omega) (v m) hm
  have hh := tendsto_tsum_of_dominated_convergence majorant_summable hp hb
  simpa only [← Q_eq_tsum, Fseries] using hh

open Filter Topology

private lemma predicted_constant_div_three :
    Real.pi*(2*Real.sqrt 3)*(7/6+(1:ℝ)-1)/3 = predictedU := by
  unfold predictedU
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith

theorem result : ¬ claim := by
  intro hc
  let v : ℕ → ℝ := fun m => (m:ℝ)*quasienergy (3*m) 1
  have hv : Tendsto v atTop (𝓝 predictedU) := by
    have h := (hc 1 (by omega)).div_const 3
    simp only [Nat.cast_one] at h
    rw [predicted_constant_div_three] at h
    convert h using 1
    funext m
    simp only [v, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hpos : 0 < predictedU :=
    lt_of_lt_of_le (by norm_num) predicted_interval.1
  have hlt : |predictedU| < 5 := by
    rw [abs_of_pos hpos]
    linarith [predicted_interval.2]
  have hbound : ∀ᶠ m in atTop, |v m| ≤ 5 :=
    (hv.abs.eventually (Iio_mem_nhds hlt)).mono (fun _ h => h.le)
  have hz : ∀ᶠ m in atTop, Q m (v m) = 0 := by
    filter_upwards [hv.eventually (Ioi_mem_nhds hpos), eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := Nat.cast_pos'.mpr hm1
    have he : 0 < quasienergy (3*m) 1 := (mul_pos_iff_of_pos_left hmpos).mp hm
    dsimp [v]
    rw [scaling_identity m (by omega) _ he, quasienergy_eval_zero _ he, mul_zero, zero_div]
  have hzero : Tendsto (fun m => Q m (v m)) atTop (𝓝 (0:ℝ)) :=
    (tendsto_congr' hz).2 tendsto_const_nhds
  have heq := tendsto_nhds_unique (Q_moving_limit v _ hv hbound) hzero
  exact (ne_of_gt predicted_series_positive) heq


end D5.S3.Quantum.SpinChains.AlcarazRamosConformalTowerRefutation
