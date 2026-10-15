/- GID: D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness
   generality: I
   mirror-B: D5/B/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Global cooling strictly beats equal parallel groups except at (6,2). -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Entropy.NamingWindow.SumProductUpdate
import Mathlib.Order.Interval.Set.Monotone

noncomputable section
open Matrix Finset
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
namespace D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness

def tau (P : ℝ) (b : Fin 2) : ℝ := if b = 0 then 1 - P else P
def thermalWeight {N : ℕ} (P : ℝ) (x : Fin N → Fin 2) : ℝ := ∏ j, tau P (x j)
def rho (N : ℕ) (P : ℝ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.diagonal (fun x => (thermalWeight P x : ℂ))
def population {N : ℕ} (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (α : Fin N) : ℂ := ∑ x, if x α = 1 then A x x else 0
def coherence {N : ℕ} (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (α : Fin N) : ℂ := ∑ x, if x α = 0 then A x (Function.update x α 1) else 0
def feasible (N M : ℕ) (P : ℝ) : Set ℝ :=
  {g | ∃ U, U ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ ∧
     ∀ α : Fin N, α.val < M →
       population (U * rho N P * star U) α = (g : ℂ) ∧ coherence (U * rho N P * star U) α = 0}
noncomputable def pGlob (N M : ℕ) (P : ℝ) : ℝ := sInf (feasible N M P)
def claim : Prop := ∀ N M : ℕ, 2 ≤ M → M + 2 ≤ N → (N, M) ≠ (6, 2) →
  ∀ P₁ : ℝ, 0 < P₁ → P₁ < 1 / 2 → pGlob N M P₁ < pGlob (N / M) 1 P₁

private def weight {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  (univ.filter (fun j => x j = 1)).card
private def q (L j : ℕ) (P : ℝ) : ℝ := P ^ j * (1 - P) ^ (L - j)
private def hotSet {n : ℕ} (a : Fin n) : Finset (Fin n → Fin 2) :=
  univ.filter (fun x => n < 2 * weight x ∨ (2 * weight x = n ∧ x a = 1))
private def pHot {n : ℕ} (a : Fin n) (P : ℝ) : ℝ :=
  ∑ x ∈ hotSet a, thermalWeight P x

private theorem weight_le {n : ℕ} (x : Fin n → Fin 2) : weight x ≤ n := by
  rw [weight.eq_1]
  simpa only [Fintype.card_fin, card_univ] using card_filter_le univ (fun j => x j = 1)

private theorem bit_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  exact (Fin.forall_fin_two (p := fun b => b = 0 ∨ b = 1)).mpr ⟨Or.inl rfl, Or.inr rfl⟩ b

private theorem thermalWeight_eq_q {n : ℕ} (P : ℝ) (x : Fin n → Fin 2) :
    thermalWeight P x = q n (weight x) P := by
  change (∏ j, if x j = 0 then 1 - P else P) = P ^ (weight x) * (1 - P) ^ (n - weight x)
  have hb (j : Fin n) : (if x j = 0 then 1 - P else P) =
      (if x j = 1 then P else 1 - P) := by
    rcases bit_cases (x j) with h | h <;> simp only [h] <;> norm_num
  simp_rw [hb]
  rw [prod_ite]
  simp only [prod_const]
  change P ^ (weight x) * (1 - P) ^ ((univ.filter (fun j => ¬ x j = 1)).card) = _
  congr 2
  have h := card_filter_add_card_filter_not (s := univ) (fun j : Fin n => x j = 1)
  rw [card_univ, Fintype.card_fin] at h
  change weight x + _ = n at h
  omega

private theorem tau_sum (P : ℝ) : ∑ b : Fin 2, tau P b = 1 := by
  rw [Fin.sum_univ_two]
  change (if (0 : Fin 2) = 0 then 1 - P else P) +
    (if (1 : Fin 2) = 0 then 1 - P else P) = 1
  norm_num

private theorem thermal_sum (N : ℕ) (P : ℝ) : ∑ x : Fin N → Fin 2, thermalWeight P x = 1 := by
  simp_rw [thermalWeight.eq_1]
  rw [← Fintype.prod_sum]
  simp only [tau_sum, prod_const_one]

private theorem weighted_coordinate_sum {I A : Type*}
    [Fintype I] [DecidableEq I] [Fintype A]
    (w : A → ℝ) (hw : ∑ a, w a = 1) (i : I) (f : A → ℝ) :
    (∑ x : I → A, f (x i) * ∏ j, w (x j)) = ∑ a, f a * w a := by
  classical
  have h := D5.S3.Entropy.NamingWindow.SumProductUpdate.sum_prod_update
    (fun _ a => w a) i (fun a => f a * w a)
  simp only [hw, prod_const_one, one_mul] at h
  convert h using 1
  apply sum_congr rfl
  intro x _
  rw [← mul_prod_erase univ (fun j => w (x j)) (mem_univ i)]
  ring

private theorem q_adjacent (L j : ℕ) (P : ℝ) (hj : j < L)
    (hP0 : 0 < P) (hP1 : P < 1 / 2) : q L (j + 1) P < q L j P := by
  have he : L - j = L - (j + 1) + 1 := by
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left] using
      (Nat.sub_add_sub_cancel (Nat.succ_le_of_lt hj) (Nat.le_succ j)).symm
  change P ^ (j + 1) * (1 - P) ^ (L - (j + 1)) < P ^ j * (1 - P) ^ (L - j)
  rw [he, pow_succ, pow_succ]
  have h1 : 0 < (1 - P) ^ (L - (j + 1)) := pow_pos (by linarith) _
  have h2 := pow_pos hP0 j
  have hp := mul_pos (mul_pos h2 h1) (by linarith : 0 < 1 - 2 * P)
  nlinarith [hp]

private theorem q_lt_q (L i j : ℕ) (P : ℝ) (hij : i < j) (hj : j ≤ L)
    (hP0 : 0 < P) (hP1 : P < 1 / 2) : q L j P < q L i P := by
  have hq : StrictAntiOn (fun j => q L j P) (Set.Iic L) :=
    strictAntiOn_Iic_of_succ_lt (fun j hj => q_adjacent L j P hj hP0 hP1)
  exact hq (hij.le.trans hj) hj hij

private theorem q_antitone (L i j : ℕ) (P : ℝ) (hij : i ≤ j) (hj : j ≤ L)
    (hP0 : 0 < P) (hP1 : P < 1 / 2) : q L j P ≤ q L i P := by
  exact (strictAntiOn_Iic_of_succ_lt (ψ := fun j => q L j P)
    (fun j hj => q_adjacent L j P hj hP0 hP1)).antitoneOn
    (hij.trans hj) hj hij

private theorem shell_gap (N M : ℕ) (hM : 2 ≤ M) (hNM : M + 2 ≤ N)
    (hne : (N, M) ≠ (6, 2)) :
    (N / M + 1) / 2 < M * ((N / M) / 2) + N % M ∧
    M * ((N / M) / 2) + N % M ≤ N := by
  have hdiv := Nat.div_add_mod N M
  have hr := Nat.mod_lt N (by omega : 0 < M)
  have hn : 0 < N / M := (Nat.le_div_iff_mul_le (by omega : 0 < M)).2 (by omega)
  have ht : (N / M) / 2 ≤ N / M := Nat.div_le_self _ _
  have hu := Nat.mul_le_mul_left M ht
  constructor
  · have hm := Nat.mul_le_mul_right ((N / M) / 2) hM
    by_cases h0 : (N / M) / 2 = 0
    · have hn1 : N / M = 1 := by omega
      simp only [hn1, Nat.mul_one] at hdiv
      omega
    · by_cases h1 : (N / M) / 2 = 1
      · have hns : N / M = 2 ∨ N / M = 3 := by omega
        rcases hns with hn2 | hn3
        · omega
        · rw [hn3] at hdiv
          have hbad : ¬ (M = 2 ∧ N % M = 0) := by
            rintro ⟨rfl, hh⟩
            simp only [hh] at hdiv
            exact hne (by congr 1; omega)
          simp only [hn3]
          norm_num only
          omega
      · omega
  · omega

private theorem diagonal_readout {I : Type*} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) (lam : I → ℝ) (i : I) :
    ((V * Matrix.diagonal (fun j => (lam j : ℂ)) * star V) i i).re =
      ∑ j, ‖V i j‖ ^ 2 * lam j := by
  have h := projected_dynamics_is_unistochastic V lam hV
  have hr := congrFun (h.2.2.2 0) i
  simpa only [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedWeights,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedOrbit,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedStep,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectiveReadout,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
    D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,
    Matrix.diagonal_apply_eq, Matrix.diag_apply, Matrix.mulVec, dotProduct,
    Complex.ofReal_re, h.2.1] using hr

private theorem threshold_sum_le {I : Type*} [Fintype I]
    (H : Finset I) (lam a : I → ℝ) (c : ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1)
    (hsum : ∑ j, a j = (H.card : ℝ))
    (hH : ∀ j ∈ H, lam j ≤ c) (hC : ∀ j ∉ H, c ≤ lam j) :
    ∑ j ∈ H, lam j ≤ ∑ j, lam j * a j := by
  classical
  have hp (j : I) : (if j ∈ H then lam j - c else 0) ≤ (lam j - c) * a j := by
    by_cases hj : j ∈ H
    · rw [if_pos hj]
      simpa only [mul_one] using
        mul_le_mul_of_nonpos_left (ha1 j) (sub_nonpos.mpr (hH j hj))
    · rw [if_neg hj]
      exact mul_nonneg (sub_nonneg.mpr (hC j hj)) (ha0 j)
  have hs := sum_le_sum (fun j (_ : j ∈ univ) => hp j)
  simp only [sum_ite_mem, univ_inter, sub_mul, sum_sub_distrib, ← mul_sum, hsum, sum_const,
    nsmul_eq_mul] at hs
  nlinarith

private theorem unitary_cutoff {I : Type*} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (lam : I → ℝ) (H R : Finset I) (c : ℝ) (hcard : H.card = R.card)
    (hH : ∀ j ∈ H, lam j ≤ c) (hC : ∀ j ∉ H, c ≤ lam j) :
    (∑ j ∈ H, lam j) ≤
      (∑ i ∈ R, (V * Matrix.diagonal (fun j => (lam j : ℂ)) * star V) i i).re := by
  have hd := projected_dynamics_is_unistochastic V lam hV
  have hds := mem_doublyStochastic_iff_sum.mp hd.2.2.1
  have hrow (i : I) : ∑ j, ‖V i j‖ ^ 2 = 1 := by
    simpa only [hd.2.1] using hds.2.1 i
  have hcol (j : I) : ∑ i, ‖V i j‖ ^ 2 = 1 := by
    simpa only [hd.2.1] using hds.2.2 j
  have ha0 (j : I) : 0 ≤ ∑ i ∈ R, ‖V i j‖ ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have ha1 (j : I) : (∑ i ∈ R, ‖V i j‖ ^ 2) ≤ 1 := by
    rw [← hcol j]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ R) (fun i _ _ => sq_nonneg _)
  have hs : (∑ j, ∑ i ∈ R, ‖V i j‖ ^ 2) = (H.card : ℝ) := by
    rw [sum_comm]
    simp only [hrow, sum_const, nsmul_eq_mul, mul_one, hcard]
  have ht := threshold_sum_le H lam (fun j => ∑ i ∈ R, ‖V i j‖ ^ 2) c ha0 ha1 hs hH hC
  convert ht using 1
  simp only [Complex.re_sum, diagonal_readout V hV lam, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

private def flip {n : ℕ} (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun j => Equiv.swap (0 : Fin 2) 1 (x j)

private theorem flip_flip {n : ℕ} (x : Fin n → Fin 2) : flip (flip x) = x := by
  funext j
  change Equiv.swap (0 : Fin 2) 1 (Equiv.swap 0 1 (x j)) = x j
  exact Equiv.swap_apply_self _ _ _

private theorem flip_bit {n : ℕ} (x : Fin n → Fin 2) (a : Fin n) :
    flip x a = 1 ↔ x a ≠ 1 := by
  change Equiv.swap (0 : Fin 2) 1 (x a) = 1 ↔ x a ≠ 1
  rcases bit_cases (x a) with h | h <;> simp only [h] <;> norm_num

private theorem flip_weight {n : ℕ} (x : Fin n → Fin 2) :
    weight (flip x) = n - weight x := by
  have he : univ.filter (fun j => flip x j = 1) = univ.filter (fun j => x j ≠ 1) := by
    exact filter_congr (fun j _ => flip_bit x j)
  have h := card_filter_add_card_filter_not (s := univ) (fun j : Fin n => x j = 1)
  rw [card_univ, Fintype.card_fin] at h
  change weight x + _ = n at h
  change (univ.filter (fun j => flip x j = 1)).card = _
  rw [he]
  have hh : weight x + (univ.filter (fun j => x j ≠ 1)).card = n := h
  omega

private theorem flip_hot {n : ℕ} (a : Fin n) (x : Fin n → Fin 2) :
    flip x ∈ hotSet a ↔ x ∉ hotSet a := by
  simp only [hotSet, mem_filter, mem_univ, true_and, flip_weight, flip_bit]
  have hw := weight_le x
  by_cases hb : x a = 1 <;> simp only [hb, and_true, and_false, or_false] <;> omega

private def coolFn {n : ℕ} (a : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  if ((x a = 1) ↔ x ∈ hotSet a) then x else flip x

private theorem coolFn_involutive {n : ℕ} (a : Fin n) :
    Function.Involutive (coolFn a) := by
  intro x
  have he : ((flip x a = 1) ↔ flip x ∈ hotSet a) ↔ ((x a = 1) ↔ x ∈ hotSet a) := by
    simpa only [flip_bit, flip_hot] using
      (not_iff_not (a := x a = 1) (b := x ∈ hotSet a))
  by_cases h : ((x a = 1) ↔ x ∈ hotSet a)
  · have hf : coolFn a x = x := by rw [coolFn, if_pos h]
    rw [hf, hf]
  · have hf : coolFn a x = flip x := by rw [coolFn, if_neg h]
    rw [hf, coolFn, if_neg (fun hh => h (he.mp hh)), flip_flip]

private def coolPerm {n : ℕ} (a : Fin n) : Equiv.Perm (Fin n → Fin 2) :=
  (coolFn_involutive a).toPerm (coolFn a)

private theorem coolPerm_target {n : ℕ} (a : Fin n) (x : Fin n → Fin 2) :
    coolPerm a x a = 1 ↔ x ∈ hotSet a := by
  change coolFn a x a = 1 ↔ _
  rw [coolFn]
  by_cases h : ((x a = 1) ↔ x ∈ hotSet a)
  · rw [if_pos h]; exact h
  · rw [if_neg h, flip_bit]
    tauto

private theorem hot_card {n : ℕ} (a : Fin n) :
    (hotSet a).card = (univ.filter (fun x : Fin n → Fin 2 => x a = 1)).card := by
  apply card_bij (fun x _ => coolPerm a x)
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (coolPerm_target a x).mpr hx⟩
  · intro x hx y hy hxy
    exact (coolPerm a).injective hxy
  · intro y hy
    refine ⟨(coolPerm a).symm y, ?_, (coolPerm a).apply_symm_apply y⟩
    apply (coolPerm_target a _).mp
    rw [(coolPerm a).apply_symm_apply]
    exact (mem_filter.mp hy).2

private theorem hot_threshold {n : ℕ} (a : Fin n) (P : ℝ)
    (hP0 : 0 < P) (hP1 : P < 1 / 2) :
    (∀ x ∈ hotSet a, thermalWeight P x ≤ q n ((n + 1) / 2) P) ∧
    (∀ x ∉ hotSet a, q n ((n + 1) / 2) P ≤ thermalWeight P x) := by
  have hn : 0 < n := Nat.zero_lt_of_lt a.isLt
  constructor
  · intro x hx
    rw [hotSet.eq_1] at hx
    have hh := (mem_filter.mp hx).2
    rw [thermalWeight_eq_q]
    exact q_antitone n _ _ P (by omega) (weight_le x) hP0 hP1
  · intro x hx
    have hh : ¬ (n < 2 * weight x ∨ (2 * weight x = n ∧ x a = 1)) := by
      simpa only [hotSet, mem_filter, mem_univ, true_and] using hx
    rw [thermalWeight_eq_q]
    exact q_antitone n _ _ P (by omega) (by omega) hP0 hP1

private theorem diagonal_coherence {n : ℕ} (d : (Fin n → Fin 2) → ℂ) (a : Fin n) :
    coherence (Matrix.diagonal d) a = 0 := by
  rw [coherence.eq_1]
  apply sum_eq_zero
  intro x hx
  by_cases h : x a = 0
  · rw [if_pos h, Matrix.diagonal_apply_ne _ (Function.ne_update_self_iff.mpr
      (by simpa only [h] using Fin.zero_ne_one))]
  · rw [if_neg h]

private theorem identity_feasible (N M : ℕ) (P : ℝ) : P ∈ feasible N M P := by
  refine ⟨1, by simp, ?_⟩
  intro a ha
  simp only [one_mul, star_one, mul_one]
  constructor
  · rw [population.eq_1]
    simp only [rho, Matrix.diagonal_apply_eq]
    have hs := weighted_coordinate_sum (tau P) (tau_sum P) a
      (fun b => if b = 1 then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul] at hs
    rw [Fin.sum_univ_two] at hs
    simp only [Fin.zero_ne_one, if_false, if_true, zero_add] at hs
    change (∑ x, if x a = 1 then thermalWeight P x else 0) =
      (if (1 : Fin 2) = 0 then 1 - P else P) at hs
    norm_num at hs
    have hp := congrArg (fun t : ℝ => (t : ℂ)) hs
    simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hp
  · exact diagonal_coherence _ a

private theorem feasible_bddBelow (N M : ℕ) (P : ℝ) (hM : 0 < M) (hMN : M ≤ N)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) : BddBelow (feasible N M P) := by
  refine ⟨0, ?_⟩
  intro g hg
  obtain ⟨U, hU, hm⟩ := hg
  let a : Fin N := ⟨0, by omega⟩
  have hp := congrArg Complex.re (hm a (by omega)).1
  change (∑ x, if x a = 1 then (U * rho N P * star U) x x else 0).re = g at hp
  rw [← hp, Complex.re_sum]
  apply sum_nonneg
  intro x hx
  simp only [apply_ite, Complex.zero_re]
  by_cases h : x a = 1
  · rw [if_pos h, rho, diagonal_readout U hU]
    apply sum_nonneg
    intro y hy
    apply mul_nonneg (sq_nonneg _)
    change 0 ≤ ∏ j, tau P (y j)
    apply prod_nonneg
    intro j hj
    change 0 ≤ if y j = 0 then 1 - P else P
    split_ifs <;> linarith
  · rw [if_neg h]

private theorem single_lower (n : ℕ) (hn : 0 < n) (P : ℝ)
    (hP0 : 0 < P) (hP1 : P < 1 / 2) :
    pHot (⟨0, hn⟩ : Fin n) P ≤ pGlob n 1 P := by
  change _ ≤ sInf (feasible n 1 P)
  apply le_csInf ⟨P, identity_feasible n 1 P⟩
  intro g hg
  obtain ⟨U, hU, hm⟩ := hg
  let a : Fin n := ⟨0, hn⟩
  have ht := hot_threshold a P hP0 hP1
  have hc := unitary_cutoff U hU (thermalWeight P) (hotSet a)
    (univ.filter (fun x => x a = 1)) (q n ((n + 1) / 2) P) (hot_card a) ht.1 ht.2
  have hp := congrArg Complex.re (hm a (by simp only [a, Nat.lt_one_iff])).1
  change (∑ x, if x a = 1 then (U * rho n P * star U) x x else 0).re = g at hp
  rw [← sum_filter] at hp
  exact hc.trans_eq hp

private def swapReflection {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → ℝ) : Matrix I I ℝ := 1 - Matrix.vecMulVec (u - v) (u - v)

private theorem reflection_diagonal_update {I : Type*} [Fintype I] [DecidableEq I]
    (d u v : I → ℝ) (a b : ℝ) (hu : dotProduct u u = 1) (hv : dotProduct v v = 1)
    (huv : dotProduct u v = 0) (hdu : ∀ x, d x * u x = a * u x)
    (hdv : ∀ x, d x * v x = b * v x) :
    swapReflection u v * (swapReflection u v).transpose = 1 ∧
    swapReflection u v * Matrix.diagonal d * (swapReflection u v).transpose =
      Matrix.diagonal d + (a - b) • (Matrix.vecMulVec v v - Matrix.vecMulVec u u) := by
  let w := u - v
  let R := Matrix.vecMulVec w w
  have hvu : dotProduct v u = 0 := by rw [dotProduct_comm, huv]
  have hw : dotProduct w w = 2 := by
    change dotProduct (u - v) (u - v) = 2
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hu, hv, huv, hvu]
    norm_num
  have hR : R.transpose = R := by
    exact Matrix.transpose_vecMulVec w w
  have hdw : Matrix.diagonal d *ᵥ w = a • u - b • v := by
    ext x
    simp only [Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    change d x * (u x - v x) = a * u x - b * v x
    rw [mul_sub, hdu, hdv]
  have hwd : w ᵥ* Matrix.diagonal d = a • u - b • v := by
    ext x
    simp only [Matrix.vecMul_diagonal, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    change (u x - v x) * d x = a * u x - b * v x
    rw [mul_comm, mul_sub, hdu, hdv]
  have hdot : dotProduct (a • u - b • v) w = a + b := by
    change dotProduct (a • u - b • v) (u - v) = _
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_dotProduct, hu, hv, huv, hvu]
    simp only [smul_eq_mul]
    ring
  have hrr : R * R = Matrix.vecMulVec w ((2 : ℝ) • w) := by
    simpa only [hw] using Matrix.vecMulVec_mul_vecMulVec w w w w
  have hrd : R * Matrix.diagonal d = Matrix.vecMulVec w (a • u - b • v) := by
    rw [Matrix.vecMulVec_mul, hwd]
  have hdr : Matrix.diagonal d * R = Matrix.vecMulVec (a • u - b • v) w := by
    rw [Matrix.mul_vecMulVec, hdw]
  have hrdr : R * Matrix.diagonal d * R = Matrix.vecMulVec w ((a + b) • w) := by
    rw [hrd, Matrix.vecMulVec_mul_vecMulVec, hdot]
  have ht : (swapReflection u v).transpose = 1 - R := by
    change (1 - R).transpose = _
    rw [Matrix.transpose_sub, Matrix.transpose_one, hR]
  constructor
  · change (1 - R) * (swapReflection u v).transpose = 1
    rw [ht]
    have he : (1 - R) * (1 - R) = 1 - R - R + R * R := by noncomm_ring
    rw [he, hrr]
    ext i j
    dsimp only [R]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · change (1 - R) * Matrix.diagonal d * (swapReflection u v).transpose = _
    rw [ht]
    have he : (1 - R) * Matrix.diagonal d * (1 - R) =
        Matrix.diagonal d - R * Matrix.diagonal d - Matrix.diagonal d * R +
          R * Matrix.diagonal d * R := by noncomm_ring
    rw [he, hrdr, hrd, hdr]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [w]
    simp only [Pi.sub_apply]
    ring

private def coordEquiv (n M r : ℕ) : Fin (n * M + r) ≃ (Fin n × Fin M) ⊕ Fin r :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _))

private def splitBasis (n M r : ℕ) :
    (Fin (n * M + r) → Fin 2) ≃ (Fin M → Fin n → Fin 2) × (Fin r → Fin 2) :=
  ((Equiv.arrowCongr (coordEquiv n M r) (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans
      (Equiv.prodCongr
        ((Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.curry _ _ _))
        (Equiv.refl _))

private theorem splitBasis_block (n M r : ℕ) (x : Fin (n * M + r) → Fin 2)
    (a : Fin M) (b : Fin n) :
    (splitBasis n M r x).1 a b = x ((coordEquiv n M r).symm (Sum.inl (b, a))) := rfl

private theorem thermal_split (n M r : ℕ) (P : ℝ) (x : Fin (n * M + r) → Fin 2) :
    thermalWeight P x = (∏ a, thermalWeight P ((splitBasis n M r x).1 a)) *
      thermalWeight P ((splitBasis n M r x).2) := by
  change (∏ j, tau P (x j)) = _
  rw [← (coordEquiv n M r).symm.prod_comp]
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  rw [prod_comm]
  rfl

private def blockPerm (M n r : ℕ) (a0 : Fin n) : Equiv.Perm (Fin (n * M + r) → Fin 2) :=
  (splitBasis n M r).trans
    ((Equiv.prodCongr (Equiv.piCongrRight (fun _ : Fin M => coolPerm a0))
      (Equiv.refl _)).trans (splitBasis n M r).symm)

private theorem blockPerm_block (M n r : ℕ) (hn : 0 < n)
    (x : Fin (n * M + r) → Fin 2) (a : Fin M) :
    (splitBasis n M r (blockPerm M n r (⟨0, hn⟩ : Fin n) x)).1 a =
      coolPerm (⟨0, hn⟩ : Fin n) ((splitBasis n M r x).1 a) := by
  change ((splitBasis n M r) ((splitBasis n M r).symm _)).1 a = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem coord_target (M n r : ℕ) (hn : 0 < n) (a : Fin M) :
    (coordEquiv n M r).symm (Sum.inl ((⟨0, hn⟩ : Fin n), a)) =
      (⟨a.val, by have := a.isLt; nlinarith⟩ : Fin (n * M + r)) := by
  apply Fin.ext
  change a.val + M * 0 = a.val
  omega

private def target (M n r : ℕ) (a0 : Fin n) (a : Fin M) : Fin (n * M + r) :=
  (coordEquiv n M r).symm (Sum.inl (a0, a))
private def rPop {N : ℕ} (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℝ)
    (α : Fin N) : ℝ := ∑ x, if x α = 1 then A x x else 0
private def rCoh {N : ℕ} (A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℝ)
    (α : Fin N) : ℝ := ∑ x, if x α = 0 then A x (Function.update x α 1) else 0

private theorem perm_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (B : Equiv.Perm I) (d : I → ℝ) :
    Equiv.Perm.permMatrix ℝ B.symm * Matrix.diagonal d *
      (Equiv.Perm.permMatrix ℝ B.symm).transpose =
      Matrix.diagonal (fun x => d (B.symm x)) := by
  rw [Matrix.transpose_permMatrix]
  change B.symm.toPEquiv.toMatrix * Matrix.diagonal d * B.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  exact Matrix.submatrix_diagonal_equiv d B.symm

private theorem baseline_population (M n r : ℕ) (hn : 0 < n) (P : ℝ) (a : Fin M) :
    rPop (Matrix.diagonal (fun x => thermalWeight P ((blockPerm M n r (⟨0, hn⟩ : Fin n)).symm x)))
      (target M n r (⟨0, hn⟩ : Fin n) a) = pHot (⟨0, hn⟩ : Fin n) P := by
  let B := blockPerm M n r (⟨0, hn⟩ : Fin n)
  let e := splitBasis n M r
  have ht (x : Fin (n * M + r) → Fin 2) :
      B x (target M n r (⟨0, hn⟩ : Fin n) a) = 1 ↔ (e x).1 a ∈ hotSet (⟨0, hn⟩ : Fin n) := by
    change B x ((coordEquiv n M r).symm (Sum.inl ((⟨0, hn⟩ : Fin n), a))) = 1 ↔ _
    rw [← splitBasis_block n M r (B x) a ⟨0, hn⟩, blockPerm_block, coolPerm_target]
  rw [rPop.eq_1]
  simp only [Matrix.diagonal_apply_eq]
  change (∑ x, if x (target M n r (⟨0, hn⟩ : Fin n) a) = 1 then
    thermalWeight P (B.symm x) else 0) = _
  rw [← Equiv.sum_comp B]
  simp only [Equiv.symm_apply_apply, ht]
  rw [← e.symm.sum_comp]
  have hfac (y : (Fin M → Fin n → Fin 2) × (Fin r → Fin 2)) :
      thermalWeight P (e.symm y) = (∏ j, thermalWeight P (y.1 j)) * thermalWeight P y.2 := by
    rw [thermal_split n M r]
    change (∏ j, thermalWeight P ((e (e.symm y)).1 j)) * thermalWeight P ((e (e.symm y)).2) = _
    rw [e.apply_symm_apply]
  simp only [hfac, Equiv.apply_symm_apply, Fintype.sum_prod_type]
  have hp (y : Fin M → Fin n → Fin 2) :
      (∑ z : Fin r → Fin 2, if y a ∈ hotSet (⟨0, hn⟩ : Fin n) then
        (∏ j, thermalWeight P (y j)) * thermalWeight P z else 0) =
      (if y a ∈ hotSet (⟨0, hn⟩ : Fin n) then 1 else 0) * ∏ j, thermalWeight P (y j) := by
    simp only [sum_ite_irrel, ← mul_sum, thermal_sum, sum_const_zero, mul_one,
      ite_mul, one_mul, zero_mul]
  change (∑ y : Fin M → Fin n → Fin 2, ∑ z : Fin r → Fin 2,
    if y a ∈ hotSet (⟨0, hn⟩ : Fin n) then
      (∏ j, thermalWeight P (y j)) * thermalWeight P z else 0) = _
  simp_rw [hp]
  rw [weighted_coordinate_sum (thermalWeight P) (thermal_sum n P) a
    (fun z => if z ∈ hotSet (⟨0, hn⟩ : Fin n) then 1 else 0)]
  change _ = ∑ x ∈ hotSet (⟨0, hn⟩ : Fin n), thermalWeight P x
  simp only [ite_mul, one_mul, zero_mul, ← sum_filter, filter_mem_eq_inter, univ_inter]

private theorem weight_sum {n : ℕ} (x : Fin n → Fin 2) :
    weight x = ∑ j, if x j = 1 then 1 else 0 := by
  change (univ.filter _).card = _
  rw [card_eq_sum_ones, sum_filter]

private theorem weight_split (n M r : ℕ) (x : Fin (n * M + r) → Fin 2) :
    weight x = (∑ a, weight ((splitBasis n M r x).1 a)) +
      weight ((splitBasis n M r x).2) := by
  simp only [weight_sum]
  rw [← (coordEquiv n M r).symm.sum_comp, Fintype.sum_sum_type,
    Fintype.sum_prod_type, sum_comm]
  rfl

private def hotString (n k : ℕ) : Fin n → Fin 2 := fun j => if j.val < k then 1 else 0
private theorem hotString_weight (n k : ℕ) (hk : k ≤ n) : weight (hotString n k) = k := by
  have he : univ.filter (fun j : Fin n => hotString n k j = 1) =
      univ.filter (fun j : Fin n => j.val < k) := by
    exact filter_congr (fun j _ => by
      simp only [hotString.eq_1, ite_eq_iff, Fin.zero_ne_one,
        and_true, and_false, or_false])
  change (univ.filter _).card = k
  rw [he]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hk]

private def donor (M n r : ℕ) (i : Fin M) : Fin (n * M + r) → Fin 2 :=
  (splitBasis n M r).symm
    (fun a => if a = i then hotString n ((n + 1) / 2) else fun _ => 0, fun _ => 0)
private def receiver (M n r : ℕ) : Fin (n * M + r) → Fin 2 :=
  (splitBasis n M r).symm (fun _ => flip (hotString n ((n + 1) / 2)), fun _ => 1)

private theorem distinguished (M n r : ℕ) (hn : 0 < n) :
    (∀ i a : Fin M, donor M n r i (target M n r (⟨0, hn⟩ : Fin n) a) = if a = i then 1 else 0) ∧
    (∀ a : Fin M, receiver M n r (target M n r (⟨0, hn⟩ : Fin n) a) = 0) ∧
    (∀ i : Fin M, weight (donor M n r i) = (n + 1) / 2) ∧
    weight (receiver M n r) = M * (n / 2) + r ∧
    (∀ i : Fin M, blockPerm M n r (⟨0, hn⟩ : Fin n) (donor M n r i) = donor M n r i) ∧
    blockPerm M n r (⟨0, hn⟩ : Fin n) (receiver M n r) = receiver M n r := by
  let a0 : Fin n := ⟨0, hn⟩
  let h := hotString n ((n + 1) / 2)
  have hw : weight h = (n + 1) / 2 := hotString_weight n _ (by omega)
  have hb : h a0 = 1 := by change (if 0 < (n + 1) / 2 then 1 else 0) = 1; rw [if_pos (by omega)]
  have hc : flip h a0 = 0 := by
    change Equiv.swap (0 : Fin 2) 1 (h a0) = 0
    rw [hb]
    exact Equiv.swap_apply_right _ _
  have hz : weight (fun _ : Fin n => (0 : Fin 2)) = 0 := by
    simp only [weight, Fin.zero_ne_one, filter_false, card_empty]
  have hh : h ∈ hotSet a0 := by
    simp only [hotSet, mem_filter, mem_univ, true_and]
    change n < 2 * weight h ∨ (2 * weight h = n ∧ h a0 = 1)
    rw [hw, hb]
    omega
  have hfix (x : Fin n → Fin 2) (hx : (x a0 = 1 ↔ x ∈ hotSet a0)) : coolPerm a0 x = x := by
    change coolFn a0 x = x
    rw [coolFn, if_pos hx]
  have hf := hfix h (by simp only [hb, hh])
  have cf := hfix (flip h) (by rw [flip_bit, flip_hot]; simp only [hb, hh]; simp)
  have zf := hfix (fun _ => 0) (by
    simp only [hotSet, mem_filter, mem_univ, true_and]
    change ((0 : Fin 2) = 1) ↔
      n < 2 * weight (fun _ : Fin n => (0 : Fin 2)) ∨
        (2 * weight (fun _ : Fin n => (0 : Fin 2)) = n ∧ (0 : Fin 2) = 1)
    rw [hz]
    norm_num)
  have dp (i : Fin M) : splitBasis n M r (donor M n r i) =
      (fun a => if a = i then h else fun _ => 0, fun _ => 0) := Equiv.apply_symm_apply _ _
  have vp : splitBasis n M r (receiver M n r) =
      (fun _ : Fin M => flip h, fun _ => 1) := Equiv.apply_symm_apply _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i a
    change donor M n r i ((coordEquiv n M r).symm (Sum.inl (a0, a))) = _
    rw [← splitBasis_block n M r (donor M n r i) a a0, dp]
    change (if a = i then h else fun _ => 0) a0 = _
    by_cases ha : a = i <;> simp only [ha, if_true, if_false, hb]
  · intro a
    change receiver M n r ((coordEquiv n M r).symm (Sum.inl (a0, a))) = 0
    rw [← splitBasis_block n M r (receiver M n r) a a0, vp]
    exact hc
  · intro i
    rw [weight_split, dp]
    have hzr : weight (fun _ : Fin r => (0 : Fin 2)) = 0 := by
      simp only [weight, Fin.zero_ne_one, filter_false, card_empty]
    simp only [apply_ite, hw, hz, sum_ite_eq', mem_univ, if_true, hzr, add_zero]
  · rw [weight_split, vp]
    have ho : weight (fun _ : Fin r => (1 : Fin 2)) = r := by
      simp only [weight, filter_true, card_univ, Fintype.card_fin]
    simp only [flip_weight, hw, sum_const, nsmul_eq_mul, ho, card_univ,
      Fintype.card_fin, Nat.cast_id]
    rw [show n - (n + 1) / 2 = n / 2 by omega]
  · intro i
    apply (splitBasis n M r).injective
    apply Prod.ext
    · funext a
      rw [blockPerm_block, dp]
      change coolPerm a0 (if a = i then h else fun _ => 0) =
        (if a = i then h else fun _ => 0)
      by_cases ha : a = i
      · rw [if_pos ha]; exact hf
      · rw [if_neg ha]; exact zf
    · change ((splitBasis n M r) ((splitBasis n M r).symm _)).2 = _
      rw [Equiv.apply_symm_apply, dp]
      rfl
  · apply (splitBasis n M r).injective
    apply Prod.ext
    · funext a; rw [blockPerm_block, vp]; exact cf
    · change ((splitBasis n M r) ((splitBasis n M r).symm _)).2 = _
      rw [Equiv.apply_symm_apply, vp]
      rfl

private theorem support_data (N M : ℕ) (hM : 0 < M)
    (e : Fin M → Fin N → Fin 2) (v0 : Fin N → Fin 2) (t : Fin M → Fin N)
    (he : ∀ i a, e i (t a) = if a = i then 1 else 0) (hv0 : ∀ a, v0 (t a) = 0) :
    let E := univ.image e
    let s := (Real.sqrt (M : ℝ))⁻¹
    let u := fun x => if x ∈ E then s else 0
    let v := fun x => if x = v0 then (1 : ℝ) else 0
    dotProduct u u = 1 ∧ dotProduct v v = 1 ∧ dotProduct u v = 0 ∧
      (∀ a, rPop (Matrix.vecMulVec u u) (t a) = 1 / (M : ℝ)) ∧
      (∀ a, rPop (Matrix.vecMulVec v v) (t a) = 0) ∧
      (∀ a, rCoh (Matrix.vecMulVec u u) (t a) = 0) ∧
      (∀ a, rCoh (Matrix.vecMulVec v v) (t a) = 0) := by
  classical
  dsimp only
  let E := univ.image e
  let s := (Real.sqrt (M : ℝ))⁻¹
  let u := fun x => if x ∈ E then s else 0
  let v := fun x => if x = v0 then (1 : ℝ) else 0
  have hi : Function.Injective e := by
    intro i j hij
    have hh := congrFun hij (t i)
    rw [he, he] at hh
    by_contra hn
    simp only [if_neg hn] at hh
    norm_num at hh
  have hcard : E.card = M := by
    rw [card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  have hvE : v0 ∉ E := by
    rintro hh
    obtain ⟨i, _, h⟩ := mem_image.mp hh
    have hb := congrFun h (t i)
    rw [he, hv0, if_pos rfl] at hb
    norm_num at hb
  have hei (i : Fin M) : e i ∈ E := mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hs : s * s = 1 / (M : ℝ) := by
    change (Real.sqrt (M : ℝ))⁻¹ * (Real.sqrt (M : ℝ))⁻¹ = _
    rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (by positivity), one_div]
  have hup (x) : u x * u x = if x ∈ E then s * s else 0 := by
    simpa only [u, mul_zero] using apply_ite₂ (fun a b : ℝ => a * b) (x ∈ E) s 0 s 0
  have hupdate (a : Fin M) (x : Fin N → Fin 2) (hx : x ∈ E) (ha : x (t a) = 0) :
      Function.update x (t a) 1 ∉ E := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    have hai : a ≠ i := (Ne.ite_eq_right_iff (Ne.symm Fin.zero_ne_one)).mp
      (by simpa only [he] using ha)
    have hti : t i ≠ t a := by
      apply ne_of_apply_ne (e i)
      rw [he, he, if_pos rfl, if_neg hai]
      exact Ne.symm Fin.zero_ne_one
    rintro hh
    obtain ⟨j, _, hj⟩ := mem_image.mp hh
    have hp := congrFun hj (t a)
    rw [Function.update_self, he] at hp
    have hja : a = j := (Ne.ite_eq_left_iff (Ne.symm Fin.zero_ne_one)).mp hp
    subst j
    have hp := congrFun hj (t i)
    rw [Function.update_of_ne hti, he, he, if_pos rfl, if_neg (Ne.symm hai)] at hp
    norm_num at hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∑ x, u x * u x) = 1
    simp_rw [hup]
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, hcard, hs]
    field_simp
  · change (∑ x, v x * v x) = 1
    simp only [v, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
      sum_ite_eq', mem_univ, if_true]
  · change (∑ x, u x * v x) = 0
    simp only [v, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
    exact if_neg hvE
  · intro a
    change (∑ x, if x (t a) = 1 then u x * u x else 0) = _
    rw [sum_eq_single (e a)]
    · simp only [he, u, hei, if_true, hs]
    · intro x hx hxa
      by_cases hxE : x ∈ E
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hxE
        have hia : a ≠ i := Ne.symm (ne_of_apply_ne e hxa)
        simp only [he, if_neg hia, Fin.zero_ne_one, if_false]
      · simp only [u, if_neg hxE, zero_mul, ite_self]
    · simp only [mem_univ, not_true_eq_false, false_implies]
  · intro a
    change (∑ x, if x (t a) = 1 then v x * v x else 0) = 0
    apply sum_eq_zero
    intro x hx
    by_cases hh : x = v0
    · subst x; simp only [hv0, Fin.zero_ne_one, if_false]
    · simp only [v, if_neg hh, zero_mul, ite_self]
  · intro a
    rw [rCoh.eq_1]
    change (∑ x, if x (t a) = 0 then u x * u (Function.update x (t a) 1) else 0) = 0
    apply sum_eq_zero
    intro x hx
    by_cases ha : x (t a) = 0
    · rw [if_pos ha]
      by_cases hxE : x ∈ E
      · simp only [u, if_neg (hupdate a x hxE ha), mul_zero]
      · simp only [u, if_neg hxE, zero_mul]
    · rw [if_neg ha]
  · intro a
    change (∑ x, if x (t a) = 0 then v x * v (Function.update x (t a) 1) else 0) = 0
    apply sum_eq_zero
    intro x hx
    by_cases hh : x = v0
    · subst x
      have hn : Function.update v0 (t a) 1 ≠ v0 := by
        exact Function.update_ne_self_iff.mpr (by rw [hv0]; exact Ne.symm Fin.zero_ne_one)
      simp only [v, if_neg hn, mul_zero, ite_self]
    · simp only [v, if_neg hh, zero_mul, ite_self]

private theorem real_feasible (N M : ℕ) (P g : ℝ)
    (O A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℝ) (hO : O * O.transpose = 1)
    (hA : O * Matrix.diagonal (thermalWeight P) * O.transpose = A)
    (hm : ∀ α : Fin N, α.val < M → rPop A α = g ∧ rCoh A α = 0) :
    g ∈ feasible N M P := by
  let U := O.map Complex.ofRealHom
  have hs : star U = O.transpose.map Complex.ofRealHom := by
    simpa only [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.conjTranspose_map (A := O) Complex.ofRealHom (by
        intro x
        simp only [star_trivial, Complex.ofRealHom_eq_coe, Complex.star_def,
          Complex.conj_ofReal])).symm
  have hr : rho N P = (Matrix.diagonal (thermalWeight P)).map Complex.ofRealHom := by
    simpa only [rho, Complex.ofRealHom_eq_coe] using
      (Matrix.diagonal_map (d := thermalWeight P) (map_zero Complex.ofRealHom)).symm
  refine ⟨U, Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [hs, ← Matrix.map_mul, hO]
    exact Matrix.map_one _ rfl rfl
  · have hc : U * rho N P * star U = A.map Complex.ofRealHom := by
      rw [hs, hr, ← Matrix.map_mul, ← Matrix.map_mul, hA]
    intro α hα
    obtain ⟨hp, hh⟩ := hm α hα
    rw [hc]
    constructor
    · have h := congrArg (fun t : ℝ => (t : ℂ)) hp
      simpa only [population, rPop, Matrix.map_apply, Complex.ofRealHom_eq_coe,
        Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using h
    · have h := congrArg (fun t : ℝ => (t : ℂ)) hh
      simpa only [coherence, rCoh, Matrix.map_apply, Complex.ofRealHom_eq_coe,
        Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using h

private theorem grouped_witness (M n r : ℕ) (hM : 0 < M) (hn : 0 < n) (P : ℝ) :
    pHot (⟨0, hn⟩ : Fin n) P -
      (q (n * M + r) ((n + 1) / 2) P - q (n * M + r) (M * (n / 2) + r) P) /
        (M : ℝ) ∈ feasible (n * M + r) M P := by
  let B := blockPerm M n r (⟨0, hn⟩ : Fin n)
  let Pmat := Equiv.Perm.permMatrix ℝ B.symm
  let d := fun x => thermalWeight P (B.symm x)
  let e := donor M n r
  let v0 := receiver M n r
  let t := target M n r (⟨0, hn⟩ : Fin n)
  let E := univ.image e
  let s := (Real.sqrt (M : ℝ))⁻¹
  let u := fun x => if x ∈ E then s else 0
  let v := fun x => if x = v0 then (1 : ℝ) else 0
  let a := q (n * M + r) ((n + 1) / 2) P
  let b := q (n * M + r) (M * (n / 2) + r) P
  obtain ⟨het, hvt, hew, hvw, hef, hvf⟩ := distinguished M n r hn
  obtain ⟨hu, hv, huv, hpu, hpv, hcu, hcv⟩ := support_data (n * M + r) M hM e v0 t het hvt
  have heig (i : Fin M) : d (e i) = a := by
    have hh : B.symm (e i) = e i := B.symm_apply_eq.mpr (hef i).symm
    change thermalWeight P (B.symm (e i)) = a
    rw [hh, thermalWeight_eq_q, hew]
  have hveig : d v0 = b := by
    have hh : B.symm v0 = v0 := B.symm_apply_eq.mpr hvf.symm
    change thermalWeight P (B.symm v0) = b
    rw [hh, thermalWeight_eq_q, hvw]
  have hdu (x) : d x * u x = a * u x := by
    by_cases hx : x ∈ E
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      rw [heig]
    · change d x * (if x ∈ E then s else 0) = a * (if x ∈ E then s else 0)
      rw [if_neg hx, mul_zero, mul_zero]
  have hdv (x) : d x * v x = b * v x := by
    by_cases hx : x = v0
    · subst x; rw [hveig]
    · change d x * (if x = v0 then 1 else 0) = b * (if x = v0 then 1 else 0)
      rw [if_neg hx, mul_zero, mul_zero]
  let S := swapReflection u v
  let A := Matrix.diagonal d + (a - b) • (Matrix.vecMulVec v v - Matrix.vecMulVec u u)
  have hS := reflection_diagonal_update d u v a b hu hv huv hdu hdv
  have hP : Pmat * Pmat.transpose = 1 := by
    change Equiv.Perm.permMatrix ℝ B.symm * (Equiv.Perm.permMatrix ℝ B.symm).transpose = 1
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp only [inv_mul_cancel, Matrix.permMatrix_one]
  have hO : (S * Pmat) * (S * Pmat).transpose = 1 := by
    rw [Matrix.transpose_mul]
    calc S * Pmat * (Pmat.transpose * S.transpose) =
        S * (Pmat * Pmat.transpose) * S.transpose := by simp only [mul_assoc]
      _ = 1 := by rw [hP, mul_one]; exact hS.1
  have hA : (S * Pmat) * Matrix.diagonal (thermalWeight P) * (S * Pmat).transpose = A := by
    rw [Matrix.transpose_mul]
    calc S * Pmat * Matrix.diagonal (thermalWeight P) * (Pmat.transpose * S.transpose) =
        S * (Pmat * Matrix.diagonal (thermalWeight P) * Pmat.transpose) * S.transpose := by
          simp only [mul_assoc]
      _ = A := by rw [perm_diagonal]; exact hS.2
  apply real_feasible (n * M + r) M P _ (S * Pmat) A hO hA
  intro α hα
  let j : Fin M := ⟨α.val, hα⟩
  have ht : t j = α := by
    change target M n r (⟨0, hn⟩ : Fin n) j = α
    rw [target, coord_target]
  rw [← ht]
  have hp : rPop A (t j) = rPop (Matrix.diagonal d) (t j) +
      (a - b) * (rPop (Matrix.vecMulVec v v) (t j) - rPop (Matrix.vecMulVec u u) (t j)) := by
    simp only [rPop, A, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul]
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    split_ifs <;> ring
  have hc : rCoh A (t j) = rCoh (Matrix.diagonal d) (t j) +
      (a - b) * (rCoh (Matrix.vecMulVec v v) (t j) - rCoh (Matrix.vecMulVec u u) (t j)) := by
    simp only [rCoh, A, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul]
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    split_ifs <;> ring
  constructor
  · rw [hp, baseline_population, hpv, hpu]
    ring
  · rw [hc, hcv, hcu]
    simp only [sub_self, mul_zero, add_zero]
    change (∑ x, if x (t j) = 0 then Matrix.diagonal d x (Function.update x (t j) 1) else 0) = 0
    apply sum_eq_zero
    intro x hx
    by_cases hh : x (t j) = 0
    · rw [if_pos hh, Matrix.diagonal_apply_ne _ (Function.ne_update_self_iff.mpr
        (by simpa only [hh] using Fin.zero_ne_one))]
    · rw [if_neg hh]

theorem result : claim := by
  intro N M hM hNM hne P hP0 hP1
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hM
  have hn : 0 < N / M := (Nat.le_div_iff_mul_le hMp).2 (by omega)
  have hNM' : M ≤ N := (Nat.le_add_right M 2).trans hNM
  have hL : N / M * M + N % M = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N M
  have hw := grouped_witness M (N / M) (N % M) hMp hn P
  rw [hL] at hw
  have hg := shell_gap N M hM hNM hne
  have hq := q_lt_q N _ _ P hg.1 hg.2 hP0 hP1
  have hδ : 0 < (q N ((N / M + 1) / 2) P -
      q N (M * ((N / M) / 2) + N % M) P) / (M : ℝ) :=
    div_pos (sub_pos.mpr hq) (by exact_mod_cast hMp)
  calc
    pGlob N M P ≤ pHot (⟨0, hn⟩ : Fin (N / M)) P -
        (q N ((N / M + 1) / 2) P - q N (M * ((N / M) / 2) + N % M) P) / (M : ℝ) :=
      csInf_le (feasible_bddBelow N M P hMp hNM' hP0.le (by linarith)) hw
    _ < pHot (⟨0, hn⟩ : Fin (N / M)) P := sub_lt_self _ hδ
    _ ≤ pGlob (N / M) 1 P := single_lower (N / M) hn P hP0 hP1

end D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
