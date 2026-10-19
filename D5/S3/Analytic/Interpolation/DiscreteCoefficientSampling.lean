/- GID: D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/DiscreteCoefficientSampling
   mirror-E: none(waiver:analytic-sampling-bound-without-executable-mirror)
   anchors: []
   utility: none
   digest: Uniform discrete samples on the scaled integer interval control all complex polynomial coefficients below a fixed degree. -/

import D5.S3.Analytic.Interpolation.UniformCoefficientBudget
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
The native build and scoped report provide the elaboration and axiom evidence.
This module states only the finite polynomial sampling estimate below.

This is the classical finite Lagrange interpolation argument with explicit
node separation, not a new interpolation theory. Mathlib's exact interpolation
is imported directly. The existing real coeffL1 algebra is imported directly
from UniformCoefficientBudget; its Causalean attribution and license notices
remain in that owner. No licensed implementation is copied here.

The new content is the uniform lower estimate, using floor(N/d) disjoint
d-point grids inside {N+1,...,2*N}. The real Lagrange bases are mapped to
complex polynomials, while the values and coefficients remain arbitrary complex
numbers. All sums of norms use inequalities. The zero polynomial, d=1 and
coefficients outside the polynomial support need no exceptional premise.

Every private helper below is consumed by the proof of the single public
theorem. There is no executable-mirror claim or bounded checker.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling

open scoped BigOperators
open Polynomial Finset
open D5.S3.Analytic.Interpolation.UniformCoefficientBudget

-- A real basis is sufficient even when all interpolation values are complex.
private theorem separated_basis_budget (d : ℕ) (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ j, |x j| ≤ 2)
    (hgap : ∀ i j, i ≠ j → (2 * (d : ℝ))⁻¹ ≤ |x i - x j|)
    (i : Fin d) :
    coeffL1 (Lagrange.basis univ x i) ≤
      (6 * (d : ℝ)) ^ (d - 1) := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hprod : ∀ s : Finset (Fin d), (∀ j ∈ s, j ≠ i) →
      coeffL1 (∏ j ∈ s, Lagrange.basisDivisor (x i) (x j)) ≤
        (6 * (d : ℝ)) ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp only [prod_empty, card_empty, pow_zero]
        change (C (1 : ℝ)).sum (fun _ c => |c|) ≤ 1
        rw [Polynomial.sum_C_index (by simp)]
        norm_num
    | @insert j s hj ih =>
        intro hs
        have hji : j ≠ i := hs j (mem_insert_self j s)
        have hdist := hgap i j hji.symm
        have htwo : 0 < 2 * (d : ℝ) := by positivity
        have hdistpos : 0 < |x i - x j| :=
          lt_of_lt_of_le (inv_pos.mpr htwo) hdist
        have hmul : 1 ≤ |x i - x j| * (2 * (d : ℝ)) := by
          apply (div_le_iff₀ htwo).mp
          simpa only [one_div] using hdist
        have hinv : |x i - x j|⁻¹ ≤ 2 * (d : ℝ) := by
          rw [← one_div]
          apply (div_le_iff₀ hdistpos).mpr
          nlinarith only [hmul]
        have hfactor : coeffL1 (Lagrange.basisDivisor (x i) (x j)) ≤
            6 * (d : ℝ) := by
          rw [Lagrange.basisDivisor, coeffL1_C_mul, coeffL1_X_sub_C, abs_inv]
          calc
            |x i - x j|⁻¹ * (1 + |x j|) ≤ (2 * (d : ℝ)) * 3 :=
              mul_le_mul hinv (by have := hx j; linarith)
                (by positivity) (le_of_lt htwo)
            _ = 6 * (d : ℝ) := by ring
        have hs' : ∀ k ∈ s, k ≠ i :=
          fun k hk => hs k (mem_insert_of_mem hk)
        rw [prod_insert hj, card_insert_of_notMem hj, pow_succ]
        calc
          coeffL1 (Lagrange.basisDivisor (x i) (x j) *
              ∏ k ∈ s, Lagrange.basisDivisor (x i) (x k)) ≤
              coeffL1 (Lagrange.basisDivisor (x i) (x j)) *
                coeffL1 (∏ k ∈ s, Lagrange.basisDivisor (x i) (x k)) :=
            coeffL1_mul_le _ _
          _ ≤ (6 * (d : ℝ)) * (6 * (d : ℝ)) ^ s.card :=
            mul_le_mul hfactor (ih hs')
              (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
          _ = (6 * (d : ℝ)) ^ s.card * (6 * (d : ℝ)) := by ring
  have hb := hprod (univ.erase i) (fun j hj => (mem_erase.mp hj).1)
  simpa [Lagrange.basis] using hb

-- The finite analytic estimate: one separated grid controls coefficient energy.
private theorem separated_grid_energy (d : ℕ) (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ j, |x j| ≤ 2)
    (hgap : ∀ i j, i ≠ j → (2 * (d : ℝ))⁻¹ ≤ |x i - x j|)
    (p : ℂ[X]) (hp : p.natDegree < d) :
    (∑ k ∈ range d, ‖p.coeff k‖ ^ 2) ≤
      (d : ℝ) * ((6 * (d : ℝ)) ^ (d - 1)) ^ 2 *
        ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ ^ 2 := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let B : ℝ := (6 * (d : ℝ)) ^ (d - 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hxin : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hgap i j hne
    rw [hij, sub_self, abs_zero] at h
    have hpos : 0 < (2 * (d : ℝ))⁻¹ := by positivity
    linarith
  have hxc : Function.Injective (fun j => (x j : ℂ)) :=
    Complex.ofReal_injective.comp hxin
  have hmap (j : Fin d) :
      (Lagrange.basis univ x j).map Complex.ofRealHom =
        Lagrange.basis univ (fun k => (x k : ℂ)) j := by
    simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod,
      Polynomial.map_mul, Polynomial.map_sub]
  have hdeg : p.degree < ((univ : Finset (Fin d)).card : WithBot ℕ) := by
    have ht : p.degree < (d : WithBot ℕ) :=
      lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hp)
    simpa using ht
  have hrepr : p = ∑ j : Fin d,
      C (p.eval (x j : ℂ)) * (Lagrange.basis univ x j).map Complex.ofRealHom := by
    simpa only [Lagrange.interpolate_apply, hmap] using
      (Lagrange.eq_interpolate hxc.injOn hdeg)
  have hcoeff (k : ℕ) : p.coeff k = ∑ j : Fin d,
      p.eval (x j : ℂ) * ((Lagrange.basis univ x j).coeff k : ℂ) := by
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_map, Complex.ofRealHom_eq_coe] using congrArg (fun f : ℂ[X] => f.coeff k) hrepr
  have htriangle (k : ℕ) : ‖p.coeff k‖ ≤ ∑ j : Fin d,
      ‖p.eval (x j : ℂ)‖ * |(Lagrange.basis univ x j).coeff k| := by
    calc
      ‖p.coeff k‖ = ‖∑ j : Fin d,
          p.eval (x j : ℂ) * ((Lagrange.basis univ x j).coeff k : ℂ)‖ :=
        congrArg norm (hcoeff k)
      _ ≤ ∑ j : Fin d,
          ‖p.eval (x j : ℂ) * ((Lagrange.basis univ x j).coeff k : ℂ)‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hrange (j : Fin d) :
      (∑ k ∈ range d, |(Lagrange.basis univ x j).coeff k|) =
        coeffL1 (Lagrange.basis univ x j) := by
    have hbdeg : (Lagrange.basis univ x j).natDegree < d := by
      rw [Lagrange.natDegree_basis hxin.injOn (mem_univ j)]
      simp only [card_univ, Fintype.card_fin]
      omega
    change _ = (Lagrange.basis univ x j).sum (fun _ a => |a|)
    exact ((Lagrange.basis univ x j).sum_over_range'
      (fun _ => abs_zero) d hbdeg).symm
  have hl1 : (∑ k ∈ range d, ‖p.coeff k‖) ≤
      B * ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ := by
    calc
      (∑ k ∈ range d, ‖p.coeff k‖) ≤
          ∑ k ∈ range d, ∑ j : Fin d,
            ‖p.eval (x j : ℂ)‖ * |(Lagrange.basis univ x j).coeff k| :=
        sum_le_sum (fun k _ => htriangle k)
      _ = ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ *
          (∑ k ∈ range d, |(Lagrange.basis univ x j).coeff k|) := by
        rw [sum_comm]
        simp only [mul_sum]
      _ ≤ ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ * B := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [hrange]
        exact separated_basis_budget d hd x hx hgap j
      _ = B * ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  have hcs : (∑ j : Fin d, ‖p.eval (x j : ℂ)‖) ^ 2 ≤
      (d : ℝ) * ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (univ : Finset (Fin d))) (f := fun j => ‖p.eval (x j : ℂ)‖))
  calc
    (∑ k ∈ range d, ‖p.coeff k‖ ^ 2) ≤
        (∑ k ∈ range d, ‖p.coeff k‖) ^ 2 :=
      sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
    _ ≤ (B * ∑ j : Fin d, ‖p.eval (x j : ℂ)‖) ^ 2 :=
      (sq_le_sq₀ (sum_nonneg (fun _ _ => norm_nonneg _))
        (mul_nonneg hB (sum_nonneg (fun _ _ => norm_nonneg _)))).mpr hl1
    _ = B ^ 2 * (∑ j : Fin d, ‖p.eval (x j : ℂ)‖) ^ 2 := by ring
    _ ≤ B ^ 2 * ((d : ℝ) * ∑ j : Fin d, ‖p.eval (x j : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by dsimp [B]; ring

private def gridMode {d q : ℕ} (N : ℕ) (r : Fin q) (j : Fin d) : ℕ :=
  N + r.val + 1 + j.val * q

private theorem grid_mode_mem {d q : ℕ} (N : ℕ) (hfit : d * q ≤ N)
    (r : Fin q) (j : Fin d) : gridMode N r j ∈ Icc (N + 1) (2 * N) := by
  have hr : r.val + 1 ≤ q := by omega
  have hj : (j.val + 1) * q ≤ d * q :=
    Nat.mul_le_mul_right q (by omega)
  apply mem_Icc.mpr
  dsimp [gridMode]
  constructor
  · omega
  · nlinarith only [hr, hj, hfit]

private theorem grid_mode_injective {d q : ℕ} (N : ℕ) (hq : 0 < q) :
    Function.Injective (fun a : Fin q × Fin d => gridMode N a.1 a.2) := by
  intro a b hab
  have hab' : a.1.val + a.2.val * q = b.1.val + b.2.val * q := by
    dsimp [gridMode] at hab
    omega
  have hr : a.1.val = b.1.val := by
    have hmod := congrArg (fun n : ℕ => n % q) hab'
    simpa [Nat.add_mod, Nat.mod_eq_of_lt a.1.isLt,
      Nat.mod_eq_of_lt b.1.isLt] using hmod
  have hj : a.2.val = b.2.val :=
    Nat.mul_right_cancel hq (by omega : a.2.val * q = b.2.val * q)
  exact Prod.ext (Fin.ext hr) (Fin.ext hj)

private theorem grid_gap {d q : ℕ} (N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (hscale : N ≤ 2 * d * q) (r : Fin q) (i j : Fin d) (hij : i ≠ j) :
    (2 * (d : ℝ))⁻¹ ≤
      |(gridMode N r i : ℝ) / (N : ℝ) - (gridMode N r j : ℝ) / (N : ℝ)| := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hneq : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hdist : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have hcast : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      rw [abs_of_nonpos (by linarith : (i.val : ℝ) - (j.val : ℝ) ≤ 0)]
      linarith
    · have hcast : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      rw [abs_of_nonneg (by linarith : 0 ≤ (i.val : ℝ) - (j.val : ℝ))]
      linarith
  have hscaleR : (N : ℝ) ≤ 2 * (d : ℝ) * (q : ℝ) := by
    exact_mod_cast hscale
  have hratio : (2 * (d : ℝ))⁻¹ ≤ (q : ℝ) / (N : ℝ) := by
    rw [← one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (d : ℝ)) hNR).mpr
    nlinarith only [hscaleR]
  have hdiff : (gridMode N r i : ℝ) / (N : ℝ) -
      (gridMode N r j : ℝ) / (N : ℝ) =
        ((i.val : ℝ) - (j.val : ℝ)) * (q : ℝ) / (N : ℝ) := by
    dsimp [gridMode]
    push_cast <;> ring
  calc
    (2 * (d : ℝ))⁻¹ ≤ (q : ℝ) / (N : ℝ) := hratio
    _ ≤ |(i.val : ℝ) - (j.val : ℝ)| * (q : ℝ) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hNR)
      have hm := mul_nonneg (sub_nonneg.mpr hdist) (Nat.cast_nonneg (α := ℝ) q)
      nlinarith only [hm]
    _ = _ := by
      simp only [hdiff, abs_div, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q), abs_of_pos hNR]

/-- A constant chosen from the degree alone controls all complex coefficients by
the discrete energy on the whole scaled interval, uniformly in N and p.
The witness used in the proof is 1 / (2*d^2*((6*d)^(d-1))^2). -/
theorem discrete_coefficient_sampling_lower (d : ℕ) (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 * d ≤ N →
      ∀ p : ℂ[X], p.natDegree < d →
        κ * (N : ℝ) * (∑ r ∈ range d, ‖p.coeff r‖ ^ 2) ≤
          ∑ m ∈ Icc (N + 1) (2 * N), ‖p.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  refine ⟨1 / (2 * (d : ℝ) ^ 2 * ((6 * (d : ℝ)) ^ (d - 1)) ^ 2),
    by positivity, ?_⟩
  intro N hN p hp
  let q : ℕ := N / d
  let B : ℝ := (6 * (d : ℝ)) ^ (d - 1)
  let E : ℝ := ∑ r ∈ range d, ‖p.coeff r‖ ^ 2
  let S : ℝ := ∑ m ∈ Icc (N + 1) (2 * N), ‖p.eval ((m : ℂ) / (N : ℂ))‖ ^ 2
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hd).mpr hN
  have hq : 0 < q := by omega
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hfit : d * q ≤ N := by
    simpa only [q, Nat.mul_comm] using Nat.div_mul_le_self N d
  have hdq : d ≤ d * q := by
    calc
      d = d * 1 := by omega
      _ ≤ d * q := Nat.mul_le_mul_left d (by omega)
  have hscale : N ≤ 2 * d * q := by
    have hm := Nat.mod_lt N hd
    have he := Nat.mod_add_div N d
    change N % d + d * q = N at he
    nlinarith only [hm, he, hdq]
  have hrow (r : Fin q) : E ≤ (d : ℝ) * B ^ 2 *
      ∑ j : Fin d, ‖p.eval ((gridMode N r j : ℂ) / (N : ℂ))‖ ^ 2 := by
    let x : Fin d → ℝ := fun j => (gridMode N r j : ℝ) / (N : ℝ)
    have hx (j : Fin d) : |x j| ≤ 2 := by
      have hm := (mem_Icc.mp (grid_mode_mem N hfit r j)).2
      have hmR : (gridMode N r j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hm
      have hx0 : 0 ≤ x j := by dsimp [x]; positivity
      rw [abs_of_nonneg hx0]
      exact (div_le_iff₀ hNR).mpr (by nlinarith only [hmR])
    have hxgap : ∀ i j, i ≠ j → (2 * (d : ℝ))⁻¹ ≤ |x i - x j| := by
      intro i j hij
      exact grid_gap N hd hNpos hscale r i j hij
    have hcast (j : Fin d) : (x j : ℂ) = (gridMode N r j : ℂ) / (N : ℂ) := by
      dsimp [x]
      push_cast <;> rfl
    simpa only [E, B, hcast] using separated_grid_energy d hd x hx hxgap p hp
  have hrows : (q : ℝ) * E ≤ (d : ℝ) * B ^ 2 *
      ∑ r : Fin q, ∑ j : Fin d,
        ‖p.eval ((gridMode N r j : ℂ) / (N : ℂ))‖ ^ 2 := by
    have hs := sum_le_sum (s := (univ : Finset (Fin q))) (fun r _ => hrow r)
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum] using hs
  let modes : Finset ℕ :=
    (univ : Finset (Fin q × Fin d)).image (fun a => gridMode N a.1 a.2)
  have hsubset : modes ⊆ Icc (N + 1) (2 * N) := by
    intro m hm
    obtain ⟨a, _, rfl⟩ := mem_image.mp hm
    exact grid_mode_mem N hfit a.1 a.2
  have hsample : (∑ r : Fin q, ∑ j : Fin d,
      ‖p.eval ((gridMode N r j : ℂ) / (N : ℂ))‖ ^ 2) ≤ S := by
    calc
      (∑ r : Fin q, ∑ j : Fin d,
          ‖p.eval ((gridMode N r j : ℂ) / (N : ℂ))‖ ^ 2) =
          ∑ a : Fin q × Fin d,
            ‖p.eval ((gridMode N a.1 a.2 : ℂ) / (N : ℂ))‖ ^ 2 :=
        (Fintype.sum_prod_type (fun a : Fin q × Fin d =>
          ‖p.eval ((gridMode N a.1 a.2 : ℂ) / (N : ℂ))‖ ^ 2)).symm
      _ = ∑ m ∈ modes, ‖p.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 := by
        symm
        exact sum_image (fun a _ b _ hab => grid_mode_injective N hq hab)
      _ ≤ S := sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => sq_nonneg _)
  have htotal : (q : ℝ) * E ≤ (d : ℝ) * B ^ 2 * S :=
    hrows.trans (mul_le_mul_of_nonneg_left hsample (by positivity))
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sq_nonneg _)
  have hscaleR : (N : ℝ) ≤ 2 * (d : ℝ) * (q : ℝ) := by exact_mod_cast hscale
  have hlarge : (N : ℝ) * E ≤ (2 * (d : ℝ) ^ 2 * B ^ 2) * S := by
    calc
      (N : ℝ) * E ≤ (2 * (d : ℝ) * (q : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hscaleR hE
      _ = (2 * (d : ℝ)) * ((q : ℝ) * E) := by ring
      _ ≤ (2 * (d : ℝ)) * ((d : ℝ) * B ^ 2 * S) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by ring
  have hden : 0 < 2 * (d : ℝ) ^ 2 * B ^ 2 := by dsimp [B]; positivity
  change (1 / (2 * (d : ℝ) ^ 2 * B ^ 2)) * (N : ℝ) * E ≤ S
  calc
    (1 / (2 * (d : ℝ) ^ 2 * B ^ 2)) * (N : ℝ) * E =
        ((N : ℝ) * E) / (2 * (d : ℝ) ^ 2 * B ^ 2) := by ring
    _ ≤ S := (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlarge)

end D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling
