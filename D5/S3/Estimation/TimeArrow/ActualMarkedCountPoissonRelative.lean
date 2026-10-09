/- GID: D5/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative Poisson transfer for one or two native marked departure rows. -/

import D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicMidpoint
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Finset MeasureTheory
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open private CycleGeodesic.stirlingError_upper
  CycleGeodesic.stirlingError_formula from
  D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicMidpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative

set_option maxHeartbeats 2000000 in
/-- Uniform relative control of actual native marked count events in both experiments.
The Poisson means use the same support and marked rows as the native history law. -/
theorem actual_marked_count_poisson_relative (κ C₀ : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (np nm : Fin k → ℕ),
            (∀ j, (np j : ℝ) ≤ C₀ * L ∧ (nm j : ℝ) ≤ C₀ * L) →
            ∀ e : Experiment,
              let T := 2 * M * L
              let μp := fun j => (L : ℝ) * (1 + b r S (.inl (m j))) / 2
              let μm := fun j => (L : ℝ) * (1 - b r S (.inl (m j))) / 2
              let P := ∑ o : Obs M T e,
                if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
                then probability r e S o else 0
              let Q := ∏ j, (Real.exp (-μp j) * (μp j) ^ np j / (np j).factorial) *
                (Real.exp (-μm j) * (μm j) ^ nm j / (nm j).factorial)
              |P / Q - 1| ≤ A * (L : ℝ) ^ (k + 1) / M := by
  classical
  let R : ℝ := 2 * (C₀ + 1) / κ
  let D : ℝ := 2 * R + 1
  let Cs : ℝ := Real.exp 2 * (Real.sqrt (2 * Real.pi) + 1)
  let A : ℝ := 40 * D ^ 2 * Cs ^ 4 * (C₀ + 1) ^ 2
  let M₀ : ℕ := max 2 ⌈4 * D⌉₊
  let η₀ : ℝ := 1 / (20 * D ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A, M₀, η₀, ?_, ?_, ?_, ?_⟩
  · dsimp [A, Cs]; positivity
  · dsimp [M₀]; omega
  · dsimp [η₀]; positivity
  intro M q L k r hMM hq hqm hr hrκ hcκ hL hLη hk S m hm np nm hn e
  let T := 2 * M * L
  let bp := fun j => b r S (.inl (m j))
  let μp := fun j => (L : ℝ) * (1 + bp j) / 2
  let μm := fun j => (L : ℝ) * (1 - bp j) / 2
  let P : ℝ := ∑ o : Obs M T e,
    if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
    then probability r e S o else 0
  let Q : ℝ := ∏ j, (Real.exp (-μp j) * (μp j) ^ np j / (np j).factorial) *
    (Real.exp (-μm j) * (μm j) ^ nm j / (nm j).factorial)
  change |P / Q - 1| ≤ A * (L : ℝ) ^ (k + 1) / M
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN : (2 * (M : ℂ)) ≠ 0 := by exact_mod_cast (show (2 * (M : ℝ)) ≠ 0 by positivity)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hr1 : r < 1 := by linarith
  have hc1 : compensation M q r < 1 := by linarith
  have hb (j : Fin k) : -(1 - κ) ≤ bp j ∧ bp j ≤ 1 - κ := by
    dsimp [bp, b]
    split_ifs <;> constructor <;> linarith
  have hbp (j : Fin k) : |bp j| ≤ 1 := by
    rw [abs_le]; have := hb j; constructor <;> linarith
  have hμp (j : Fin k) : 0 < μp j ∧ κ * L / 2 ≤ μp j := by
    dsimp [μp]; have := hb j
    have hLpos : (0 : ℝ) < L := by linarith
    constructor
    · apply div_pos _ (by norm_num); apply mul_pos hLpos; linarith
    · nlinarith
  have hμm (j : Fin k) : 0 < μm j ∧ κ * L / 2 ≤ μm j := by
    dsimp [μm]; have := hb j
    have hLpos : (0 : ℝ) < L := by linarith
    constructor
    · apply div_pos _ (by norm_num); apply mul_pos hLpos; linarith
    · nlinarith
  have hQ : 0 < Q := by
    dsimp [Q]
    exact prod_pos fun j _ => mul_pos
      (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμp j).1 _)) (by positivity))
      (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμm j).1 _)) (by positivity))
  let ρp := fun j => ((np j : ℝ) + 1) / μp j
  let ρm := fun j => ((nm j : ℝ) + 1) / μm j
  have hρp (j : Fin k) : 0 < ρp j ∧ ρp j ≤ R := by
    refine ⟨div_pos (by positivity) (hμp j).1, ?_⟩
    apply (div_le_iff₀ (hμp j).1).mpr
    have hRκ : R * κ = 2 * (C₀ + 1) := by dsimp [R]; field_simp
    have hh := mul_le_mul_of_nonneg_left (hμp j).2 hR.le
    have hn' := (hn j).1
    nlinarith
  have hρm (j : Fin k) : 0 < ρm j ∧ ρm j ≤ R := by
    refine ⟨div_pos (by positivity) (hμm j).1, ?_⟩
    apply (div_le_iff₀ (hμm j).1).mpr
    have hRκ : R * κ = 2 * (C₀ + 1) := by dsimp [R]; field_simp
    have hh := mul_le_mul_of_nonneg_left (hμm j).2 hR.le
    have hn' := (hn j).2
    nlinarith
  let F (a : Experiment) (zp zm : Fin k → ℂ) : ℂ :=
    ∑ o : Obs M T a, (probability r a S o : ℂ) *
      ∏ j, zp j ^ count a o (m j) 1 * zm j ^ count a o (m j) (-1)
  have hpair (zp zm : Fin k → ℂ) : F .pair zp zm = (1 + driftA r S m zp zm) ^ T := by
    let u := tiltU zp zm
    let v := tiltV zp zm
    let U (x : Vertex M) : ℂ := ∑ j, if x = .inl (m j) then u j else 0
    let W (x : Vertex M) : ℂ := ∑ j, if x = .inl (m j) then v j else 0
    let g (j : Fin k) (x y : Vertex M) : ℂ :=
      (if x = .inl (m j) ∧ chi y = 1 then zp j else 1) *
      (if x = .inl (m j) ∧ chi y = -1 then zm j else 1)
    have hcount (o : Obs M T .pair) (j : Fin k) :
        zp j ^ count .pair o (m j) 1 * zm j ^ count .pair o (m j) (-1) =
        ∏ t : Fin T, g j (o t).1 (o t).2 := by
      dsimp [g]
      rw [prod_mul_distrib]
      simp only [prod_ite, prod_const, one_pow, mul_one, count, edges]
      rfl
    have hedge (x y : Vertex M) : ∏ j, g j x y = 1 + U x + W x * (chi y : ℂ) := by
      by_cases hx : ∃ j, x = .inl (m j)
      · obtain ⟨j, hj⟩ := hx
        have hother (i : Fin k) (hi : i ≠ j) : x ≠ .inl (m i) := by
          intro he; exact hi (hm (Sum.inl.inj (hj.symm.trans he)).symm)
        have hU : U x = u j := by
          dsimp [U]; rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp), if_pos hj]
        have hW : W x = v j := by
          dsimp [W]; rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp), if_pos hj]
        rw [prod_eq_single j (fun i _ hi => by simp [g, hother i hi]) (by simp), hU, hW]
        cases y <;> norm_num [g, hj, chi, u, v, tiltU, tiltV] <;> ring
      · have hnone (j : Fin k) : x ≠ .inl (m j) := fun hj => hx ⟨j, hj⟩
        simp [g, U, W, hnone]
    let K (p : Vertex M × Vertex M) : ℂ :=
      (2 * (M : ℂ))⁻¹ * (transition r S p.1 p.2 : ℂ) *
        (1 + U p.1 + W p.1 * (chi p.2 : ℂ))
    have hmass (o : Obs M T .pair) :
        (probability r .pair S o : ℂ) *
          (∏ j, zp j ^ count .pair o (m j) 1 * zm j ^ count .pair o (m j) (-1)) =
        ∏ t : Fin T, K (o t) := by
      simp_rw [hcount]
      rw [prod_comm]
      simp_rw [hedge]
      simp only [probability, Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_ofNat, prod_mul_distrib, K]
    have hsparse (a : Fin k → ℂ) :
        ∑ x : Vertex M, (∑ j, if x = .inl (m j) then a j else 0) = ∑ j, a j := by
      rw [sum_comm]; simp
    have hweighted : ∑ x : Vertex M, (b r S x : ℂ) * W x =
        ∑ j, (bp j : ℂ) * v j := by
      dsimp [W]
      simp_rw [mul_sum, mul_ite, mul_zero]
      rw [sum_comm]; simp [bp]
    have hrow (x : Vertex M) :
        ∑ y : Vertex M, K (x, y) =
          (1 + U x + (b r S x : ℂ) * W x) / (2 * M) := by
      dsimp [K, transition]
      simp only [Fintype.sum_sum_type, chi, Complex.ofReal_div, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_neg,
        Complex.ofReal_natCast, Complex.ofReal_ofNat, mul_one, mul_neg_one,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hMc]; ring
    have htotal : ∑ p : Vertex M × Vertex M, K p = 1 + driftA r S m zp zm := by
      rw [Fintype.sum_prod_type]
      simp_rw [hrow]
      rw [← sum_div, sum_add_distrib, sum_add_distrib, hweighted]
      rw [show (∑ x : Vertex M, U x) = ∑ j, u j from hsparse u]
      simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      dsimp [driftA, u, v, bp]
      rw [sum_add_distrib]
      push_cast
      field_simp [hMc]; ring
    dsimp [F]
    simp_rw [hmass]
    change (∑ o : Fin T → Vertex M × Vertex M, ∏ t, K (o t)) = _
    rw [← Fintype.prod_sum (fun (_ : Fin T) p => K p)]
    simp_rw [htotal]
    simp
  have hMbound : 4 * D ≤ (M : ℝ) := by
    have hh : ⌈4 * D⌉₊ ≤ M := (le_max_right _ _).trans hMM
    exact (Nat.le_ceil (4 * D)).trans (by exact_mod_cast hh)
  let η : ℝ := D / M
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 4 := by dsimp [η]; apply (div_le_iff₀ hM).mpr; linarith
  have hTη : (T : ℝ) * η ^ 2 ≤ 1 / 10 := by
    have hid : (T : ℝ) * η ^ 2 = 2 * D ^ 2 * ((L : ℝ) / M) := by
      dsimp [T, η]; push_cast; field_simp
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2 * D ^ 2 by positivity)
    dsimp [η₀] at hh
    have heq : 2 * D ^ 2 * (1 / (20 * D ^ 2)) = (1 : ℝ) / 10 := by
      field_simp; ring
    rwa [heq] at hh
  have hmean (zp zm : Fin k → ℂ) : (T : ℂ) * driftA r S m zp zm =
      ∑ j, ((μp j : ℂ) * (zp j - 1) + (μm j : ℂ) * (zm j - 1)) := by
    dsimp [T, driftA, μp, μm, bp, tiltU, tiltV]
    push_cast
    have hh (x : ℂ) : 2 * (M : ℂ) * L * (x / (2 * M)) = (L : ℂ) * x := by
      field_simp [hMc] <;> ring
    rw [hh, mul_sum]
    apply sum_congr rfl
    intro j _
    field_simp [hMc]; ring
  have hdrifts (zp zm : Fin k → ℂ) (hp : ∀ j, ‖zp j‖ ≤ R) (hm' : ∀ j, ‖zm j‖ ≤ R) :
      ‖driftA r S m zp zm‖ ≤ η ∧ ‖driftB r S m zp zm‖ ≤ η := by
    have hu (j : Fin k) : ‖tiltU zp zm j‖ ≤ R + 1 := by
      calc
        ‖tiltU zp zm j‖ ≤ ‖(zp j + zm j) / 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 := by
          rw [norm_div]; norm_num
          have := norm_add_le (zp j) (zm j)
          nlinarith [hp j, hm' j]
    have hv (j : Fin k) : ‖tiltV zp zm j‖ ≤ R := by
      dsimp [tiltV]; rw [norm_div]; norm_num
      have := norm_sub_le (zp j) (zm j)
      nlinarith [hp j, hm' j]
    have hb' (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hbp j
    have ha (j : Fin k) :
        ‖tiltU zp zm j + (b r S (.inl (m j)) : ℂ) * tiltV zp zm j‖ ≤ D := by
      have hmul := mul_le_mul (hb' j) (hv j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have := norm_add_le (tiltU zp zm j) ((b r S (.inl (m j)) : ℂ) * tiltV zp zm j)
      rw [norm_mul] at this
      dsimp [D]; nlinarith [hu j]
    have hb'' (j : Fin k) :
        ‖tiltV zp zm j + (b r S (.inl (m j)) : ℂ) * tiltU zp zm j‖ ≤ D := by
      have hmul := mul_le_mul (hb' j) (hu j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have := norm_add_le (tiltV zp zm j) ((b r S (.inl (m j)) : ℂ) * tiltU zp zm j)
      rw [norm_mul] at this
      dsimp [D]; nlinarith [hv j]
    have hsum (f : Fin k → ℂ) (hf : ∀ j, ‖f j‖ ≤ D) : ‖∑ j, f j‖ ≤ 2 * D := by
      calc
        ‖∑ j, f j‖ ≤ ∑ j, ‖f j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin k, D := sum_le_sum fun j _ => hf j
        _ ≤ 2 * D := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          rcases hk with rfl | rfl <;> norm_num <;> linarith
    constructor
    · dsimp [driftA]
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.norm_natCast]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
      have he : η * (2 * M) = 2 * D := by dsimp [η]; field_simp
      rw [he]; exact hsum _ ha
    · dsimp [driftB]
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.norm_natCast]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
      have he : η * (2 * M) = 2 * D := by dsimp [η]; field_simp
      rw [he]; exact hsum _ hb''
  have hpath (zp zm : Fin k → ℂ) (hp : ∀ j, ‖zp j‖ ≤ R) (hm' : ∀ j, ‖zm j‖ ≤ R) :
      ‖F .path zp zm - Complex.exp ((T : ℂ) * driftA r S m zp zm)‖ ≤
        20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * (driftA r S m zp zm).re) := by
    exact actual_marked_path_pgf_poisson_envelope hq hqm hr hr1 hc1 S hk m hm zp zm
      hη hη1 (hdrifts zp zm hp hm').1 (hdrifts zp zm hp hm').2 hTη
  have hpairEnvelope (zp zm : Fin k → ℂ) (hp : ∀ j, ‖zp j‖ ≤ R)
      (hm' : ∀ j, ‖zm j‖ ≤ R) :
      ‖F .pair zp zm - Complex.exp ((T : ℂ) * driftA r S m zp zm)‖ ≤
        20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * (driftA r S m zp zm).re) := by
    let a := driftA r S m zp zm
    have ha : ‖a‖ ≤ η := (hdrifts zp zm hp hm').1
    have halt : ‖a‖ < 1 := by linarith
    have hh : 1 + a ≠ 0 := by
      intro hh
      have he : a = -1 := by linear_combination hh
      rw [he, norm_neg, norm_one] at ha
      linarith
    let δ := Complex.log (1 + a) - a
    have hd : ‖δ‖ ≤ (2 / 3) * η ^ 2 := by
      have hlog := Complex.norm_log_one_add_sub_self_le halt
      have hden : 0 < 2 * (1 - ‖a‖) := by positivity
      have hb : ‖a‖ ^ 2 / (2 * (1 - ‖a‖)) ≤ (2 / 3) * η ^ 2 := by
        apply (div_le_iff₀ hden).mpr
        have hs : ‖a‖ ^ 2 ≤ η ^ 2 := by nlinarith [norm_nonneg a]
        have he : 3 / 2 ≤ 2 * (1 - ‖a‖) := by linarith
        nlinarith [sq_nonneg η]
      calc
        ‖δ‖ ≤ ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2 := hlog
        _ = ‖a‖ ^ 2 / (2 * (1 - ‖a‖)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]; ring
        _ ≤ (2 / 3) * η ^ 2 := hb
    have hδT : ‖(T : ℂ) * δ‖ ≤ (T : ℝ) * ((2 / 3) * η ^ 2) := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
    have he : ‖Complex.exp ((T : ℂ) * δ) - 1‖ ≤
        (4 / 3) * (T : ℝ) * η ^ 2 := by
      apply (Complex.norm_exp_sub_one_le (hδT.trans (by nlinarith))).trans
      nlinarith
    have hid : (1 + a) ^ T - Complex.exp ((T : ℂ) * a) =
        Complex.exp ((T : ℂ) * a) * (Complex.exp ((T : ℂ) * δ) - 1) := by
      have hex : (1 + a) ^ T =
          Complex.exp ((T : ℂ) * a) * Complex.exp ((T : ℂ) * δ) := by
        rw [← Complex.exp_add]
        have hg : (T : ℂ) * a + (T : ℂ) * δ =
            (T : ℂ) * Complex.log (1 + a) := by dsimp [δ]; ring
        rw [hg, Complex.exp_nat_mul, Complex.exp_log hh]
      rw [hex]; ring
    rw [hpair, hid, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero]
    have hexp := Real.exp_pos ((T : ℝ) * a.re)
    change Real.exp ((T : ℝ) * a.re) * ‖Complex.exp ((T : ℂ) * δ) - 1‖ ≤
      20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * a.re)
    calc
      _ ≤ Real.exp ((T : ℝ) * a.re) * ((4 / 3) * (T : ℝ) * η ^ 2) :=
        mul_le_mul_of_nonneg_left he hexp.le
      _ ≤ 20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * a.re) := by
        have ht : 0 ≤ (T : ℝ) * η ^ 2 := mul_nonneg (Nat.cast_nonneg T) (sq_nonneg η)
        nlinarith only [mul_nonneg ht hexp.le]
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let I := Fin k × Bool
  let n (a : I) : ℕ := if a.2 then nm a.1 else np a.1
  let ρ (a : I) : ℝ := if a.2 then ρm a.1 else ρp a.1
  let c (o : Obs M T e) (a : I) : ℕ := count e o (m a.1) (if a.2 then -1 else 1)
  let z (t : UnitAddTorus I) (a : I) : ℂ := (ρ a : ℂ) * fourier 1 (t a)
  let W : ℂ := ∏ a : I, (ρ a : ℂ) ^ n a
  have hznorm (t : UnitAddTorus I) (a : I) : ‖z t a‖ = ρ a := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    apply abs_of_pos
    cases a with | mk j s => cases s <;> simp only [ρ, Bool.false_eq_true, if_false, if_true]
                            <;> exact (by first | exact (hρp j).1 | exact (hρm j).1)
  have hfourierpow (t : UnitAddCircle) (N : ℕ) :
      (fourier 1 t : ℂ) ^ N = fourier (N : ℤ) t := by
    induction N with
    | zero => simp [fourier_zero]
    | succ N ih => simpa only [pow_succ, ih, Nat.cast_add, Nat.cast_one] using
        (fourier_add (m := (N : ℤ)) (n := 1) (x := t)).symm
  have hmono (v : I → ℕ) :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        ∏ a, z t a ^ v a) =
        if v = n then W else 0 := by
    have hchar (t : UnitAddTorus I) :
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * (∏ a, z t a ^ v a) =
        (∏ a : I, (ρ a : ℂ) ^ v a) *
          ∏ a : I, (fourier (-(n a : ℤ)) (t a) * fourier (v a : ℤ) (t a)) := by
      simp only [z, mul_pow, hfourierpow, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
      rw [prod_mul_distrib, prod_mul_distrib]; ring
    simp_rw [hchar]
    rw [integral_const_mul]
    rw [integral_fintype_prod_volume_eq_prod
      (fun a (t : UnitAddCircle) => fourier (-(n a : ℤ)) t * fourier (v a : ℤ) t)]
    have hi (a : I) :
        (∫ t : UnitAddCircle, fourier (-(n a : ℤ)) t * fourier (v a : ℤ) t) =
          if n a = v a then (1 : ℂ) else 0 := by
      change fourierCoeff (fourier (v a : ℤ)) (n a : ℤ) = _
      rw [fourierCoeff_fourier]
      simp [Pi.single_apply]
    simp_rw [hi]
    by_cases hv : v = n
    · subst v; simp [W]
    · obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
      rw [if_neg hv]
      have hz : (∏ a : I, if n a = v a then (1 : ℂ) else 0) = 0 := by
        apply prod_eq_zero (mem_univ a)
        exact if_neg (Ne.symm ha)
      rw [hz, mul_zero]
  have hcounts (o : Obs M T e) : (c o = n) ↔
      (∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j) := by
    constructor
    · intro h j
      exact ⟨congrFun h (j, false), congrFun h (j, true)⟩
    · intro h; funext a
      rcases a with ⟨j, s⟩
      cases s <;> first | exact (h j).1 | exact (h j).2
  have hproduct (o : Obs M T e) (t : UnitAddTorus I) :
      (∏ j, z t (j, false) ^ count e o (m j) 1 * z t (j, true) ^ count e o (m j) (-1)) =
        ∏ a : I, z t a ^ c o a := by
    rw [Fintype.prod_prod_type]
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, c, Bool.false_eq_true, if_false, if_true]
    exact mul_comm _ _
  have hNativeCoefficient :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        F e (fun j => z t (j, false)) (fun j => z t (j, true))) = (P : ℂ) * W := by
    simp only [F, mul_sum]
    rw [integral_finsetSum]
    · simp_rw [hproduct]
      have hterm (o : Obs M T e) :
          (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
            ((probability r e S o : ℂ) * ∏ a, z t a ^ c o a)) =
          (if c o = n then (probability r e S o : ℂ) else 0) * W := by
        simp_rw [mul_left_comm _ (probability r e S o : ℂ)]
        rw [integral_const_mul, hmono]
        split_ifs <;> simp
      simp_rw [hterm, hcounts]
      simp only [← sum_mul, P, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]
    · intro o _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp [z, UnitAddTorus.mFourier, F]
      fun_prop
  let G (t : UnitAddTorus I) : ℂ := Complex.exp
    (∑ j, ((μp j : ℂ) * (z t (j, false) - 1) + (μm j : ℂ) * (z t (j, true) - 1)))
  have hPoissonCoefficient :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * G t) =
        (Q : ℂ) * W := by
    let μ (a : I) : ℝ := if a.2 then μm a.1 else μp a.1
    have hsingle (a : I) :
        (∫ t : UnitAddCircle, fourier (-(n a : ℤ)) t *
          Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1))) =
        Complex.exp (-(μ a : ℂ)) * (μ a : ℂ) ^ n a /
          (n a).factorial * (ρ a : ℂ) ^ n a := by
      let f (N : ℕ) (t : UnitAddCircle) : ℂ :=
        fourier (-(n a : ℤ)) t * (((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t) ^ N /
          (N.factorial : ℂ))
      have hf (N : ℕ) : Integrable (f N) := by
        apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        dsimp only [f]; fun_prop
      have hnorm (N : ℕ) (t : UnitAddCircle) :
          ‖f N t‖ = ‖(μ a : ℂ) * (ρ a : ℂ)‖ ^ N / (N.factorial : ℝ) := by
        simp only [f, norm_mul, fourier_apply, Circle.norm_coe, one_mul, norm_div, norm_pow,
          mul_one, Complex.norm_natCast]
      have hsum : Summable (fun N => ∫ t : UnitAddCircle, ‖f N t‖) := by
        simp_rw [hnorm]
        simpa using Real.summable_pow_div_factorial ‖(μ a : ℂ) * (ρ a : ℂ)‖
      have hexp (t : UnitAddCircle) :
          (∑' N, f N t) = fourier (-(n a : ℤ)) t *
            Complex.exp ((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t) := by
        dsimp only [f]
        rw [tsum_mul_left]
        rw [Complex.exp_eq_exp_ℂ]
        exact congrArg (fun w : ℂ => fourier (-(n a : ℤ)) t * w)
          (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq
      have hterm (N : ℕ) :
          (∫ t : UnitAddCircle, f N t) =
          if N = n a then ((μ a : ℂ) * (ρ a : ℂ)) ^ n a / (n a).factorial else 0 := by
        have he (t : UnitAddCircle) : f N t =
            (((μ a : ℂ) * (ρ a : ℂ)) ^ N / (N.factorial : ℂ)) *
              (fourier (-(n a : ℤ)) t * fourier (N : ℤ) t) := by
          dsimp only [f]; rw [mul_pow, hfourierpow]; ring
        simp_rw [he]
        rw [integral_const_mul]
        change _ * fourierCoeff (fourier (N : ℤ)) (n a : ℤ) = _
        rw [fourierCoeff_fourier]
        by_cases h : N = n a
        · subst N; simp [Pi.single_apply]
        · simp [Pi.single_apply, h, Ne.symm h]
      have he (t : UnitAddCircle) :
          fourier (-(n a : ℤ)) t *
            Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1)) =
          Complex.exp (-(μ a : ℂ)) *
            (fourier (-(n a : ℤ)) t *
              Complex.exp ((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t)) := by
        rw [show (μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1) =
          -(μ a : ℂ) + (μ a : ℂ) * (ρ a : ℂ) * fourier 1 t by ring,
          Complex.exp_add]; ring
      simp_rw [he]
      rw [integral_const_mul]
      simp_rw [← hexp]
      rw [← integral_tsum_of_summable_integral_norm hf hsum]
      simp_rw [hterm]
      rw [tsum_ite_eq]
      rw [mul_pow]; ring
    have hG (t : UnitAddTorus I) : G t =
        ∏ a : I, Complex.exp ((μ a : ℂ) * (z t a - 1)) := by
      dsimp [G]
      rw [← Complex.exp_sum]
      congr 1
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro j _
      simp only [Fintype.sum_bool, μ, Bool.false_eq_true, if_false, if_true]
      ring
    simp_rw [hG]
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, ← prod_mul_distrib]
    dsimp only [z]
    rw [integral_fintype_prod_volume_eq_prod
      (fun a (t : UnitAddCircle) => fourier (-(n a : ℤ)) t *
        Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1)))]
    simp_rw [hsingle]
    rw [prod_mul_distrib]
    congr 1
    dsimp [Q]
    rw [Fintype.prod_prod_type]
    push_cast
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, μ, n, Bool.false_eq_true, if_false, if_true]
    ring
  let H : ℝ := Real.exp (∑ j, (μp j * (ρp j - 1) + μm j * (ρm j - 1)))
  have hpoint (t : UnitAddTorus I) :
      ‖F e (fun j => z t (j, false)) (fun j => z t (j, true)) - G t‖ ≤
        20 * (T : ℝ) * η ^ 2 * H := by
    have hp (j : Fin k) : ‖z t (j, false)‖ ≤ R := by
      rw [hznorm]; exact (hρp j).2
    have hm' (j : Fin k) : ‖z t (j, true)‖ ≤ R := by
      rw [hznorm]; exact (hρm j).2
    have henvelope :
        ‖F e (fun j => z t (j, false)) (fun j => z t (j, true)) -
          Complex.exp ((T : ℂ) * driftA r S m
            (fun j => z t (j, false)) (fun j => z t (j, true)))‖ ≤
          20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) *
            (driftA r S m (fun j => z t (j, false)) (fun j => z t (j, true))).re) := by
      cases e
      · exact hpairEnvelope _ _ hp hm'
      · exact hpath _ _ hp hm'
    have hre : (T : ℝ) *
        (driftA r S m (fun j => z t (j, false)) (fun j => z t (j, true))).re ≤
        ∑ j, (μp j * (ρp j - 1) + μm j * (ρm j - 1)) := by
      have hh := congrArg Complex.re (hmean (fun j => z t (j, false))
        (fun j => z t (j, true)))
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.one_re] at hh
      rw [hh]
      apply sum_le_sum
      intro j _
      have hzp : (z t (j, false)).re ≤ ρp j := by
        exact (Complex.re_le_norm _).trans_eq (hznorm t (j, false))
      have hzm : (z t (j, true)).re ≤ ρm j := by
        exact (Complex.re_le_norm _).trans_eq (hznorm t (j, true))
      nlinarith [(hμp j).1, (hμm j).1]
    have heq : G t = Complex.exp ((T : ℂ) * driftA r S m
        (fun j => z t (j, false)) (fun j => z t (j, true))) := by
      dsimp only [G]; rw [hmean]
    rw [heq]
    exact henvelope.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre)
      (by positivity))
  have hcharNorm (t : UnitAddTorus I) :
      ‖UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, prod_const_one]
  have herror : |P - Q| * ‖W‖ ≤ 20 * (T : ℝ) * η ^ 2 * H := by
    have hiF : Integrable (fun t : UnitAddTorus I =>
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
          F e (fun j => z t (j, false)) (fun j => z t (j, true))) := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp only [F, z, UnitAddTorus.mFourier]; fun_prop
    have hiG : Integrable (fun t : UnitAddTorus I =>
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * G t) := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp only [G, z, UnitAddTorus.mFourier]; fun_prop
    have hid : (P : ℂ) * W - (Q : ℂ) * W =
        ∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
          (F e (fun j => z t (j, false)) (fun j => z t (j, true)) - G t) := by
      simp_rw [mul_sub]
      rw [integral_sub hiF hiG, hNativeCoefficient, hPoissonCoefficient]
    have hh := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (UnitAddTorus I)))
      (C := 20 * (T : ℝ) * η ^ 2 * H)
      (f := fun t : UnitAddTorus I => UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        (F e (fun j => z t (j, false)) (fun j => z t (j, true)) - G t))
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul, hcharNorm, one_mul]
        exact hpoint t)
    rw [← hid, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at hh
    simpa using hh
  have hStirling (N : ℕ) :
      Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N ≤
        Cs * Real.sqrt ((N : ℝ) + 1) := by
    by_cases hN0 : N = 0
    · subst N
      simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
        mul_one, pow_zero, div_one, Real.sqrt_one]
      dsimp only [Cs]
      have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), Real.exp_pos 2]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hNp : (0 : ℝ) < N := by linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfac : (0 : ℝ) < N.factorial := by positivity
    have hupper : CycleGeodesic.stirlingError N ≤ 1 := by
      have hh := CycleGeodesic.stirlingError_upper (N - 1)
      have hi : N - 1 + 1 = N := by omega
      rw [hi] at hh
      have hj : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hi
      rw [hj] at hh
      exact hh.trans ((div_le_iff₀ (by positivity : (0 : ℝ) < 12 * N)).mpr
        (by linarith))
    have hf := CycleGeodesic.stirlingError_formula hN0
    have hlog := Real.log_le_log hNp (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (N : ℝ) + 1 / 2 by positivity)
    let X : ℝ := Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N
    have hX : 0 < X := by dsimp only [X]; positivity
    have hlogX : Real.log X ≤ 2 + (1 / 2) * Real.log ((N : ℝ) + 1) +
        (1 / 2) * Real.log (2 * Real.pi) := by
      dsimp only [X]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (Real.exp_ne_zero _) hfac.ne', Real.log_exp, Real.log_pow]
      nlinarith [hupper, hf]
    have hsqrtN : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 hN1
    have hsqrtpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have he := Real.exp_le_exp.mpr hlogX
    rw [Real.exp_log hX] at he
    have hs1 : (1 / 2) * Real.log ((N : ℝ) + 1) = Real.log (Real.sqrt ((N : ℝ) + 1)) := by
      rw [Real.log_sqrt hN1.le]; ring
    have hs2 : (1 / 2) * Real.log (2 * Real.pi) = Real.log (Real.sqrt (2 * Real.pi)) := by
      rw [Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi)]; ring
    rw [hs1, hs2, Real.exp_add, Real.exp_add, Real.exp_log hsqrtN, Real.exp_log hsqrtpi] at he
    dsimp only [X] at he
    exact he.trans (by dsimp only [Cs]; nlinarith [Real.exp_pos 2])
  have hweight (μ : ℝ) (hμ : 0 < μ) (N : ℕ) :
      Real.exp (μ * (((N : ℝ) + 1) / μ - 1)) ≤
        (Real.exp (-μ) * μ ^ N / (N.factorial : ℝ) *
          (((N : ℝ) + 1) / μ) ^ N) * Cs * Real.sqrt ((N : ℝ) + 1) := by
    let w := Real.exp (-μ) * μ ^ N / (N.factorial : ℝ) * (((N : ℝ) + 1) / μ) ^ N
    have hw : 0 < w := by dsimp only [w]; positivity
    have hid : Real.exp (μ * (((N : ℝ) + 1) / μ - 1)) =
        w * (Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N) := by
      have he : μ * (((N : ℝ) + 1) / μ - 1) = -μ + ((N : ℝ) + 1) := by
        field_simp [hμ.ne']; ring
      rw [he, Real.exp_add]
      dsimp only [w]
      rw [div_pow]
      field_simp [hμ.ne']
    rw [hid]
    exact (mul_le_mul_of_nonneg_left (hStirling N) hw.le).trans_eq (by ring)
  let B₀ : ℝ := (C₀ + 1) * L
  let w (j : Fin k) : ℝ :=
    (Real.exp (-μp j) * μp j ^ np j / (np j).factorial * ρp j ^ np j) *
      (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial * ρm j ^ nm j)
  have hwpos (j : Fin k) : 0 < w j := by
    have hp := (hμp j).1
    have hm := (hμm j).1
    have hrp := (hρp j).1
    have hrm := (hρm j).1
    dsimp only [w]; positivity
  have hWnorm : ‖W‖ = ∏ j, ρp j ^ np j * ρm j ^ nm j := by
    dsimp only [W]
    rw [norm_prod, Fintype.prod_prod_type]
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      ρ, n, Bool.false_eq_true, if_false, if_true]
    rw [abs_of_pos (hρp j).1, abs_of_pos (hρm j).1]
    ring
  have hWpos : 0 < ‖W‖ := by rw [hWnorm]; exact prod_pos fun j _ => mul_pos (pow_pos (hρp j).1 _) (pow_pos (hρm j).1 _)
  have hqw : Q * ‖W‖ = ∏ j, w j := by
    rw [hWnorm]
    dsimp only [Q, w]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    ring
  have hnormalization : H ≤ Q * ‖W‖ * (Cs ^ 2 * B₀) ^ k := by
    have hHP : H = ∏ j, Real.exp (μp j * (ρp j - 1)) *
        Real.exp (μm j * (ρm j - 1)) := by
      dsimp only [H]
      rw [Real.exp_sum]
      simp_rw [Real.exp_add]
    have hp (j : Fin k) :
        Real.exp (μp j * (ρp j - 1)) * Real.exp (μm j * (ρm j - 1)) ≤
          w j * (Cs ^ 2 * B₀) := by
      have hsp := hweight (μp j) (hμp j).1 (np j)
      have hsm := hweight (μm j) (hμm j).1 (nm j)
      change Real.exp (μp j * (ρp j - 1)) ≤ _ at hsp
      change Real.exp (μm j * (ρm j - 1)) ≤ _ at hsm
      have hnp : (np j : ℝ) + 1 ≤ B₀ := by
        dsimp only [B₀]; nlinarith [(hn j).1]
      have hnm : (nm j : ℝ) + 1 ≤ B₀ := by
        dsimp only [B₀]; nlinarith [(hn j).2]
      have hs : Real.sqrt ((np j : ℝ) + 1) * Real.sqrt ((nm j : ℝ) + 1) ≤ B₀ := by
        calc
          _ ≤ Real.sqrt B₀ * Real.sqrt B₀ := by gcongr
          _ = B₀ := Real.mul_self_sqrt (by dsimp only [B₀]; positivity)
      have hc : 0 ≤ Cs := by dsimp only [Cs]; positivity
      have hmp := (hμp j).1
      have hrp := (hρp j).1
      have hh := mul_le_mul hsp hsm (Real.exp_pos _).le (by positivity)
      have hnw : 0 ≤ w j * Cs ^ 2 := mul_nonneg (hwpos j).le (sq_nonneg Cs)
      have he : (Real.exp (-μp j) * μp j ^ np j / (np j).factorial * ρp j ^ np j *
          Cs * Real.sqrt ((np j : ℝ) + 1)) *
          (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial * ρm j ^ nm j *
          Cs * Real.sqrt ((nm j : ℝ) + 1)) =
            w j * Cs ^ 2 * (Real.sqrt ((np j : ℝ) + 1) * Real.sqrt ((nm j : ℝ) + 1)) := by
        dsimp only [w]; ring
      rw [he] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_left hs hnw).trans_eq (by ring))
    rw [hHP, hqw]
    have hh := prod_le_prod₀ (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
      (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le) (fun j _ => hp j)
    simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, mul_pow] using hh
  have hCs : 1 ≤ Cs := by
    dsimp only [Cs]
    have he : 1 ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have hscale : (Cs ^ 2 * B₀) ^ k ≤ Cs ^ 4 * (C₀ + 1) ^ 2 * (L : ℝ) ^ k := by
    dsimp only [B₀]
    rcases hk with rfl | rfl
    · simp only [pow_one]
      have hcs2 : 1 ≤ Cs ^ 2 := by nlinarith
      have hs : Cs ^ 2 ≤ Cs ^ 4 := by nlinarith [sq_nonneg (Cs ^ 2 - 1)]
      have hc : C₀ + 1 ≤ (C₀ + 1) ^ 2 := by nlinarith
      have hh := mul_le_mul hs hc (by linarith : 0 ≤ C₀ + 1) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg L)
    · apply le_of_eq; ring
  have hrelative : |P / Q - 1| ≤
      20 * (T : ℝ) * η ^ 2 * (Cs ^ 4 * (C₀ + 1) ^ 2 * (L : ℝ) ^ k) := by
    have hn := hnormalization.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
    have he := herror.trans (mul_le_mul_of_nonneg_left hn (by positivity :
      0 ≤ 20 * (T : ℝ) * η ^ 2))
    rw [div_sub_one hQ.ne', abs_div, abs_of_pos hQ]
    apply (div_le_iff₀ hQ).mpr
    apply (mul_le_mul_iff_right₀ hWpos).mp
    nlinarith
  apply hrelative.trans_eq
  dsimp only [A, T, η]
  rw [pow_succ]
  push_cast
  field_simp
  ring

#print axioms actual_marked_count_poisson_relative
end D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative
