/- GID: D5/S3/Estimation/TimeArrow/ArbitraryMarkedCountPoissonRelative
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ArbitraryMarkedCountPoissonRelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative forward count transfer at exact means and arbitrary integer observation lengths. -/

import D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
import D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

open Finset MeasureTheory
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative

/-- Exact generating function of actual forward independent adjacent pairs. -/
theorem actual_marked_pair_pgf {M q s k : ℕ} (hMnat : 0 < M)
    (r : ℝ) (S : Support M q) (m : Fin k → Fin M) (hm : Function.Injective m)
    (zp zm : Fin k → ℂ) :
    (∑ o : Obs M s .pair, (probability r .pair S o : ℂ) *
      ∏ j, zp j ^ count .pair o (m j) 1 * zm j ^ count .pair o (m j) (-1)) =
      (1 + driftA r S m zp zm) ^ s := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let T := s
  let bp := fun j => b r S (.inl (m j))
  let F (a : Experiment) (zp zm : Fin k → ℂ) : ℂ :=
    ∑ o : Obs M T a, (probability r a S o : ℂ) *
      ∏ j, zp j ^ count a o (m j) 1 * zm j ^ count a o (m j) (-1)
  change F .pair zp zm = (1 + driftA r S m zp zm) ^ T

  let u := tiltU zp zm
  let v := tiltV zp zm
  let U (x : Vertex M) : ℂ := ∑ j, if x = .inl (m j) then u j else 0
  let W (x : Vertex M) : ℂ := ∑ j, if x = .inl (m j) then v j else 0
  let K (p : Vertex M × Vertex M) : ℂ :=
    (2 * (M : ℂ))⁻¹ * (transition r S p.1 p.2 : ℂ) *
      (1 + U p.1 + W p.1 * (chi p.2 : ℂ))
  have hmass (o : Obs M T .pair) :
      (probability r .pair S o : ℂ) *
        (∏ j, zp j ^ count .pair o (m j) 1 * zm j ^ count .pair o (m j) (-1)) =
      ∏ t : Fin T, K (o t) := by
    rw [D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.count_monomial .pair m zp zm o]
    simp_rw [D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.edgeTilt_eq_affine m hm zp zm]
    change (probability r .pair S o : ℂ) *
      (∏ t : Fin T, (1 + U (o t).1 + W (o t).1 * (chi (o t).2 : ℂ))) = _
    simp only [probability, Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, prod_mul_distrib, K]
  have hsparse (a : Fin k → ℂ) :
      ∑ x : Vertex M, (∑ j, if x = .inl (m j) then a j else 0) = ∑ j, a j := by
    simpa only [one_mul, D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.sparse] using
      D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.sparse_sum m (fun _ => 1) a
  have hweighted : ∑ x : Vertex M, (b r S x : ℂ) * W x =
      ∑ j, (bp j : ℂ) * v j :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.sparse_sum m (fun x => (b r S x : ℂ)) v
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

set_option maxHeartbeats 2000000 in
/-- Uniform relative control of actual native marked count events in both experiments.
The Poisson means use the same support and marked rows as the native history law. -/
theorem arbitrary_marked_count_poisson_relative (κ C₀ : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q s k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        let L := (s : ℝ) / (2 * M)
        1 ≤ L → L / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (np nm : Fin k → ℕ),
            (∀ j, (np j : ℝ) ≤ C₀ * L ∧ (nm j : ℝ) ≤ C₀ * L) →
            ∀ e : Experiment,
              let T := s
              let μp := fun j => L * (1 + b r S (.inl (m j))) / 2
              let μm := fun j => L * (1 - b r S (.inl (m j))) / 2
              let P := ∑ o : Obs M T e,
                if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
                then probability r e S o else 0
              let Q := ∏ j, (Real.exp (-μp j) * (μp j) ^ np j / (np j).factorial) *
                (Real.exp (-μm j) * (μm j) ^ nm j / (nm j).factorial)
              |P / Q - 1| ≤ A * L ^ (k + 1) / M := by
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
  intro M q s k r hMM hq hqm hr hrκ hcκ L hL hLη hk S m hm np nm hn e
  let T := s
  let bp := fun j => b r S (.inl (m j))
  let μp := fun j => L * (1 + bp j) / 2
  let μm := fun j => L * (1 - bp j) / 2
  let P : ℝ := ∑ o : Obs M T e,
    if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
    then probability r e S o else 0
  let Q : ℝ := ∏ j, (Real.exp (-μp j) * (μp j) ^ np j / (np j).factorial) *
    (Real.exp (-μm j) * (μm j) ^ nm j / (nm j).factorial)
  change |P / Q - 1| ≤ A * L ^ (k + 1) / M
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN : (2 * (M : ℂ)) ≠ 0 := by exact_mod_cast (show (2 * (M : ℝ)) ≠ 0 by positivity)
  have hLr : (1 : ℝ) ≤ L := hL
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
  let F (a : Experiment) (zp zm : Fin k → ℂ) : ℂ :=
    ∑ o : Obs M T a, (probability r a S o : ℂ) *
      ∏ j, zp j ^ count a o (m j) 1 * zm j ^ count a o (m j) (-1)
  have hpair (zp zm : Fin k → ℂ) : F .pair zp zm = (1 + driftA r S m zp zm) ^ T :=
    actual_marked_pair_pgf (by omega) r S m hm zp zm
  have hMbound : 4 * D ≤ (M : ℝ) := by
    have hh : ⌈4 * D⌉₊ ≤ M := (le_max_right _ _).trans hMM
    exact (Nat.le_ceil (4 * D)).trans (by exact_mod_cast hh)
  let η : ℝ := D / M
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 4 := by dsimp [η]; apply (div_le_iff₀ hM).mpr; linarith
  have hTη : (T : ℝ) * η ^ 2 ≤ 1 / 10 := by
    have hid : (T : ℝ) * η ^ 2 = 2 * D ^ 2 * (L / M) := by
      dsimp [T, η, L]; push_cast; field_simp
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2 * D ^ 2 by positivity)
    dsimp [η₀] at hh
    have heq : 2 * D ^ 2 * (1 / (20 * D ^ 2)) = (1 : ℝ) / 10 := by
      field_simp; ring
    rwa [heq] at hh
  have hmean (zp zm : Fin k → ℂ) : (T : ℂ) * driftA r S m zp zm =
      ∑ j, ((μp j : ℂ) * (zp j - 1) + (μm j : ℂ) * (zm j - 1)) := by
    dsimp [T, driftA, μp, μm, bp, tiltU, tiltV, L]
    push_cast
    rw [← mul_div_assoc, mul_sum, sum_div]
    apply sum_congr rfl
    intro j _
    field_simp [hMc]
    ring
  have hdrifts (zp zm : Fin k → ℂ) (hp : ∀ j, ‖zp j‖ ≤ R) (hm' : ∀ j, ‖zm j‖ ≤ R) :
      ‖driftA r S m zp zm‖ ≤ η ∧ ‖driftB r S m zp zm‖ ≤ η := by
    have huv := D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.tilt_norms zp zm R hp hm'
    have hu (j : Fin k) : ‖tiltU zp zm j‖ ≤ R + 1 := (huv j).1
    have hv (j : Fin k) : ‖tiltV zp zm j‖ ≤ R := (huv j).2
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
    have hsum (f : Fin k → ℂ) (hf : ∀ j, ‖f j‖ ≤ D) : ‖∑ j, f j‖ ≤ 2 * D :=
      D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.marked_sum_norm hk D hD.le f hf
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
  have hrelative : |P / Q - 1| ≤
      20 * (T : ℝ) * η ^ 2 * (Cs ^ 4 * (C₀ + 1) ^ 2 * L ^ k) := by
    apply (D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient.finite_count_poisson_relative
      κ C₀ L (20 * (T : ℝ) * η ^ 2) hκ hC hLr (by positivity) hk
      (fun o : Obs M T e => probability r e S o)
      (fun o j => count e o (m j) 1) (fun o j => count e o (m j) (-1))
      μp μm hμp hμm np nm hn ?_).trans_eq (by dsimp [Cs]; ring)
    intro zp zm hp hm'
    have he : ‖F e zp zm - Complex.exp ((T : ℂ) * driftA r S m zp zm)‖ ≤
        20 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * (driftA r S m zp zm).re) := by
      cases e
      · exact hpairEnvelope zp zm hp hm'
      · exact hpath zp zm hp hm'
    have hreal := congrArg Complex.re (hmean zp zm)
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.one_re] at hreal
    simpa only [F, hmean zp zm, hreal] using he
  apply hrelative.trans_eq
  have hs : (s : ℝ) = 2 * (M : ℝ) * L := by dsimp [L]; field_simp
  dsimp only [A, T, η]
  rw [hs, pow_succ]
  field_simp [hM.ne'] <;> ring

#print axioms arbitrary_marked_count_poisson_relative
end D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative
