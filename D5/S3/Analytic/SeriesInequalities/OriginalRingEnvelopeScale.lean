/- GID: D5/S3/Analytic/SeriesInequalities/OriginalRingEnvelopeScale
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/OriginalRingEnvelopeScale
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-scale coefficient control for the original Lorentz ring centers. -/

import D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability

open Finset Polynomial Complex Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 800000

namespace D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale

open LorentzLowDegreeCoefficientRemainder LorentzLocalCoefficientKernel
open LorentzCoefficientRemainder LorentzWeightedHolderControl LorentzCommonGridStability

private lemma delta_eq_radius (n : ℕ) (x : ℝ) :
    delta n x = derivativeRadius n 1 x := by simp [delta, derivativeRadius]

private lemma coarse_delta {n b : ℕ} (hn : 0 < n) (hb : 1 ≤ b)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    delta n x ≤ (b : ℝ) * delta (n*b) x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hv : 0 ≤ x*(1-x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  unfold delta
  rw [mul_max_of_nonneg _ _ hb0.le]
  apply max_le_max
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    push_cast
    have he : (b : ℝ)^2 * (x*(1-x)/((n : ℝ)*b)) =
        (b : ℝ)*(x*(1-x)/n) := by field_simp
    rw [he]
    exact le_mul_of_one_le_left (by positivity) hbR
  · push_cast
    field_simp
    rfl

private lemma residual_coefficient_control (r : ℕ) (ρ : ℝ) (hρ : (r : ℝ) < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n b : ℕ, 0 < n → r ≤ n*b → 1 ≤ b →
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ P : ℂ[X], ∀ A : ℝ, 0 ≤ A →
      (∀ ν ≤ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x -
          (derivative^[ν] P).eval (x : ℂ)‖ ≤ A * delta n x ^ (ρ - (ν : ℝ))) →
      ∀ J ≤ n*b+r,
        ‖bernsteinCoefficient (n*b+r) J
          (holderOperator (n*b) r (fun x : ℝ => f x - P.eval (x : ℂ)))‖ ≤
            K * A * ((b : ℝ)*((r : ℝ)+1))^ρ *
              delta (n*b) ((J : ℝ)/(n*b+r))^ρ := by
  obtain ⟨K, hK, hcoef⟩ := local_coefficient_bound r
  refine ⟨K, by linarith, ?_⟩
  intro n b hn hr hb f hf P A hA he J hJ
  have hb0 : 0 < b := by omega
  have hnb : 0 < n*b := Nat.mul_pos hn hb0
  let p : ℝ := (J : ℝ)/(n*b+r)
  let d := delta (n*b) p
  let c : ℝ := (b : ℝ)*((r : ℝ)+1)
  have hd : 0 < d := delta_pos hnb p
  have hc : 1 ≤ c := by
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    dsimp [c]
    nlinarith [show (0 : ℝ) ≤ r by positivity]
  have hcc : 0 < c := by linarith
  have hbound := hcoef (n*b) hnb hr J hJ (A*c^ρ*d^ρ) (by positivity)
    (fun ν i => iteratedDerivWithin ν
      (fun x : ℝ => f x-P.eval (x : ℂ)) (Set.Icc 0 1) ((i : ℝ)/(n*b)))
  have hjet : ∀ ν ≤ r, ∀ i : ℕ, i ≤ n*b → i ≤ J → J ≤ i+r →
      ‖iteratedDerivWithin ν (fun x : ℝ => f x-P.eval (x : ℂ))
        (Set.Icc 0 1) ((i : ℝ)/(n*b))‖ ≤
          (A*c^ρ*d^ρ)/(derivativeRadius (n*b) 1 p)^ν := by
    intro ν hν i hi hiJ hJi
    obtain ⟨ht, hp, hdist⟩ := grid_geometry hnb hJ hi hiJ hJi
    simp only [Nat.cast_mul] at ht hp hdist
    have hloc : delta (n*b) ((i : ℝ)/(n*b)) ≤ ((r : ℝ)+1)*d := by
      simpa only [delta_eq_radius, p, d, Nat.cast_add, Nat.cast_mul] using
        radius_local_comparison hnb ht hp (by simpa only [Nat.cast_mul] using hdist)
    have hscale : delta n ((i : ℝ)/(n*b)) ≤ c*d := by
      calc
        _ ≤ (b : ℝ)*delta (n*b) ((i : ℝ)/(n*b)) := coarse_delta hn hb ht
        _ ≤ (b : ℝ)*(((r : ℝ)+1)*d) := mul_le_mul_of_nonneg_left hloc (by positivity)
        _ = c*d := by dsimp [c]; ring
    have hνR : (ν : ℝ) ≤ r := by exact_mod_cast hν
    have hexp : 0 ≤ ρ-(ν : ℝ) := by linarith
    have hcν : c^(ρ-(ν : ℝ)) ≤ c^ρ :=
      Real.rpow_le_rpow_of_exponent_le hc (by have := Nat.cast_nonneg (α := ℝ) ν; linarith)
    rw [residual_jet hν hf P ht]
    calc
      _ ≤ A*delta n ((i : ℝ)/(n*b))^(ρ-(ν : ℝ)) := he ν hν _ ht
      _ ≤ A*(c*d)^(ρ-(ν : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (delta_pos hn _).le hscale hexp) hA
      _ = A*(c^(ρ-(ν : ℝ))*d^(ρ-(ν : ℝ))) := by rw [Real.mul_rpow hcc.le hd.le]
      _ ≤ A*(c^ρ*d^(ρ-(ν : ℝ))) := by gcongr
      _ = (A*c^ρ*d^ρ)/(derivativeRadius (n*b) 1 p)^ν := by
        rw [Real.rpow_sub hd, Real.rpow_natCast]
        rw [← delta_eq_radius]
        change A*(c^ρ*(d^ρ/d^ν)) = A*c^ρ*d^ρ/d^ν
        ring
  simpa only [holderOperator, mul_assoc, c, d, p, Nat.cast_mul] using
    hbound (by simpa only [p, Nat.cast_mul] using hjet)

private lemma delta_upper {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : delta n x ≤ (n : ℝ)^(-(1/2 : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hv : 0 ≤ x*(1-x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hv1 : x*(1-x) ≤ 1 := by nlinarith [sq_nonneg x]
  have he : Real.sqrt (1/(n : ℝ)) = (n : ℝ)^(-(1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow hn0.le, Real.rpow_neg hn0.le]
  rw [← he]
  apply max_le
  · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hv1 hn0.le)
  · have hi0 : 0 ≤ 1/(n : ℝ) := by positivity
    have hi1 : 1/(n : ℝ) ≤ 1 := (div_le_one hn0).mpr hnR
    have hs := Real.sq_sqrt hi0
    nlinarith [Real.sqrt_nonneg (1/(n : ℝ))]

private lemma coefficient_const (D J : ℕ) (c : ℂ) :
    bernsteinCoefficient D J (C c) = c := by
  simp [bernsteinCoefficient, coeff_C, ite_div]

private lemma jet_coefficient_term (ν : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m r J : ℕ, 0 < m → r ≤ m → ν ≤ r → J ≤ m+r →
      ∀ f : ℕ → ℂ, ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖f i‖ ≤ A) →
      ‖bernsteinCoefficient (m+r) J ((C (((m : ℂ)^ν)⁻¹)*tau m ν) *
        ∑ i ∈ range (m+1), C (f i)*bernsteinPolynomial ℂ m i)‖ ≤
          K*A*delta m ((J : ℝ)/(m+r))^ν := by
  obtain ⟨K,hK,hbound⟩ := weighted_tau_bound ν
  refine ⟨K,hK,?_⟩
  intro m r J hm hr hν hJ f A hA hf
  let P := C (((m : ℂ)^ν)⁻¹)*tau m ν
  have hd : P.natDegree ≤ ν := (natDegree_C_mul_le _ _).trans (tau_degree m ν)
  change ‖bernsteinCoefficient (m+r) J (P * _)‖ ≤ _
  rw [← bernstein_reconstruction P ν hd, sum_mul, bernstein_coefficient_sum]
  calc
    _ ≤ ∑ h ∈ range (ν+1), ‖bernsteinCoefficient (m+r) J
        (C (bernsteinCoefficient ν h P)*bernsteinPolynomial ℂ ν h *
          ∑ i ∈ range (m+1), C (f i)*bernsteinPolynomial ℂ m i)‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ range (ν+1), ‖bernsteinCoefficient ν h P‖ *
        (A*samplingWeight (m+r) J ν h) := by
      apply sum_le_sum
      intro h hh
      rw [mul_assoc, bernstein_coefficient_C_mul, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact basis_times_local_bound hν (by have := mem_range.mp hh; omega) hJ f
        (fun i hi _ _ => hf i hi)
    _ = A * ∑ h ∈ range (ν+1), samplingWeight (m+r) J ν h *
        ‖bernsteinCoefficient ν h P‖ := by
      rw [mul_sum]
      apply sum_congr rfl
      intros
      ring
    _ ≤ A * (K*delta m ((J : ℝ)/(m+r))^ν) := by
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [P, delta_eq_radius, Nat.cast_add] using
        hbound m (m+r) J hm (by omega) (by omega) hJ
    _ = _ := by ring

private lemma initial_coefficient_control (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → r ≤ m → ∀ J ≤ m+r,
      ∀ f : ℕ → ℕ → ℂ, ∀ c : ℂ, ∀ M A s : ℝ, 0 ≤ M → 0 ≤ A → 0 < s →
      (∀ i ≤ m, ‖f 0 i-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ i ≤ m, ‖f ν i‖ ≤ A*s^(-(ν : ℝ))) →
      ‖bernsteinCoefficient (m+r) J (lorentzJet m r f)-c‖ ≤
        M + K*A*∑ ν ∈ Icc 1 r, (m : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ)) := by
  choose B hB hterm using jet_coefficient_term
  let K := 1+∑ ν ∈ Icc 1 r, B ν
  have hK : 0 < K := by
    have := sum_nonneg (s := Icc 1 r) (fun ν _ => (zero_le_one.trans (hB ν)))
    dsimp [K]
    linarith
  refine ⟨K,hK,?_⟩
  intro m hm hr J hJ f c M A s hM hA hs hf0 hf
  have hp : (J : ℝ)/(m+r) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < m+r)).mpr
      exact_mod_cast hJ
  let Z : ℂ[X] := ∑ i ∈ range (m+1), C (f 0 i-c)*bernsteinPolynomial ℂ m i
  have hZ : ‖bernsteinCoefficient (m+r) J Z‖ ≤ M := by
    let a : Fin (m+1) → ℂ := fun i => f 0 i-c
    have ha : ‖a‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr (fun i => hf0 i (by omega))
    have he : Z = bernsteinRealization m a := by
      unfold Z bernsteinRealization
      simp only [a]
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        C (f 0 i-c)*bernsteinPolynomial ℂ m i) (m+1)).symm
    rw [he]
    exact (original_coefficient_bound (Nat.le_add_right m r) hJ a).trans ha
  have hsplit : lorentzJet m r f-C c = Z + ∑ ν ∈ Icc 1 r,
      (C (((m : ℂ)^ν)⁻¹)*tau m ν) *
        ∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i := by
    unfold lorentzJet
    rw [sum_range_succ']
    have hzero : (C (((m : ℂ)^0)⁻¹)*tau m 0) *
        (∑ i ∈ range (m+1), C (f 0 i)*bernsteinPolynomial ℂ m i) - C c = Z := by
      simp only [tau, pow_zero, inv_one, C_1, one_mul]
      unfold Z
      simp only [map_sub, sub_mul, sum_sub_distrib, ← mul_sum, bernsteinPolynomial.sum,
        mul_one]
    have hsum : (∑ k ∈ range r, (C (((m : ℂ)^(k+1))⁻¹)*tau m (k+1)) *
        ∑ i ∈ range (m+1), C (f (k+1) i)*bernsteinPolynomial ℂ m i) =
        ∑ ν ∈ Icc 1 r, (C (((m : ℂ)^ν)⁻¹)*tau m ν) *
          ∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_comm]
    rw [hsum]
    linear_combination hzero
  rw [← coefficient_const (m+r) J c, ← coefficient_sub, hsplit]
  have hadd : ∀ P Q : ℂ[X], bernsteinCoefficient (m+r) J (P+Q) =
      bernsteinCoefficient (m+r) J P + bernsteinCoefficient (m+r) J Q := by
    intros
    simp [bernsteinCoefficient, coeff_add, add_mul, add_div, sum_add_distrib]
  rw [hadd]
  apply (norm_add_le _ _).trans
  apply add_le_add hZ
  rw [bernstein_coefficient_sum]
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro ν hν
  have hνr := (mem_Icc.mp hν).2
  have hBK : B ν ≤ K := by
    have := single_le_sum (s := Icc 1 r) (f := B)
      (fun i _ => zero_le_one.trans (hB i)) hν
    dsimp [K]
    linarith
  calc
    _ ≤ B ν*(A*s^(-(ν : ℝ)))*delta m ((J : ℝ)/(m+r))^ν :=
      hterm ν m r J hm hr hνr hJ (f ν) (A*s^(-(ν : ℝ))) (by positivity) (hf ν hν)
    _ ≤ K*(A*s^(-(ν : ℝ)))*((m : ℝ)^(-(1/2 : ℝ)))^ν := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hBK (by positivity))
        (pow_le_pow_left₀ (delta_pos hm _).le (delta_upper hm hp) ν)
        (pow_nonneg (delta_pos hm _).le _) (by positivity)
    _ = K*A*((m : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) := by
      rw [← Real.rpow_mul_natCast (by positivity), show -(1/2 : ℝ)*(ν : ℝ) = -(ν : ℝ)/2 by ring]
      ring

private lemma coefficient_add (D J : ℕ) (P Q : ℂ[X]) :
    bernsteinCoefficient D J (P+Q) = bernsteinCoefficient D J P +
      bernsteinCoefficient D J Q := by
  simp [bernsteinCoefficient, coeff_add, add_mul, add_div, sum_add_distrib]

private lemma elevation_bound {d D J : ℕ} (hdD : d ≤ D) (hJ : J ≤ D)
    (P : ℂ[X]) (hP : P.natDegree ≤ d) (c : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i ≤ d, ‖bernsteinCoefficient d i P-c‖ ≤ M) :
    ‖bernsteinCoefficient D J P-c‖ ≤ M := by
  let a : Fin (d+1) → ℂ := fun i => bernsteinCoefficient d i P-c
  have ha : ‖a‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr (fun i => hb i (by omega))
  have he : P-C c = bernsteinRealization d a := by
    unfold bernsteinRealization a
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      C (bernsteinCoefficient d i P-c)*bernsteinPolynomial ℂ d i) (d+1)]
    simp only [map_sub, sub_mul, sum_sub_distrib, ← mul_sum, bernsteinPolynomial.sum, mul_one]
    rw [bernstein_reconstruction P d hP]
  rw [← coefficient_const D J c, ← coefficient_sub, he]
  exact (original_coefficient_bound hdD hJ a).trans ha

private lemma grid_power {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b) (k : ℕ) (e : ℝ) :
    ((τ*b^k : ℕ) : ℝ)^e = (τ : ℝ)^e*((b : ℝ)^e)^k := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by positivity), mul_comm (k : ℝ) e,
    Real.rpow_mul_natCast (by positivity)]

private lemma center_coefficient_control (r : ℕ) (ρ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b → ∃ K : ℝ, 0 < K ∧
      ∀ τ : ℕ, 0 < τ → r ≤ τ → ∀ f : ℝ → ℂ,
      ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M A H s : ℝ, 0 ≤ M → 0 ≤ A → 0 ≤ H → 0 < s →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤ A*s^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤ H*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ, ∀ J ≤ τ*b^k+r,
        ‖bernsteinCoefficient (τ*b^k+r) J (center τ b r f k)-c‖ ≤
          M + K*A*(∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) +
            K*H*(τ : ℝ)^(-ρ/2) := by
  obtain ⟨B,hB,U,V,E,hU,hV,hE,hstable⟩ := common_grid_stability r ρ hρ hρ1
  obtain ⟨I,hI,hinit⟩ := initial_coefficient_control r
  obtain ⟨L,hL,hlocal⟩ := residual_coefficient_control r ρ hρ
  refine ⟨B,hB,?_⟩
  intro b hb
  have hb2 : 2 ≤ b := hB.trans hb
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb2
  have hρ0 : 0 < ρ := lt_of_le_of_lt (Nat.cast_nonneg r) hρ
  let q : ℝ := (b : ℝ)^(-ρ/2)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hbR (by linarith)
  let T : ℝ := L*E*((b : ℝ)*((r : ℝ)+1))^ρ
  have hT : 0 < T := by dsimp [T]; positivity
  let K := I+T/(1-q)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro τ hτ hr f hf c M A H s hM hA hH hs hfc hfd hfh
  have hst := hstable b hb τ hτ f hf H hH hfh
  have hdegree (k : ℕ) := (hst k).1
  have hgrid (k : ℕ) : 0 < τ*b^k := Nat.mul_pos hτ (pow_pos hb0 k)
  have hτk (k : ℕ) : τ ≤ τ*b^k := by
    exact Nat.le_mul_of_pos_right τ (pow_pos hb0 k)
  have hinit' : ∀ J ≤ τ+r, ‖bernsteinCoefficient (τ+r) J (center τ b r f 0)-c‖ ≤
      M+I*A*(∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) := by
    intro J hJ
    apply hinit τ hτ hr J hJ _ c M A s hM hA hs
    · intro i hi
      apply hfc
      exact ⟨by positivity, (div_le_one (by exact_mod_cast hτ : (0 : ℝ)<τ)).mpr
        (by exact_mod_cast hi)⟩
    · intro ν hν i hi
      apply hfd ν hν
      exact ⟨by positivity, (div_le_one (by exact_mod_cast hτ : (0 : ℝ)<τ)).mpr
        (by exact_mod_cast hi)⟩
  have hinc (k : ℕ) (J : ℕ) (hJ : J ≤ τ*b^(k+1)+r) :
      ‖bernsteinCoefficient (τ*b^(k+1)+r) J (holderOperator (τ*b^(k+1)) r
        (fun x : ℝ => f x-(center τ b r f k).eval (x : ℂ)))‖ ≤
          T*H*(τ : ℝ)^(-ρ/2)*q^(k+1) := by
    have hng : τ*b^k*b = τ*b^(k+1) := by rw [pow_succ]; ring
    have hj : J ≤ τ*b^k*b+r := by rwa [hng]
    have hnb : r ≤ τ*b^k*b := by rw [hng]; exact hr.trans (hτk _)
    have he := hlocal (τ*b^k) b (hgrid k) hnb (by omega) f hf (center τ b r f k)
      (E*H) (by positivity) (hst k).2.2.2 J hj
    rw [hng] at he
    have hp : (J : ℝ)/(τ*b^(k+1)+r) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one (by positivity : (0 : ℝ)<τ*b^(k+1)+r)).mpr
        exact_mod_cast hJ
    have hd := Real.rpow_le_rpow (delta_pos (hgrid (k+1)) _).le
      (delta_upper (hgrid (k+1)) (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hp)) hρ0.le
    calc
      _ ≤ L*(E*H)*((b : ℝ)*((r : ℝ)+1))^ρ *
          delta (τ*b^(k+1)) ((J : ℝ)/(τ*b^(k+1)+r))^ρ := by
        simpa only [Nat.cast_mul,Nat.cast_pow,pow_succ,mul_assoc] using he
      _ ≤ L*(E*H)*((b : ℝ)*((r : ℝ)+1))^ρ *
          (((τ*b^(k+1) : ℕ) : ℝ)^(-(1/2 : ℝ)))^ρ := by
        exact mul_le_mul_of_nonneg_left hd (by positivity)
      _ = T*H*(τ : ℝ)^(-ρ/2)*q^(k+1) := by
        rw [← Real.rpow_mul (by positivity), show -(1/2 : ℝ)*ρ = -ρ/2 by ring,
          grid_power hτ hb0]
        dsimp [T,q]
        ring
  let Z := M+I*A*(∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ)))
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hall (k : ℕ) : ∀ J ≤ τ*b^k+r,
      ‖bernsteinCoefficient (τ*b^k+r) J (center τ b r f k)-c‖ ≤
        Z+T*H*(τ : ℝ)^(-ρ/2)*(∑ i ∈ range (k+1), q^i) := by
    induction k with
    | zero =>
      intro J hJ
      have hi := hinit' J (by simpa using hJ)
      simpa only [pow_zero,mul_one] using hi.trans
        (show Z ≤ Z+T*H*(τ : ℝ)^(-ρ/2)*(∑ i ∈ range (0+1), q^i) by
          exact le_add_of_nonneg_right (by positivity))
    | succ k ih =>
      intro J hJ
      have hmono : τ*b^k+r ≤ τ*b^(k+1)+r := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left τ
          (Nat.pow_le_pow_right (by omega : 0 < b) (by omega : k ≤ k+1))) r
      have he := elevation_bound hmono hJ (center τ b r f k) (hdegree k) c
        (by positivity : 0 ≤ Z+T*H*(τ : ℝ)^(-ρ/2)*(∑ i ∈ range (k+1), q^i)) ih
      rw [center, coefficient_add]
      have hnorm := norm_add_le
        (bernsteinCoefficient (τ*b^(k+1)+r) J (center τ b r f k)-c)
        (bernsteinCoefficient (τ*b^(k+1)+r) J (holderOperator (τ*b^(k+1)) r
          (fun x : ℝ => f x-(center τ b r f k).eval (x : ℂ))))
      rw [show ∀ z w : ℂ, z+w-c = (z-c)+w by intros; ring]
      apply hnorm.trans
      have hsum : (∑ i ∈ range (k+1+1), q^i) = (∑ i ∈ range (k+1), q^i)+q^(k+1) := sum_range_succ _ _
      rw [hsum]
      nlinarith [hinc k J hJ]
  intro k J hJ
  have hsum : (∑ i ∈ range (k+1), q^i) ≤ 1/(1-q) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := k+1) hq0 hq1
  have hIK : I ≤ K := by dsimp [K]; exact le_add_of_nonneg_right (by positivity)
  have hTK : T/(1-q) ≤ K := by dsimp [K]; linarith
  calc
    _ ≤ Z+T*H*(τ : ℝ)^(-ρ/2)*(∑ i ∈ range (k+1), q^i) := hall k J hJ
    _ ≤ Z+T*H*(τ : ℝ)^(-ρ/2)*(1/(1-q)) := by gcongr
    _ = M+I*A*(∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) +
        (T/(1-q))*H*(τ : ℝ)^(-ρ/2) := by dsimp [Z]; ring
    _ ≤ _ := by gcongr

/-- The proportional reference scale. -/
def ringScale (xstar : ℝ) (b j : ℕ) : ℝ :=
  xstar*(b : ℝ)^(-(j : ℝ)/2)

private lemma ring_scale_cancel {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
    {xstar : ℝ} (hx : 0 < xstar) (j : ℕ) (e : ℝ) :
    ((N*b^j : ℕ) : ℝ)^(-e/2)*(ringScale xstar b j)^(-e) =
      (N : ℝ)^(-e/2)*xstar^(-e) := by
  rw [Nat.cast_mul,Nat.cast_pow,Real.mul_rpow (by positivity) (by positivity)]
  unfold ringScale
  rw [Real.mul_rpow hx.le (by positivity), ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  have he : (j : ℝ)*(-e/2)+(-(j : ℝ)/2)*(-e) = 0 := by ring
  calc
    _ = (N : ℝ)^(-e/2)*xstar^(-e)*
        ((b : ℝ)^((j : ℝ)*(-e/2))*(b : ℝ)^((-(j : ℝ)/2)*(-e))) := by ring
    _ = _ := by rw [← Real.rpow_add (by positivity),he,Real.rpow_zero,mul_one]

/-- A single initial degree controls every proportional ring and every level
of its actual center history. The input family may be signed or complex.
The initial degree is selected before the ring and the input function. -/
theorem uniform_ring_center_margin (r : ℕ) (ρ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar A H ε : ℝ, 0 < xstar → 0 ≤ A → 0 ≤ H → 0 < ε →
      ∃ N : ℕ, 3*r+1 ≤ N ∧ ∀ j : ℕ,
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤ A*(ringScale xstar b j)^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤
            H*(ringScale xstar b j)^(-ρ)*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ, ∀ J ≤ (N*b^j)*b^k+r,
        ‖bernsteinCoefficient ((N*b^j)*b^k+r) J (center (N*b^j) b r f k)-c‖ ≤ M+ε := by
  obtain ⟨B,hB,hcontrol⟩ := center_coefficient_control r ρ hρ hρ1
  refine ⟨B,hB,?_⟩
  intro b hb xstar A H ε hx hA hH hε
  obtain ⟨K,hK,hbound⟩ := hcontrol b hb
  have hb0 : 0 < b := by omega
  have hρ0 : 0 < ρ := lt_of_le_of_lt (Nat.cast_nonneg r) hρ
  let budget : ℕ → ℝ := fun N =>
    K*A*(∑ ν ∈ Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) +
      K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ)
  have hlim : Tendsto budget atTop (𝓝 0) := by
    have hsum : Tendsto (fun N : ℕ => ∑ ν ∈ Icc 1 r,
        (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) atTop (𝓝 0) := by
      have hterms : ∀ ν ∈ Icc 1 r, Tendsto
          (fun N : ℕ => (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) atTop (𝓝 0) := by
        intro ν hν
        have hν0 : (0 : ℝ) < ν := by exact_mod_cast (mem_Icc.mp hν).1
        have hn := (tendsto_rpow_neg_atTop (show 0 < (ν : ℝ)/2 by positivity)).comp
          tendsto_natCast_atTop_atTop
        simpa [Function.comp_def,neg_div] using hn.mul_const (xstar^(-(ν : ℝ)))
      simpa using tendsto_finset_sum (Icc 1 r) hterms
    have hlast : Tendsto (fun N : ℕ => (N : ℝ)^(-ρ/2)) atTop (𝓝 0) := by
      simpa [Function.comp_def,neg_div] using
        (tendsto_rpow_neg_atTop (show 0 < ρ/2 by positivity)).comp tendsto_natCast_atTop_atTop
    simpa only [budget,mul_zero,zero_mul,add_zero] using
      (hsum.const_mul (K*A)).add ((hlast.const_mul (K*H)).mul_const (xstar^(-ρ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let N := max (3*r+1) N₀
  have hN : 3*r+1 ≤ N := le_max_left _ _
  have hN0 : 0 < N := by omega
  have hbudget : budget N ≤ ε := (hN₀ N (le_max_right _ _)).le
  refine ⟨N,hN,?_⟩
  intro j f hf c M hM hfc hfd hfh k J hJ
  have hn : 0 < N*b^j := Nat.mul_pos hN0 (pow_pos hb0 j)
  have hNr : r ≤ N*b^j := (by omega : r ≤ N).trans
    (Nat.le_mul_of_pos_right N (pow_pos hb0 j))
  have hs : 0 < ringScale xstar b j := by unfold ringScale; positivity
  have hh := hbound (N*b^j) hn hNr f hf c M A (H*(ringScale xstar b j)^(-ρ))
    (ringScale xstar b j) hM hA (by positivity) hs hfc hfd hfh k J hJ
  have hsum : (∑ ν ∈ Icc 1 r, ((N*b^j : ℕ) : ℝ)^(-(ν : ℝ)/2)*
      (ringScale xstar b j)^(-(ν : ℝ))) =
      ∑ ν ∈ Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)) := by
    apply sum_congr rfl
    intro ν _
    exact ring_scale_cancel hN0 hb0 hx j (ν : ℝ)
  rw [hsum] at hh
  have hlast : K*(H*(ringScale xstar b j)^(-ρ))*((N*b^j : ℕ) : ℝ)^(-ρ/2) =
      K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ) := by
    calc
      _ = K*H*(((N*b^j : ℕ) : ℝ)^(-ρ/2)*(ringScale xstar b j)^(-ρ)) := by ring
      _ = _ := by rw [ring_scale_cancel hN0 hb0 hx]; ring
  rw [hlast] at hh
  have he : M+K*A*(∑ ν ∈ Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)))+
      K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ) = M+budget N := by dsimp [budget]; ring
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl hbudget)

end D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
