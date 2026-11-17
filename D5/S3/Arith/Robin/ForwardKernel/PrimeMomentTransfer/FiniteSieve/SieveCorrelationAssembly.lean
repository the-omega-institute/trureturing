/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sieve interval moments transfer to uniform full singular series correlations. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveCRTMoments
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveCollisionRemoval
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveCorrelationEnvelope

/-! Uniform full correlations from finite sieve interval estimates. -/

open scoped BigOperators Topology
open Set Filter
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private lemma sieve_distinct_eq (y : ℕ) (M H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (a b : Fin k → ℝ) (hab : admissible M a b) :
    distinctIndexMoment (sieveFunctional ⟨primorial y, primorial_pos y⟩)
      (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable ⟨primorial y, primorial_pos y⟩ d.val)
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = corr (finiteSingularSeries y) H a b := by
  classical
  rw [← distinct_interval_weight_moment (finiteSingularSeries y) M H hH a b hab]
  unfold distinctIndexMoment formalDistinct
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  have hinj := (Finset.mem_filter.mp hd).2
  have hv : Function.Injective (fun i => (d i).val) := Subtype.val_injective.comp hinj
  have he : (Finset.univ.image d).image Subtype.val =
      Finset.univ.image (fun i => (d i).val) := Finset.image_image
  have hc := centerFinite_image (finiteSingularSeries y) Subtype.val Subtype.val_injective
    (Finset.univ.image d)
  change centerFinite _ _ = center (finiteSingularSeries y) _ at hc
  rw [he] at hc
  rw [hc]
  change sieveExpectation ⟨primorial y, primorial_pos y⟩ _ = _
  rw [← centered_sieve_moment]
  congr 1
  funext x
  simp only [Finset.prod_apply]
  symm
  exact Finset.prod_image (f := fun d => sieveVariable ⟨primorial y, primorial_pos y⟩ d x) hv.injOn

private lemma tail_monomial_le (M H : ℝ) (hM : 1 ≤ M) (hH : 2 ≤ H)
    (u v w : ℕ) (hw : u+v+2 ≤ w) :
    H^u * Real.log H^v / (((M+5)*H)^w) ≤ 1/H^2 := by
  have hH0 : 0 ≤ H := by linarith
  have hHp : 0 < H := by linarith
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hL : Real.log H ≤ H :=
    (Real.log_le_sub_one_of_pos hHp).trans (by linarith)
  have hden : 0 < ((M+5)*H)^w := pow_pos (by positivity) _
  apply (div_le_div_iff₀ hden (sq_pos_of_pos hHp)).2
  simp only [one_mul]
  calc
    (H^u * Real.log H^v) * H^2 ≤ (H^u * H^v) * H^2 := by gcongr
    _ = H^(u+v+2) := by rw [pow_add, pow_add]
    _ ≤ H^w := pow_le_pow_right₀ (by linarith) hw
    _ ≤ ((M+5)*H)^w := by gcongr; nlinarith

private lemma correlation_tail_inverse_square (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ H : ℝ, 2 ≤ H →
      ∀ a b : Fin k → ℝ, admissible M a b →
      |corr concreteSS H a b - finiteDistinctCorrelation M H a b| ≤ C / H^2 := by
  obtain ⟨C,hC,h⟩ := correlation_tail_bound M hM
  refine ⟨C,hC,?_⟩
  intro k hk hk4 H hH a b hab
  calc
    _ ≤ C * H^k * Real.log H^4 / (((M+5)*H)^10) := h k hk hk4 H hH a b hab
    _ = C * (H^k * Real.log H^4 / (((M+5)*H)^10)) := by ring
    _ ≤ C * (1/H^2) := mul_le_mul_of_nonneg_left
      (tail_monomial_le M H hM hH k 4 10 (by omega)) hC
    _ = _ := by ring

private lemma finite_two_bound (hMS : MSSecond) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ H : ℝ in atTop,
      ∀ a b : Fin 2 → ℝ, admissible M a b →
        |finiteDistinctCorrelation M H a b| ≤ K * H * Real.log H := by
  obtain ⟨B,hB,hfull⟩ := second_correlation_bound hMS M hM
  obtain ⟨C,hC,htail⟩ := correlation_tail_inverse_square M hM
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with H hH hL a b hab
  have hH0 : 0 ≤ H := by linarith
  have hHL : 1 ≤ H*Real.log H := by nlinarith
  have ht := htail 2 (by norm_num) (by norm_num) H hH a b hab
  have he : C/H^2 ≤ C := div_le_self hC (by nlinarith)
  calc
    _ = |corr concreteSS H a b - (corr concreteSS H a b - finiteDistinctCorrelation M H a b)| := by ring_nf
    _ ≤ |corr concreteSS H a b| + |corr concreteSS H a b - finiteDistinctCorrelation M H a b| := abs_sub _ _
    _ ≤ B*H*Real.log H+C := add_le_add (hfull H hH a b hab) (ht.trans he)
    _ ≤ (B+C)*H*Real.log H := by nlinarith [mul_le_mul_of_nonneg_left hHL hC]

private lemma finite_higher_small (hMS : MSSecond) (hS : FiniteSieveIntervals)
    (M : ℝ) (hM : 1 ≤ M) :
    UniformIntervalSmall 3 (fun H a b => finiteDistinctCorrelation M H a b) M ∧
    UniformIntervalSmall 4 (fun H a b => finiteDistinctCorrelation M H a b - finitePairCorrelation M H a b) M := by
  obtain ⟨B,hB,hden⟩ := density_log_bound M hM
  obtain ⟨K,hK,htwo⟩ := finite_two_bound hMS M hM
  have hQ : ∀ᶠ H : ℝ in atTop, sieveDensity (primorialSieveModulus M H) ≤ max B 1 * Real.log H := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with H hH
    apply (hden H hH).trans
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith))
  have htwo' : ∀ᶠ H : ℝ in atTop, ∀ f g : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
        (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val) ![f,g]| ≤ K*H*Real.log H := by
    filter_upwards [htwo,eventually_ge_atTop (2 : ℝ)] with H ht hH f g hf hg
    obtain ⟨a,b,hab,he⟩ := interval_weight_family ![f,g] (by intro i; fin_cases i <;> assumption)
    rw [he]
    exact (congrArg abs (sieve_distinct_eq (sieveCutoff M H) M H
      (by linarith) a b hab)).le.trans (ht a b hab)
  obtain ⟨h3,h4⟩ := sieve_collision_removal hS M (max B 1) K hM
    (le_max_right _ _) hQ htwo'
  have heq {k : ℕ} (H : ℝ) (hH : 0 ≤ H) (a b : Fin k → ℝ) (hab : admissible M a b) :
      distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
        (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
        (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = finiteDistinctCorrelation M H a b :=
    sieve_distinct_eq (sieveCutoff M H) M H hH a b hab
  refine ⟨?_,?_⟩
  · intro ε hε
    filter_upwards [h3 ε hε,eventually_ge_atTop (2 : ℝ)] with H ht hH a b hab
    simpa only [heq H (by linarith) a b hab] using ht a b hab
  · intro ε hε
    filter_upwards [h4 ε hε,eventually_ge_atTop (2 : ℝ)] with H ht hH a b hab
    have hp (i j : Fin 4) : admissible M ![a i,a j] ![b i,b j] := by
      intro r; fin_cases r <;> exact hab _
    have hpair (i j : Fin 4) :
        distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
          (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
          ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i),
            intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a j) (b j)] =
          finiteDistinctCorrelation M H ![a i,a j] ![b i,b j] := by
      have hf : (![intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i),
          intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a j) (b j)] :
          Fin 2 → Finset.Iic ⌊M*H⌋₊ → ℝ) =
          (fun r => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (![a i,a j] r) (![b i,b j] r)) := by
        funext r
        fin_cases r <;> rfl
      rw [hf]
      exact heq H (by linarith) ![a i,a j] ![b i,b j] (hp i j)
    have hh := ht a b hab
    dsimp only at hh
    rw [heq H (by linarith) a b hab] at hh
    simpa only [perfectPairingSum,hpair,finitePairCorrelation,pairCorr,finiteDistinctCorrelation] using hh

private lemma inverse_square_small (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, C/H^2 ≤ ε * momentScale k H := by
  have ht : Tendsto (fun H : ℝ => C/H^2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  filter_upwards [ht.eventually_le_const hε,eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with H hsmall hH hL
  have hs : 1 ≤ momentScale k H := Real.one_le_rpow (by nlinarith : 1 ≤ H*Real.log H)
    (by positivity)
  exact hsmall.trans (le_mul_of_one_le_right hε.le hs)

private lemma full_higher_small (hMS : MSSecond) (hS : FiniteSieveIntervals)
    (M : ℝ) (hM : 1 ≤ M) :
    UniformIntervalSmall 3 (fun H a b => corr concreteSS H a b) M ∧
    UniformIntervalSmall 4 (fun H a b => corr concreteSS H a b - pairCorr concreteSS H a b) M := by
  obtain ⟨h3,h4⟩ := finite_higher_small hMS hS M hM
  obtain ⟨C,hC,htail⟩ := correlation_tail_inverse_square M hM
  obtain ⟨D,hD,hpair⟩ := pairing_tail_bound hMS M hM
  have hp (H : ℝ) (hH : 2 ≤ H) (a b : Fin 4 → ℝ) (hab : admissible M a b) :
      |pairCorr concreteSS H a b - finitePairCorrelation M H a b| ≤ (2*D)/H^2 := by
    calc
      _ ≤ D * (H^3*Real.log H^5/(((M+5)*H)^10)+
          H^4*Real.log H^8/(((M+5)*H)^20)) := hpair H hH a b hab
      _ ≤ D * (1/H^2+1/H^2) := mul_le_mul_of_nonneg_left
        (add_le_add (tail_monomial_le M H hM hH 3 5 10 (by norm_num))
          (tail_monomial_le M H hM hH 4 8 20 (by norm_num))) hD
      _ = _ := by ring
  refine ⟨?_,?_⟩
  · intro ε hε
    filter_upwards [h3 (ε/2) (half_pos hε), inverse_square_small C 3 (ε/2) (half_pos hε),
      eventually_ge_atTop (2 : ℝ)] with H h3H he hH a b hab
    calc
      _ = |finiteDistinctCorrelation M H a b + (corr concreteSS H a b - finiteDistinctCorrelation M H a b)| := by ring_nf
      _ ≤ |finiteDistinctCorrelation M H a b| + |corr concreteSS H a b - finiteDistinctCorrelation M H a b| := abs_add_le _ _
      _ ≤ (ε/2)*momentScale 3 H+(ε/2)*momentScale 3 H := add_le_add (h3H a b hab)
        ((htail 3 (by norm_num) (by norm_num) H hH a b hab).trans he)
      _ = ε*momentScale 3 H := by ring
  · intro ε hε
    filter_upwards [h4 (ε/2) (half_pos hε),
      inverse_square_small (C+2*D) 4 (ε/2) (half_pos hε),
      eventually_ge_atTop (2 : ℝ)] with H h4H he hH a b hab
    calc
      _ = |(finiteDistinctCorrelation M H a b - finitePairCorrelation M H a b) +
          (corr concreteSS H a b - finiteDistinctCorrelation M H a b) -
          (pairCorr concreteSS H a b - finitePairCorrelation M H a b)| := by congr 1; ring
      _ ≤ |finiteDistinctCorrelation M H a b - finitePairCorrelation M H a b| +
          |corr concreteSS H a b - finiteDistinctCorrelation M H a b| +
          |pairCorr concreteSS H a b - finitePairCorrelation M H a b| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (ε/2)*momentScale 4 H + (C/H^2 + (2*D)/H^2) := by
        have hh := add_le_add (add_le_add (h4H a b hab)
          (htail 4 (by norm_num) (by norm_num) H hH a b hab)) (hp H hH a b hab)
        linarith only [hh]
      _ = (ε/2)*momentScale 4 H + (C+2*D)/H^2 := by ring
      _ ≤ (ε/2)*momentScale 4 H + (ε/2)*momentScale 4 H := add_le_add le_rfl he
      _ = ε*momentScale 4 H := by ring

private lemma fourth_pairing_leading (hMS : MSSecond) (M : ℝ) (hM : 1 ≤ M) :
    UniformIntervalSmall 4 (fun H a b => pairCorr concreteSS H a b -
      H^2 * Real.log H^2 * W4 a b) M := by
  obtain ⟨C,hC,hcov⟩ := concrete_interval_covariance hMS M hM
  let D := 3*(2*M*C+C^2)
  have hlim : Tendsto (fun H : ℝ => D/Real.log H) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  intro ε hε
  filter_upwards [hlim.eventually_le_const hε,eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with H hsmall hH hL a b hab
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ Real.log H := by linarith
  let R (i j : Fin 4) := corr concreteSS H ![a i,a j] ![b i,b j]
  let T (i j : Fin 4) := -H*Real.log H*sigma (a i) (b i) (a j) (b j)
  have had (i j : Fin 4) : admissible M ![a i,a j] ![b i,b j] := by
    intro r; fin_cases r <;> exact hab _
  have he (i j : Fin 4) : |R i j - T i j| ≤ C*H := by
    simpa [R,T,sub_eq_add_neg] using hcov H (by linarith) _ _ (had i j)
  have ht (i j : Fin 4) : |T i j| ≤ M*H*Real.log H := by
    dsimp [T]
    have hs := sigma_bound (d := b j) (by linarith : 0 ≤ M)
      (hab i).1 (hab i).2.2 (hab j).1
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hH0,abs_of_nonneg hL0,abs_of_nonneg hs.1]
    nlinarith [mul_le_mul_of_nonneg_left hs.2 (mul_nonneg hH0 hL0)]
  have hp (i j k l : Fin 4) :
      |R i j*R k l - T i j*T k l| ≤ (2*M*C+C^2)*H^2*Real.log H :=
    geom_product_error _ _ _ _ C H (Real.log H) M hH0 hL hC (by linarith)
      (he i j) (he k l) (ht i j) (ht k l)
  have hb : |pairCorr concreteSS H a b - H^2*Real.log H^2*W4 a b| ≤ D*H^2*Real.log H := by
    have hid : pairCorr concreteSS H a b-H^2*Real.log H^2*W4 a b =
        (R 0 1*R 2 3-T 0 1*T 2 3)+(R 0 2*R 1 3-T 0 2*T 1 3)+
        (R 0 3*R 1 2-T 0 3*T 1 2) := by dsimp [pairCorr,W4,R,T]; ring
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (by dsimp [D]; linarith only [hp 0 1 2 3,hp 0 2 1 3,hp 0 3 1 2])
  calc
    _ ≤ D*H^2*Real.log H := hb
    _ = (D/Real.log H)*momentScale 4 H := by
      norm_num [momentScale, mul_pow]
      field_simp
    _ ≤ ε*momentScale 4 H := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (by positivity) _)

private lemma local_fourth_errors (M : ℝ) (hM : 1 ≤ M) :
    LocallyBoundedIntervalError (k := 4) (fun H a b => corr concreteSS H a b - pairCorr concreteSS H a b) M ∧
    LocallyBoundedIntervalError (k := 4) (fun H a b => pairCorr concreteSS H a b - H^2*Real.log H^2*W4 a b) M := by
  have h2 := correlation_locally_bounded concreteSS 2 M (by linarith)
  have h4 := correlation_locally_bounded concreteSS 4 M (by linarith)
  have hp (T : ℝ) (hT : 2 ≤ T) : ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℝ, H ∈ Icc 2 T →
      ∀ a b : Fin 4 → ℝ, admissible M a b →
        |pairCorr concreteSS H a b| ≤ B*momentScale 4 H := by
    obtain ⟨C,hC,hbound⟩ := h2 T hT
    refine ⟨3*C^2,by positivity,?_⟩
    intro H hH a b hab
    have had (i j : Fin 4) : admissible M ![a i,a j] ![b i,b j] := by
      intro r; fin_cases r <;> exact hab _
    have he (i j : Fin 4) : |corr concreteSS H ![a i,a j] ![b i,b j]| ≤ C*(H*Real.log H) := by
      simpa [momentScale] using hbound H hH _ _ (had i j)
    have hprod (i j k l : Fin 4) :
        |corr concreteSS H ![a i,a j] ![b i,b j]*corr concreteSS H ![a k,a l] ![b k,b l]| ≤
          C^2*(H*Real.log H)^2 := by
      rw [abs_mul]
      convert mul_le_mul (he i j) (he k l) (abs_nonneg _)
        (mul_nonneg hC (mul_nonneg (by linarith [hH.1]) (Real.log_nonneg (by linarith [hH.1])))) using 1 <;> ring
    simp only [abs_mul] at hprod
    unfold pairCorr
    calc
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3*C^2*momentScale 4 H := by
        norm_num [momentScale]
        linarith only [hprod 0 1 2 3,hprod 0 2 1 3,hprod 0 3 1 2]
  have hw (a b : Fin 4 → ℝ) (hab : admissible M a b) : |W4 a b| ≤ 3*M^2 := by
    have hs (i j : Fin 4) := sigma_bound (d := b j) (by linarith : 0 ≤ M)
      (hab i).1 (hab i).2.2 (hab j).1
    have hb (i j k l : Fin 4) : sigma (a i) (b i) (a j) (b j)*sigma (a k) (b k) (a l) (b l) ≤ M^2 := by
      simpa [pow_two] using mul_le_mul (hs i j).2 (hs k l).2 (hs k l).1 (by linarith : 0 ≤ M)
    rw [abs_of_nonneg (by unfold W4 sigma; positivity)]
    unfold W4
    linarith only [hb 0 1 2 3,hb 0 2 1 3,hb 0 3 1 2]
  constructor
  · intro T hT
    obtain ⟨C,hC,hbound⟩ := h4 T hT
    obtain ⟨B,hB,hpair⟩ := hp T hT
    refine ⟨C+B,add_nonneg hC hB,?_⟩
    intro H hH a b hab
    exact (abs_sub _ _).trans (by
      have hh := add_le_add (hbound H hH a b hab) (hpair H hH a b hab)
      nlinarith only [hh])
  · intro T hT
    obtain ⟨B,hB,hpair⟩ := hp T hT
    refine ⟨B+3*M^2,by positivity,?_⟩
    intro H hH a b hab
    have hs : 0 ≤ momentScale 4 H := Real.rpow_nonneg (by
      exact mul_nonneg (by linarith [hH.1]) (Real.log_nonneg (by linarith [hH.1]))) _
    have he : |H^2*Real.log H^2*W4 a b| ≤ (3*M^2)*momentScale 4 H := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hh := mul_le_mul_of_nonneg_left (hw a b hab)
        (mul_nonneg (sq_nonneg H) (sq_nonneg (Real.log H)))
      norm_num [momentScale,mul_pow] at hh ⊢
      nlinarith only [hh]
    exact (abs_sub _ _).trans (by
      have hh := add_le_add (hpair H hH a b hab) he
      nlinarith only [hh])

/-- Second-order singular-series control and uniform finite-sieve interval moments give the
full second, third and fourth interval correlation estimates with one decreasing modulus. -/
theorem interval_correlations_of_sieve_inputs
    (hMS : MSSecond) (hS : FiniteSieveIntervals) : IntervalCorrelations concreteSS := by
  intro M hM
  obtain ⟨C,hC,hcov⟩ := concrete_interval_covariance hMS M hM
  obtain ⟨h3,h4⟩ := full_higher_small hMS hS M hM
  obtain ⟨hl4,hlp⟩ := local_fourth_errors M hM
  obtain ⟨η3,hη3,ha3,ht3,hb3⟩ := antitone_error_envelope 3 M _ h3
    (correlation_locally_bounded concreteSS 3 M (by linarith))
  obtain ⟨η4,hη4,ha4,ht4,hb4⟩ := antitone_error_envelope 4 M _ h4 hl4
  obtain ⟨ηp,hηp,hap,htp,hbp⟩ := antitone_error_envelope 4 M _
    (fourth_pairing_leading hMS M hM) hlp
  let η := fun H => η3 H+η4 H+ηp H
  have hη (H : ℝ) : 0 ≤ η H := add_nonneg (add_nonneg (hη3 H) (hη4 H)) (hηp H)
  have h3le (H : ℝ) : η3 H ≤ η H := by dsimp [η]; linarith [hη4 H,hηp H]
  have h4le (H : ℝ) : η4 H ≤ η H := by dsimp [η]; linarith [hη3 H,hηp H]
  refine ⟨C,hC,hcov,η,hη,?_,?_,?_,?_,?_⟩
  · exact (ha3.add ha4).add hap
  · simpa only [add_zero] using (ht3.add ht4).add htp
  · intro H hH a b hab
    exact (hb3 H hH a b hab).trans (mul_le_mul_of_nonneg_right (h3le H)
      (Real.rpow_nonneg (by exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) _))
  · intro H hH a b hab
    have hh := (hb4 H hH a b hab).trans (mul_le_mul_of_nonneg_right (h4le H)
      (Real.rpow_nonneg (by exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) _))
    simpa only [momentScale,show ((4:ℕ):ℝ)/2=2 by norm_num,Real.rpow_two,mul_pow,mul_assoc] using hh
  · intro H hH a b hab
    have he := (abs_add_le (corr concreteSS H a b-pairCorr concreteSS H a b)
      (pairCorr concreteSS H a b-H^2*Real.log H^2*W4 a b)).trans
      (add_le_add (hb4 H hH a b hab) (hbp H hH a b hab))
    rw [sub_add_sub_cancel] at he
    have hh : η4 H+ηp H ≤ η H := by dsimp [η]; linarith [hη3 H]
    have hs : 0 ≤ momentScale 4 H := Real.rpow_nonneg (by
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) _
    have he' := he.trans (show η4 H*momentScale 4 H+ηp H*momentScale 4 H ≤ η H*momentScale 4 H by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right hh hs)
    simpa only [momentScale,show ((4:ℕ):ℝ)/2=2 by norm_num,Real.rpow_two,mul_pow,mul_assoc] using he'

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
