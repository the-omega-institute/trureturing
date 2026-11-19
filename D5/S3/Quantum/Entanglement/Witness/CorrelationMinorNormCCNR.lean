/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal dimensional actual CCNR specialization without filter normal form. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The normalized-identity observation and the equal-dimensional p=1 comparison
are credited to Li, Poon and Sze (2011), Lemma 2.1 and Theorem 2.4. This module
proves the stated operator specialization for actual densities satisfying CCNR;
separability and FNF are not premises. It leaves intermediate finite p, h<d,
and unequal general dimensions open. -/
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCCNR

private lemma product_le_average_power {k : ℕ} (hk : 0 < k)
    (y : Fin k → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∏ i, y i ≤ ((∑ i, y i)/(k:ℝ))^k := by
  have hm := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin k => (1:ℝ)) y
    (by intro i _; norm_num) (by simpa using (show (0:ℝ)<k by exact_mod_cast hk))
    (fun i _ => hy i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at hm
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hy i)) _)
    hm (Nat.cast_nonneg k)
  rw [← Real.rpow_mul (Finset.prod_nonneg (fun i _ => hy i)),
    inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hk)), Real.rpow_one,
    Real.rpow_natCast] at hp
  exact hp

private lemma head_tail_product_bound (d k : ℕ) (hd : 2 ≤ d) (hk : 0 < k)
    (hdk : d ≤ k+1) (x : ℝ) (hx : 1/(d:ℝ) ≤ x)
    (y : Fin k → ℝ) (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i ≤ 1-x) :
    x * ∏ i, y i ≤ (1/(d:ℝ))*(((d:ℝ)-1)/((d:ℝ)*k))^k := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hsum0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  have hx1 : x ≤ 1 := by linarith
  have hmono : AntitoneOn (fun z : ℝ => z*(1-z)^k) (Set.Icc (1/(d:ℝ)) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · fun_prop
    · fun_prop
    · intro z hz
      have hz' := interior_subset hz
      have hz0 : 0 ≤ 1-z := sub_nonneg.mpr hz'.2
      have hdz : (1:ℝ) ≤ (k+1:ℕ)*z := by
        have hdk' : (d:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hdk
        have hzlo : (1:ℝ) ≤ (d:ℝ)*z := by simpa [mul_comm] using (div_le_iff₀ hd0).mp hz'.1
        have hzn : 0 ≤ z := (le_of_lt (div_pos (by norm_num : (0:ℝ)<1) hd0)).trans hz'.1
        exact hzlo.trans (mul_le_mul_of_nonneg_right hdk' hzn)
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
      have hder : HasDerivAt (fun z : ℝ => z*(1-z)^(l+1))
          ((1-z)^l*(1-((l:ℝ)+2)*z)) z := by
        convert (hasDerivAt_id z).mul
          (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).pow (l+1)) using 1
        · funext w
          simp
        · simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, Nat.add_sub_cancel,
            Nat.cast_add, Nat.cast_one, pow_succ]
          ring
      rw [hder.deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hz0 l)
      push_cast at hdz
      linarith
  have hprod := product_le_average_power hk y hy
  have hs0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  have hp : x * ∏ i, y i ≤ x * ((1-x)/(k:ℝ))^k := by
    apply mul_le_mul_of_nonneg_left _ hx0
    exact hprod.trans (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right hs hk0.le) k)
  have hlo : 1/(d:ℝ) ≤ 1 := by rw [div_le_one hd0]; exact_mod_cast (by omega : 1 ≤ d)
  have hg := hmono ⟨le_rfl,hlo⟩ ⟨hx,hx1⟩ hx
  calc
    _ ≤ x * ((1-x)/(k:ℝ))^k := hp
    _ = (x*(1-x)^k)/(k:ℝ)^k := by rw [div_pow]; ring
    _ ≤ ((1/(d:ℝ))*(1-1/(d:ℝ))^k)/(k:ℝ)^k :=
      div_le_div_of_nonneg_right hg (by positivity)
    _ = _ := by
      rw [show ((d:ℝ)-1)/((d:ℝ)*k) = (1-1/(d:ℝ))/(k:ℝ) by field_simp]
      rw [div_pow]
      ring

private lemma correlation_pairing {da db : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin (da^2) → Matrix (Fin da) (Fin da) ℂ) (ha : IsHermBasis a)
    (b : Fin (db^2) → Matrix (Fin db) (Fin db) ℂ) (hb : IsHermBasis b)
    (A : Matrix (Fin da) (Fin da) ℂ) (hA : A.IsHermitian)
    (B : Matrix (Fin db) (Fin db) ℂ) (hB : B.IsHermitian) :
    ⟪coordinates a A,(corr ρ a b).toEuclideanLin (coordinates b B)⟫_ℝ =
      (ρ*(A ⊗ₖ B)).trace.re := by
  conv_rhs => rw [coordinate_reconstruction a ha A hA, coordinate_reconstruction b hb B hB]
  have hsum : (∑ i, ((coordinates a A i : ℝ) : ℂ) • a i) ⊗ₖ
      (∑ j, ((coordinates b B j : ℝ) : ℂ) • b j) =
      ∑ i, ∑ j, (((coordinates a A i * coordinates b B j : ℝ) : ℂ)) • (a i ⊗ₖ b j) := by
    ext r s
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Finset.sum_mul, Finset.mul_sum, smul_eq_mul, Complex.ofReal_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp only [Matrix.smul_kronecker,
    Matrix.kronecker_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_smul, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, corr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual normalized identity supplies s1≥1/d in every complete local
normalized Hermitian basis. This uses only the actual trace-one density premise,
without separability or FNF. Li--Poon--Sze (2011), Lemma 2.1. -/
theorem normalized_identity_singular_lower (d : ℕ) (hd : 0 < d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : IsDensity ρ)
    (a b : Fin (d^2) → Matrix (Fin d) (Fin d) ℂ) (ha : IsHermBasis a) (hb : IsHermBasis b) :
    1/(d:ℝ) ≤ (corr ρ a b).toEuclideanLin.singularValues 0 := by
  let J : Matrix (Fin d) (Fin d) ℂ := ((1/Real.sqrt (d:ℝ) : ℝ) : ℂ) • 1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hs : Real.sqrt (d:ℝ)^2 = d := Real.sq_sqrt hd0.le
  have hJ : J.IsHermitian := by
    apply Matrix.IsHermitian.smul
    · exact Matrix.isHermitian_one
    · simp [isSelfAdjoint_iff]
  have hn (c : Fin (d^2) → Matrix (Fin d) (Fin d) ℂ) (hc : IsHermBasis c) :
      ‖coordinates c J‖ = 1 := by
    have hh := coordinates_purity c hc J hJ
    have hp : (J*J).trace.re = 1 := by
      simp [J, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_one]
      field_simp
      nlinarith
    rw [hp] at hh
    nlinarith [norm_nonneg (coordinates c J)]
  have hv := correlation_pairing ρ a ha b hb J hJ J hJ
  have hJJ : J ⊗ₖ J = ((1/(d:ℝ) : ℝ) : ℂ) • 1 := by
    simp only [J, Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
    congr 1
    push_cast
    field_simp
    exact_mod_cast hs.symm
  rw [hJJ] at hv
  have hv' : ⟪coordinates a J,(corr ρ a b).toEuclideanLin (coordinates b J)⟫_ℝ = 1/(d:ℝ) := by
    simpa [Matrix.mul_smul, Matrix.trace_smul, hρ.2] using hv
  have hh := real_inner_le_norm (coordinates a J) ((corr ρ a b).toEuclideanLin (coordinates b J))
  rw [hn a ha, one_mul, hv'] at hh
  have hu := Matrix.l2_opNorm_mulVec (corr ρ a b) (coordinates b J)
  change ‖(corr ρ a b).toEuclideanLin (coordinates b J)‖ ≤ ‖corr ρ a b‖ * ‖coordinates b J‖ at hu
  rw [hn b hb, mul_one, opNorm_eq_native_first] at hu
  exact hh.trans hu

private lemma equal_bound_formula (d h : ℕ) (hd : 2 ≤ d) (hh : 2 ≤ h) :
    bound d d h = (1/(d:ℝ))*(((d:ℝ)-1)/((d:ℝ)*((h-1:ℕ):ℝ)))^(h-1) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hh0 : (0:ℝ)<((h-1:ℕ):ℝ) := by exact_mod_cast (by omega : 0<h-1)
  have hcast : (h:ℝ)-1 = ((h-1:ℕ):ℝ) := by rw [Nat.cast_sub (by omega : 1≤h)]; norm_num
  have hq : 0 ≤ ((d:ℝ)-1)/((d:ℝ)*((h-1:ℕ):ℝ)) :=
    div_nonneg (by
      have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith) (by positivity)
  unfold bound
  simp only [max_self,min_self,hcast]
  rw [Real.sqrt_mul_self hd0.le, ← pow_two,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul hq]
  have he : (2:ℝ)*(((h-1:ℕ):ℝ)/2) = ((h-1:ℕ):ℝ) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_natCast]

/-- Equal-dimensional CCNR implies the proposed operator bound on the entire
original range d≤h≤d². The state may be entangled: neither separability nor
filter normal form is assumed. -/
theorem equal_dimensional_ccnr (d h : ℕ) (hd : 2 ≤ d) (hdh : d ≤ h) (hhn : h ≤ d^2)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : IsDensity ρ)
    (a b : Fin (d^2) → Matrix (Fin d) (Fin d) ℂ) (ha : IsHermBasis a) (hb : IsHermBasis b)
    (hccnr : ∑ i : Fin (d^2), (corr ρ a b).toEuclideanLin.singularValues i ≤ 1) :
    cmnInf h (corr ρ a b) ≤ bound d d h := by
  let C := corr ρ a b
  have hh2 : 2 ≤ h := hd.trans hdh
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  subst h
  have hk0 : 0<k := by omega
  have hx := normalized_identity_singular_lower d (by omega) ρ hρ a b ha hb
  let x := C.toEuclideanLin.singularValues 0
  let y : Fin k → ℝ := fun i => C.toEuclideanLin.singularValues (i.val+1)
  have hs : ∑ i, y i ≤ 1-x := by
    have hp : (∑ i ∈ Finset.range (k+1), C.toEuclideanLin.singularValues i) ≤
        ∑ i : Fin (d^2), C.toEuclideanLin.singularValues i := by
      rw [← Finset.sum_range]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hhn)
      intro i _ _
      exact C.toEuclideanLin.singularValues_nonneg i
    have hpre : (∑ i ∈ Finset.range (k+1), C.toEuclideanLin.singularValues i) = x+∑ i, y i := by
      rw [Finset.sum_range_succ']
      simp [x,y,Finset.sum_range,add_comm]
    rw [hpre] at hp
    change (∑ i : Fin (d^2), C.toEuclideanLin.singularValues i) ≤ 1 at hccnr
    linarith
  have hp := head_tail_product_bound d k hd hk0 hdh x hx y
    (fun i => C.toEuclideanLin.singularValues_nonneg _) hs
  rw [cmnInf_eq_native_product C (k+1) hhn, Fin.prod_univ_succ,
    equal_bound_formula d (k+1) hd (by omega)]
  simpa [x,y] using hp

/-- At full order the CCNR specialization holds for every actual finite Schatten
p≥1 as well as infinity, because the increasing compound has a sole row. -/
theorem equal_dimensional_ccnr_full (d : ℕ) (hd : 2 ≤ d)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hρ : IsDensity ρ)
    (a b : Fin (d^2) → Matrix (Fin d) (Fin d) ℂ) (ha : IsHermBasis a) (hb : IsHermBasis b)
    (hccnr : ∑ i : Fin (d^2), (corr ρ a b).toEuclideanLin.singularValues i ≤ 1) :
    cmnInf (d^2) (corr ρ a b) ≤ bound d d (d^2) ∧
    ∀ p : ℝ, 1 ≤ p → cmnP p (d^2) (corr ρ a b) ≤ bound d d (d^2) := by
  have hdh : d ≤ d^2 := by nlinarith
  have hi := equal_dimensional_ccnr d (d^2) hd hdh le_rfl ρ hρ a b ha hb hccnr
  refine ⟨hi,fun p hp => ?_⟩
  rw [(full_order_norms (corr ρ a b)).2 p hp]
  rwa [(full_order_norms (corr ρ a b)).1] at hi

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCCNR
