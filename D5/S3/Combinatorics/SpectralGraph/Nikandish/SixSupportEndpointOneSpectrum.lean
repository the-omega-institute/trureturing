/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointOneSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact real endpoint-one residual spectrum and sharp cutoff. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportSpectralGap
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointOneBound
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointOneArithmetic
import D5.S3.Weil.ZetaLinear.PoleCapacityRankOne
import D5.S3.SpectralTopology.PointGapExactInertia

/-! Source: the complete endpoint-one-spectrum theorem and sharpness proof,
revision b93becea662a746badeadba42fdc3d3eb3db9382, blob
b61e5619a508f11c7df335dd468ce61e2aa60000. The exact real cutoff and
repeated parameters are retained. Counts always concern the actual quotient
characteristic multiset, with multiplicities. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneSpectrum
open Matrix Polynomial Finset
open D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
open D5.S3.Combinatorics.SpectralGraph.SixSupportSpectralGap
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

private theorem negative_dimension_bound {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (W : Submodule ℝ (n → ℝ))
    (hW : ∀ x ∈ W, 0 ≤ RHLinalg.hermForm A x) :
    negativeCount A + Module.finrank ℝ W ≤ Fintype.card n := by
  let V := LinearMap.range (RHLinalg.hermNegPart hA).mulVecLin
  have hV := D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart hA
  have hd : Disjoint V W := by
    rw [Submodule.disjoint_def]
    intro x hxV hxW
    by_contra hn
    have hp := hV x hxV hn
    have hnn := hW x hxW
    have he : RHLinalg.hermForm (-A) x = -RHLinalg.hermForm A x := by
      unfold RHLinalg.hermForm
      rw [neg_mulVec,dotProduct_neg,map_neg]
    rw [he] at hp
    linarith
  have hr : Module.finrank ℝ V = negativeCount A := by
    rw [negativeCount_eq hA]
    exact D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex hA
  have h := Submodule.finrank_add_finrank_le_of_disjoint hd
  simpa only [hr,Module.finrank_pi,Module.finrank_self,mul_one] using h

private def pairEmbedding : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun z := ![0,0,0,z 0,z 1,z 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' t x := by ext i; fin_cases i <;> simp

private theorem pairEmbedding_injective : Function.Injective pairEmbedding := by
  intro x y hxy
  ext i
  fin_cases i
  · exact congrFun hxy 3
  · exact congrFun hxy 4
  · exact congrFun hxy 5

private theorem pair_form (a b c x : ℝ) (z : Fin 3 → ℝ) :
    RHLinalg.hermForm (symmetric a b c-Matrix.scalar (Fin 6) x) (pairEmbedding z) =
      (a-x)*(z 0)^2+(b-x)*(z 1)^2+(c-x)*(z 2)^2 := by
  simp [RHLinalg.hermForm,pairEmbedding,symmetric,Matrix.scalar,Matrix.sub_mulVec,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ,Matrix.diagonal_apply]
  ring

private theorem shifted_hermitian (a b c x : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (symmetric a b c-Matrix.scalar (Fin 6) x).IsHermitian := by
  apply (quotient_geometry a b c ha (ha.trans_le hab) (ha.trans_le (hab.trans hbc))).2.1.1.sub
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)

/-- The full pair-support principal space bounds negative inertia even at
singular pivots and repeated parameters. -/
theorem lower_exponent_inertia (a b c : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    negativeCount (symmetric a b c-Matrix.scalar (Fin 6) a) ≤ 3 := by
  have h := negative_dimension_bound (shifted_hermitian a b c a ha hab hbc)
    (LinearMap.range pairEmbedding) ?_
  · have hr : Module.finrank ℝ (LinearMap.range pairEmbedding) = 3 := by
      simpa using LinearMap.finrank_range_of_inj pairEmbedding_injective
    rw [hr] at h
    change negativeCount _ + 3 ≤ 6 at h
    omega
  · rintro _ ⟨z,rfl⟩
    rw [pair_form]
    exact add_nonneg (add_nonneg (by simp) (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)))
      (mul_nonneg (sub_nonneg.mpr (hab.trans hbc)) (sq_nonneg _))

/-- At the upper exponent the same actual subspace is nonpositive. -/
theorem upper_exponent_inertia (a b c : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    negativeCount (-(symmetric a b c-Matrix.scalar (Fin 6) c)) ≤ 3 := by
  have h := negative_dimension_bound (shifted_hermitian a b c c ha hab hbc).neg
    (LinearMap.range pairEmbedding) ?_
  · have hr : Module.finrank ℝ (LinearMap.range pairEmbedding) = 3 := by
      simpa using LinearMap.finrank_range_of_inj pairEmbedding_injective
    rw [hr] at h
    change negativeCount _ + 3 ≤ 6 at h
    omega
  · rintro _ ⟨z,rfl⟩
    have hn : RHLinalg.hermForm (-(symmetric a b c-Matrix.scalar (Fin 6) c))
        (pairEmbedding z) =
        -RHLinalg.hermForm (symmetric a b c-Matrix.scalar (Fin 6) c) (pairEmbedding z) := by
      unfold RHLinalg.hermForm
      rw [neg_mulVec,dotProduct_neg,map_neg]
    rw [hn,pair_form]
    have h0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hab.trans hbc)) (sq_nonneg (z 0))
    have h1 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbc) (sq_nonneg (z 1))
    simp only [sub_self,zero_mul,add_zero]
    linarith

private theorem product_sign (s : Multiset ℝ) :
    s.prod = (-1 : ℝ)^(s.countP (fun t => t < 0)) * (s.map abs).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons t s ih =>
    by_cases ht : t < 0
    · simp only [Multiset.prod_cons,Multiset.countP_cons,ht,ite_true,
        Multiset.map_cons,pow_add,pow_one,abs_of_neg ht]
      rw [ih]
      ring
    · simp only [Multiset.prod_cons,Multiset.countP_cons,ht,ite_false,
        Multiset.map_cons,abs_of_nonneg (not_lt.mp ht),Nat.add_zero]
      rw [ih]
      ring

private theorem negative_parity {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hd : 0 < A.det) :
    Even (negativeCount A) := by
  have hs := product_sign A.charpoly.roots
  rw [← Matrix.det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly] at hs
  have hp : 0 ≤ (A.charpoly.roots.map abs).prod :=
    Multiset.prod_nonneg fun t ht => by
      obtain ⟨u,_,rfl⟩ := Multiset.mem_map.mp ht
      exact abs_nonneg u
  rcases Nat.even_or_odd (negativeCount A) with he | ho
  · exact he
  · change Odd (A.charpoly.roots.countP (fun t => t < 0)) at ho
    rw [ho.neg_one_pow] at hs
    linarith

private theorem quotient_factor (a b c : ℝ) (he : h a b c 1 = 0) :
    (quotient a b c).charpoly = X*((X-1)*SixSupportEndpointOneArithmetic.quartic a b c) := by
  have hq : (quotient a b c).charpoly = X*quintic a b c := by
    change (SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
    rw [SixSupportLaplacianPolynomial.charpoly_zero_factor,quintic_eq_reduced]
  rw [hq,SixSupportEndpointOneArithmetic.factorization]
  simp [he]

/-- Exact residual quartic decomposition of the entire actual spectrum. -/
theorem residual_roots (a b c : ℝ) (he : h a b c 1 = 0) :
    (quotient a b c).charpoly.roots =
      {0} + {1} + (SixSupportEndpointOneArithmetic.quartic a b c).roots := by
  have hf := quotient_factor a b c he
  have hp : (X : ℝ[X])*((X-1)*SixSupportEndpointOneArithmetic.quartic a b c) ≠ 0 := by
    rw [← hf]
    exact (quotient a b c).charpoly_monic.ne_zero
  rw [hf,Polynomial.roots_mul hp,Polynomial.roots_mul (mul_ne_zero_iff.mp hp).2]
  have hr1 : (X-1 : ℝ[X]).roots = {1} := by
    simpa only [Polynomial.C_1] using Polynomial.roots_X_sub_C (1 : ℝ)
  simp [hr1,Multiset.cons_swap]

private theorem shifted_det (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    (symmetric a b c-Matrix.scalar (Fin 6) x).det = x*h a b c x := by
  have hn : symmetric a b c-Matrix.scalar (Fin 6) x =
      -(Matrix.scalar (Fin 6) x-symmetric a b c) := by abel
  rw [hn,Matrix.det_neg]
  norm_num only [Fintype.card_fin,even_two,Even.neg_pow,one_pow,one_mul]
  rw [← Matrix.eval_charpoly,symmetric_charpoly a b c ha hab hbc]
  simp only [Polynomial.eval_mul,Polynomial.eval_X]
  rfl

/-- Above the exact real cutoff, precisely zero and one lie below a.
No simplicity or root-order premise is assumed. -/
theorem endpoint_count (a b c : ℝ) (ha : 2 + Real.sqrt 3 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (he : h a b c 1 = 0) :
    below a b c a = 2 ∧ multiplicity a b c a = 0 := by
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have ha2 : 2 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hc0 : 0 < c := hb0.trans_le hbc
  have hsum := (SixSupportEndpointOneBound.result a b c ha2 hab hbc he).1
  have hpos : 0 < a^2-4*a+1 := by
    nlinarith [mul_pos (show 0 < a-2-Real.sqrt 3 by linarith)
      (show 0 < a-2+Real.sqrt 3 by linarith)]
  have hev := (SixSupportEndpointOneArithmetic.exponent_value a b c).1
  have hh : 0 < h a b c a := by
    rw [hev]
    have hf : a^2+3*a-(a+b+c) < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg (by exact neg_neg_of_pos (by positivity)) hf
  have hd : 0 < (symmetric a b c-Matrix.scalar (Fin 6) a).det := by
    rw [shifted_det a b c a ha0 hab hbc]
    exact mul_pos ha0 hh
  have hn := lower_exponent_inertia a b c ha0 hab hbc
  have hp := negative_parity (shifted_hermitian a b c a ha0 hab hbc) hd
  rw [(shifted_roots a b c a ha0 hab hbc).1] at hn hp
  have hr := residual_roots a b c he
  have hlow : 2 ≤ below a b c a := by
    dsimp [below]
    rw [hr]
    simp [ha0,show 1 < a by linarith]
  have heq : below a b c a = 2 := by
    obtain ⟨k,hk⟩ := hp
    omega
  refine ⟨heq,?_⟩
  have heval : (quotient a b c).charpoly.eval a ≠ 0 := by
    have hq : (quotient a b c).charpoly.eval a = a*h a b c a := by
      rw [Matrix.eval_charpoly,determinant]
    rw [hq]
    exact mul_ne_zero ha0.ne' hh.ne'
  apply Multiset.countP_eq_zero.mpr
  intro t ht
  intro ht0
  subst t
  exact heval ((Polynomial.mem_roots (quotient a b c).charpoly_monic.ne_zero).mp ht)

/-- Every root of the literal residual quartic is strictly greater than a
on the whole original real endpoint domain. -/
theorem residual_above_minimum (a b c : ℝ) (ha : 2 + Real.sqrt 3 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (he : h a b c 1 = 0) :
    ∀ t ∈ (SixSupportEndpointOneArithmetic.quartic a b c).roots, a < t := by
  classical
  have hc := endpoint_count a b c ha hab hbc he
  have hr := residual_roots a b c he
  have ha0 : 0 < a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have ha1 : 1 < a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have hf : (SixSupportEndpointOneArithmetic.quartic a b c).roots.countP (fun t => t < a) = 0 := by
    have hn := hc.1
    dsimp [below] at hn
    rw [hr] at hn
    simp [ha0,ha1] at hn
    omega
  intro t ht
  have hge := le_of_not_gt (Multiset.countP_eq_zero.mp hf t ht)
  have hne : t ≠ a := by
    intro hta
    subst t
    have hm : a ∈ (quotient a b c).charpoly.roots := by rw [hr]; simp [ht]
    exact (Multiset.countP_eq_zero.mp hc.2 a hm) rfl
  exact lt_of_le_of_ne hge hne.symm

/-- One is simple and is the smallest positive root of the actual full
quotient, with the complete real endpoint domain retained. -/
theorem simple_smallest (a b c : ℝ) (ha : 2 + Real.sqrt 3 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (he : h a b c 1 = 0) :
    multiplicity a b c 1 = 1 ∧
      ∀ t ∈ (quotient a b c).charpoly.roots, 0 < t → 1 ≤ t := by
  classical
  have hr := residual_roots a b c he
  have ha1 : 1 < a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have hF : (SixSupportEndpointOneArithmetic.quartic a b c).roots.countP (fun t => t = 1) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro t ht hte
    have hgt := residual_above_minimum a b c ha hab hbc he t ht
    linarith
  constructor
  · dsimp [SixSupportInertia.multiplicity]
    rw [hr,Multiset.countP_add,Multiset.countP_add,hF]
    change Multiset.countP (fun t : ℝ => t = 1) (0 ::ₘ (0 : Multiset ℝ)) +
      Multiset.countP (fun t : ℝ => t = 1) (1 ::ₘ (0 : Multiset ℝ)) + 0 = 1
    simp only [Multiset.countP_cons,Multiset.countP_zero]
    norm_num
  · intro t ht ht0
    rw [hr] at ht
    simp only [Multiset.mem_add,Multiset.mem_singleton] at ht
    rcases ht with (rfl | rfl) | ht
    · linarith
    · exact le_rfl
    · exact ha1.le.trans (residual_above_minimum a b c ha hab hbc he t ht).le

/-- All four residual roots are real, with their full algebraic multiplicity. -/
theorem residual_card (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (he : h a b c 1 = 0) :
    (SixSupportEndpointOneArithmetic.quartic a b c).roots.card = 4 := by
  have hs := symmetric_charpoly a b c ha hab hbc
  have hq : (quotient a b c).charpoly = X*quintic a b c := by
    change (SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
    rw [SixSupportLaplacianPolynomial.charpoly_zero_factor,quintic_eq_reduced]
  rw [← hq] at hs
  have hS := (quotient_geometry a b c ha (ha.trans_le hab) (ha.trans_le (hab.trans hbc))).2.1.1
  have hn : (quotient a b c).charpoly.roots.card = 6 := by
    rw [← hs,hS.roots_charpoly_eq_eigenvalues]
    simp
  rw [residual_roots a b c he] at hn
  simp only [Multiset.card_add,Multiset.card_singleton] at hn
  omega

private theorem above_count_lower (a b c : ℝ) (ha : 2 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    3 ≤ below a b c c ∧ multiplicity a b c c = 0 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hc0 : 0 < c := hb0.trans_le hbc
  have hq : c^2+3*c-(a+b+c) > 0 := by
    nlinarith [sq_pos_of_pos hc0]
  have hh : h a b c c < 0 := by
    rw [(SixSupportEndpointOneArithmetic.exponent_value a b c).2.2]
    exact mul_neg_of_neg_of_pos (by exact neg_neg_of_pos (by positivity)) hq
  let A := symmetric a b c-Matrix.scalar (Fin 6) c
  have hA : A.IsHermitian := shifted_hermitian a b c c ha0 hab hbc
  have hd : A.det ≠ 0 := by
    change (symmetric a b c-Matrix.scalar (Fin 6) c).det ≠ 0
    rw [shifted_det a b c c ha0 hab hbc]
    exact mul_ne_zero hc0.ne' hh.ne
  have hfull : A.rank = 6 := by
    exact Matrix.rank_of_isUnit A (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd))
  have hn := upper_exponent_inertia a b c ha0 hab hbc
  change negativeCount (-A) ≤ 3 at hn
  rw [negativeCount_eq hA.neg] at hn
  have hexc := D5.S3.SpectralTopology.FiniteSpectralLocalizer.posIndex_neg_eq_negIndex hA.neg
  simp only [neg_neg] at hexc
  rw [← hexc] at hn
  have hpart := D5.S3.SpectralTopology.PointGapExactInertia.posIndex_add_negIndex_eq_rank hA
  rw [hfull,← negativeCount_eq hA,(shifted_roots a b c c ha0 hab hbc).1] at hpart
  have hz := zeroCount_eq hA
  rw [hfull] at hz
  norm_num only [Fintype.card_fin,Nat.sub_self] at hz
  rw [(shifted_roots a b c c ha0 hab hbc).2] at hz
  exact ⟨by omega,hz⟩

/-- The complete endpoint-one residual separation. There are exactly four
real residual roots. Precisely one lies below min(c,a+b); the other three,
with multiplicities, lie above s. The real cutoff is not rounded to integers. -/
theorem result (a b c : ℝ) (ha : 2 + Real.sqrt 3 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (he : h a b c 1 = 0) :
    ∃ μ : ℝ, ∃ r : Multiset ℝ,
      (SixSupportEndpointOneArithmetic.quartic a b c).roots = {μ}+r ∧
      r.card = 3 ∧ a < μ ∧ μ < min c (a+b) ∧
      (∀ t ∈ r, a+b+c < t) := by
  classical
  have ha0 : 0 < a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have ha2 : 2 ≤ a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have ha1 : 1 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hr := residual_roots a b c he
  have hg := SixSupportSpectralGap.result a b c ha2 hab hbc
  have hu := above_count_lower a b c ha2 hab hbc
  have hmon (x y : ℝ) (hxy : x ≤ y) : below a b c x ≤ below a b c y := by
    dsimp [below]
    simp only [Multiset.countP_eq_card_filter]
    exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun t ht => ht.trans_le hxy)
  have hcc : below a b c c = 3 := by
    have hle := hmon c (a+b+c) (by linarith)
    rw [hg.2.2.2.1] at hle
    omega
  have hmin : below a b c (min c (a+b)) = 3 := by
    rcases le_total c (a+b) with hle | hle
    · rw [min_eq_left hle]; exact hcc
    · rw [min_eq_right hle]; exact hg.1
  have hcut : 1 < min c (a+b) := by
    exact lt_min (ha1.trans_le (hab.trans hbc)) (by linarith)
  have hFmin : (SixSupportEndpointOneArithmetic.quartic a b c).roots.countP
      (fun t => t < min c (a+b)) = 1 := by
    dsimp [below] at hmin
    rw [hr] at hmin
    have hz : ({0} : Multiset ℝ).countP (fun t => t < min c (a+b)) = 1 := by
      change Multiset.countP (fun t => t < min c (a+b)) (0 ::ₘ (0 : Multiset ℝ)) = 1
      rw [Multiset.countP_cons]
      simp only [Multiset.countP_zero,ite_eq_left (show 0 < min c (a+b) by linarith),Nat.zero_add]
    have ho : ({1} : Multiset ℝ).countP (fun t => t < min c (a+b)) = 1 := by
      change Multiset.countP (fun t => t < min c (a+b)) (1 ::ₘ (0 : Multiset ℝ)) = 1
      rw [Multiset.countP_cons]
      simp only [Multiset.countP_zero,ite_eq_left hcut,Nat.zero_add]
    rw [Multiset.countP_add,Multiset.countP_add,hz,ho] at hmin
    omega
  have hFs : (SixSupportEndpointOneArithmetic.quartic a b c).roots.countP
      (fun t => t < a+b+c) = 1 := by
    have htot := hg.2.2.2.1
    dsimp [below] at htot
    rw [hr] at htot
    simp [show 0 < a+b+c by positivity,show 1 < a+b+c by linarith] at htot
    omega
  have hsz : multiplicity a b c (a+b+c) = 0 := by
    rw [hg.2.2.2.2]
    exact if_neg (by rintro ⟨rfl,_,_⟩; have := Real.sqrt_nonneg (3 : ℝ); linarith)
  obtain ⟨μ,hμmem,hμlt⟩ := Multiset.countP_pos.mp (show 0 <
      (SixSupportEndpointOneArithmetic.quartic a b c).roots.countP
        (fun t => t < min c (a+b)) by omega)
  let r := (SixSupportEndpointOneArithmetic.quartic a b c).roots.erase μ
  have herase : (SixSupportEndpointOneArithmetic.quartic a b c).roots = {μ}+r := by
    simpa [r] using (Multiset.cons_erase hμmem).symm
  have hμs : μ < a+b+c := hμlt.trans_le ((min_le_right _ _).trans (by linarith))
  have hrcard := residual_card a b c ha0 hab hbc he
  rw [herase] at hrcard hFs
  simp only [Multiset.card_add,Multiset.card_singleton] at hrcard
  simp [hμs] at hFs
  refine ⟨μ,r,herase,by omega,residual_above_minimum a b c ha hab hbc he μ hμmem,hμlt,?_⟩
  intro t ht
  have hge : a+b+c ≤ t := le_of_not_gt (Multiset.countP_eq_zero.mp hFs t ht)
  have hne : t ≠ a+b+c := by
    intro hts
    subst t
    have hm : a+b+c ∈ (quotient a b c).charpoly.roots := by
      rw [hr,herase]
      simp [ht]
    exact (Multiset.countP_eq_zero.mp hsz (a+b+c) hm) rfl
  exact lt_of_le_of_ne hge hne.symm

private theorem negative_odd {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hd : A.det < 0) :
    Odd (negativeCount A) := by
  have hs := product_sign A.charpoly.roots
  rw [← Matrix.det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly] at hs
  have hp : 0 ≤ (A.charpoly.roots.map abs).prod :=
    Multiset.prod_nonneg fun t ht => by
      obtain ⟨u,_,rfl⟩ := Multiset.mem_map.mp ht
      exact abs_nonneg u
  rcases Nat.even_or_odd (negativeCount A) with he | ho
  · change Even (A.charpoly.roots.countP (fun t => t < 0)) at he
    rw [he.neg_one_pow] at hs
    linarith
  · exact ho

/-- The original endpoint-one family and the exact cutoff determinant. -/
theorem sharp_family (a : ℝ) :
    h a a ((a-1)*(2*a-1)) 1 = 0 ∧
      h a a ((a-1)*(2*a-1)) a =
        a^4*(a-1)^2*(2*a-1)^2*(a^2-4*a+1) := by
  simp [h,quintic]
  constructor <;> ring

/-- Below the exact cutoff, a residual root lies below a. This includes
all real 2<=a<2+sqrt(3), not just a numerical counterexample. -/
theorem below_cutoff (a : ℝ) (ha : 2 ≤ a) (hlt : a < 2 + Real.sqrt 3) :
    ((SixSupportEndpointOneArithmetic.quartic a a ((a-1)*(2*a-1))).roots.countP
      (fun t => t < a)) = 1 := by
  have ha0 : 0 < a := by linarith
  have hac : a ≤ (a-1)*(2*a-1) := by
    nlinarith [mul_nonneg (show 0 ≤ a-2 by linarith) (show 0 ≤ a by linarith)]
  have hs0 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hv : a^2-4*a+1 < 0 := by
    nlinarith [mul_neg_of_neg_of_pos (show a-2-Real.sqrt 3 < 0 by linarith)
      (show 0 < a-2+Real.sqrt 3 by linarith)]
  have hh : h a a ((a-1)*(2*a-1)) a < 0 := by
    rw [(sharp_family a).2]
    have h1 : 0 < a-1 := by linarith
    have h2 : 0 < 2*a-1 := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) hv
  have hd : (symmetric a a ((a-1)*(2*a-1))-Matrix.scalar (Fin 6) a).det < 0 := by
    rw [shifted_det a a ((a-1)*(2*a-1)) a ha0 le_rfl hac]
    exact mul_neg_of_pos_of_neg ha0 hh
  have hn := lower_exponent_inertia a a ((a-1)*(2*a-1)) ha0 le_rfl hac
  have ho := negative_odd (shifted_hermitian a a ((a-1)*(2*a-1)) a ha0 le_rfl hac) hd
  rw [(shifted_roots a a ((a-1)*(2*a-1)) a ha0 le_rfl hac).1] at hn ho
  have hr := residual_roots a a ((a-1)*(2*a-1)) (sharp_family a).1
  have hcount : below a a ((a-1)*(2*a-1)) a =
      2+(SixSupportEndpointOneArithmetic.quartic a a ((a-1)*(2*a-1))).roots.countP
        (fun t => t < a) := by
    dsimp [below]
    rw [hr]
    simp [ha0,show 1 < a by linarith]
    omega
  obtain ⟨k,hk⟩ := ho
  omega

/-- At the exact real cutoff a residual root equals a, so the strict
endpoint separation cannot be extended to that boundary. -/
theorem at_cutoff :
    (SixSupportEndpointOneArithmetic.quartic (2+Real.sqrt 3) (2+Real.sqrt 3)
      (((2+Real.sqrt 3)-1)*(2*(2+Real.sqrt 3)-1))).eval (2+Real.sqrt 3) = 0 := by
  let a : ℝ := 2 + Real.sqrt 3
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have ha1 : a-1 ≠ 0 := by dsimp [a]; have := Real.sqrt_nonneg (3 : ℝ); linarith
  have hv : a^2-4*a+1 = 0 := by dsimp [a]; nlinarith
  have hf := congrArg (Polynomial.eval a)
    (SixSupportEndpointOneArithmetic.factorization a a ((a-1)*(2*a-1)))
  change h a a ((a-1)*(2*a-1)) a = _ at hf
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C,(sharp_family a).1,
    zero_mul,add_zero] at hf
  rw [(sharp_family a).2,hv,mul_zero] at hf
  exact (mul_eq_zero.mp hf.symm).resolve_left ha1

#print axioms simple_smallest
#print axioms at_cutoff
#print axioms below_cutoff
#print axioms result
#print axioms residual_above_minimum
#print axioms endpoint_count
#print axioms lower_exponent_inertia
#print axioms upper_exponent_inertia
end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneSpectrum
