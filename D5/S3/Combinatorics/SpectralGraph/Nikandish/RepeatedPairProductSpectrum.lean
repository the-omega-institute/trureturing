/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete arbitrary-index repeated-pair product criterion, including equality. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairProductTail
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! Source: repeated-pair-product-tail, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, blob
66664013207b88567bf74f1a9a0c6eaf65d07f24. Equality requires two distinct
tail coordinates. No conclusion about the three-prime equality block or
the condition-failing higher-prime region is asserted. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductSpectrum
open RepeatedPairSupport RepeatedPairProductTail
open PairedIdealIntersectionObstructions
open IdealIntersectionSupport IdealIntersectionObstructions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rootWeight (k : ι → ℝ) (T : Finset ι) : ℝ := Real.sqrt (weight k T)

def symmetricK (a : ℝ) (k : ι → ℝ) : Matrix (Finset ι) (Finset ι) ℝ :=
  diagonal (fun T => (a+1)*diagonalFactor k T)+
    a • Matrix.of (fun T U => if Disjoint T U then rootWeight k T*rootWeight k U else 0)

private theorem weight_pos (k : ι → ℝ) (hk : ∀ i, 0 < k i) (T : Finset ι) :
    0 < weight k T := prod_pos (fun i _ => hk i)

private theorem root_pos (k : ι → ℝ) (hk : ∀ i, 0 < k i) (T : Finset ι) :
    0 < rootWeight k T := Real.sqrt_pos.mpr (weight_pos k hk T)

private theorem root_sq (k : ι → ℝ) (hk : ∀ i, 0 < k i) (T : Finset ι) :
    (rootWeight k T)^2 = weight k T := Real.sq_sqrt (weight_pos k hk T).le

theorem hermitian (a : ℝ) (k : ι → ℝ) : (symmetricK a k).IsHermitian := by
  ext T U
  by_cases h : T = U
  · subst U; simp [symmetricK,conjTranspose_apply]
  · simp [symmetricK,conjTranspose_apply,diagonal_apply,h,Ne.symm h,disjoint_comm]
    split_ifs <;> ring

theorem intertwine (a : ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i) :
    diagonal (rootWeight k)*K a k = symmetricK a k*diagonal (rootWeight k) := by
  ext T U
  simp only [diagonal_mul,mul_diagonal,K,symmetricK,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,disjointKernel,Matrix.of_apply]
  have hw : (∏ i ∈ U, k i) = (rootWeight k U)^2 := (root_sq k hk U).symm
  rw [hw]
  by_cases h : T = U
  · subst U
    simp only [diagonal_apply_eq]
    split_ifs <;> ring
  · simp only [diagonal_apply_ne _ h]
    split_ifs <;> ring

theorem eigenpair_transport (a : ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (e : ℝ) (v : Finset ι → ℝ) (hv : v ≠ 0) (he : symmetricK a k*ᵥv = e • v) :
    ∃ h : Finset ι → ℝ, h ≠ 0 ∧ K a k*ᵥh = e • h := by
  let D := diagonal (rootWeight k)
  let h : Finset ι → ℝ := fun T => v T/rootWeight k T
  have hDh : D*ᵥh = v := by
    ext T
    simp only [D,h,mulVec_diagonal,Pi.mul_apply]
    field_simp [(root_pos k hk T).ne']
  have hinj : Function.Injective D.mulVec := by
    intro x y hxy
    ext T
    have hh := congrFun hxy T
    simp only [D,mulVec_diagonal,Pi.mul_apply] at hh
    exact mul_left_cancel₀ (root_pos k hk T).ne' hh
  refine ⟨h,?_,?_⟩
  · intro hh
    apply hv
    rw [← hDh,hh,mulVec_zero]
  · apply hinj
    rw [mulVec_mulVec,intertwine a k hk,← mulVec_mulVec,hDh,he,mulVec_smul,hDh]

private theorem energy_transport (a : ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (h : Finset ι → ℝ) :
    let v := diagonal (rootWeight k)*ᵥh
    dotProduct v ((symmetricK a k-(2:ℝ) • 1)*ᵥv) =
      ∑ T, weight k T*h T*(((K a k-(2:ℝ) • 1)*ᵥh) T) := by
  dsimp only
  have he : (symmetricK a k-(2:ℝ) • 1)*ᵥ(diagonal (rootWeight k)*ᵥh) =
      diagonal (rootWeight k)*ᵥ((K a k-(2:ℝ) • 1)*ᵥh) := by
    simp only [sub_mulVec,smul_mulVec,one_mulVec]
    rw [mulVec_mulVec,← intertwine a k hk,← mulVec_mulVec,mulVec_sub,mulVec_smul]
  rw [he]
  simp only [dotProduct,mulVec_diagonal,Pi.mul_apply]
  apply sum_congr rfl
  intro T _
  calc
    _ = (rootWeight k T)^2*h T*(((K a k-(2:ℝ) • 1)*ᵥh) T) := by ring
    _ = _ := by rw [root_sq k hk T]

private def trial (T : Finset ι) (x y z : ℝ) : Finset ι → ℝ :=
  Pi.single ∅ x+Pi.single univ y+Pi.single T z

set_option maxHeartbeats 1000000 in
private theorem trial_energy (a : ℝ) (k : ι → ℝ) (T : Finset ι)
    (hT : T.Nonempty) (hTu : T ≠ univ) (x y z : ℝ) :
    let h := trial T x y z
    (∑ U, weight k U*h U*(((K a k-(2:ℝ) • 1)*ᵥh) U)) =
      ((a+1)*diagonalFactor k ∅+a-2)*x^2+
      2*a*weight k univ*x*y+weight k univ*(a-1)*y^2+
      weight k T*((a+1)*diagonalFactor k T-2)*z^2+2*weight k T*a*x*z := by
  dsimp only
  have h0u : (∅ : Finset ι) ≠ univ := by
    intro he
    obtain ⟨i,_⟩ := hT
    have hm : i ∈ (∅ : Finset ι) := he.symm ▸ mem_univ i
    simpa using hm
  have h0T := Ne.symm hT.ne_empty
  have huT := Ne.symm hTu
  have hduT : ¬Disjoint (univ : Finset ι) T := by
    intro hd
    obtain ⟨i,hi⟩ := hT
    exact Finset.disjoint_left.mp hd (mem_univ i) hi
  have hdTu : ¬Disjoint T (univ : Finset ι) := fun hd => hduT hd.symm
  have hduu : ¬Disjoint (univ : Finset ι) univ := by
    intro hd
    obtain ⟨i,_⟩ := hT
    exact Finset.disjoint_left.mp hd (mem_univ i) (mem_univ i)
  have hw : diagonal (weight k)*ᵥtrial T x y z =
      Pi.single ∅ x+Pi.single univ (weight k univ*y)+Pi.single T (weight k T*z) := by
    simp only [trial,mulVec_add,diagonal_mulVec_single]
    simp [weight]
  have hdot (f g : Finset ι → ℝ) :
      dotProduct (diagonal (weight k)*ᵥf) g = ∑ U, weight k U*f U*g U := by
    simp only [dotProduct,mulVec_diagonal,Pi.mul_apply]
  rw [← hdot]
  rw [hw]
  simp only [add_dotProduct,single_dotProduct,trial,mulVec_add,mulVec_single,Pi.add_apply]
  simp [K,diagonal_apply,disjointKernel,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,hT.ne_empty,Ne.symm hT.ne_empty,hTu,huT,h0u,Ne.symm h0u,
    disjoint_self,hduT,hdTu,hduu,
    diagonalFactor,weight]
  ring

private theorem one_le_diagonal (k : ι → ℝ) (hk : ∀ i, 0 < k i) (T : Finset ι) :
    1 ≤ diagonalFactor k T := by
  unfold diagonalFactor
  induction (univ \ T) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi]
    nlinarith [hk i]

/-- The full general-index product criterion, including equality. The
nontrivial tail is essential: it provides an intermediate support, so this
does not assert strictness for the three-prime equality block. -/
private theorem product_low_eigenpair [Nontrivial ι] (a : ℝ) (k : ι → ℝ)
    (ha : 1 ≤ a) (hk : ∀ i, 0 < k i)
    (hcrit : (a^2-1)*diagonalFactor k ∅+(a-1)*(a-2) ≤ a^2*weight k univ) :
    ∃ e : ℝ, 1 < e ∧ e < 2 ∧ ∃ h : Finset ι → ℝ,
      h ≠ 0 ∧ K a k *ᵥ h = e • h := by
  obtain ⟨i,j,hij⟩ := exists_pair_ne ι
  let T : Finset ι := {i}
  have hT : T.Nonempty := singleton_nonempty _
  have hTu : T ≠ univ := by
    intro he
    have hj : j ∈ T := he.symm ▸ mem_univ j
    exact hij (by simpa [T,eq_comm] using hj)
  have hA := weight_pos k hk univ
  have hB := one_le_diagonal k hk ∅
  have hW := weight_pos k hk T
  have hP := one_le_diagonal k hk T
  have hneg : ∃ h : Finset ι → ℝ,
      (∑ U, weight k U*h U*(((K a k-(2:ℝ) • 1)*ᵥh) U)) < 0 := by
    by_cases ha1 : a = 1
    · refine ⟨trial T 1 (-diagonalFactor k ∅/weight k univ) 0,?_⟩
      rw [trial_energy a k T hT hTu]
      rw [ha1]
      have he :
          ((1+1)*diagonalFactor k ∅+1-2)*1^2+
          2*1*weight k univ*1*(-diagonalFactor k ∅/weight k univ)+
          weight k univ*(1-1)*(-diagonalFactor k ∅/weight k univ)^2+
          weight k T*((1+1)*diagonalFactor k T-2)*0^2+2*weight k T*1*1*0 = -1 := by
        field_simp [hA.ne']
        ring
      rw [he]
      norm_num
    · have hapos : 0 < a-1 := by
        have hlt : 1 < a := lt_of_le_of_ne ha (Ne.symm ha1)
        linarith
      let d := (a+1)*diagonalFactor k T-2
      have hd : 0 < d := by dsimp [d]; nlinarith
      refine ⟨trial T (a-1) (-a) (-a*(a-1)/d),?_⟩
      rw [trial_energy a k T hT hTu]
      have he :
          ((a+1)*diagonalFactor k ∅+a-2)*(a-1)^2+
          2*a*weight k univ*(a-1)*(-a)+weight k univ*(a-1)*(-a)^2+
          weight k T*((a+1)*diagonalFactor k T-2)*(-a*(a-1)/d)^2+
          2*weight k T*a*(a-1)*(-a*(a-1)/d) =
          (a-1)*((a^2-1)*diagonalFactor k ∅+(a-1)*(a-2)-a^2*weight k univ)-
          weight k T*a^2*(a-1)^2/d := by
        dsimp [d]
        field_simp [hd.ne']
        ring
      rw [he]
      have hn : (a-1)*((a^2-1)*diagonalFactor k ∅+(a-1)*(a-2)-a^2*weight k univ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hapos.le (by linarith)
      have hp : 0 < weight k T*a^2*(a-1)^2/d :=
        div_pos (mul_pos (mul_pos hW (sq_pos_of_pos (by linarith))) (sq_pos_of_pos hapos)) hd
      linarith
  let M := symmetricK a k-(2:ℝ) • 1
  have hM : M.IsHermitian := (hermitian a k).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    obtain ⟨h,hh⟩ := hneg
    have hn := hp.dotProduct_mulVec_nonneg (diagonal (rootWeight k)*ᵥh)
    simp only [star_trivial] at hn
    rw [show M = symmetricK a k-(2:ℝ) • 1 from rfl,energy_transport a k hk h] at hn
    linarith
  obtain ⟨e,he,v,hv,hve⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hvS : symmetricK a k*ᵥv = (e+2) • v := by
    have hh : M*ᵥv = symmetricK a k*ᵥv-(2:ℝ) • v := by
      simp [M,sub_mulVec,smul_mulVec,one_mulVec]
    rw [hh] at hve
    ext T
    have ht := congrFun hve T
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  obtain ⟨h,hh,hhe⟩ := eigenpair_transport a k hk (e+2) v hv hvS
  refine ⟨e+2,eigenvalue_gt_one a k (by linarith) hk (e+2) h hh hhe,by linarith,h,hh,hhe⟩

private theorem spectral_index (a : ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i)
    (e : ℝ) (h : Finset ι → ℝ) (hh : h ≠ 0) (he : K a k *ᵥ h = e • h) :
    ∃ T, (hermitian a k).eigenvalues T = e := by
  let v := diagonal (rootWeight k)*ᵥh
  have hv : v ≠ 0 := by
    intro hz
    apply hh
    ext T
    have ht := congrFun hz T
    simp only [v,mulVec_diagonal,Pi.mul_apply,Pi.zero_apply] at ht
    exact (mul_eq_zero.mp ht).resolve_left (root_pos k hk T).ne'
  have hve : symmetricK a k*ᵥv = e • v := by
    dsimp [v]
    rw [mulVec_mulVec,← intertwine a k hk,← mulVec_mulVec,he,mulVec_smul]
  have hspec : e ∈ spectrum ℝ (symmetricK a k) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    change (symmetricK a k).charpoly.eval e = 0
    rw [Matrix.eval_charpoly]
    by_contra hd
    apply hv
    apply Matrix.eq_zero_of_mulVec_eq_zero hd
    rw [sub_mulVec,hve]
    ext T
    simp [Matrix.scalar,Matrix.mulVec_diagonal]
  rw [(hermitian a k).spectrum_real_eq_range_eigenvalues] at hspec
  exact hspec

/-- The actual smallest eigenvalue of the complete repeated-pair operator
lies strictly between one and two under the source product inequality.
The minimum comparison quantifies over every real eigenpair of K. -/
theorem product_minimum_window [Nontrivial ι] (a : ℝ) (k : ι → ℝ)
    (ha : 1 ≤ a) (hk : ∀ i, 0 < k i)
    (hcrit : (a^2-1)*diagonalFactor k ∅+(a-1)*(a-2) ≤ a^2*weight k univ) :
    ∃ e : ℝ, 1 < e ∧ e < 2 ∧ ∃ h : Finset ι → ℝ,
      h ≠ 0 ∧ K a k *ᵥ h = e • h ∧
      ∀ r : ℝ, ∀ z : Finset ι → ℝ, z ≠ 0 → K a k *ᵥ z = r • z → e ≤ r := by
  obtain ⟨T,_,hT⟩ := (univ : Finset (Finset ι)).exists_min_image
    (hermitian a k).eigenvalues univ_nonempty
  let e := (hermitian a k).eigenvalues T
  let v : Finset ι → ℝ := (hermitian a k).eigenvectorBasis T
  have hv : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.mpr ((hermitian a k).eigenvectorBasis.orthonormal.ne_zero T)
  have he : symmetricK a k*ᵥv = e • v := (hermitian a k).mulVec_eigenvectorBasis T
  obtain ⟨h,hh,hhe⟩ := eigenpair_transport a k hk e v hv he
  have hmin (r : ℝ) (z : Finset ι → ℝ) (hz : z ≠ 0) (hze : K a k*ᵥz = r • z) : e ≤ r := by
    obtain ⟨U,hU⟩ := spectral_index a k hk r z hz hze
    simpa only [hU] using hT U (mem_univ U)
  obtain ⟨r,_,hr,z,hz,hze⟩ := product_low_eigenpair a k ha hk hcrit
  exact ⟨e,eigenvalue_gt_one a k (by linarith) hk e h hh hhe,
    lt_of_le_of_lt (hmin r z hz hze) hr,h,hh,hhe,hmin⟩

/-- On the entire original positive-natural domain with at least four
distinct primes, the product inequality gives a noninteger eigenvalue
strictly between V-1 and V on the actual ideal graph, also at equality. -/
theorem actual_product_tail [Nontrivial ι] (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (hcrit : (((a : ℝ)^2-1)*(∏ i, ((k i : ℝ)+1))+((a : ℝ)-1)*((a : ℝ)-2)) ≤
      (a : ℝ)^2*(∏ i, (k i : ℝ))) :
    let V : ℕ := (a+1)^2*(∏ i, (k i+1))-2
    (∃ ell : ℝ, HasActualEigenvalue (modulus p (pairExponents a k)) ell ∧
      (V : ℝ)-1 < ell ∧ ell < (V : ℝ)) ∧
      ¬ActualLaplacianIntegral (modulus p (pairExponents a k)) := by
  dsimp only
  have hkR (i : ι) : 0 < (k i : ℝ) := by exact_mod_cast hk i
  have hcrit' : ((a : ℝ)^2-1)*diagonalFactor (fun i => (k i : ℝ)) ∅+
      ((a : ℝ)-1)*((a : ℝ)-2) ≤
      (a : ℝ)^2*weight (fun i => (k i : ℝ)) univ := by
    simpa [diagonalFactor,weight] using hcrit
  obtain ⟨e,hel,heu,h,hh,hhe,_⟩ :=
    product_minimum_window (a : ℝ) (fun i => (k i : ℝ))
      (by exact_mod_cast (show 1 ≤ a from ha)) hkR hcrit'
  let V : ℕ := (a+1)^2*(∏ i, (k i+1))-2
  let ell : ℝ := (V : ℝ)+1-e
  have hEll : HasActualEigenvalue (modulus p (pairExponents a k)) ell :=
    actual_paired_eigenvalue p hp hinj a k ha hk e h hh hhe
  have hl : (V : ℝ)-1 < ell := by dsimp [ell]; linarith
  have hu : ell < (V : ℝ) := by dsimp [ell]; linarith
  refine ⟨⟨ell,hEll,hl,hu⟩,?_⟩
  intro hI
  obtain ⟨z,hz⟩ := hI ell hEll
  have hzL : (V : ℤ)-1 < z := by exact_mod_cast (show (V : ℝ)-1 < (z : ℝ) by simpa [hz] using hl)
  have hzU : z < (V : ℤ) := by exact_mod_cast (show (z : ℝ) < (V : ℝ) by simpa [hz] using hu)
  omega

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductSpectrum
