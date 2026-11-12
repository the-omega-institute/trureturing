/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairModular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RepeatedPairModular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-prime splitting obstruction for actual repeated-pair ideal graphs. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.TraceOneTensorFactors
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Source: repeated-pair-modular, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02, blob
68f394977f82d9f5f20003d20797bb5706a72bff. The full finite tail set and
every prime divisor of a+1 occur. Factor splitting is necessary, including
zero and repeated roots; passing the obstruction does not imply integrality.
The escape audit is unfinished, disclosed in issue #28398. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
open Finset Matrix Polynomial
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairModular
open RepeatedPairSupport RepeatedPairIntegralPolynomial
open TraceOneTensorSplitting TraceOneTensorFactors
open IdealIntersectionSupport IdealIntersectionObstructions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Presence coordinates identify every subset with every tensor coordinate. -/
def subsetBits : Finset ι ≃ (ι → Fin 2) where
  toFun T i := if i ∈ T then 1 else 0
  invFun x := univ.filter (fun i => x i=1)
  left_inv T := by ext i; simp
  right_inv x := by
    funext i
    have hi : x i=0 ∨ x i=1 := by omega
    rcases hi with hi|hi <;> simp [hi]

/-- The trace-one factor attached to a tail exponent. -/
def factor {R : Type*} [CommRing R] (k : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1,k;1,0]

/-- The disjointness kernel is the entire tensor, with no omitted supports. -/
theorem kernel_tensor {R : Type*} [CommRing R] (k : ι → R) :
    Matrix.reindex subsetBits subsetBits (disjointKernel k)=
      tensor (fun i => factor (k i)) := by
  have hentry (T U : Finset ι) :
      disjointKernel k T U=
        ∏ i, factor (k i) (subsetBits T i) (subsetBits U i) := by
    by_cases h : Disjoint T U
    · rw [disjointKernel,if_pos h]
      symm
      calc
        (∏ i, factor (k i) (subsetBits T i) (subsetBits U i))=
            ∏ i, (if i ∈ U then k i else 1) := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i ∈ T <;> by_cases hj : i ∈ U
          · exact (Finset.disjoint_left.mp h hi hj).elim
          all_goals simp [factor,subsetBits,hi,hj]
        _ = ∏ i ∈ U, k i := Fintype.prod_ite_mem U k
    · rw [disjointKernel,if_neg h]
      obtain ⟨i,hi,hj⟩ := Finset.not_disjoint_iff.mp h
      symm
      apply Finset.prod_eq_zero (mem_univ i)
      simp [factor,subsetBits,hi,hj]
  ext x y
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, tensor, Equiv.apply_symm_apply] using
    hentry (subsetBits.symm x) (subsetBits.symm y)

/-- Negating an operator preserves splitting, without diagonalizability. -/
theorem splits_of_neg {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hs : (-M).charpoly.Splits) : M.charpoly.Splits := by
  let E := AlgebraicClosure K
  let f : K →+* E := algebraMap K E
  have hsplit : (M.charpoly.map f).Splits := IsAlgClosed.splits _
  apply hsplit.of_splits_map f
  intro x hx
  have hxroot : (M.map f).charpoly.IsRoot x := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero M.charpoly_monic.ne_zero)).mp hx
  obtain ⟨v,hv,he⟩ := eigenpair_of_root (M.map f) x hxroot
  have hmap : (-M).map f = -(M.map f) := by
    ext i j
    exact _root_.map_neg f (M i j)
  have hn : ((-M).map f)*ᵥv=(-x) • v := by
    rw [hmap, Matrix.neg_mulVec, he, neg_smul]
  have hr := root_of_eigenpair ((-M).map f) (-x) v hv hn
  rw [Matrix.charpoly_map] at hr
  obtain ⟨y,hy⟩ := hs.mem_range_of_isRoot (-M).charpoly_monic.ne_zero hr
  refine ⟨-y,?_⟩
  calc
    f (-y) = -(f y) := _root_.map_neg f y
    _ = -(-x) := congrArg Neg.neg hy
    _ = x := neg_neg x

/-- Reduction at any field where a+1 vanishes forces every tail factor
to split. The graph hypothesis supplies the full characteristic polynomial. -/
theorem actual_factor_splits (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    {F : Type*} [Field F] (hchar : (a : F)+1=0) :
    ∀ i, (X^2-X-C (k i : F)).Splits := by
  have hs := actual_reduction_splits p hp hinj a k ha hk H (R := F)
  have haF : (a : F) = -1 := eq_neg_of_add_eq_zero_left hchar
  have hK : K (a : F) (fun i => (k i : F))=
      -disjointKernel (fun i => (k i : F)) := by
    ext T U
    simp [K,haF]
  rw [hK] at hs
  have ht : (tensor (fun i => factor (k i : F))).charpoly.Splits := by
    rw [← kernel_tensor,Matrix.charpoly_reindex]
    exact splits_of_neg _ hs
  have htr (i : ι) : (factor (k i : F)).trace=1 := by
    simp [factor,Matrix.trace,Fin.sum_univ_two]
  have hf := factors_split (fun i => factor (k i : F)) htr ht
  intro i
  have hc : (factor (k i : F)).charpoly=X^2-X-C (k i : F) := by
    simp [Matrix.charpoly_fin_two,factor]
    ring
  simpa only [hc] using hf i

/-- The full arbitrary-prime necessary condition on actual ideal graphs. -/
theorem actual_prime_splits (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ a+1) :
    ∀ i, (X^2-X-C (k i : ZMod ℓ)).Splits := by
  apply actual_factor_splits p hp hinj a k ha hk H
  have hh : ((a+1 : ℕ) : ZMod ℓ)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hℓ
  simpa using hh

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairModular
