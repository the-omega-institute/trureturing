/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RepeatedPairSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General-index repeated-pair invariant support operator and actual graph lift. -/
import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
import Mathlib.Data.Finset.Sum

/-! Source: repeated-pair-product-tail, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, exact blob
66664013207b88567bf74f1a9a0c6eaf65d07f24. The two equal coordinates and
every finite tail coordinate are represented. The full support operator,
zero sum and nonzero actual ideal-graph lift are required: a principal
compression alone is not an eigenvector embedding. The existing four-index
PairedIdealIntersectionLift remains the supplier for its original scope. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairSupport
open IdealIntersectionSupport IdealIntersectionObstructions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairExponents (a : ℕ) (k : ι → ℕ) : Fin 2 ⊕ ι → ℕ :=
  Sum.elim (fun _ => a) k

def diagonalFactor {R : Type*} [CommRing R] (k : ι → R) (T : Finset ι) : R :=
  ∏ i ∈ univ \ T, (k i+1)

def disjointKernel {R : Type*} [CommRing R] (k : ι → R) : Matrix (Finset ι) (Finset ι) R :=
  fun T U => if Disjoint T U then ∏ i ∈ U, k i else 0

/-- Subset form of the entire tensor, with all 2^card(iota) coordinates. -/
def K {R : Type*} [CommRing R] (a : R) (k : ι → R) : Matrix (Finset ι) (Finset ι) R :=
  diagonal (fun T => (a+1)*diagonalFactor k T)+a • disjointKernel k

def pairedValue (h : Finset ι → ℝ) (S : Finset (Fin 2 ⊕ ι)) : ℝ :=
  if S.toLeft = {0} then h S.toRight
  else if S.toLeft = {1} then -h S.toRight else 0

theorem sum_four (f : Finset (Fin 2 ⊕ ι) → ℝ) :
    (∑ S, f S) = (∑ T, f ((∅ : Finset (Fin 2)).disjSum T))+
      (∑ T, f (({0} : Finset (Fin 2)).disjSum T))+
      (∑ T, f (({1} : Finset (Fin 2)).disjSum T))+
      (∑ T, f ((univ : Finset (Fin 2)).disjSum T)) := by
  have he := Equiv.sum_comp (Finset.sumEquiv (α := Fin 2) (β := ι)).toEquiv.symm f
  rw [← he]
  change (∑ i : Finset (Fin 2) × Finset ι, f (i.1.disjSum i.2)) = _
  rw [Fintype.sum_prod_type]
  have h4 : (univ : Finset (Finset (Fin 2))) = {∅,{0},{1},univ} := by decide
  rw [h4]
  simp (disch := decide) only [sum_insert,sum_singleton]
  ring

theorem disjoint_sum (A B : Finset (Fin 2)) (T U : Finset ι) :
    Disjoint (A.disjSum T) (B.disjSum U) ↔ Disjoint A B ∧ Disjoint T U := by
  constructor
  · intro h
    constructor
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      exact Finset.disjoint_left.mp h (by simpa using hi : Sum.inl i ∈ A.disjSum T)
        (by simpa using hj : Sum.inl i ∈ B.disjSum U)
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      exact Finset.disjoint_left.mp h (by simpa using hi : Sum.inr i ∈ A.disjSum T)
        (by simpa using hj : Sum.inr i ∈ B.disjSum U)
  · rintro ⟨hA,hT⟩
    apply Finset.disjoint_left.mpr
    intro i hi hj
    cases i with
    | inl i => exact Finset.disjoint_left.mp hA (by simpa using hi) (by simpa using hj)
    | inr i => exact Finset.disjoint_left.mp hT (by simpa using hi) (by simpa using hj)

private theorem weight_sum (a : ℕ) (k : ι → ℕ) (A : Finset (Fin 2)) (T : Finset ι) :
    supportWeight (pairExponents a k) (A.disjSum T) =
      (a : ℝ)^A.card*supportWeight k T := by
  simp [supportWeight,Finset.prod_disjSum,pairExponents]

theorem pairedValue_sum (h : Finset ι → ℝ) (A : Finset (Fin 2)) (T : Finset ι) :
    pairedValue h (A.disjSum T) =
      if A = {0} then h T else if A = {1} then -h T else 0 := by
  simp only [pairedValue,Finset.toLeft_disjSum,Finset.toRight_disjSum]

private theorem disjSum_nonempty (A : Finset (Fin 2)) (T : Finset ι) :
    (A.disjSum T).Nonempty ↔ A.Nonempty ∨ T.Nonempty := by
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i,by simpa using hi⟩
    | inr i => exact Or.inr ⟨i,by simpa using hi⟩
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Sum.inl i,by simpa using hi⟩
    · exact ⟨Sum.inr i,by simpa using hi⟩

private theorem universe_sum : (univ : Finset (Fin 2 ⊕ ι)) =
    (univ : Finset (Fin 2)).disjSum (univ : Finset ι) := by
  ext i
  cases i <;> simp

private theorem tail_degree (k : ι → ℕ) (T : Finset ι) :
    (∑ U : Finset ι, if Disjoint T U then supportWeight k U else 0) =
      diagonalFactor (fun i => (k i : ℝ)) T := by
  have hsub (U : Finset ι) : Disjoint T U ↔ U ⊆ univ \ T := by
    constructor
    · intro h i hi
      exact mem_sdiff.mpr ⟨mem_univ i,fun ht => Finset.disjoint_left.mp h ht hi⟩
    · intro h
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp (h hj)).2 hi
  simp_rw [hsub]
  have hf : (univ : Finset (Finset ι)).filter (fun U => U ⊆ univ \ T) =
      (univ \ T).powerset := by ext U; simp
  rw [← Finset.sum_filter,hf]
  exact (Finset.prod_add_one (univ \ T)).symm

private theorem tail_degree_nonempty (k : ι → ℕ) (T : Finset ι) :
    (∑ U : Finset ι, if U.Nonempty ∧ Disjoint T U then supportWeight k U else 0) =
      diagonalFactor (fun i => (k i : ℝ)) T-1 := by
  have hpoint (U : Finset ι) :
      (if Disjoint T U then supportWeight k U else 0) =
        (if U=∅ then 1 else 0)+
        (if U.Nonempty ∧ Disjoint T U then supportWeight k U else 0) := by
    by_cases hU : U = ∅
    · subst U; simp [supportWeight]
    · simp [hU,Finset.nonempty_iff_ne_empty]
  have hs := Finset.sum_congr (s₁ := (univ : Finset (Finset ι))) rfl
    (fun U _ => hpoint U)
  rw [tail_degree,Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  linarith

/-- Exact weighted symmetry for every real tail, including zero and
negative parameters. Positivity assumptions belong to spectral consumers. -/
theorem weighted_symmetry (a : ℝ) (k : ι → ℝ) :
    (diagonal (fun T => ∏ i ∈ T, k i)*K a k).IsHermitian := by
  ext T U
  by_cases hTU : T = U
  · subst U
    simp [K,diagonal_mul,disjointKernel]
  · simp [K,diagonal_mul,Matrix.conjTranspose_apply,disjointKernel,
      hTU,Ne.symm hTU,disjoint_comm]
    split_ifs <;> ring

/-- Equal weights cancel on every paired cell, on the full actual
vertex set. No finite set of test supports is substituted. -/
theorem paired_lift_sum (a : ℕ) (k : ι → ℕ) (ha : 0 < a)
    (hk : ∀ i, 0 < k i) (h : Finset ι → ℝ) :
    (∑ x : BoxVertex (pairExponents a k),
      supportLift (pairExponents a k) (pairedValue h) x) = 0 := by
  have hpos (i : Fin 2 ⊕ ι) : 0 < pairExponents a k i := by
    cases i <;> simp [pairExponents,ha,hk]
  have he : (∅ : Finset (Fin 2 ⊕ ι)) = (∅ : Finset (Fin 2)).disjSum ∅ := by
    ext i
    cases i <;> simp
  have h0 : pairedValue h ∅ = 0 := by
    rw [he,pairedValue_sum]
    norm_num
  have hu : pairedValue h univ = 0 := by
    rw [universe_sum]
    rw [pairedValue_sum]
    norm_num [show (univ : Finset (Fin 2)) ≠ {0} by decide,
      show (univ : Finset (Fin 2)) ≠ {1} by decide]
  rw [show (∑ x : BoxVertex (pairExponents a k),
      supportLift (pairExponents a k) (pairedValue h) x) =
      ∑ S, supportWeight (pairExponents a k) S*pairedValue h S from
    support_lift_sum _ hpos _ h0 hu]
  rw [sum_four]
  simp only [weight_sum,pairedValue_sum]
  norm_num [show (univ : Finset (Fin 2)) ≠ {0} by decide,
    show (univ : Finset (Fin 2)) ≠ {1} by decide,← sum_add_distrib]

/-- Every nonzero tail function has a nonzero actual graph lift. -/
theorem paired_lift_nonzero (a : ℕ) (k : ι → ℕ) (ha : 0 < a)
    (hk : ∀ i, 0 < k i) (h : Finset ι → ℝ) (hh : h ≠ 0) :
    supportLift (pairExponents a k) (pairedValue h) ≠ 0 := by
  have hpos (i : Fin 2 ⊕ ι) : 0 < pairExponents a k i := by
    cases i <;> simp [pairExponents,ha,hk]
  obtain ⟨T,hT⟩ : ∃ T, h T ≠ 0 := Function.ne_iff.mp hh
  let S := ({0} : Finset (Fin 2)).disjSum T
  have hS : S.Nonempty := ⟨Sum.inl 0,by simp [S]⟩
  have hSu : S ≠ univ := by
    intro hs
    have hh : Sum.inl (1 : Fin 2) ∈ S := hs.symm ▸ mem_univ _
    simpa [S] using hh
  apply support_lift_nonzero _ hpos _ S hS hSu
  simpa [S,pairedValue] using hT


private theorem K_action (a : ℝ) (k : ι → ℕ) (h : Finset ι → ℝ)
    (T : Finset ι) :
    ((K a (fun i => (k i : ℝ))-1)*ᵥh) T =
      ((a+1)*diagonalFactor (fun i => (k i : ℝ)) T-1)*h T+
      a*(∑ U, if Disjoint T U then supportWeight k U*h U else 0) := by
  rw [K,sub_mulVec,add_mulVec,smul_mulVec,one_mulVec]
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mulVec_diagonal]
  simp only [mulVec,dotProduct]
  simp only [disjointKernel,ite_mul,zero_mul,supportWeight]
  ring

private theorem disjSum_ne_univ (A : Finset (Fin 2)) (T : Finset ι)
    (hA : A ≠ univ) : A.disjSum T ≠ univ := by
  intro he
  apply hA
  have hh := congrArg Finset.toLeft he
  have hu : (univ : Finset (Fin 2 ⊕ ι)).toLeft = univ := by ext; simp
  simpa only [Finset.toLeft_disjSum,hu] using hh

set_option maxHeartbeats 2000000 in
/-- Full invariant action, including the zero cells, for any finite tail.
This is an operator identity on the whole support domain. -/
theorem paired_support_action (a : ℕ) (k : ι → ℕ) (h : Finset ι → ℝ)
    (S : Finset (Fin 2 ⊕ ι)) :
    supportComplementOp (pairExponents a k) (pairedValue h) S =
      pairedValue ((K (a : ℝ) (fun i => (k i : ℝ))-1)*ᵥh) S := by
  have hs : S = S.toLeft.disjSum S.toRight := by
    ext i
    cases i <;> simp
  rw [hs]
  generalize S.toLeft = A
  generalize S.toRight = T
  have hA : A ∈ ({∅,{0},{1},univ} : Finset (Finset (Fin 2))) := by
    have he : ({∅,{0},{1},univ} : Finset (Finset (Fin 2))) = univ := by decide
    rw [he]
    exact mem_univ _
  have hn0 (U : Finset ι) := disjSum_ne_univ ({0} : Finset (Fin 2)) U (by decide)
  have hn1 (U : Finset ι) := disjSum_ne_univ ({1} : Finset (Fin 2)) U (by decide)
  have hne (U : Finset ι) := disjSum_ne_univ (∅ : Finset (Fin 2)) U (by decide)
  have hu0 : (univ : Finset (Fin 2)) ≠ {0} := by decide
  have hu1 : (univ : Finset (Fin 2)) ≠ {1} := by decide
  have hue : (univ : Finset (Fin 2)) ≠ ∅ := by decide
  have hd00 : ¬Disjoint ({0} : Finset (Fin 2)) {0} := by decide
  have hd11 : ¬Disjoint ({1} : Finset (Fin 2)) {1} := by decide
  have hd01 : Disjoint ({0} : Finset (Fin 2)) {1} := by decide
  have hd10 : Disjoint ({1} : Finset (Fin 2)) {0} := by decide
  have hdu0 : ¬Disjoint (univ : Finset (Fin 2)) {0} := by decide
  have hdu1 : ¬Disjoint (univ : Finset (Fin 2)) {1} := by decide
  simp only [mem_insert,mem_singleton] at hA
  rcases hA with rfl | rfl | rfl | rfl <;>
    simp only [supportComplementOp,sum_four] <;>
    simp only [pairedValue_sum,weight_sum,disjoint_sum,disjSum_nonempty] <;>
    simp [-Finset.empty_disjSum,hn0,hn1,hne,hu0,hu1,hue,
      hd00,hd11,hd01,hd10,hdu0,hdu1]
  · rw [← sum_add_distrib]
    apply sum_eq_zero
    intro U _
    split_ifs <;> ring
  · rw [K_action]
    have hsplit (U : Finset ι) :
        (if U.Nonempty ∧ Disjoint T U then supportWeight k U*h T else 0)+
          (if Disjoint T U then (a : ℝ)*supportWeight k U*(h T+h U) else 0) =
        (if U.Nonempty ∧ Disjoint T U then supportWeight k U else 0)*h T+
          (a : ℝ)*(if Disjoint T U then supportWeight k U else 0)*h T+
          (a : ℝ)*(if Disjoint T U then supportWeight k U*h U else 0) := by
      split_ifs <;> ring
    rw [← sum_add_distrib]
    simp_rw [hsplit]
    rw [sum_add_distrib,sum_add_distrib,← sum_mul,← sum_mul,← mul_sum,
      ← mul_sum,tail_degree,tail_degree_nonempty]
    ring
  · rw [K_action]
    have hsplit (U : Finset ι) :
        (if U.Nonempty ∧ Disjoint T U then -(supportWeight k U*h T) else 0)+
          (if Disjoint T U then (a : ℝ)*supportWeight k U*(-h T-h U) else 0) =
        -((if U.Nonempty ∧ Disjoint T U then supportWeight k U else 0)*h T+
          (a : ℝ)*(if Disjoint T U then supportWeight k U else 0)*h T+
          (a : ℝ)*(if Disjoint T U then supportWeight k U*h U else 0)) := by
      split_ifs <;> ring
    rw [← sum_add_distrib]
    simp_rw [hsplit]
    rw [sum_neg_distrib]
    rw [sum_add_distrib,sum_add_distrib,← sum_mul,← sum_mul,← mul_sum,
      ← mul_sum,tail_degree,tail_degree_nonempty]
    ring

/-- Every eigenvector of the complete repeated-pair restriction yields an
actual ideal-graph eigenvalue, for all positive exponents and distinct primes. -/
theorem actual_paired_eigenvalue (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (e : ℝ) (h : Finset ι → ℝ) (hh : h ≠ 0)
    (he : K (a : ℝ) (fun i => (k i : ℝ)) *ᵥ h = e • h) :
    HasActualEigenvalue (modulus p (pairExponents a k))
      (((((a+1)^2*(∏ i, (k i+1)))-2 : ℕ) : ℝ)+1-e) := by
  have hpos (i : Fin 2 ⊕ ι) : 0 < pairExponents a k i := by
    cases i <;> simp [pairExponents,ha,hk]
  have hlap : (supportGraph (pairExponents a k))ᶜ.lapMatrix ℝ *ᵥ
      supportLift (pairExponents a k) (pairedValue h) =
      (e-1) • supportLift (pairExponents a k) (pairedValue h) := by
    ext x
    rw [support_complement_intertwining _ hpos,paired_support_action]
    rw [sub_mulVec,he,one_mulVec]
    simp only [supportLift,pairedValue,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    split_ifs <;> ring
  have hactual := actual_eigenvalue_of_support p hp hinj (pairExponents a k) hpos
    (e-1) (supportLift (pairExponents a k) (pairedValue h))
    (paired_lift_nonzero a k ha hk h hh) (paired_lift_sum a k ha hk h) hlap
  have hprod : (∏ i, (pairExponents a k i+1)) =
      (a+1)^2*(∏ i, (k i+1)) := by
    simp [pairExponents,Fintype.prod_sum_type]
  rw [hprod] at hactual
  convert hactual using 1 <;> ring

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairSupport
