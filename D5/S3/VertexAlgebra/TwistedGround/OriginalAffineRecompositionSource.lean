/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite affine recomposition and the complete original corrected Gaussian Laurent row. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource

/-! Finite affine recomposition of the original charged corrected row.
The native Gaussian insertion identity extracts the auxiliary Z*Y factor;
`ElementaryGaussianContraction.coefficient_contraction` then contracts the
shared residual and auxiliary occupations. The shared auxiliary factorial is
cancelled before the bounded auxiliary sums are rearranged. -/

/-
Proof-shape proposal: content through the non-binding occupation comparisons;
organizational normalization helpers are retained only with actual consumers.
Candidate escape witness: right_auxiliary_factorization proves the auxiliary Z*Y coefficient by induction; affine_recomposition uses it on the live finite contraction path to the original corrected row.
Admission basis proposed for independent review: escape-witness.
Utility kind is none: these are general algebraic identities for arbitrary
lattice data, finite embeddings and unbounded occupations or integer modes.
They are not bounded enumeration, a checker, a numerical reduction or a
certified finite instance. The finite sums implement general coefficients.
No novelty, substantive admission or downstream identityK completion is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource

open MvPolynomial LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField OriginalFourMChargeCoset SignedOscillatorWick
open OriginalChargedRowSource OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open FactorialFockMetric (weight weight_pos)
open FactorialFockQuadraticEstimate (gaussianCoefficient)
open NativeGaussianMoment (nativeMoment nativeMoment_step)
open ElementaryGaussianContraction (leftKernel rightKernel effectiveKernel)
open D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
  (sourceCovariance sourceMean sourceCovariance_symm correctionMatrix correctionMean
   affineLaurent_apply)
open D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
  (normalMatrix_symm restricted_reconstruct embedded_weight)
open D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
  (auxiliary_coefficient auxiliary_sum affineMoment_coefficient)
open D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
  (left_symm right_symm left_vanish coefficient_support)

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

private theorem join_degree {J : Type v} [Fintype J] [DecidableEq J]
    (d : I →₀ ℕ) (n : J →₀ ℕ) : (d.sumElim n).degree = d.degree+n.degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr]

private theorem join_weight {J : Type v} [DecidableEq J]
    (d : I →₀ ℕ) (n : J →₀ ℕ) : weight (d.sumElim n) = weight d * weight n := by
  exact Finsupp.prod_sumElim d n (fun _ k => k.factorial)

private theorem unit_weight (k : ℕ) : weight (Finsupp.single () k) = k.factorial := by
  simp [weight, Finsupp.prod_single_index]

private theorem weight_ne_zero {J : Type v} [DecidableEq J] (d : J →₀ ℕ) :
    (weight d : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (weight_pos d))

/-- The finite auxiliary sum, converted back to its native coefficient.
This helper is consumed in the right auxiliary summation below. -/
private theorem auxiliary_coefficient_sum {J : Type v} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (mu : J → ℂ) (hs : ∀ i j, A i j = A j i)
    (d : J →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    (∑ k ∈ Finset.range (N+1),
      gaussianCoefficient (affineKernel A mu) (d.sumElim (Finsupp.single () k))) =
      affineCoefficient A mu d := by
  apply mul_left_cancel₀ (weight_ne_zero d)
  rw [Finset.mul_sum]
  simp_rw [← auxiliary_coefficient]
  rw [auxiliary_sum A mu hs d N hN, affineMoment_coefficient]

private def homR (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    Matrix I (I ⊕ Unit) ℂ := fun i x => match x with
  | .inl j => (1 : Matrix I I ℂ) i j
  | .inr _ => sourceMean D a label i

private def homQ (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    Matrix ((I ⊕ I) ⊕ Unit) ((I ⊕ I) ⊕ Unit) ℂ :=
  affineKernel (fun v w => normalMatrix D label (.inr v) (.inr w))
    (fun v => normalMean D a label (.inr v))

private def homS (D : LatticeData) (label : I ↪ Index D) :
    Matrix (I ⊕ Unit) ((I ⊕ I) ⊕ Unit) ℂ := fun x y => match x,y with
  | .inl i, .inl v => normalMatrix D label (.inl i) (.inr v)
  | .inr _, .inr _ => 1
  | _, _ => 0

private def homLeft (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :=
  leftKernel (sourceCovariance D label) (homR D a label)

private def homRight (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :=
  rightKernel (homQ D a label) (homS D label)

private def homEffective (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :=
  effectiveKernel (sourceCovariance D label) (homQ D a label)
    (homR D a label) (homS D label)

private theorem homQ_symm (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    ∀ i j, homQ D a label i j = homQ D a label j i := by
  exact left_symm _ _ (fun i j => normalMatrix_symm D label (.inr i) (.inr j))

private theorem homRight_symm (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    ∀ i j, homRight D a label i j = homRight D a label j i :=
  right_symm _ _ (homQ_symm D a label)

/-- Associativity embedding fixing the auxiliary coordinate. -/
private def assocEmbedding {A : Type u} {B : Type v} :
    ((A ⊕ B) ⊕ Unit) ↪ A ⊕ (B ⊕ Unit) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr j) => .inr (.inl j)
    | .inr z => .inr (.inr z)
  inj' := by
    rintro ((i | j) | z) ((k | l) | w) h <;> simp_all

private theorem assoc_occupation {A : Type u} {B : Type v}
    (d : A →₀ ℕ) (n : B →₀ ℕ) (k : ℕ) :
    ((d.sumElim n).sumElim (Finsupp.single () k)).mapDomain assocEmbedding =
      d.sumElim (n.sumElim (Finsupp.single () k)) := by
  ext (i | (j | z))
  · exact Finsupp.mapDomain_apply_of_injective assocEmbedding.injective _ (.inl (.inl i))
  · exact Finsupp.mapDomain_apply_of_injective assocEmbedding.injective _ (.inl (.inr j))
  · exact Finsupp.mapDomain_apply_of_injective assocEmbedding.injective _ (.inr z)

private theorem homLeft_pullback (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    (fun i j => homLeft D a label (assocEmbedding i) (assocEmbedding j)) =
      affineKernel (correctionMatrix D label) (correctionMean D a label) := by
  funext x y
  rcases x with (i | i) | z <;> rcases y with (j | j) | w <;>
    simp [homLeft, homR, assocEmbedding, correctionMatrix, correctionMean,
      affineKernel, leftKernel, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

private theorem homLeft_coefficient (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (m : ℕ) :
    gaussianCoefficient (homLeft D a label)
        (d.sumElim (delta.sumElim (Finsupp.single () m))) =
      gaussianCoefficient (affineKernel (correctionMatrix D label) (correctionMean D a label))
        ((d.sumElim delta).sumElim (Finsupp.single () m)) := by
  rw [← assoc_occupation, InfiniteGaussianFock.gaussianCoefficient_enlarge _
    assocEmbedding assocEmbedding.injective, homLeft_pullback]

/-- The normal Gaussian embeds with Z occupation zero. -/
private def normalEmbedding :
    ((I ⊕ (I ⊕ I)) ⊕ Unit) ↪ (I ⊕ Unit) ⊕ ((I ⊕ I) ⊕ Unit) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr v) => .inr (.inl v)
    | .inr z => .inr (.inr z)
  inj' := by
    rintro ((i | j) | z) ((k | l) | w) h <;> simp_all

private theorem normal_embedding_occupation (delta h l : I →₀ ℕ) (k : ℕ) :
    ((threeOccupation delta h l).sumElim (Finsupp.single () k)).mapDomain normalEmbedding =
      (delta.sumElim (Finsupp.single () 0)).sumElim
        ((h.sumElim l).sumElim (Finsupp.single () k)) := by
  ext ((i | z) | (v | w))
  · exact Finsupp.mapDomain_apply_of_injective normalEmbedding.injective _ (.inl (.inl i))
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp [Finsupp.sumElim_apply]
    · rintro ⟨((i | v) | w), he⟩ <;> cases he
  · exact Finsupp.mapDomain_apply_of_injective normalEmbedding.injective _ (.inl (.inr v))
  · exact Finsupp.mapDomain_apply_of_injective normalEmbedding.injective _ (.inr w)

private theorem homRight_pullback (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    (fun i j => homRight D a label (normalEmbedding i) (normalEmbedding j)) =
      affineKernel (normalMatrix D label) (normalMean D a label) := by
  funext x y
  rcases x with (i | (i | i)) | z <;> rcases y with (j | (j | j)) | w <;>
    rfl

private def leftCoefficient (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d delta : I →₀ ℕ) (m : ℕ) : ℂ :=
  gaussianCoefficient (homLeft D a label)
    (d.sumElim (delta.sumElim (Finsupp.single () m)))

private def normalCoefficient (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (delta h l : I →₀ ℕ) (t : ℕ) : ℂ :=
  gaussianCoefficient (affineKernel (normalMatrix D label) (normalMean D a label))
    ((threeOccupation delta h l).sumElim (Finsupp.single () t))

private def rightCoefficient (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (delta h l : I →₀ ℕ) (m k : ℕ) : ℂ :=
  gaussianCoefficient (homRight D a label)
    ((delta.sumElim (Finsupp.single () m)).sumElim
      ((h.sumElim l).sumElim (Finsupp.single () k)))

private theorem right_zero_auxiliary (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta h l : I →₀ ℕ) (k : ℕ) :
    rightCoefficient D a label delta h l 0 k = normalCoefficient D a label delta h l k := by
  unfold rightCoefficient normalCoefficient
  rw [← normal_embedding_occupation, InfiniteGaussianFock.gaussianCoefficient_enlarge _
    normalEmbedding normalEmbedding.injective, homRight_pullback]

/-- Native coefficient insertion at Z. Z has precisely the Y partner.
This is derived from gaussianCoefficient through nativeMoment_step. -/
private theorem right_auxiliary_moment_step (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta h l : I →₀ ℕ) (m k : ℕ) :
    nativeMoment (homRight D a label)
      ((delta.sumElim (Finsupp.single () (m+1))).sumElim
        ((h.sumElim l).sumElim (Finsupp.single () k))) =
      (k : ℂ) * nativeMoment (homRight D a label)
        ((delta.sumElim (Finsupp.single () m)).sumElim
          ((h.sumElim l).sumElim (Finsupp.single () (k-1)))) := by
  let r := (delta.sumElim (Finsupp.single () m)).sumElim
    ((h.sumElim l).sumElim (Finsupp.single () k))
  have ha : r + Finsupp.single (.inl (.inr ())) 1 =
      (delta.sumElim (Finsupp.single () (m+1))).sumElim
        ((h.sumElim l).sumElim (Finsupp.single () k)) := by
    ext ((i | z) | (v | w)) <;> simp [r, Finsupp.sumElim_apply, Finsupp.single_apply]
  have hs : r - Finsupp.single (.inr (.inr ())) 1 =
      (delta.sumElim (Finsupp.single () m)).sumElim
        ((h.sumElim l).sumElim (Finsupp.single () (k-1))) := by
    ext ((i | z) | (v | w)) <;> simp [r, Finsupp.sumElim_apply, Finsupp.single_apply]
  have he := nativeMoment_step (homRight D a label) (homRight_symm D a label)
    r (.inl (.inr ()))
  rw [ha] at he
  simpa [homRight, rightKernel, homS, Matrix.transpose_apply,
    Fintype.sum_sum_type, r, Finsupp.sumElim_apply, hs] using he

private theorem right_auxiliary_zero (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta h l : I →₀ ℕ) (m : ℕ) :
    rightCoefficient D a label delta h l (m+1) 0 = 0 := by
  have he := right_auxiliary_moment_step D a label delta h l m 0
  rw [nativeMoment] at he
  simp only [Nat.cast_zero, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (weight_ne_zero _)

private theorem right_auxiliary_succ (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta h l : I →₀ ℕ) (m k : ℕ) :
    (m+1 : ℂ) * rightCoefficient D a label delta h l (m+1) (k+1) =
      rightCoefficient D a label delta h l m k := by
  have he := right_auxiliary_moment_step D a label delta h l m (k+1)
  simp only [nativeMoment, join_weight, unit_weight, Nat.add_sub_cancel,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at he
  let c : ℂ := (weight delta : ℂ) * (m.factorial : ℂ) *
    (weight (h.sumElim l) : ℂ) * (k.factorial : ℂ) * (k+1 : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (weight_ne_zero delta)
      (by exact_mod_cast Nat.factorial_ne_zero m)) (weight_ne_zero _))
      (by exact_mod_cast Nat.factorial_ne_zero k))
      (by exact_mod_cast Nat.succ_ne_zero k)
  apply mul_left_cancel₀ hc
  change c * ((m+1 : ℂ) * gaussianCoefficient _ _) = c * gaussianCoefficient _ _
  convert he using 1 <;> dsimp [c] <;> simp only [join_weight, Nat.cast_mul] <;> ring

/-- EXACT Z*Y factorization. No auxiliary support premise is assumed.
The m! denominator is the ordinary exponential coefficient, including m=0. -/
private theorem right_auxiliary_factorization (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (delta h l : I →₀ ℕ) (m k : ℕ) :
    rightCoefficient D a label delta h l m k =
      if m ≤ k then normalCoefficient D a label delta h l (k-m) / (m.factorial : ℂ)
      else 0 := by
  induction m generalizing k with
  | zero => simp [right_zero_auxiliary]
  | succ m ih =>
    cases k with
    | zero => simp [right_auxiliary_zero]
    | succ k =>
      have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      apply mul_left_cancel₀ hm
      rw [right_auxiliary_succ, ih]
      by_cases hmk : m ≤ k
      · rw [if_pos hmk, if_pos (Nat.succ_le_succ hmk)]
        simp only [Nat.succ_sub_succ_eq_sub, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hf, hm] <;> ring
      · rw [if_neg hmk, if_neg (by omega : ¬ m+1 ≤ k+1), mul_zero]

private theorem homR_mul_homS (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (i : I) (y : (I ⊕ I) ⊕ Unit) :
    (homR D a label * homS D label) i y = match y with
      | .inl v => normalMatrix D label (.inl i) (.inr v)
      | .inr _ => sourceMean D a label i := by
  cases y <;> simp [Matrix.mul_apply, Fintype.sum_sum_type,
    homR, homS, Matrix.one_apply]

/-- The effective kernel is the ORIGINAL charged corrected affine kernel,
under the stated injective associativity relabeling. -/
private theorem homEffective_pullback (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) :
    (fun i j => homEffective D a label (assocEmbedding i) (assocEmbedding j)) =
      affineKernel (correctedMatrix D label) (correctedMean D a label) := by
  funext x y
  rcases x with (i | (i | i)) | z <;> rcases y with (j | (j | j)) | w <;>
    simp [homEffective, effectiveKernel, assocEmbedding,
      Matrix.transpose_apply, homR_mul_homS, homQ, affineKernel,
      leftKernel, correctedMatrix, correctedMean, normalMatrix, normalMean,
      Matrix.mul_apply, Fintype.sum_sum_type, homR, homS, Matrix.one_apply]

private theorem leftCoefficient_vanish (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) (m : ℕ)
    (hm : d.degree < delta.degree+m) : leftCoefficient D a label d delta m = 0 := by
  have he := left_vanish (sourceCovariance D label) (homR D a label)
    (sourceCovariance_symm D label) d (delta.sumElim (Finsupp.single () m))
    (by simpa only [join_degree, Finsupp.degree_single] using hm)
  rw [nativeMoment] at he
  exact (mul_eq_zero.mp he).resolve_left (weight_ne_zero _)

/-- Finite left auxiliary support permits the SAME upper bound d.degree for
all residual occupations. The larger normal affine bound is removed by vanishing. -/
private theorem leftCoefficient_sum (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta : I →₀ ℕ) :
    (∑ m ∈ Finset.range (d.degree+1), leftCoefficient D a label d delta m) =
      affineCoefficient (correctionMatrix D label) (correctionMean D a label)
        (d.sumElim delta) := by
  classical
  calc
    _ = ∑ m ∈ Finset.range ((d.sumElim delta).degree+1),
        leftCoefficient D a label d delta m := by
      apply Finset.sum_subset
        (Finset.range_mono (by rw [join_degree]; omega))
      intro m hm hout
      apply leftCoefficient_vanish
      have hn : ¬ m < d.degree+1 := by simpa only [Finset.mem_range] using hout
      omega
    _ = _ := by
      unfold affineCoefficient
      apply Finset.sum_congr rfl
      intro m hm
      exact homLeft_coefficient D a label d delta m

/-- Explicit finite decomposition n=(delta,m), with BOTH forward and inverse
membership proofs. The rectangular index set introduces only zero summands. -/
private theorem split_shared_sum (N : ℕ) (c : ((I ⊕ Unit) →₀ ℕ) → ℂ)
    (hc : ∀ n, N < n.degree → c n = 0) :
    (∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) N).toFinset, c n) =
      ∑ delta ∈ (Finsupp.finite_of_degree_le (σ := I) N).toFinset,
        ∑ m ∈ Finset.range (N+1), c (delta.sumElim (Finsupp.single () m)) := by
  classical
  symm
  rw [← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1.sumElim (Finsupp.single () p.2))
    ?_ ?_ ?_ ?_
  · intro p hp hn
    have hle : (p.1.sumElim (Finsupp.single () p.2)).degree ≤ N := by
      by_contra hh
      exact hn (hc _ (Nat.lt_of_not_ge hh))
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hle
  · intro p hp hn q hq hn' he
    apply Prod.ext
    · ext i
      exact congrArg (fun n : (I ⊕ Unit) →₀ ℕ => n (.inl i)) he
    · simpa only [Finsupp.sumElim_inr, Finsupp.single_eq_same] using
        congrArg (fun n : (I ⊕ Unit) →₀ ℕ => n (.inr ())) he
  · intro n hn hne
    let delta := n.comapDomain Sum.inl Sum.inl_injective.injOn
    let m := n (.inr ())
    have hj : delta.sumElim (Finsupp.single () m) = n := by
      ext (i | z)
      · rfl
      · cases z; simp [m, Finsupp.sumElim_apply]
    have hdeg : delta.degree+m ≤ N := by
      have hnd : n.degree ≤ N := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
      rw [← hj, join_degree, Finsupp.degree_single] at hnd
      exact hnd
    have hp : (delta,m) ∈
        (Finsupp.finite_of_degree_le (σ := I) N).toFinset ×ˢ Finset.range (N+1) := by
      apply Finset.mem_product.mpr
      constructor
      · simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using
          (show delta.degree ≤ N by omega)
      · exact Finset.mem_range.mpr (by omega)
    exact ⟨(delta,m),hp,by simpa only [hj] using hne,hj⟩
  · intro p hp hn
    rfl

/-- The frozen supplier is applied with its exact minimum bound, then
extended to the source bound using its proved two-sided support theorem.
The RHS is transported by gaussianCoefficient_enlarge, not asserted equal. -/
private theorem homogeneous_contraction (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) (k : ℕ) :
    (∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) d.degree).toFinset,
      (weight n : ℂ) * gaussianCoefficient (homLeft D a label) (d.sumElim n) *
        gaussianCoefficient (homRight D a label)
          (n.sumElim ((h.sumElim l).sumElim (Finsupp.single () k)))) =
      gaussianCoefficient (affineKernel (correctedMatrix D label) (correctedMean D a label))
        ((threeOccupation d h l).sumElim (Finsupp.single () k)) := by
  classical
  let e := (h.sumElim l).sumElim (Finsupp.single () k)
  have he := ElementaryGaussianContraction.coefficient_contraction
    (sourceCovariance D label) (homQ D a label) (homR D a label) (homS D label)
    (sourceCovariance_symm D label) (homQ_symm D a label) d e
  have hsub :
      (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) (min d.degree e.degree)).toFinset ⊆
        (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) d.degree).toFinset := by
    intro n hn
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn ⊢
    exact hn.trans (Nat.min_le_left _ _)
  have hsum :
      (∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) (min d.degree e.degree)).toFinset,
        (weight n : ℂ) * gaussianCoefficient (homLeft D a label) (d.sumElim n) *
          gaussianCoefficient (homRight D a label) (n.sumElim e)) =
      ∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) d.degree).toFinset,
        (weight n : ℂ) * gaussianCoefficient (homLeft D a label) (d.sumElim n) *
          gaussianCoefficient (homRight D a label) (n.sumElim e) := by
    apply Finset.sum_subset hsub
    intro n hn hout
    apply coefficient_support _ _ _ _ (sourceCovariance_symm D label)
      (homQ_symm D a label)
    have hh : ¬ n.degree ≤ min d.degree e.degree := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hout
    omega
  rw [← hsum]
  change (∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) (min d.degree e.degree)).toFinset,
    (weight n : ℂ) * gaussianCoefficient (homLeft D a label) (d.sumElim n) *
      gaussianCoefficient (homRight D a label) (n.sumElim e)) =
    gaussianCoefficient (homEffective D a label) (d.sumElim e) at he
  rw [he]
  change gaussianCoefficient (homEffective D a label) (d.sumElim e) = _
  dsimp only [e]
  rw [← assoc_occupation, InfiniteGaussianFock.gaussianCoefficient_enlarge _
    assocEmbedding assocEmbedding.injective, homEffective_pullback]
  rfl

/-- Cancel shared m! BEFORE the finite Y summation. The upper bound is
N=d.degree+h.degree+l.degree, and m+delta.degree<=d.degree proves that the
remaining normal auxiliary range contains its entire normal affine support. -/
private theorem auxiliary_contraction_sum (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d delta h l : I →₀ ℕ) (m : ℕ) :
    (∑ k ∈ Finset.range (d.degree+(h.sumElim l).degree+1),
      (weight (delta.sumElim (Finsupp.single () m)) : ℂ) *
        leftCoefficient D a label d delta m * rightCoefficient D a label delta h l m k) =
      (weight delta : ℂ) * leftCoefficient D a label d delta m *
        affineCoefficient (normalMatrix D label) (normalMean D a label)
          (threeOccupation delta h l) := by
  classical
  by_cases hdm : delta.degree+m ≤ d.degree
  · let N := d.degree+(h.sumElim l).degree
    have hm : m ≤ N := by dsimp only [N]; omega
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hterm (k : ℕ) :
        (weight (delta.sumElim (Finsupp.single () m)) : ℂ) *
          leftCoefficient D a label d delta m * rightCoefficient D a label delta h l m k =
        if m ≤ k then (weight delta : ℂ) * leftCoefficient D a label d delta m *
          normalCoefficient D a label delta h l (k-m) else 0 := by
      rw [right_auxiliary_factorization, join_weight, unit_weight, Nat.cast_mul]
      by_cases hmk : m ≤ k
      · rw [if_pos hmk, if_pos hmk]
        field_simp [hf] <;> ring
      · rw [if_neg hmk, if_neg hmk, mul_zero]
    simp_rw [hterm]
    change (∑ k ∈ Finset.range (N+1), _) = _
    have hN : N+1 = m+(N-m+1) := by omega
    rw [hN, Finset.sum_range_add]
    have hzero : (∑ k ∈ Finset.range m,
        if m ≤ k then (weight delta : ℂ) * leftCoefficient D a label d delta m *
          normalCoefficient D a label delta h l (k-m) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (by have := Finset.mem_range.mp hk; omega)
    rw [hzero, zero_add]
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    rw [← Finset.mul_sum]
    congr 1
    apply auxiliary_coefficient_sum _ _ (normalMatrix_symm D label)
    simp only [threeOccupation, join_degree]
    dsimp only [N]
    rw [join_degree]
    omega
  · rw [leftCoefficient_vanish D a label d delta m (Nat.lt_of_not_ge hdm)]
    simp

/-- The finite affine contraction, with no recomposition, recurrence,
boundary or support premise. All support and auxiliary factorial cancellation
are proved above from the native Gaussian coefficients and frozen supplier.
The ordinary coefficients retain their finite source-degree bound. -/
private theorem affine_recomposition (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    (∑ delta ∈ (Finsupp.finite_of_degree_le (σ := I) d.degree).toFinset,
      (weight delta : ℂ) * affineCoefficient (correctionMatrix D label)
        (correctionMean D a label) (d.sumElim delta) *
          affineCoefficient (normalMatrix D label) (normalMean D a label)
            (threeOccupation delta h l)) =
      affineCoefficient (correctedMatrix D label) (correctedMean D a label)
        (threeOccupation d h l) := by
  classical
  let N := d.degree+(h.sumElim l).degree
  let c := fun (k : ℕ) (n : (I ⊕ Unit) →₀ ℕ) =>
    (weight n : ℂ) * gaussianCoefficient (homLeft D a label) (d.sumElim n) *
      gaussianCoefficient (homRight D a label)
        (n.sumElim ((h.sumElim l).sumElim (Finsupp.single () k)))
  have hc (k : ℕ) (n : (I ⊕ Unit) →₀ ℕ) (hn : d.degree < n.degree) : c k n = 0 := by
    have he := left_vanish (sourceCovariance D label) (homR D a label)
      (sourceCovariance_symm D label) d n hn
    rw [nativeMoment] at he
    have hz := (mul_eq_zero.mp he).resolve_left (weight_ne_zero _)
    simp only [c, homLeft, hz, mul_zero, zero_mul]
  have hnative :
      (∑ k ∈ Finset.range (N+1),
        ∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) d.degree).toFinset, c k n) =
      affineCoefficient (correctedMatrix D label) (correctedMean D a label)
        (threeOccupation d h l) := by
    unfold affineCoefficient
    have hdegree : (threeOccupation d h l).degree = N := by
      simp only [threeOccupation, join_degree, N]
    rw [hdegree]
    apply Finset.sum_congr rfl
    intro k hk
    exact homogeneous_contraction D a label d h l k
  have hsplit (k : ℕ) :
      (∑ n ∈ (Finsupp.finite_of_degree_le (σ := I ⊕ Unit) d.degree).toFinset, c k n) =
        ∑ delta ∈ (Finsupp.finite_of_degree_le (σ := I) d.degree).toFinset,
          ∑ m ∈ Finset.range (d.degree+1), c k (delta.sumElim (Finsupp.single () m)) :=
    split_shared_sum d.degree (c k) (hc k)
  rw [← hnative]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro delta hdelta
  rw [Finset.sum_comm]
  change _ = ∑ m ∈ Finset.range (d.degree+1),
    ∑ k ∈ Finset.range (N+1),
      (weight (delta.sumElim (Finsupp.single () m)) : ℂ) *
        leftCoefficient D a label d delta m * rightCoefficient D a label delta h l m k
  dsimp only [N]
  simp_rw [auxiliary_contraction_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, leftCoefficient_sum]

/-- Recomposition of the finite amplitude, retaining the source factorial. -/
theorem recompositionAmplitude_eq (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    recompositionAmplitude D a label d h l =
      (weight d : ℂ) * affineCoefficient (correctedMatrix D label)
        (correctedMean D a label) (threeOccupation d h l) := by
  unfold recompositionAmplitude
  rw [affine_recomposition]

/-- Literal original corrected Gaussian Laurent row, including empty K and
all integer exponents. The only determinant hypothesis is the original hu.
No neutral Corr substitution or complex-z/Laurent transfer occurs here.
The two-row sewing identity is a separate downstream statement. -/
theorem original_corrected_gaussian_row (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (alpha beta gamma : Index D →₀ ℕ) (e : ℤ) :
    wick D (monomial gamma 1)
      (oscillatorCorrected D hu a e (monomial alpha 1) (monomial beta 1)) =
      let K := rowSupport D alpha beta gamma
      let label := supportLabel D K
      (weight alpha : ℂ) * (weight beta : ℂ) * (weight gamma : ℂ) *
        affineLaurent (correctedMatrix D label) (correctedMean D a label)
          (normalWeight D label)
          (threeOccupation (restricted D K alpha) (restricted D K beta)
            (restricted D K gamma)) (e+chargeNorm D a) := by
  classical
  let K := rowSupport D alpha beta gamma
  let label := supportLabel D K
  let d := restricted D K alpha
  let h := restricted D K beta
  let l := restricted D K gamma
  have ha : alpha.support ⊆ K := Finset.subset_union_left.trans Finset.subset_union_left
  have hra := restricted_reconstruct D K alpha ha
  have hwd : weight d = weight alpha := by
    calc
      _ = weight (d.embDomain label) := (embedded_weight D label d).symm
      _ = _ := congrArg weight hra
  rw [original_corrected_row_finite_reduction]
  change (weight beta : ℂ) * (weight gamma : ℂ) *
    (if e+chargeNorm D a = Finsupp.weight (normalWeight D label) (threeOccupation d h l)
      then recompositionAmplitude D a label d h l else 0) =
    (weight alpha : ℂ) * (weight beta : ℂ) * (weight gamma : ℂ) *
      affineLaurent (correctedMatrix D label) (correctedMean D a label)
        (normalWeight D label) (threeOccupation d h l) (e+chargeNorm D a)
  rw [recompositionAmplitude_eq, hwd]
  rw [affineLaurent_apply]
  by_cases he : e+chargeNorm D a = Finsupp.weight (normalWeight D label) (threeOccupation d h l)
  · simp only [he, ite_true]
    ring
  · simp only [he, Ne.symm he, ite_false, mul_zero]

end D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
