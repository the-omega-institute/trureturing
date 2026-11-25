/- GID: D5/S3/Quantum/Information/PartialTrace/LowRankPartialTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/PartialTrace/LowRankPartialTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the joint projection mass of two disjoint sites under a matrix rank cap. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

/-!
The Frobenius norm uses the unnormalized trace. Normalized partial traces
act as commuting Hilbert–Schmidt projections on disjoint tensor factors.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.LowRankPartialTrace

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteTraceDistance (exists_svd_sqrt_eigenvalues)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceLeft_add partialTraceLeft_kronecker)

private theorem frobenius_sq_entries {r c : Type*} [Fintype r] [Fintype c]
    (X : Matrix r c ℂ) : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem frobenius_sq_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) : ‖Matrix.diagonal d‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
  rw [Matrix.frobenius_norm_diagonal]
  exact PiLp.norm_sq_eq_of_L2 (fun _ : n => ℂ) (WithLp.toLp 2 d)

private theorem unitary_column_sq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, ‖U.val j i‖ ^ 2 = 1 := by
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  have hii := congrArg (fun X : Matrix n n ℂ => X i i) hU
  apply Complex.ofReal_injective
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_one] using hii

private theorem frobenius_sq_mul_unitaries {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n ℂ) (D : Matrix n n ℂ) :
    ‖U.val * D * V.valᴴ‖ ^ 2 = ‖D‖ ^ 2 := by
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  have hV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.prop
  apply Complex.ofReal_injective
  rw [frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace]
  calc
    _ = (V.val * (Dᴴ * (U.valᴴ * U.val) * D) * V.valᴴ).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (V.val * (Dᴴ * D) * V.valᴴ).trace := by rw [hU, Matrix.mul_one]
    _ = (Dᴴ * D).trace := by rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

variable {A B : Type*} [Fintype A] [Fintype B]

private def partialTraceLeftLinear :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' z X := by
    ext b c
    simp [partialTraceLeft, Finset.mul_sum]

/-- The partial trace of the outer product is the product of the reshaped
vectors. The columns of these rectangular matrices are indexed by `A`. -/
private theorem frobenius_partialTraceLeft_outer_le_one (u v : A × B → ℂ)
    (hu : ∑ p, ‖u p‖ ^ 2 = 1) (hv : ∑ p, ‖v p‖ ^ 2 = 1) :
    ‖partialTraceLeft (Matrix.vecMulVec u (fun p => star (v p)))‖ ≤ 1 := by
  let X : Matrix B A ℂ := fun b a => u (a, b)
  let Y : Matrix B A ℂ := fun b a => v (a, b)
  have htrace : partialTraceLeft (Matrix.vecMulVec u (fun p => star (v p))) = X * Yᴴ := by
    apply Matrix.ext
    intro b c
    rfl
  have hX : ‖X‖ = 1 := (sq_eq_sq₀ (norm_nonneg X) zero_le_one).mp (by
    rw [frobenius_sq_entries, one_pow]
    change (∑ b : B, ∑ a : A, ‖u (a, b)‖ ^ 2) = 1
    exact (Fintype.sum_prod_type_right (fun p : A × B => ‖u p‖ ^ 2)).symm.trans hu)
  have hY : ‖Y‖ = 1 := (sq_eq_sq₀ (norm_nonneg Y) zero_le_one).mp (by
    rw [frobenius_sq_entries, one_pow]
    change (∑ b : B, ∑ a : A, ‖v (a, b)‖ ^ 2) = 1
    exact (Fintype.sum_prod_type_right (fun p : A × B => ‖v p‖ ^ 2)).symm.trans hv)
  rw [htrace]
  calc
    ‖X * Yᴴ‖ ≤ ‖X‖ * ‖Yᴴ‖ := Matrix.frobenius_norm_mul X Yᴴ
    _ = 1 := by rw [Matrix.frobenius_norm_conjTranspose, hX, hY, mul_one]

variable [DecidableEq A] [DecidableEq B]

/-- The unnormalized partial trace obeys the Frobenius bound with the actual
matrix rank, for arbitrary finite complex matrices. -/
theorem frobenius_sq_partialTraceLeft_le_rank_mul
    (K : Matrix (A × B) (A × B) ℂ) :
    ‖partialTraceLeft K‖ ^ 2 ≤ (K.rank : ℝ) * ‖K‖ ^ 2 := by
  classical
  let H : (Kᴴ * K).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self K).1
  let s : A × B → ℝ := fun i => Real.sqrt (H.eigenvalues i)
  let D : Matrix (A × B) (A × B) ℂ := Matrix.diagonal (fun i => (s i : ℂ))
  obtain ⟨U, V, hSvd⟩ := exists_svd_sqrt_eigenvalues K
  have hK : K = U.val * D * V.valᴴ := hSvd
  let support : Finset (A × B) := Finset.univ.filter (fun i => s i ≠ 0)
  let outer : A × B → Matrix (A × B) (A × B) ℂ := fun i =>
    Matrix.vecMulVec (fun p => U.val p i) (fun p => star (V.val p i))
  have hzero (i : A × B) (hi : i ∉ support) : s i = 0 := by
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩)
  have hs_nonneg (i : A × B) : 0 ≤ s i := Real.sqrt_nonneg _
  have hD_rank : D.rank = support.card := by
    change (Matrix.diagonal (fun i => (s i : ℂ))).rank = _
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    apply congrArg Finset.card
    ext i
    simp [support]
  have hrank : K.rank = support.card := by
    have hV : IsUnit (V.valᴴ).det := Matrix.UnitaryGroup.det_isUnit (star V)
    rw [hK, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit U), hD_rank]
  have hF : ‖K‖ ^ 2 = ∑ i ∈ support, (s i) ^ 2 := by
    calc
      ‖K‖ ^ 2 = ‖D‖ ^ 2 := by rw [hK, frobenius_sq_mul_unitaries]
      _ = ∑ i, (s i) ^ 2 := by
        change ‖Matrix.diagonal (fun i => (s i : ℂ))‖ ^ 2 = _
        rw [frobenius_sq_diagonal]
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs_nonneg i)]
      _ = ∑ i ∈ support, (s i) ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        simp [hzero i hi]
  have hsum : K = ∑ i ∈ support, (s i : ℂ) • outer i := by
    calc
      K = ∑ i, (s i : ℂ) • outer i := by
        apply Matrix.ext
        intro p q
        rw [hK, Matrix.mul_apply, Matrix.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp only [D, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.smul_apply,
          smul_eq_mul, outer, Matrix.vecMulVec_apply]
        ring
      _ = ∑ i ∈ support, (s i : ℂ) • outer i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        simp [hzero i hi]
  have htraceSum : partialTraceLeft K =
      ∑ i ∈ support, (s i : ℂ) • partialTraceLeft (outer i) := by
    change partialTraceLeftLinear K =
      ∑ i ∈ support, (s i : ℂ) • partialTraceLeftLinear (outer i)
    rw [hsum, map_sum]
    simp only [map_smul]
  have houter (i : A × B) : ‖partialTraceLeft (outer i)‖ ≤ 1 :=
    frobenius_partialTraceLeft_outer_le_one _ _
      (unitary_column_sq_sum U i) (unitary_column_sq_sum V i)
  have hnorm : ‖partialTraceLeft K‖ ≤ ∑ i ∈ support, s i := by
    rw [htraceSum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs_nonneg i)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (houter i) (hs_nonneg i)
  calc
    ‖partialTraceLeft K‖ ^ 2 ≤ (∑ i ∈ support, s i) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (Finset.sum_nonneg fun i _ => hs_nonneg i)).mpr hnorm
    _ ≤ (support.card : ℝ) * ∑ i ∈ support, (s i) ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := support) (f := s)
    _ = (K.rank : ℝ) * ‖K‖ ^ 2 := by rw [hrank, hF]

/-- Tensoring with a first-factor identity multiplies the norm square by
the dimension of that factor. -/
private theorem frobenius_sq_one_kronecker (X : Matrix B B ℂ) :
    ‖(1 : Matrix A A ℂ) ⊗ₖ X‖ ^ 2 = (Fintype.card A : ℝ) * ‖X‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, frobenius_norm_sq_eq_trace,
    frobenius_norm_sq_eq_trace, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker, Matrix.trace_one]

/-- The norm of the actual normalized site projection from the Petz argument. -/
private theorem frobenius_sq_normalized_partialTraceLeft [Nonempty A]
    (K : Matrix (A × B) (A × B) ℂ) :
    ‖(Fintype.card A : ℂ)⁻¹ • ((1 : Matrix A A ℂ) ⊗ₖ partialTraceLeft K)‖ ^ 2 =
      ‖partialTraceLeft K‖ ^ 2 / (Fintype.card A : ℝ) := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  rw [norm_smul, norm_inv, Complex.norm_natCast, mul_pow, frobenius_sq_one_kronecker]
  field_simp [hcard]

/-- The Petz projection bound with a supplied rank cap `m`. -/
private theorem frobenius_sq_normalized_partialTraceLeft_le [Nonempty A]
    (K : Matrix (A × B) (A × B) ℂ) {m : ℕ} (hm : K.rank ≤ m) :
    ‖(Fintype.card A : ℂ)⁻¹ • ((1 : Matrix A A ℂ) ⊗ₖ partialTraceLeft K)‖ ^ 2 ≤
      ((m : ℝ) / (Fintype.card A : ℝ)) * ‖K‖ ^ 2 := by
  have hm' : (K.rank : ℝ) ≤ m := by exact_mod_cast hm
  have hbound := (frobenius_sq_partialTraceLeft_le_rank_mul K).trans
    (mul_le_mul_of_nonneg_right hm' (sq_nonneg ‖K‖))
  rw [frobenius_sq_normalized_partialTraceLeft]
  calc
    _ ≤ ((m : ℝ) * ‖K‖ ^ 2) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The Hilbert–Schmidt expectation onto matrices acting trivially on the first factor. -/
def expectation {S T : Type*} [Fintype S] [DecidableEq S] :
    Matrix (S × T) (S × T) ℂ →ₗ[ℂ] Matrix (S × T) (S × T) ℂ where
  toFun X := (Fintype.card S : ℂ)⁻¹ • ((1 : Matrix S S ℂ) ⊗ₖ partialTraceLeft X)
  map_add' X Y := by
    ext ⟨s,t⟩ ⟨u,v⟩
    simp [partialTraceLeft, Finset.sum_add_distrib, mul_add]
  map_smul' z X := by
    ext ⟨s,t⟩ ⟨u,v⟩
    simp only [Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul, partialTraceLeft,
      ← Finset.mul_sum, RingHom.id_apply]
    ring

private theorem expectation_apply {S T : Type*} [Fintype S] [DecidableEq S]
    (X : Matrix (S × T) (S × T) ℂ) (s u : S) (t v : T) :
    expectation X (s,t) (u,v) =
      if s = u then (Fintype.card S : ℂ)⁻¹ * ∑ a, X (a,t) (a,v) else 0 := by
  by_cases h : s = u <;>
    simp [expectation, h, partialTraceLeft]

private theorem expectation_tensor {S T : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (Y : Matrix T T ℂ) : expectation ((1 : Matrix S S ℂ) ⊗ₖ Y) = 1 ⊗ₖ Y := by
  change (Fintype.card S : ℂ)⁻¹ • Matrix.kronecker (1 : Matrix S S ℂ)
    (partialTraceLeft (Matrix.kronecker (1 : Matrix S S ℂ) Y)) = _
  rw [partialTraceLeft_kronecker, Matrix.trace_one]
  change (Fintype.card S : ℂ)⁻¹ •
    ((1 : Matrix S S ℂ) ⊗ₖ ((Fintype.card S : ℂ) • Y)) = _
  rw [Matrix.kronecker_smul, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

private def pairing {S : Type*} [Fintype S] (X Y : Matrix S S ℂ) : ℂ :=
  (Xᴴ * Y).trace

private theorem pairing_expectation {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]
    (X Y : Matrix (S × T) (S × T) ℂ) :
    pairing X (expectation Y) = pairing (expectation X) Y := by
  have hstar : partialTraceLeft Xᴴ = (partialTraceLeft X)ᴴ := by
    ext i j
    simp [partialTraceLeft, star_sum]
  have hc : star ((Fintype.card S : ℂ)⁻¹) = (Fintype.card S : ℂ)⁻¹ := by simp
  change trace (Xᴴ * ((Fintype.card S : ℂ)⁻¹ • ((1 : Matrix S S ℂ) ⊗ₖ
    partialTraceLeft Y))) = trace
    (((Fintype.card S : ℂ)⁻¹ • ((1 : Matrix S S ℂ) ⊗ₖ partialTraceLeft X))ᴴ * Y)
  rw [Matrix.mul_smul, Matrix.conjTranspose_smul, hc, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.trace_mul_comm ((1 : Matrix S S ℂ) ⊗ₖ
      (partialTraceLeft X)ᴴ) Y, Matrix.trace_mul_one_kron_right, Matrix.trace_mul_one_kron_right]
  change (Fintype.card S : ℂ)⁻¹ * trace (partialTraceLeft Xᴴ * partialTraceLeft Y) =
    (Fintype.card S : ℂ)⁻¹ * trace (partialTraceLeft Y * (partialTraceLeft X)ᴴ)
  rw [hstar, Matrix.trace_mul_comm]

private theorem pairing_reindex {S T : Type*} [Fintype S] [Fintype T]
    (e : T ≃ S) (X Y : Matrix S S ℂ) :
    pairing (X.submatrix e e) (Y.submatrix e e) = pairing X Y := by
  change trace ((Xᴴ.submatrix e e) * (Y.submatrix e e)) = _
  rw [Matrix.submatrix_mul_equiv]
  exact e.sum_comp (fun i => (Xᴴ * Y) i i)

private theorem projection_pythagoras {S : Type*} [Fintype S]
    (P : Matrix S S ℂ →ₗ[ℂ] Matrix S S ℂ)
    (hP : ∀ X, P (P X) = P X) (hSym : ∀ X Y, pairing X (P Y) = pairing (P X) Y)
    (X : Matrix S S ℂ) : ‖X - P X‖ ^ 2 = ‖X‖ ^ 2 - ‖P X‖ ^ 2 := by
  have h := hSym X (P X)
  rw [hP] at h
  have h' := (hSym (P X) X).symm
  rw [hP] at h'
  apply Complex.ofReal_injective
  simp only [pairing] at h h'
  simp only [Complex.ofReal_sub, frobenius_norm_sq_eq_trace, Matrix.conjTranspose_sub,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, h, h']
  ring

private def expectationAlong {S T U : Type*} [Fintype S] [DecidableEq S]
    (e : S × T ≃ U) : Matrix U U ℂ →ₗ[ℂ] Matrix U U ℂ where
  toFun X := (expectation (X.submatrix e e)).submatrix e.symm e.symm
  map_add' X Y := by
    change (expectation (X.submatrix e e + Y.submatrix e e)).submatrix _ _ = _
    rw [map_add]
    rfl
  map_smul' z X := by
    change (expectation (z • X.submatrix e e)).submatrix _ _ = _
    rw [map_smul]
    rfl

private theorem expectationAlong_idem {S T U : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (e : S × T ≃ U) (X : Matrix U U ℂ) :
    expectationAlong e (expectationAlong e X) = expectationAlong e X := by
  have h (Y : Matrix (S × T) (S × T) ℂ) :
      (Y.submatrix e.symm e.symm).submatrix e e = Y := by
    ext i j
    simp
  change (expectation (((expectation (X.submatrix e e)).submatrix e.symm e.symm).submatrix
    e e)).submatrix _ _ = _
  rw [h]
  congr 1
  let Z := X.submatrix e e
  change expectation (expectation Z) = expectation Z
  change expectation ((Fintype.card S : ℂ)⁻¹ • ((1 : Matrix S S ℂ) ⊗ₖ
    partialTraceLeft Z)) = _
  rw [map_smul, expectation_tensor]
  rfl

private theorem expectationAlong_adjoint {S T U : Type*} [Fintype S] [Finite T] [Fintype U]
    [DecidableEq S] (e : S × T ≃ U) (X Y : Matrix U U ℂ) :
    pairing X (expectationAlong e Y) = pairing (expectationAlong e X) Y := by
  let : Fintype T := Fintype.ofFinite T
  have h (Z : Matrix U U ℂ) :
      (expectationAlong e Z).submatrix e e = expectation (Z.submatrix e e) := by
    ext i j
    simp [expectationAlong]
  rw [← pairing_reindex e X (expectationAlong e Y),
    ← pairing_reindex e (expectationAlong e X) Y, h, h, pairing_expectation]

section TwoSites

variable {C : Type*} [Fintype C]

private abbrev TensorMatrix (A B C : Type*) :=
  Matrix ((A × B) × C) ((A × B) × C) ℂ

private def firstSite (A B C : Type*) : A × (B × C) ≃ (A × B) × C :=
  (Equiv.prodAssoc A B C).symm

private def secondSite (A B C : Type*) : B × (A × C) ≃ (A × B) × C :=
  (Equiv.prodAssoc B A C).symm.trans ((Equiv.prodComm B A).prodCongr (Equiv.refl C))

/-- Trace out the first site and insert its normalized identity. -/
def expectA : TensorMatrix A B C →ₗ[ℂ] TensorMatrix A B C :=
  expectationAlong (firstSite A B C)

/-- Trace out the second site and insert its normalized identity. -/
def expectB : TensorMatrix A B C →ₗ[ℂ] TensorMatrix A B C :=
  expectationAlong (secondSite A B C)

omit [Fintype B] [DecidableEq B] [Fintype C] in
private theorem expectA_apply (X : TensorMatrix A B C) (a a' : A) (b b' : B) (c c' : C) :
    expectA X ((a,b),c) ((a',b'),c') =
      if a = a' then (Fintype.card A : ℂ)⁻¹ * ∑ i, X ((i,b),c) ((i,b'),c') else 0 :=
  expectation_apply _ a a' (b,c) (b',c')

omit [Fintype A] [DecidableEq A] [Fintype C] in
private theorem expectB_apply (X : TensorMatrix A B C) (a a' : A) (b b' : B) (c c' : C) :
    expectB X ((a,b),c) ((a',b'),c') =
      if b = b' then (Fintype.card B : ℂ)⁻¹ * ∑ j, X ((a,j),c) ((a',j),c') else 0 :=
  expectation_apply _ b b' (a,c) (a',c')

omit [Fintype C] in
private theorem expect_union (X : TensorMatrix A B C) :
    expectB (expectA X) = expectation X ∧ expectA (expectB X) = expectation X := by
  constructor <;> ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩ <;>
    by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp only [expectA_apply, expectB_apply, expectation_apply, Prod.mk.injEq, ha, hb,
      ite_true, ite_false, and_false, false_and, Finset.sum_const_zero, mul_zero,
      Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev, Fintype.sum_prod_type,
      ← Finset.mul_sum]
  · rw [Finset.sum_comm (f := fun j i => X ((i,j),c) ((i,j),c'))]
    ac_rfl
  · ac_rfl

private theorem two_site_complement [Nonempty A] [Nonempty B] (X : TensorMatrix A B C) :
    ‖X - expectA X - expectB (X - expectA X)‖ ^ 2 =
      ‖X‖ ^ 2 + ‖expectation X‖ ^ 2 - (‖expectA X‖ ^ 2 + ‖expectB X‖ ^ 2) := by
  have hA := projection_pythagoras (expectA : TensorMatrix A B C →ₗ[ℂ] _)
    (expectationAlong_idem _) (expectationAlong_adjoint _) X
  have hB (Y : TensorMatrix A B C) := projection_pythagoras (expectB : TensorMatrix A B C →ₗ[ℂ] _)
    (expectationAlong_idem _) (expectationAlong_adjoint _) Y
  have hDiff : expectB (X - expectA X) = expectB X - expectation X := by
    rw [map_sub, (expect_union X).1]
  have hUnion := hB (X - expectA X)
  rw [hA, hDiff] at hUnion
  have hOther := projection_pythagoras (expectA : TensorMatrix A B C →ₗ[ℂ] _)
    (expectationAlong_idem _) (expectationAlong_adjoint _) (expectB X)
  rw [(expect_union X).2] at hOther
  rw [hDiff]
  linarith only [hUnion, hOther]

private theorem two_site_mass_le [Nonempty A] [Nonempty B]
    (h : Fintype.card A = Fintype.card B) (X : TensorMatrix A B C)
    (hX : X.rank ≤ Fintype.card A) :
    ‖expectA X‖ ^ 2 + ‖expectB X‖ ^ 2 ≤
      (1 + (Fintype.card A : ℝ)⁻¹) * ‖X‖ ^ 2 := by
  let : DecidableEq C := Classical.decEq C
  have hpos : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hratio : (Fintype.card A : ℝ) / (Fintype.card (A × B) : ℝ) =
      (Fintype.card A : ℝ)⁻¹ := by
    rw [Fintype.card_prod, Nat.cast_mul, ← h]
    field_simp
  have hU : ‖expectation X‖ ^ 2 ≤ (Fintype.card A : ℝ)⁻¹ * ‖X‖ ^ 2 := by
    rw [← hratio]
    exact frobenius_sq_normalized_partialTraceLeft_le X hX
  have hP := two_site_complement X
  have hN := sq_nonneg ‖X - expectA X - expectB (X - expectA X)‖
  linarith only [hU, hP, hN]

/-- Two alternative equal-dimensional sites share the same rank budget across a finite family. -/
theorem two_site_mass_sum_le [Nonempty A] [Nonempty B] {L : Type*} [Fintype L]
    (h : Fintype.card A = Fintype.card B) (K : L → TensorMatrix A B C)
    (hK : ∀ l, (K l).rank ≤ Fintype.card A) :
    (∑ l, (‖expectA (K l)‖ ^ 2 + ‖expectB (K l)‖ ^ 2)) ≤
      (1 + (Fintype.card A : ℝ)⁻¹) * ∑ l, ‖K l‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun l _ => two_site_mass_le h (K l) (hK l))

variable [DecidableEq C]

/-- Store the first site and record the product-basis outcome on the complement. -/
def basisEncoder (q : B × C) : Matrix A ((A × B) × C) ℂ :=
  fun a p => if p = ((a,q.1),q.2) then 1 else 0

private theorem basisEncoder_coisometry (q : B × C) :
    (basisEncoder q : Matrix A _ ℂ) * (basisEncoder q : Matrix A _ ℂ)ᴴ = 1 := by
  ext a a'
  by_cases h : a = a'
  · subst a'
    simp [Matrix.mul_apply, basisEncoder, apply_ite]
  · rw [Matrix.one_apply_ne h, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : p = ((a,q.1),q.2)
    · subst p
      simpa [basisEncoder] using h
    · simp [basisEncoder, hp]

omit [Fintype B] [Fintype C] in
private theorem basisEncoder_projection (q : B × C) :
    ((basisEncoder q : Matrix A _ ℂ)ᴴ * basisEncoder q : TensorMatrix A B C) =
      diagonal (fun p : (A × B) × C => if (p.1.2,p.2) = q then (1 : ℂ) else 0) := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
  change (∑ i : A, star (basisEncoder q i ((a,b),c)) * basisEncoder q i ((a',b'),c')) = _
  rw [Matrix.diagonal_apply]
  by_cases hq : (b,c) = q
  · by_cases hp : ((a,b),c) = ((a',b'),c')
    · have hEntry (i : A) : (basisEncoder q : Matrix A _ ℂ) i ((a,b),c) =
          if a = i then 1 else 0 := by
        have hb : b = q.1 := congrArg Prod.fst hq
        have hc : c = q.2 := congrArg Prod.snd hq
        simp [basisEncoder, Prod.mk.injEq, hb, hc]
      simp only [← hp, hEntry, hq, ite_true, apply_ite, star_one, star_zero]
      simp
    · simp only [hp, ite_false]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : ((a,b),c) = ((i,q.1),q.2)
      · have hj : ((a',b'),c') ≠ ((i,q.1),q.2) := by
          intro h
          exact hp (hi.trans h.symm)
        simp [basisEncoder, hi, hj]
      · simp [basisEncoder, hi]
  · simp only [hq, ite_false, ite_self]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ((a,b),c) ≠ ((i,q.1),q.2) :=
      fun h => hq (congrArg (fun p : (A × B) × C => (p.1.2,p.2)) h)
    simp [basisEncoder, hi]

private theorem basisEncoder_complete :
    (∑ q : B × C, ((basisEncoder q : Matrix A _ ℂ)ᴴ * basisEncoder q :
      TensorMatrix A B C)) = 1 := by
  ext p p'
  simp only [Matrix.sum_apply, basisEncoder_projection, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = p'
  · simp [h]
  · simp [h]

private theorem single_sq {S : Type*} [Fintype S] [DecidableEq S] (s : S) :
    ‖Matrix.single s s (1 : ℂ)‖ ^ 2 = 1 := by
  apply Complex.ofReal_injective
  rw [frobenius_norm_sq_eq_trace, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_single_same, one_mul, Matrix.trace_single_eq_same, Complex.ofReal_one]

private theorem basisEncoder_masses [Nonempty A] [Nonempty B]
    (h : Fintype.card A = Fintype.card B) (q : B × C) :
    let K := (basisEncoder q : Matrix A _ ℂ)ᴴ * basisEncoder q
    ‖K‖ ^ 2 = (Fintype.card A : ℝ) ∧ expectA K = K ∧ ‖expectB K‖ ^ 2 = 1 := by
  intro K
  have hK := basisEncoder_projection (A := A) q
  change K = _ at hK
  have hNorm : ‖K‖ ^ 2 = (Fintype.card A : ℝ) := by
    rw [hK, frobenius_sq_diagonal, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [← Fintype.sum_prod_type (f := fun p : B × C =>
      ‖if p = q then (1 : ℂ) else 0‖ ^ 2)]
    simp only [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, norm_zero,
      one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_one]
  have hFixed : expectA K = K := by
    have hc : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [hK]
    ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
    simp only [expectA_apply, Matrix.diagonal_apply, Prod.mk.injEq, true_and]
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hcc : c = c' <;>
      simp only [ha, hb, hcc, and_true, and_false, ite_true, ite_false,
        Finset.sum_const_zero, mul_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
  have hTrace : partialTraceLeft K = (Fintype.card A : ℂ) • Matrix.single q.2 q.2 1 := by
    rw [hK]
    ext c c'
    by_cases hcc : c = c'
    · subst c'
      simp only [partialTraceLeft, Matrix.diagonal_apply_eq, Fintype.sum_prod_type,
        Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, and_self]
      simp only [Prod.ext_iff]
      by_cases hc : c = q.2
      · subst c
        simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, nsmul_one, mul_one]
      · simp only [hc, Ne.symm hc, and_false, ite_false, Finset.sum_const_zero, mul_zero]
    · have hne (p : A × B) : (p,c) ≠ (p,c') := fun h => hcc (congrArg Prod.snd h)
      have hq : ¬ (q.2 = c ∧ q.2 = c') := fun h => hcc (h.1.symm.trans h.2)
      simp [partialTraceLeft, hne, hq]
  have hB : ‖expectB K‖ ^ 2 = 1 := by
    have hBoth : expectB K = expectation K := by
      rw [← (expect_union K).1, hFixed]
    rw [hBoth]
    change ‖(Fintype.card (A × B) : ℂ)⁻¹ •
      ((1 : Matrix (A × B) (A × B) ℂ) ⊗ₖ partialTraceLeft K)‖ ^ 2 = _
    rw [frobenius_sq_normalized_partialTraceLeft, hTrace, norm_smul, mul_pow, single_sq,
      mul_one, Complex.norm_natCast, Fintype.card_prod, Nat.cast_mul, ← h]
    have hc : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  exact ⟨hNorm, hFixed, hB⟩

/-- The basis encoder has identity output Gram in each block and attains the bound
with the actual normalized reverse products. -/
theorem basis_encoder_attains [Nonempty A] [Nonempty B]
    (h : Fintype.card A = Fintype.card B) :
    let V : B × C → Matrix A ((A × B) × C) ℂ := basisEncoder
    let K := fun q => (V q)ᴴ * V q
    (∀ q, V q * (V q)ᴴ = 1) ∧ (∑ q, K q) = 1 ∧
      (∀ q, (K q).rank = Fintype.card A) ∧
      (∀ q, ‖K q‖ ^ 2 = (Fintype.card A : ℝ) ∧ expectA (K q) = K q ∧
        ‖expectB (K q)‖ ^ 2 = 1) ∧
      (∑ q, (‖expectA (K q)‖ ^ 2 + ‖expectB (K q)‖ ^ 2)) =
        (1 + (Fintype.card A : ℝ)⁻¹) * ∑ q, ‖K q‖ ^ 2 := by
  intro V K
  refine ⟨basisEncoder_coisometry, basisEncoder_complete, ?_, basisEncoder_masses h, ?_⟩
  · intro q
    change ((V q)ᴴ * V q).rank = _
    rw [Matrix.rank_conjTranspose_mul_self]
    have hV : V q * (V q)ᴴ = 1 := basisEncoder_coisometry q
    have hr := Matrix.rank_mul_le_left (V q) (V q)ᴴ
    rw [hV, Matrix.rank_one] at hr
    exact le_antisymm (Matrix.rank_le_card_height _) hr
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨hNorm, hA, hB⟩ := basisEncoder_masses (A := A) h q
    change ‖K q‖ ^ 2 = _ at hNorm
    change expectA (K q) = K q at hA
    change ‖expectB (K q)‖ ^ 2 = 1 at hB
    rw [hA, hB]
    rw [hNorm, add_mul, one_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

end TwoSites

end D5.S3.Quantum.Information.LowRankPartialTrace
