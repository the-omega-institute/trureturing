/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Kronecker]
   utility: none
   digest: Raw interior observations give conditional phase recovery for arbitrary competitors. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import D5.S3.Quantum.Schatten.RankOneHadamard

/-! Raw interior windows retain their actual left and right complements. The
common-core conclusion is conditional on target spanning and positive definite
environments. Injective target transfer additionally gives full-state phase
recovery. No genericity is asserted. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix
open PeriodicMPSParentIntersection
open OpenBoundaryMPSMarginalBirationality (mpsState)
open OpenBoundaryMPSDensityRecovery

noncomputable section

/-- Columns retain both actual exterior words, in their original positions. -/
def interiorColumns (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) :
    Matrix (Word k) (Word p × Word q) ℂ :=
  fun u ab => ψ (Fin.append (Fin.append ab.1 u) ab.2)

/-- Unnormalized Hermitian interior observation. -/
def rawInterior (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) :
    Matrix (Word k) (Word k) ℂ :=
  interiorColumns p k q ψ * (interiorColumns p k q ψ)ᴴ

/-- Trace-pairing coordinates: the matrix entry is deliberately transposed. -/
def feature (A : Fin 2 → Bond) (k : ℕ) : Matrix (Word k) (Fin 2 × Fin 2) ℂ :=
  fun u ij => wordMatrix A u ij.2 ij.1

/-- Actual context coefficients, with right exterior before the left exterior. -/
def context (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p q : ℕ) :
    Matrix (Fin 2 × Fin 2) (Word p × Word q) ℂ :=
  fun ij ab => (wordMatrix A ab.2 *ᵥ r) ij.1 * (l ᵥ* wordMatrix A ab.1) ij.2

/-- Dual transfer for bilinear left boundary coordinates. -/
def dualTransfer (A : Fin 2 → Bond) (X : Bond) : Bond :=
  ∑ i : Fin 2, (A i)ᴴ * X * A i

private lemma feature_gamma (A : Fin 2 → Bond) (k : ℕ) (X : Bond) :
    feature A k *ᵥ (fun ij => X ij.1 ij.2) = gamma A k X := by
  funext w
  simp only [feature, mulVec, dotProduct, Fintype.sum_prod_type, gamma,
    trace, diag, mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private lemma state_gamma (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (n : ℕ) :
    mpsState n (A 0) (A 1) l r = gamma A n (vecMulVec r l) := by
  funext w
  rw [state_formula, gamma, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
    dotProduct_comm]

private lemma interior_columns_factor (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p k q : ℕ) :
    interiorColumns p k q (mpsState ((p + k) + q) (A 0) (A 1) l r) =
      feature A k * context A l r p q := by
  ext u ab
  rw [interiorColumns, state_formula, wordMatrix_append, wordMatrix_append]
  simp only [mul_apply, Fintype.sum_prod_type, feature, context]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [mulVec, vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma left_boundary_gram (A : Fin 2 → Bond) (l : Fin 2 → ℂ) (p : ℕ) :
    (prefixMap A l p)ᴴ * prefixMap A l p =
      (dualTransfer A)^[p] (vecMulVec (star l) l) := by
  have hs (k : ℕ) : (prefixMap A l k)ᴴ * prefixMap A l k =
      ∑ w : Word k, vecMulVec (star (l ᵥ* wordMatrix A w)) (l ᵥ* wordMatrix A w) := by
    ext i j
    simp only [mul_apply, conjTranspose_apply, prefixMap, Matrix.sum_apply,
      vecMulVec_apply, Pi.star_apply]
  rw [hs]
  induction p with
  | zero => simp [wordMatrix, Function.iterate_zero]
  | succ p ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (p + 1) => Fin 2)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, wordMatrix_snoc, ← vecMul_vecMul]
    simp only [dualTransfer, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro w _
    simp only [mul_vecMulVec, vecMulVec_mul, star_vecMul]

private lemma context_gram (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p q : ℕ) :
    context A l r p q * (context A l r p q)ᴴ =
      (transfer A)^[q] (vecMulVec r (star r)) ⊗ₖ
        ((dualTransfer A)^[p] (vecMulVec (star l) l))ᵀ := by
  rw [← tail_gram, ← left_boundary_gram]
  ext ij kt
  rcases ij with ⟨i, j⟩
  rcases kt with ⟨k, t⟩
  simp only [mul_apply, conjTranspose_apply, context, kronecker_apply,
    transpose_apply, tailMap, prefixMap, Fintype.sum_prod_type, star_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma interior_density_dictionary (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p k q : ℕ) :
    rawInterior p k q (mpsState ((p + k) + q) (A 0) (A 1) l r) =
      feature A k * ((transfer A)^[q] (vecMulVec r (star r)) ⊗ₖ
        ((dualTransfer A)^[p] (vecMulVec (star l) l))ᵀ) * (feature A k)ᴴ := by
  rw [rawInterior, interior_columns_factor, conjTranspose_mul]
  simp only [← context_gram, Matrix.mul_assoc]

private lemma feature_injective (A : Fin 2 → Bond) (hA : TwoSiteSpanning A) :
    Function.Injective (feature A 3).mulVec := by
  intro x y h
  have he : gamma A 3 (fun i j => x (i, j)) =
      gamma A 3 (fun i j => y (i, j)) := by
    exact (feature_gamma A 3 (fun i j => x (i, j))).symm.trans
      (h.trans (feature_gamma A 3 (fun i j => y (i, j))))
  have hm := trace_separates A hA 1 _ _ (congrFun he)
  funext ij
  exact congrFun (congrFun hm ij.1) ij.2

private lemma context_surjective (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (p q : ℕ)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef) :
    Function.Surjective (context A l r p q).mulVec := by
  have hdetP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp hP.isUnit).ne_zero
  have hdetH : ((transfer A)^[q] (vecMulVec r (star r))).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp hH.isUnit).ne_zero
  apply mulVec_surjective_iff_rank_eq_card.mpr
  rw [← rank_self_mul_conjTranspose, context_gram]
  apply rank_of_det_ne_zero
  rw [det_kronecker, det_transpose]
  exact mul_ne_zero (pow_ne_zero _ hdetH) (pow_ne_zero _ hdetP)

private lemma context_range (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) (p k q : ℕ)
    (hK : Function.Surjective (context A l r p q).mulVec) :
    LinearMap.range (interiorColumns p k q
      (mpsState ((p + k) + q) (A 0) (A 1) l r)).mulVecLin =
      LinearMap.range (feature A k).mulVecLin := by
  rw [← gram_range]
  change LinearMap.range (rawInterior p k q
    (mpsState ((p + k) + q) (A 0) (A 1) l r)).mulVecLin = _
  rw [interior_density_dictionary, ← context_gram]
  have hg : feature A k * (context A l r p q * (context A l r p q)ᴴ) *
      (feature A k)ᴴ =
      (feature A k * context A l r p q) * (feature A k * context A l r p q)ᴴ := by
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hg, gram_range, mulVecLin_mul, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hK, Submodule.map_top]

private lemma observed_all_coefficients (A B : Fin 2 → Bond)
    (l r lprime rprime : Fin 2 → ℂ) (p q : ℕ) (hA : TwoSiteSpanning A)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef)
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∀ X : Bond, ∃ Y : Bond, gamma B 3 X = gamma A 3 Y := by
  let CA := interiorColumns p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)
  let CB := interiorColumns p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime)
  have hCA : LinearMap.range CA.mulVecLin = LinearMap.range (feature A 3).mulVecLin :=
    context_range A l r p 3 q (context_surjective A l r p q hP hH)
  have he : LinearMap.range CB.mulVecLin = LinearMap.range CA.mulVecLin := by
    rw [← gram_range CB, ← gram_range CA]
    exact congrArg (fun M => LinearMap.range M.mulVecLin) hraw
  have hrA : Module.finrank ℂ (LinearMap.range CA.mulVecLin) = 4 := by
    rw [hCA, LinearMap.finrank_range_of_inj (feature_injective A hA)]
    norm_num
  have hle : LinearMap.range CB.mulVecLin ≤ LinearMap.range (feature B 3).mulVecLin := by
    dsimp [CB]
    rw [interior_columns_factor, mulVecLin_mul, LinearMap.range_comp]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, rfl⟩
  have hsat : LinearMap.range CB.mulVecLin = LinearMap.range (feature B 3).mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [he, hrA]
      simpa only [Matrix.rank, Fintype.card_prod, Fintype.card_fin,
        Nat.reduceMul] using (feature B 3).rank_le_card_width)
  intro X
  have hx : gamma B 3 X ∈ LinearMap.range CB.mulVecLin := by
    rw [hsat]
    exact ⟨fun ij => X ij.1 ij.2, feature_gamma B 3 X⟩
  rw [he, hCA] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨fun i j => y (i, j), ?_⟩
  exact hy.symm.trans (feature_gamma A 3 (fun i j => y (i, j)))

/-- Parent propagation for every virtual coefficient of an arbitrary competitor.
The induction generalizes X; no cyclicity of the physical state is assumed. -/
theorem all_coefficient_parent_induction (A B : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (hthree : ∀ X : Bond, ∃ Y : Bond, gamma B 3 X = gamma A 3 Y)
    (m : ℕ) (X : Bond) :
    ∃ Y : Bond, gamma B (m + 3) X = gamma A (m + 3) Y := by
  classical
  induction m generalizing X with
  | zero => exact hthree X
  | succ m ih =>
    apply (parent_intersection A hA m (gamma B (m + 4) X)).mp
    constructor
    · choose Y hY using fun j => ih (B j * X)
      refine ⟨Y, ?_⟩
      intro w j
      rw [← congrFun (hY j) w]
      simpa only [gamma, wordMatrix_snoc, ← Matrix.mul_assoc] using
        Matrix.trace_mul_cycle X (wordMatrix B w) (B j)
    · choose Y hY using fun i => ih (X * B i)
      refine ⟨Y, ?_⟩
      intro i w
      rw [← congrFun (hY i) w]
      simp only [gamma, wordMatrix_cons, Matrix.mul_assoc]

/-- An actual raw interior three-site observation forces every actual bond-two
competitor to have the target core with one unrestricted virtual coefficient.
Only the target has spanning and positive definite environment hypotheses. -/
theorem interior_common_core (A B : Fin 2 → Bond)
    (l r lprime rprime : Fin 2 → ℂ) (p q : ℕ) (_hp : 1 ≤ p) (_hq : 1 ≤ q)
    (hA : TwoSiteSpanning A)
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef)
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∃ X : Bond, mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime =
      gamma A ((p + 3) + q) X := by
  have hthree := observed_all_coefficients A B l r lprime rprime p q hA hP hH hraw
  have h := all_coefficient_parent_induction A B hA hthree (p + q) (vecMulVec rprime lprime)
  have hn : p + q + 3 = (p + 3) + q := by omega
  rw [hn] at h
  simpa only [state_gamma] using h

/-- The two-site flattening weighted by a virtual coefficient. -/
private def weightedTwoFlattening (A : Fin 2 → Bond) (X : Bond) (s : ℕ) :
    Matrix (Fin 2 × Fin 2) (Word (s + 2)) ℂ :=
  fun ij w => gamma A (2 + (s + 2)) X (Fin.append ![ij.1, ij.2] w)

private lemma weighted_rank_of_spanning (A : Fin 2 → Bond)
    (hA : TwoSiteSpanning A) (X : Bond) (hdet : X.det ≠ 0) (s : ℕ) :
    (weightedTwoFlattening A X s).rank = 4 := by
  classical
  let L : Bond →ₗ[ℂ] (Word (s + 2) → ℂ) :=
    { toFun := fun Y => gamma A (s + 2) (X * Y)
      map_add' := by
        intros Y Z
        ext w
        change trace ((X * (Y + Z)) * wordMatrix A w) =
          trace ((X * Y) * wordMatrix A w) + trace ((X * Z) * wordMatrix A w)
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      map_smul' := by
        intros c Y
        ext w
        change trace ((X * (c • Y)) * wordMatrix A w) =
          c • trace ((X * Y) * wordMatrix A w)
        rw [Matrix.mul_smul, smul_mul_assoc, Matrix.trace_smul] }
  have hu : IsUnit X :=
    (Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective L := by
    intro Y Z he
    exact hu.mul_left_cancel
      (trace_separates A hA s (X * Y) (X * Z) (congrFun he))
  have heq : LinearMap.range L = Submodule.span ℂ
      (Set.range (weightedTwoFlattening A X s).row) := by
    calc
      LinearMap.range L = (Submodule.span ℂ
          (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2)).map L := by
        rw [hA, Submodule.map_top]
      _ = _ := by
        rw [Submodule.map_span, ← Set.range_comp]
        have he : (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2)) =
            (weightedTwoFlattening A X s).row := by
          funext p b
          change ((X * (A p.1 * A p.2)) *
              (List.ofFn fun i => A (b i)).prod).trace =
            (X * (List.ofFn fun i => A (Fin.append ![p.1, p.2] b i)).prod).trace
          rw [List.ofFn_comp' (Fin.append ![p.1, p.2] b) A,
            List.ofFn_fin_append, List.map_append, List.prod_append]
          simp [List.map_ofFn, List.ofFn_succ, Matrix.mul_assoc, Function.comp_def]
        change Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 =>
          L (A p.1 * A p.2))) = _
        rw [he]
  rw [Matrix.rank_eq_finrank_span_row, ← heq,
    LinearMap.finrank_range_of_inj hinj]
  norm_num [Bond, Module.finrank_matrix]

/-- Any actual bond-two state in the target parent space has rank at most one
and can therefore be refactored through the target core. -/
theorem common_core_rank_one (A B : Fin 2 → Bond)
    (lprime rprime : Fin 2 → ℂ) (N : ℕ) (hN : 4 ≤ N)
    (hA : TwoSiteSpanning A) (X : Bond)
    (hX : mpsState N (B 0) (B 1) lprime rprime = gamma A N X) :
    X.rank ≤ 1 ∧ ∃ lA rA : Fin 2 → ℂ,
      X = vecMulVec rA lA ∧
      mpsState N (B 0) (B 1) lprime rprime =
        mpsState N (A 0) (A 1) lA rA := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, N = 2 + (s + 2) := by
    refine ⟨N - 4, ?_⟩
    omega
  have hflat : weightedTwoFlattening A X s =
      (amplitudeColumns 2 (s + 2)
        (mpsState (2 + (s + 2)) (B 0) (B 1) lprime rprime)).submatrix
        (fun ij : Fin 2 × Fin 2 => ![ij.1, ij.2]) id := by
    ext ij w
    exact (congrFun hX (Fin.append ![ij.1, ij.2] w)).symm
  have hupper : (weightedTwoFlattening A X s).rank ≤ 2 := by
    rw [hflat]
    calc
      _ ≤ (amplitudeColumns 2 (s + 2)
          (mpsState (2 + (s + 2)) (B 0) (B 1) lprime rprime)).rank :=
        Matrix.rank_submatrix_le _ _ _
      _ = (prefixMap B lprime 2 * tailMap B rprime (s + 2)).rank := by
        rw [columns_factor]
      _ ≤ (prefixMap B lprime 2).rank := Matrix.rank_mul_le_left _ _
      _ ≤ 2 := by simpa using (prefixMap B lprime 2).rank_le_card_width
  have hzero : X.det = 0 := by
    by_contra hdet
    have hfour := weighted_rank_of_spanning A hA X hdet s
    omega
  have hxupper : X.rank ≤ 2 := by simpa using X.rank_le_card_width
  have hrank : X.rank ≤ 1 := by
    by_contra hn
    have hfull : X.rank = Fintype.card (Fin 2) := by
      simpa using (show X.rank = 2 by omega)
    have hunit : IsUnit X :=
      Matrix.mulVec_surjective_iff_isUnit.mp
        (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hfull)
    exact ((Matrix.isUnit_iff_isUnit_det X).mp hunit).ne_zero hzero
  obtain ⟨rA, lA, hfactor⟩ :=
    D5.S3.Quantum.Schatten.exists_rank_one_factors X hrank
  refine ⟨hrank, lA, rA, hfactor, ?_⟩
  calc
    mpsState (2 + (s + 2)) (B 0) (B 1) lprime rprime =
        gamma A (2 + (s + 2)) X := hX
    _ = gamma A (2 + (s + 2)) (vecMulVec rA lA) :=
        congrArg (gamma A (2 + (s + 2))) hfactor
    _ = mpsState (2 + (s + 2)) (A 0) (A 1) lA rA :=
        (state_gamma A lA rA (2 + (s + 2))).symm

/-- The existing sandwich cancellation with arbitrary finite column indices. -/
private lemma sandwich_injective_any {ι κ : Type} [Fintype κ]
    (F : Matrix ι κ ℂ) (hF : Function.Injective F.mulVec) :
    Function.Injective (fun X : Matrix κ κ ℂ => F * X * Fᴴ) := by
  have hleft {η : Type} (X Y : Matrix κ η ℂ) (h : F * X = F * Y) : X = Y := by
    ext i j
    exact congrFun (hF (show F *ᵥ X.col j = F *ᵥ Y.col j from
      congrArg (fun M => M.col j) h)) i
  intro X Y h
  have he : X * Fᴴ = Y * Fᴴ := hleft _ _ (by
    simpa only [Matrix.mul_assoc] using h)
  have hc : F * Xᴴ = F * Yᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
      congrArg conjTranspose he
  exact conjTranspose_injective (hleft _ _ hc)

private def transferLinear (A : Fin 2 → Bond) : Bond →ₗ[ℂ] Bond where
  toFun := transfer A
  map_add' X Y := by simp [transfer, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [transfer]

private def dualTransferLinear (A : Fin 2 → Bond) : Bond →ₗ[ℂ] Bond where
  toFun := dualTransfer A
  map_add' X Y := by
    simp [dualTransfer, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [dualTransfer]

private lemma linear_iterate_smul (T : Bond →ₗ[ℂ] Bond) (n : ℕ) (c : ℂ) (X : Bond) :
    (T : Bond → Bond)^[n] (c • X) = c • (T : Bond → Bond)^[n] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_smul]

private lemma transfer_trace_pairing (A : Fin 2 → Bond) (Y X : Bond) :
    trace (Y * transfer A X) = trace (dualTransfer A Y * X) := by
  simp only [transfer, dualTransfer, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle Y (A i * X) (A i)ᴴ)

private lemma dualTransfer_injective (A : Fin 2 → Bond)
    (hE : Function.Injective (transfer A)) : Function.Injective (dualTransfer A) := by
  have hs : Function.Surjective (transferLinear A) :=
    LinearMap.injective_iff_surjective.mp hE
  intro Y Z h
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨W, rfl⟩ := hs X
  change trace (Y * transfer A W) = trace (Z * transfer A W)
  rw [transfer_trace_pairing, transfer_trace_pairing, h]

/-- Dimension-generic, zero-safe form of DensityRecovery.boundary_phase. -/
private lemma outer_gram_phase {ι : Type} (x y : ι → ℂ)
    (h : vecMulVec x (star x) = vecMulVec y (star y)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ y = z • x := by
  classical
  by_cases hx : x = 0
  · have hy : y = 0 := by
      funext i
      have hd := congrFun (congrFun h i) i
      simp only [hx, vecMulVec_apply, Pi.star_apply, Pi.zero_apply, zero_mul] at hd
      rcases mul_eq_zero.mp hd.symm with hi | hi
      · exact hi
      · exact star_eq_zero.mp hi
    exact ⟨1, norm_one, by simp [hx, hy]⟩
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    have hd : x i * star (x i) = y i * star (y i) := congrFun (congrFun h i) i
    have hy : y i ≠ 0 := by
      intro hy
      rw [hy, zero_mul] at hd
      exact (mul_ne_zero hi (star_ne_zero.mpr hi)) hd
    have hn : ‖x i‖ = ‖y i‖ := by
      have he := congrArg norm hd
      simp only [norm_mul, norm_star] at he
      nlinarith [norm_nonneg (x i), norm_nonneg (y i)]
    refine ⟨star (x i) / star (y i), ?_, ?_⟩
    · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.mpr hy)]
    · funext j
      have hj : x j * star (x i) = y j * star (y i) := congrFun (congrFun h j) i
      change y j = star (x i) / star (y i) * x j
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff (star_ne_zero.mpr hy)).mpr (by
        simpa only [mul_comm] using hj.symm)

private lemma same_core_phase (A : Fin 2 → Bond) (l r lhat rhat : Fin 2 → ℂ)
    (p q : ℕ) (hA : TwoSiteSpanning A) (hE : Function.Injective (transfer A))
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) lhat rhat) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      mpsState ((p + 3) + q) (A 0) (A 1) lhat rhat =
        z • mpsState ((p + 3) + q) (A 0) (A 1) l r := by
  let L := vecMulVec (star l) l
  let R := vecMulVec r (star r)
  let Lhat := vecMulVec (star lhat) lhat
  let Rhat := vecMulVec rhat (star rhat)
  let P := (dualTransfer A)^[p] L
  let Phat := (dualTransfer A)^[p] Lhat
  let H := (transfer A)^[q] R
  let Hhat := (transfer A)^[q] Rhat
  have hW : Hhat ⊗ₖ Phatᵀ = H ⊗ₖ Pᵀ := by
    apply sandwich_injective_any (feature A 3) (feature_injective A hA)
    simpa only [interior_density_dictionary] using hraw
  have hR (t j : Fin 2) : Phat t j • Rhat = P t j • R := by
    apply hE.iterate q
    change (transferLinear A : Bond → Bond)^[q] (Phat t j • Rhat) =
      (transferLinear A : Bond → Bond)^[q] (P t j • R)
    rw [linear_iterate_smul, linear_iterate_smul]
    change Phat t j • Hhat = P t j • H
    ext i k
    have he := congrFun (congrFun hW (i, j)) (k, t)
    simpa only [kronecker_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul,
      mul_comm] using he
  have hL (i k : Fin 2) : Rhat i k • Lhat = R i k • L := by
    apply (dualTransfer_injective A hE).iterate p
    change (dualTransferLinear A : Bond → Bond)^[p] (Rhat i k • Lhat) =
      (dualTransferLinear A : Bond → Bond)^[p] (R i k • L)
    rw [linear_iterate_smul, linear_iterate_smul]
    change Rhat i k • Phat = R i k • P
    ext t j
    have he := congrFun (congrFun (hR t j) i) k
    simpa only [Matrix.smul_apply, smul_eq_mul, mul_comm] using he
  let x : (Fin 2 × Fin 2) → ℂ := fun ij => r ij.1 * l ij.2
  let y : (Fin 2 × Fin 2) → ℂ := fun ij => rhat ij.1 * lhat ij.2
  have hGram : vecMulVec x (star x) = vecMulVec y (star y) := by
    ext ⟨i, j⟩ ⟨k, t⟩
    have he := congrFun (congrFun (hL i k) t) j
    change (rhat i * star (rhat k)) * (star (lhat t) * lhat j) =
      (r i * star (r k)) * (star (l t) * l j) at he
    change r i * l j * star (r k * l t) = rhat i * lhat j * star (rhat k * lhat t)
    rw [star_mul, star_mul]
    calc
      _ = (r i * star (r k)) * (star (l t) * l j) := by ring
      _ = (rhat i * star (rhat k)) * (star (lhat t) * lhat j) := he.symm
      _ = _ := by ring
  obtain ⟨z, hz, hxy⟩ := outer_gram_phase x y hGram
  refine ⟨z, hz, ?_⟩
  rw [state_gamma, state_gamma]
  have hcoeff : vecMulVec rhat lhat = z • vecMulVec r l := by
    ext i j
    exact congrFun hxy (i, j)
  rw [hcoeff]
  funext w
  change trace ((z • vecMulVec r l) * wordMatrix A w) =
    z • trace (vecMulVec r l * wordMatrix A w)
  rw [smul_mul_assoc, trace_smul]

/-- Complete raw interior three-site equality determines every actual competitor
up to a unit complex scalar, under target-only spanning, injective transfer and
positive definite actual environments. This is a conditional static theorem. -/
theorem interior_phase_recovery (A B : Fin 2 → Bond)
    (l r lprime rprime : Fin 2 → ℂ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hA : TwoSiteSpanning A) (hE : Function.Injective (transfer A))
    (hP : ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef)
    (hH : ((transfer A)^[q] (vecMulVec r (star r))).PosDef)
    (hraw : rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime =
        z • mpsState ((p + 3) + q) (A 0) (A 1) l r := by
  obtain ⟨X, hX⟩ := interior_common_core A B l r lprime rprime p q hp hq hA hP hH hraw
  obtain ⟨_, lhat, rhat, _, hstate⟩ :=
    common_core_rank_one A B lprime rprime ((p + 3) + q) (by omega) hA X hX
  obtain ⟨z, hz, he⟩ := same_core_phase A l r lhat rhat p q hA hE (by
    rw [← hstate]
    exact hraw)
  exact ⟨z, hz, hstate.trans he⟩

#print axioms all_coefficient_parent_induction
#print axioms interior_common_core
#print axioms common_core_rank_one
#print axioms interior_phase_recovery

end
end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
