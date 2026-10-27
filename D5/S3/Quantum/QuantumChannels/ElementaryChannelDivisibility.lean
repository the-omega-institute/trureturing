/- GID: D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Elementary right division of finite complex quantum channels. -/

import D5.S3.Quantum.Recovery.ActualChannelAlgebra

/-!
The elementary channel and the two Kraus-space criteria are those of
Frederik vom Ende, *A Sufficient Criterion for Divisibility of Quantum
Channels*, arXiv:2407.17103v3, Definition 1, Proposition 1, Theorem 1 and
Section V. Choi coordinates are input-first, as in that source.
-/

noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem factor_of_kernel (R S : Matrix n n ℂ)
    (hker : ∀ v, R *ᵥ v = 0 → S *ᵥ v = 0) :
    ∃ C : Matrix n n ℂ, S = C * R := by
  let r := R.mulVecLin
  let s := S.mulVecLin
  have hk : r.ker ≤ s.ker := hker
  let f : r.range →ₗ[ℂ] (n → ℂ) :=
    (r.ker.liftQ s hk).comp r.quotKerEquivRange.symm.toLinearMap
  obtain ⟨c, hc⟩ := f.exists_extend
  refine ⟨LinearMap.toMatrix' c, ?_⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have he := LinearMap.congr_fun hc ⟨r v, LinearMap.mem_range_self r v⟩
  have hf : f ⟨r v, LinearMap.mem_range_self r v⟩ = s v := by
    change r.ker.liftQ s hk
      (r.quotKerEquivRange.symm ⟨r v, LinearMap.mem_range_self r v⟩) = s v
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  exact hf.symm.trans he.symm

private theorem sqrt_kernel (A : Matrix n n ℂ) (hA : A.PosSemidef) (v : n → ℂ) :
    CFC.sqrt A *ᵥ v = 0 ↔ A *ᵥ v = 0 := by
  have hR : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hRR : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  simpa only [hR, hRR] using
    (Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt A) v).symm

private theorem support_domination (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v, A *ᵥ v = 0 → B *ᵥ v = 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (A - t • B).PosSemidef := by
  let R := CFC.sqrt A
  let S := CFC.sqrt B
  have hR : Rᴴ = R := (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  obtain ⟨C, hC⟩ := factor_of_kernel R S fun v hv =>
    (sqrt_kernel B hB v).mpr (hker v ((sqrt_kernel A hA v).mp hv))
  let M : ℝ := ‖C‖ ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have hbound : B ≤ M • A := by
    have h := CStarAlgebra.star_mul_le_algebraMap_norm_sq C
    have hcong := star_left_conjugate_le_conjugate h R
    change Rᴴ * (Cᴴ * C) * R ≤
      Rᴴ * algebraMap ℝ (Matrix n n ℂ) (‖C‖ ^ 2) * R at hcong
    have hB : Rᴴ * (Cᴴ * C) * R = B := by
      calc
        _ = (C * R)ᴴ * (C * R) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = B := by rw [← hC, hS, hSS]
    rw [hB] at hcong
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hR, hRR, M] using hcong
  let t : ℝ := 1 / (2 * (M + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; rw [div_lt_iff₀ (by positivity)]; linarith
  have htM : t * M ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨t, ht, ht1, Matrix.le_iff.mp ?_⟩
  calc
    t • B ≤ t • (M • A) := smul_le_smul_of_nonneg_left hbound ht.le
    _ = (t * M) • A := smul_smul t M A
    _ ≤ A := by simpa using smul_le_smul_of_nonneg_right htM hA.nonneg

/-- Ordered orthogonal unit vectors, with the complex Euclidean normalization. -/
def OrthogonalUnitPair (x y : n → ℂ) : Prop :=
  star x ⬝ᵥ x = 1 ∧ star y ⬝ᵥ y = 1 ∧ star x ⬝ᵥ y = 0

/-- The rank-one operator sending v to u times the inner product of w with v. -/
def ketbra (u w : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec u (star w)

/-- The first Kraus operator in source Definition 1. -/
def elementaryK (t : ℝ) (x : n → ℂ) : Matrix n n ℂ :=
  1 + ((Real.sqrt (1 - t) : ℂ) - 1) • ketbra x x

/-- The second Kraus operator in source Definition 1. -/
def elementaryL (t : ℝ) (x y : n → ℂ) : Matrix n n ℂ :=
  (Real.sqrt t : ℂ) • ketbra y x

private def ad (K : Matrix n n ℂ) : MatrixMap n n ℂ :=
  LinearMap.mulLeftRight ℂ (K, Kᴴ)

/-- Exactly the source two-Kraus elementary channel. -/
def elementary (t : ℝ) (x y : n → ℂ) : MatrixMap n n ℂ :=
  ad (elementaryK t x) + ad (elementaryL t x y)

/-- Source equation (2), for an orthogonal pair and 0 < t < 1. -/
def elementaryInverse (t : ℝ) (x y : n → ℂ) : MatrixMap n n ℂ :=
  ad (1 + (((Real.sqrt (1 - t) : ℂ))⁻¹ - 1) • ketbra x x) -
    ((t / (1 - t) : ℝ) : ℂ) • ad (ketbra y x)

/-- Actual complete positivity at every finite amplification and all-matrix trace preservation. -/
def CPTP (Φ : MatrixMap n n ℂ) : Prop :=
  Φ.IsCompletelyPositive ∧ ∀ X, Matrix.trace (Φ X) = Matrix.trace X

/-- Right division by the specified source elementary channel, preserving the ordered pair. -/
def Divides (Φ : MatrixMap n n ℂ) (x y : n → ℂ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    MatrixMap.IsCompletelyPositive (Φ.comp (elementaryInverse t x y))

/-- Source Proposition 1 criterion for a given finite Kraus representation. -/
def Necessary {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (x y : n → ℂ) : Prop :=
  ∀ G : Matrix n n ℂ,
    (∀ H ∈ Submodule.span ℂ (Set.range K), Matrix.trace (Hᴴ * G) = 0) →
      ∀ j, star y ⬝ᵥ (((K j)ᴴ * G) *ᵥ x) = 0

/-- Source Theorem 1 criterion, including its extra diagonal clause. -/
def Sufficient {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (x y : n → ℂ) : Prop :=
  Necessary K x y ∧ ∀ G : Matrix n n ℂ,
    (∀ H ∈ Submodule.span ℂ (Set.range K), Matrix.trace (Hᴴ * G) = 0) →
      ∀ j, star x ⬝ᵥ (((K j)ᴴ * G) *ᵥ x) = 0

private theorem hs_span_iff {ι : Type*} (K : ι → Matrix n n ℂ)
    (G : Matrix n n ℂ) :
    (∀ H ∈ Submodule.span ℂ (Set.range K), Matrix.trace (Hᴴ * G) = 0) ↔
      ∀ j, Matrix.trace ((K j)ᴴ * G) = 0 := by
  constructor
  · intro h j
    exact h (K j) (Submodule.subset_span ⟨j, rfl⟩)
  · intro h H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨j, rfl⟩ := hH
      exact h j
    | zero => simp
    | add H J _ _ hH hJ =>
      simp [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, hH, hJ]
    | smul c H _ hH =>
      simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, hH]

theorem ketbra_star (u w : n → ℂ) : (ketbra u w)ᴴ = ketbra w u := by
  ext i j
  simp [ketbra, Matrix.vecMulVec_apply, mul_comm]

private theorem ketbra_mul (u v w z : n → ℂ) :
    ketbra u v * ketbra w z = (star v ⬝ᵥ w) • ketbra u z := by
  rw [ketbra, ketbra, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, ketbra, Pi.smul_apply,
    smul_eq_mul]
  ring

private theorem ad_apply (K X : Matrix n n ℂ) : ad K X = K * X * Kᴴ := rfl

private theorem elementary_apply (t : ℝ) (ht : 0 ≤ t) (x y : n → ℂ)
    (X : Matrix n n ℂ) :
    elementary t x y X = elementaryK t x * X * (elementaryK t x)ᴴ +
      (t : ℂ) • (ketbra y x * X * ketbra x y) := by
  change elementaryK t x * X * (elementaryK t x)ᴴ +
    elementaryL t x y * X * (elementaryL t x y)ᴴ = _
  congr 1
  have hs : star (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    rw [show star (Real.sqrt t : ℂ) = (Real.sqrt t : ℂ) by simp]
    exact_mod_cast Real.mul_self_sqrt ht
  rw [elementaryL, Matrix.conjTranspose_smul, ketbra_star,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, hs]

private theorem elementary_kraus (t : ℝ) (x y : n → ℂ) :
    elementary t x y = MatrixMap.of_kraus
      (![elementaryK t x, elementaryL t x y] : Fin 2 → Matrix n n ℂ)
      ![elementaryK t x, elementaryL t x y] := by
  ext X i j
  simp [elementary, ad, MatrixMap.of_kraus, Fin.sum_univ_two]

private theorem elementary_cp (t : ℝ) (x y : n → ℂ) :
    (elementary t x y).IsCompletelyPositive := by
  rw [elementary_kraus]
  exact MatrixMap.of_kraus_isCompletelyPositive _

private theorem filter_mul (a b : ℂ) (x : n → ℂ) (hx : star x ⬝ᵥ x = 1) :
    (1 + (a - 1) • ketbra x x) * (1 + (b - 1) • ketbra x x) =
      1 + (a * b - 1) • ketbra x x := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    ketbra_mul, hx, one_smul, smul_smul]
  module

private theorem filter_star (a : ℝ) (x : n → ℂ) :
    (1 + ((a : ℂ) - 1) • ketbra x x)ᴴ =
      1 + ((a : ℂ) - 1) • ketbra x x := by
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, ketbra_star]

private theorem elementary_tp (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : n → ℂ) (hxy : OrthogonalUnitPair x y) :
    ∀ X, Matrix.trace (elementary t x y X) = Matrix.trace X := by
  have hK : (elementaryK t x)ᴴ = elementaryK t x := filter_star _ _
  have hKK : elementaryK t x * elementaryK t x = 1 - (t : ℂ) • ketbra x x := by
    rw [elementaryK, filter_mul _ _ x hxy.1]
    have hs : (Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ) = 1 - (t : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr ht1)
    rw [hs]
    module
  intro X
  rw [elementary_apply t ht, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_mul_cycle, hK, hKK, Matrix.trace_mul_cycle,
    ketbra_mul, hxy.2.1, one_smul]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring

private theorem elementary_as_sum (t : ℝ) (ht : 0 ≤ t) (x y : n → ℂ) :
    elementary t x y = ad (elementaryK t x) + (t : ℂ) • ad (ketbra y x) := by
  ext X i j
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, ad_apply, ketbra_star,
    Matrix.add_apply, Matrix.smul_apply] using
    congrFun (congrFun (elementary_apply t ht x y X) i) j

private theorem ad_comp (A B : Matrix n n ℂ) :
    (ad A).comp (ad B) = ad (A * B) := by
  ext X i j
  simp only [LinearMap.comp_apply, ad_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem ad_smul (c : ℂ) (A : Matrix n n ℂ) :
    ad (c • A) = (c * star c) • ad A := by
  ext X i j
  simp [ad, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ring

private theorem ad_one : ad (1 : Matrix n n ℂ) = LinearMap.id := by
  ext X i j
  simp [ad]

private theorem ad_zero : ad (0 : Matrix n n ℂ) = 0 := by
  ext X i j
  simp [ad]

private theorem elementary_inverse_identities (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (x y : n → ℂ) (hxy : OrthogonalUnitPair x y) :
    (elementary t x y).comp (elementaryInverse t x y) = LinearMap.id ∧
      (elementaryInverse t x y).comp (elementary t x y) = LinearMap.id := by
  let a : ℝ := Real.sqrt (1 - t)
  let P := ketbra x x
  let T := ketbra y x
  let K := 1 + ((a : ℂ) - 1) • P
  let R := 1 + (((a : ℂ))⁻¹ - 1) • P
  have ha : 0 < a := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have ha2 : (a : ℂ) * (a : ℂ) = 1 - (t : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_pos.mpr ht1).le
  have haStar : star (a : ℂ) = (a : ℂ) := by simp
  have hKR : K * R = 1 := by
    dsimp only [K, R, P]
    rw [filter_mul _ _ _ hxy.1, mul_inv_cancel₀ ha0, sub_self, zero_smul, add_zero]
  have hRK : R * K = 1 := by
    dsimp only [K, R, P]
    rw [filter_mul _ _ _ hxy.1, inv_mul_cancel₀ ha0, sub_self, zero_smul, add_zero]
  have hKT : K * T = T := by
    simp [K, P, T, Matrix.add_mul, Matrix.smul_mul, ketbra_mul, hxy.2.2]
  have hRT : R * T = T := by
    simp [R, P, T, Matrix.add_mul, Matrix.smul_mul, ketbra_mul, hxy.2.2]
  have hTK : T * K = (a : ℂ) • T := by
    simp only [K, P, T, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ketbra_mul, hxy.1, one_smul]
    module
  have hTR : T * R = (a : ℂ)⁻¹ • T := by
    simp only [R, P, T, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ketbra_mul, hxy.1, one_smul]
    module
  have hTT : T * T = 0 := by simp [T, ketbra_mul, hxy.2.2]
  have hc : ((t / (1 - t) : ℝ) : ℂ) = (t : ℂ) / ((a : ℂ) * (a : ℂ)) := by
    push_cast
    rw [ha2]
  rw [elementary_as_sum t ht.le]
  change (ad K + (t : ℂ) • ad T).comp
      (ad R - ((t / (1 - t) : ℝ) : ℂ) • ad T) = LinearMap.id ∧
    (ad R - ((t / (1 - t) : ℝ) : ℂ) • ad T).comp
      (ad K + (t : ℂ) • ad T) = LinearMap.id
  simp only [LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_add,
    LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul, ad_comp,
    hKR, hRK, hKT, hRT, hTK, hTR, hTT, ad_zero, ad_one, ad_smul,
    star_inv₀, haStar, hc, smul_zero, sub_zero, add_zero, smul_smul]
  constructor <;> match_scalars <;> field_simp <;> ring

private def columns {ι : Type*} (K : ι → Matrix n n ℂ) : Matrix (n × n) ι ℂ :=
  fun p j => K j p.2 p.1

private theorem inputChoi_gram {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) :
    Original8340Global.inputChoi (MatrixMap.of_kraus K K) = columns K * (columns K)ᴴ := by
  rw [Original8340Global.inputChoi_index_swap, MatrixMap.choi_of_kraus]
  ext p q
  simp [columns, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

private theorem columns_right {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (R : Matrix n n ℂ) :
    columns (fun j => K j * R) = (Rᵀ ⊗ₖ (1 : Matrix n n ℂ)) * columns K := by
  ext p j
  have h := congrFun (Matrix.kronecker_mulVec_vec (1 : Matrix n n ℂ) (K j) Rᵀ) p
  simpa only [Matrix.transpose_transpose, Matrix.one_mul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.vec, columns] using h.symm

private theorem comp_ad_kraus {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (R : Matrix n n ℂ) :
    (MatrixMap.of_kraus K K).comp (ad R) =
      MatrixMap.of_kraus (fun j => K j * R) (fun j => K j * R) := by
  ext X i j
  simp only [LinearMap.comp_apply, MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk, ad_apply, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, Matrix.sum_apply]

private theorem inputChoi_comp_ad {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (R : Matrix n n ℂ) :
    Original8340Global.inputChoi ((MatrixMap.of_kraus K K).comp (ad R)) =
      (Rᵀ ⊗ₖ (1 : Matrix n n ℂ)) *
        Original8340Global.inputChoi (MatrixMap.of_kraus K K) *
          (Rᵀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ := by
  rw [comp_ad_kraus, inputChoi_gram, inputChoi_gram, columns_right,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem inputChoi_cp_iff (Φ : MatrixMap n n ℂ) :
    (Original8340Global.inputChoi Φ).PosSemidef ↔ Φ.IsCompletelyPositive := by
  constructor
  · intro h
    apply (MatrixMap.choi_PSD_iff_CP_map Φ).mpr
    convert h.submatrix Prod.swap using 1
    ext p q
    rfl
  · exact Original8340Global.inputChoi_posSemidef Φ

private theorem columns_adjoint_vec {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (G : Matrix n n ℂ) (j : ι) :
    ((columns K)ᴴ *ᵥ Matrix.vec G) j = Matrix.trace ((K j)ᴴ * G) := by
  exact Matrix.star_vec_dotProduct_vec (K j) G

private theorem choi_kernel {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (G : Matrix n n ℂ) :
    Original8340Global.inputChoi (MatrixMap.of_kraus K K) *ᵥ Matrix.vec G = 0 ↔
      ∀ j, Matrix.trace ((K j)ᴴ * G) = 0 := by
  rw [inputChoi_gram, Matrix.self_mul_conjTranspose_mulVec_eq_zero]
  simp only [funext_iff, Pi.zero_apply, columns_adjoint_vec]

private theorem trace_ketbra_mul (x y : n → ℂ) (H : Matrix n n ℂ) :
    Matrix.trace (ketbra x y * H) = star y ⬝ᵥ (H *ᵥ x) := by
  rw [Matrix.trace_mul_comm]
  simp only [ketbra, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

private theorem hs_right (K G : Matrix n n ℂ) (x y : n → ℂ) :
    Matrix.trace ((K * ketbra y x)ᴴ * G) = star y ⬝ᵥ ((Kᴴ * G) *ᵥ x) := by
  rw [Matrix.conjTranspose_mul, ketbra_star, Matrix.mul_assoc, trace_ketbra_mul]

private theorem necessary_kernel {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (x y : n → ℂ) :
    Necessary K x y ↔ ∀ v : n × n → ℂ,
      Original8340Global.inputChoi (MatrixMap.of_kraus K K) *ᵥ v = 0 →
        (((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)) *
          Original8340Global.inputChoi (MatrixMap.of_kraus K K) *
            ((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ) *ᵥ v = 0 := by
  have hB : ((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)) *
      Original8340Global.inputChoi (MatrixMap.of_kraus K K) *
        ((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ =
      Original8340Global.inputChoi
        (MatrixMap.of_kraus (fun j => K j * ketbra y x) (fun j => K j * ketbra y x)) := by
    rw [← inputChoi_comp_ad, comp_ad_kraus]
  rw [show Necessary K x y = (∀ G : Matrix n n ℂ,
      (∀ j, Matrix.trace ((K j)ᴴ * G) = 0) →
        ∀ j, Matrix.trace ((K j * ketbra y x)ᴴ * G) = 0) by
    simp only [Necessary, hs_span_iff, hs_right]]
  simp_rw [hB]
  constructor
  · intro h v hv
    obtain ⟨G, rfl⟩ := Matrix.vec_bijective.surjective v
    exact (choi_kernel _ G).mpr (h G ((choi_kernel K G).mp hv))
  · intro h G hG
    exact (choi_kernel _ G).mp (h (Matrix.vec G) ((choi_kernel K G).mpr hG))

private theorem necessary_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → Matrix n n ℂ) (L : κ → Matrix n n ℂ)
    (hKL : MatrixMap.of_kraus K K = MatrixMap.of_kraus L L) (x y : n → ℂ) :
    Necessary K x y ↔ Necessary L x y := by
  simp only [necessary_kernel, hKL]

theorem kernel_of_sub_psd (A B : Matrix n n ℂ)
    (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t) (hAB : (A - t • B).PosSemidef) :
    ∀ v, A *ᵥ v = 0 → B *ᵥ v = 0 := by
  intro v hv
  apply hB.dotProduct_mulVec_zero_iff.mp
  have hq := hB.dotProduct_mulVec_nonneg v
  have hd := hAB.dotProduct_mulVec_nonneg v
  have heq : star v ⬝ᵥ ((A - t • B) *ᵥ v) =
      -(t • (star v ⬝ᵥ (B *ᵥ v))) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, zero_sub, dotProduct_neg,
      dotProduct_smul]
  rw [heq] at hd
  have hqre := (Complex.nonneg_iff.mp hq).1
  have hdre := (Complex.nonneg_iff.mp hd).1
  have hzre : (star v ⬝ᵥ (B *ᵥ v)).re = 0 := by
    simp only [Complex.neg_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hdre
    nlinarith
  apply Complex.ext
  · exact hzre
  · exact (Complex.nonneg_iff.mp hq).2.symm

private theorem elementary_inverse_tp (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (x y : n → ℂ) (hxy : OrthogonalUnitPair x y) :
    ∀ X, Matrix.trace (elementaryInverse t x y X) = Matrix.trace X := by
  intro X
  have h := LinearMap.congr_fun (elementary_inverse_identities t ht ht1 x y hxy).1 X
  have htp := elementary_tp t ht.le ht1.le x y hxy (elementaryInverse t x y X)
  change elementary t x y (elementaryInverse t x y X) = X at h
  rw [h] at htp
  exact htp.symm

private theorem residual_choi {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (x y : n → ℂ) (hx : star x ⬝ᵥ x = 1) :
    let A := Original8340Global.inputChoi (MatrixMap.of_kraus K K)
    let Z := (ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)
    let R := 1 + (((Real.sqrt (1 - t) : ℂ))⁻¹ - 1) • ketbra x x
    let D := Rᵀ ⊗ₖ (1 : Matrix n n ℂ)
    Original8340Global.inputChoi
      ((MatrixMap.of_kraus K K).comp (elementaryInverse t x y)) =
        D * (A - t • (Z * A * Zᴴ)) * Dᴴ := by
  intro A Z R D
  let a : ℝ := Real.sqrt (1 - t)
  let T := ketbra y x
  have ha : 0 < a := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have ha2 : a * a = 1 - t := Real.mul_self_sqrt (sub_pos.mpr ht1).le
  have hTR : T * R = (a : ℂ)⁻¹ • T := by
    simp only [T, R, a, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ketbra_mul, hx, one_smul]
    module
  have hDZ : D * Z = (a : ℂ)⁻¹ • Z := by
    change (Rᵀ ⊗ₖ (1 : Matrix n n ℂ)) * (Tᵀ ⊗ₖ (1 : Matrix n n ℂ)) = _
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.transpose_mul, hTR,
      Matrix.transpose_smul, Matrix.smul_kronecker]
  have hcong : D * (Z * A * Zᴴ) * Dᴴ =
      ((a : ℂ)⁻¹ * (a : ℂ)⁻¹) • (Z * A * Zᴴ) := by
    calc
      _ = (D * Z) * A * (D * Z)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hDZ, Matrix.conjTranspose_smul]
        simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have ha2c : (a : ℂ) * (a : ℂ) = 1 - (t : ℂ) := by exact_mod_cast ha2
  have hc : (t : ℂ) * ((a : ℂ)⁻¹ * (a : ℂ)⁻¹) = ((t / (1 - t) : ℝ) : ℂ) := by
    push_cast
    rw [← ha2c]
    field_simp
  have hlin : Original8340Global.inputChoi
      ((MatrixMap.of_kraus K K).comp (elementaryInverse t x y)) =
      Original8340Global.inputChoi ((MatrixMap.of_kraus K K).comp (ad R)) -
        ((t / (1 - t) : ℝ) : ℂ) •
          Original8340Global.inputChoi ((MatrixMap.of_kraus K K).comp (ad T)) := by
    ext p q
    simp only [Original8340Global.inputChoi, elementaryInverse, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, Matrix.sub_apply,
      Matrix.smul_apply, R, T]
  rw [hlin, inputChoi_comp_ad, inputChoi_comp_ad]
  change D * A * Dᴴ - ((t / (1 - t) : ℝ) : ℂ) • (Z * A * Zᴴ) = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hcong,
    smul_smul]
  exact congrArg (fun c : ℂ => D * A * Dᴴ - c • (Z * A * Zᴴ)) hc.symm

private theorem residual_cp_iff {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (x y : n → ℂ) (hx : star x ⬝ᵥ x = 1) :
    MatrixMap.IsCompletelyPositive
      ((MatrixMap.of_kraus K K).comp (elementaryInverse t x y)) ↔
        (Original8340Global.inputChoi (MatrixMap.of_kraus K K) -
          t • (((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)) *
            Original8340Global.inputChoi (MatrixMap.of_kraus K K) *
              ((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ)).PosSemidef := by
  let R := 1 + (((Real.sqrt (1 - t) : ℂ))⁻¹ - 1) • ketbra x x
  let D := Rᵀ ⊗ₖ (1 : Matrix n n ℂ)
  let H := (elementaryK t x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)
  have ha : (Real.sqrt (1 - t) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sub_pos.mpr ht1)).ne'
  have hRK : R * elementaryK t x = 1 := by
    dsimp only [R, elementaryK]
    rw [filter_mul _ _ _ hx, inv_mul_cancel₀ ha, sub_self, zero_smul, add_zero]
  have hHD : H * D = 1 := by
    dsimp only [H, D]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.transpose_mul,
      hRK, Matrix.transpose_one, Matrix.one_kronecker_one]
  rw [← inputChoi_cp_iff, residual_choi K t ht ht1 x y hx]
  constructor
  · intro h
    let C := Original8340Global.inputChoi (MatrixMap.of_kraus K K) -
      t • (((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)) *
        Original8340Global.inputChoi (MatrixMap.of_kraus K K) *
          ((ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ))ᴴ)
    change (D * C * Dᴴ).PosSemidef at h
    have h' := h.mul_mul_conjTranspose_same H
    have heq : H * (D * C * Dᴴ) * Hᴴ = C := calc
      _ = (H * D) * C * (H * D)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hHD, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    rw [heq] at h'
    exact h'
  · intro h
    exact h.mul_mul_conjTranspose_same D

private theorem fixed_pair_iff {ι : Type*} [Fintype ι]
    (K : ι → Matrix n n ℂ) (x y : n → ℂ) (hxy : OrthogonalUnitPair x y) :
    Necessary K x y ↔ Divides (MatrixMap.of_kraus K K) x y := by
  let A := Original8340Global.inputChoi (MatrixMap.of_kraus K K)
  let Z := (ketbra y x)ᵀ ⊗ₖ (1 : Matrix n n ℂ)
  have hA : A.PosSemidef := (inputChoi_cp_iff _).mpr
    (MatrixMap.of_kraus_isCompletelyPositive K)
  have hB : (Z * A * Zᴴ).PosSemidef := hA.mul_mul_conjTranspose_same Z
  rw [necessary_kernel]
  constructor
  · intro hker
    obtain ⟨t, ht, ht1, hpos⟩ := support_domination A (Z * A * Zᴴ) hA hB hker
    exact ⟨t, ht, ht1, (residual_cp_iff K t ht ht1 x y hxy.1).mpr hpos⟩
  · rintro ⟨t, ht, ht1, hcp⟩
    exact kernel_of_sub_psd A (Z * A * Zᴴ) hB t ht
      ((residual_cp_iff K t ht ht1 x y hxy.1).mp hcp)

private theorem basis_pair (r s : n) (hrs : r ≠ s) :
    OrthogonalUnitPair (Pi.single r 1) (Pi.single s 1 : n → ℂ) := by
  simp [OrthogonalUnitPair, Pi.star_single, single_dotProduct, hrs, hrs.symm]

private theorem basis_ketbra (r s : n) :
    ketbra (Pi.single r 1) (Pi.single s 1 : n → ℂ) = Matrix.single r s 1 := by
  ext i j
  by_cases hi : r = i <;> by_cases hj : s = j <;>
    simp [ketbra, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single,
      hi, hj, eq_comm]

private theorem no_diagonal_criterion (r s : n) (hrs : r ≠ s)
    (hcard : 2 ≤ Fintype.card n) (a : ℝ) (ha : a ≠ 0) (b : ℂ)
    (u : n → ℂ) (hu : star u ⬝ᵥ u = 1) :
    ¬ Necessary (![1 + ((a : ℂ) - 1) • Matrix.single r r 1,
      b • Matrix.single s r 1] : Fin 2 → Matrix n n ℂ) u u := by
  let P : Matrix n n ℂ := Matrix.single r r 1
  let D : Matrix n n ℂ := 1 + ((a : ℂ) - 1) • P
  let T : Matrix n n ℂ := Matrix.single s r 1
  have hD : Dᴴ = D := by
    simp [D, P, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  have hT : Tᴴ = Matrix.single r s 1 := by simp [T]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  intro h
  simp only [Necessary, hs_span_iff] at h
  have hoff (i : n) (hi : r ≠ i) : (a : ℂ) * star (u r) * u i = 0 := by
    let G : Matrix n n ℂ := Matrix.single r i 1
    have hDG : Dᴴ * G = (a : ℂ) • G := by
      rw [hD]
      dsimp only [D, P, G]
      simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.single_mul_single_same, one_mul]
      module
    have hTG : (b • T)ᴴ * G = 0 := by
      rw [Matrix.conjTranspose_smul, hT, Matrix.smul_mul]
      simp [G, Matrix.single_mul_single_of_ne (c := (1 : ℂ)) r s r hrs.symm 1]
    have hg : ∀ j : Fin 2, Matrix.trace
        (((![D, b • T] : Fin 2 → Matrix n n ℂ) j)ᴴ * G) = 0 := by
      intro j
      fin_cases j
      · change Matrix.trace (Dᴴ * G) = 0
        rw [hDG, Matrix.trace_smul]
        simp [G, hi]
      · change Matrix.trace ((b • T)ᴴ * G) = 0
        rw [hTG, Matrix.trace_zero]
    have hz := h G hg 0
    change star u ⬝ᵥ ((Dᴴ * G) *ᵥ u) = 0 at hz
    rw [hDG] at hz
    simpa [G, Matrix.smul_mulVec, Matrix.single_mulVec_eq, dotProduct_smul,
      dotProduct_single, mul_assoc, mul_left_comm, mul_comm] using hz
  let c : ℂ := (1 - (Fintype.card n : ℂ)) / (a : ℂ)
  let G : Matrix n n ℂ := 1 + (c - 1) • P
  have hDG : Dᴴ * G = 1 - (Fintype.card n : ℂ) • P := by
    rw [hD]
    dsimp only [D, G, P]
    rw [← basis_ketbra r r]
    rw [filter_mul _ _ _ (basis_pair r s hrs).1]
    have hac : (a : ℂ) * c = 1 - (Fintype.card n : ℂ) := by
      dsimp [c]
      field_simp
    rw [hac, basis_ketbra]
    module
  have hTG : (b • T)ᴴ * G = star b • Matrix.single r s 1 := by
    rw [Matrix.conjTranspose_smul, hT, Matrix.smul_mul]
    dsimp only [G, P]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.single_mul_single_of_ne (c := (1 : ℂ)) r s r hrs.symm 1,
      smul_zero, add_zero]
  have hg : ∀ j : Fin 2, Matrix.trace
      (((![D, b • T] : Fin 2 → Matrix n n ℂ) j)ᴴ * G) = 0 := by
    intro j
    fin_cases j
    · change Matrix.trace (Dᴴ * G) = 0
      rw [hDG]
      simp [P, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    · change Matrix.trace ((b • T)ᴴ * G) = 0
      rw [hTG]
      simp [Matrix.trace_smul, hrs]
  have hz := h G hg 0
  change star u ⬝ᵥ ((Dᴴ * G) *ᵥ u) = 0 at hz
  rw [hDG] at hz
  have hdiag : 1 - (Fintype.card n : ℂ) * (star (u r) * u r) = 0 := by
    simpa [P, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.single_mulVec_eq, dotProduct_sub, dotProduct_smul, dotProduct_single,
      hu, mul_assoc, mul_left_comm, mul_comm] using hz
  have hur : u r ≠ 0 := by
    intro hzero
    simp [hzero] at hdiag
  have hrest (i : n) (hi : r ≠ i) : u i = 0 := by
    exact (mul_eq_zero.mp (hoff i hi)).resolve_left (mul_ne_zero haC (star_ne_zero.mpr hur))
  have heq : u = Pi.single r (u r) := by
    ext i
    by_cases hi : r = i
    · subst i; simp
    · simp [Pi.single_apply, hi, hrest i hi]
  have hnorm : star (u r) * u r = 1 := by
    rw [heq] at hu
    simpa [Pi.star_single, single_dotProduct] using hu
  rw [hnorm, mul_one, sub_eq_zero] at hdiag
  have hd : Fintype.card n = 1 := by exact_mod_cast hdiag.symm
  omega

private theorem elementary_square (x y : n → ℂ) (hxy : OrthogonalUnitPair x y) :
    (elementary (3 / 4) x y).comp (elementary (3 / 4) x y) =
      elementary (15 / 16) x y := by
  have hs : Real.sqrt (1 - (3 / 4 : ℝ)) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr
    norm_num
  have hs' : Real.sqrt (1 - (15 / 16 : ℝ)) = 1 / 4 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr
    norm_num
  let K := elementaryK (3 / 4) x
  let T := ketbra y x
  have hKK : K * K = elementaryK (15 / 16) x := by
    dsimp only [K, elementaryK]
    rw [filter_mul _ _ _ hxy.1, hs, hs']
    norm_num
  have hKT : K * T = T := by
    simp [K, elementaryK, T, Matrix.add_mul, Matrix.smul_mul, ketbra_mul, hxy.2.2]
  have hTK : T * K = (1 / 2 : ℂ) • T := by
    dsimp only [K, elementaryK, T]
    rw [hs]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ketbra_mul,
      hxy.1, one_smul]
    push_cast
    module
  have hTT : T * T = 0 := by simp [T, ketbra_mul, hxy.2.2]
  rw [elementary_as_sum _ (by norm_num), elementary_as_sum _ (by norm_num)]
  change (ad K + ((3 / 4 : ℝ) : ℂ) • ad T).comp
      (ad K + ((3 / 4 : ℝ) : ℂ) • ad T) = _
  simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp,
    LinearMap.comp_smul, ad_comp, hKK, hKT, hTK, hTT, ad_zero, ad_smul,
    smul_zero, add_zero, smul_smul]
  change _ = ad (elementaryK (15 / 16) x) + ((15 / 16 : ℝ) : ℂ) • ad T
  norm_num
  module

private theorem counterexample (hcard : 2 ≤ Fintype.card n) :
    ∃ Φ : MatrixMap n n ℂ, CPTP Φ ∧
      (∃ x y : n → ℂ, OrthogonalUnitPair x y ∧ Divides Φ x y) ∧
      ∀ (ι : Type*) [Fintype ι] (K : ι → Matrix n n ℂ),
        MatrixMap.of_kraus K K = Φ →
          ∀ u v : n → ℂ, OrthogonalUnitPair u v → ¬ Sufficient K u v := by
  obtain ⟨r, s, hrs⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card n)
  let x : n → ℂ := Pi.single r 1
  let y : n → ℂ := Pi.single s 1
  have hxy : OrthogonalUnitPair x y := basis_pair r s hrs
  let Φ := elementary (15 / 16) x y
  let Q := elementary (3 / 4) x y
  have hQQ : Q.comp Q = Φ := elementary_square x y hxy
  have hres : Φ.comp (elementaryInverse (3 / 4) x y) = Q := by
    rw [← hQQ, LinearMap.comp_assoc,
      (elementary_inverse_identities (3 / 4) (by norm_num) (by norm_num) x y hxy).1,
      LinearMap.comp_id]
  refine ⟨Φ, ⟨elementary_cp _ _ _, elementary_tp _ (by norm_num) (by norm_num) x y hxy⟩,
    ⟨x, y, hxy, (3 / 4), by norm_num, by norm_num, ?_⟩, ?_⟩
  · rw [hres]
    exact elementary_cp _ _ _
  · intro ι _ K hK u v huv hS
    let L : Fin 2 → Matrix n n ℂ :=
      ![elementaryK (15 / 16) x, elementaryL (15 / 16) x y]
    have hKL : MatrixMap.of_kraus K K = MatrixMap.of_kraus L L := by
      rw [hK]
      exact elementary_kraus _ _ _
    have hNu : Necessary L u u :=
      (necessary_independent K L hKL u u).mp hS.2
    have ha : Real.sqrt (1 - (15 / 16 : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (by norm_num)).ne'
    apply no_diagonal_criterion r s hrs hcard _ ha (Real.sqrt (15 / 16 : ℝ)) u huv.1
    simpa only [L, elementaryK, elementaryL, x, y, basis_ketbra] using hNu

/-- The necessary Kraus-space criterion is exact, while the sufficient criterion
is not necessary, both for a fixed pair and for existence of a pair. -/
theorem result (hcard : 2 ≤ Fintype.card n) :
    (∀ Φ : MatrixMap n n ℂ, CPTP Φ →
      ∃ K : (n × n) → Matrix n n ℂ, MatrixMap.of_kraus K K = Φ) ∧
    (∀ (ι : Type*) [Fintype ι] (K : ι → Matrix n n ℂ)
      (Φ : MatrixMap n n ℂ), CPTP Φ → MatrixMap.of_kraus K K = Φ →
        ∀ x y : n → ℂ, OrthogonalUnitPair x y →
          (Necessary K x y ↔ Divides Φ x y)) ∧
    (∀ (ι : Type*) [Fintype ι] (K : ι → Matrix n n ℂ)
      (Φ : MatrixMap n n ℂ), CPTP Φ → MatrixMap.of_kraus K K = Φ →
        ((∃ x y : n → ℂ, OrthogonalUnitPair x y ∧ Necessary K x y) ↔
          ∃ x y : n → ℂ, OrthogonalUnitPair x y ∧ Divides Φ x y)) ∧
    (∀ (t : ℝ), 0 < t → t < 1 → ∀ x y : n → ℂ, OrthogonalUnitPair x y →
      CPTP (elementary t x y) ∧
      (elementary t x y).comp (elementaryInverse t x y) = LinearMap.id ∧
      (elementaryInverse t x y).comp (elementary t x y) = LinearMap.id ∧
      (∀ X, Matrix.trace (elementaryInverse t x y X) = Matrix.trace X) ∧
      ∀ Φ : MatrixMap n n ℂ, CPTP Φ →
        MatrixMap.IsCompletelyPositive (Φ.comp (elementaryInverse t x y)) →
          CPTP (Φ.comp (elementaryInverse t x y)) ∧
            (Φ.comp (elementaryInverse t x y)).comp (elementary t x y) = Φ) ∧
    (∃ Φ : MatrixMap n n ℂ, CPTP Φ ∧
      (∃ x y : n → ℂ, OrthogonalUnitPair x y ∧ Divides Φ x y) ∧
      ∀ (ι : Type*) [Fintype ι] (K : ι → Matrix n n ℂ),
        MatrixMap.of_kraus K K = Φ →
          ∀ u v : n → ℂ, OrthogonalUnitPair u v → ¬ Sufficient K u v) := by
  refine ⟨?_, ?_, ?_, ?_, counterexample hcard⟩
  · intro Φ hΦ
    obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hΦ.1
    exact ⟨K, hK.symm⟩
  · intro ι _ K Φ _ hK x y hxy
    rw [← hK]
    exact fixed_pair_iff K x y hxy
  · intro ι _ K Φ _ hK
    rw [← hK]
    constructor
    · rintro ⟨x, y, hxy, hN⟩
      exact ⟨x, y, hxy, (fixed_pair_iff K x y hxy).mp hN⟩
    · rintro ⟨x, y, hxy, hE⟩
      exact ⟨x, y, hxy, (fixed_pair_iff K x y hxy).mpr hE⟩
  · intro t ht ht1 x y hxy
    obtain ⟨hi, hi'⟩ := elementary_inverse_identities t ht ht1 x y hxy
    refine ⟨⟨elementary_cp _ _ _, elementary_tp t ht.le ht1.le x y hxy⟩,
      hi, hi', elementary_inverse_tp t ht ht1 x y hxy, ?_⟩
    intro Φ hΦ hcp
    refine ⟨⟨hcp, ?_⟩, ?_⟩
    · intro X
      change Matrix.trace (Φ (elementaryInverse t x y X)) = Matrix.trace X
      rw [hΦ.2, elementary_inverse_tp t ht ht1 x y hxy]
    · rw [LinearMap.comp_assoc, hi', LinearMap.comp_id]

end D5.S3.Quantum.QuantumChannels.ElementaryChannelDivisibility
