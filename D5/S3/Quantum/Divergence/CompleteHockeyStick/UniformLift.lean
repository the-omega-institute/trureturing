/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Full Kraus-product span gives a uniform lift through amplified complementary compression. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! A uniform operator-norm lift through the amplified complementary compression. -/

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift

open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Foundation.FiniteStateChannel

universe u v k w

noncomputable section

section OperatorNorm

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Simultaneously permuting the rows and columns preserves the operator norm. -/
theorem norm_reindex (e : m ≃ n) (X : Matrix m m ℂ) :
    ‖Matrix.reindex e e X‖ = ‖X‖ := by
  let reindexStar : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
    StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      intro X
      ext i j
      rfl)
  change ‖reindexStar X‖ = ‖X‖
  exact StarAlgEquiv.norm_map reindexStar X

private def tensorIdentity :
    Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix n n ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' X Y := Matrix.add_kronecker X Y _
  map_smul' z X := Matrix.smul_kronecker z X _
  map_mul' X Y := by
    simpa only [Matrix.one_mul] using
      (Matrix.mul_kronecker_mul X Y (1 : Matrix n n ℂ) 1)
  map_star' X := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

private theorem norm_kronecker_le (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    ‖X ⊗ₖ Y‖ ≤ ‖X‖ * ‖Y‖ := by
  have hX : ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖X‖ :=
    NonUnitalStarAlgHom.norm_apply_le (tensorIdentity (m := m) (n := n)) X
  have hswap :
      Matrix.reindex (Equiv.prodComm n m) (Equiv.prodComm n m)
        (Y ⊗ₖ (1 : Matrix m m ℂ)) = (1 : Matrix m m ℂ) ⊗ₖ Y := by
    ext ⟨i, a⟩ ⟨j, b⟩
    change Y a b * (1 : Matrix m m ℂ) i j = (1 : Matrix m m ℂ) i j * Y a b
    exact mul_comm _ _
  have hY : ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ ≤ ‖Y‖ := by
    rw [← hswap, norm_reindex]
    exact NonUnitalStarAlgHom.norm_apply_le (tensorIdentity (m := n) (n := m)) Y
  calc
    ‖X ⊗ₖ Y‖ = ‖(X ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Y)‖ := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    _ ≤ ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ ‖X‖ * ‖Y‖ := mul_le_mul hX hY (norm_nonneg _) (norm_nonneg _)

end OperatorNorm

section Blocks

variable {A : Type u} [Fintype A] [DecidableEq A]
variable {R : Type w} [Fintype R] [DecidableEq R]

private def coordinateInclusion (i : A) : Matrix (R × A) R ℂ :=
  Matrix.of fun p r => if p = (r, i) then 1 else 0

private theorem mul_coordinateInclusion_apply {M : Type*}
    (X : Matrix M (R × A) ℂ) (i : A) (x : M) (r : R) :
    (X * coordinateInclusion (R := R) i : Matrix M R ℂ) x r = X x (r, i) := by
  simp [Matrix.mul_apply, coordinateInclusion, mul_ite, Finset.sum_ite_eq']

private theorem adjoint_coordinateInclusion_mul_apply {M : Type*}
    (X : Matrix (R × A) M ℂ) (i : A) (r : R) (x : M) :
    ((coordinateInclusion (R := R) i)ᴴ * X : Matrix R M ℂ) r x = X (r, i) x := by
  have h (p : R × A) :
      star (coordinateInclusion i p r) = if p = (r, i) then (1 : ℂ) else 0 := by
    by_cases hp : p = (r, i) <;> simp [coordinateInclusion, hp]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem norm_coordinateInclusion_le (i : A) :
    ‖coordinateInclusion (R := R) i‖ ≤ 1 := by
  let J := coordinateInclusion (R := R) i
  have hJ : Jᴴ * J = 1 := by
    ext r s
    change ((coordinateInclusion (R := R) i)ᴴ * J : Matrix R R ℂ) r s = _
    rw [adjoint_coordinateInclusion_mul_apply J i r s]
    simp [J, coordinateInclusion, Matrix.one_apply]
  have hOne : ‖(1 : Matrix R R ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ => by simp)
  change ‖J‖ ≤ 1
  apply (sq_le_sq₀ (norm_nonneg J) zero_le_one).mp
  simpa only [pow_two, one_mul, ← Matrix.l2_opNorm_conjTranspose_mul_self, hJ] using hOne

private def coefficientBlock (U : Matrix (R × A) (R × A) ℂ) (i j : A) :
    Matrix R R ℂ :=
  U.submatrix (fun r => (r, i)) (fun s => (s, j))

private theorem norm_coefficientBlock_le (U : Matrix (R × A) (R × A) ℂ) (i j : A) :
    ‖coefficientBlock U i j‖ ≤ ‖U‖ := by
  let Ji := coordinateInclusion (R := R) i
  let Jj := coordinateInclusion (R := R) j
  have hblock : Jiᴴ * U * Jj = coefficientBlock U i j := by
    ext r s
    change (((coordinateInclusion (R := R) i)ᴴ * U : Matrix R (R × A) ℂ) *
      coordinateInclusion (R := R) j : Matrix R R ℂ) r s = U (r, i) (s, j)
    rw [mul_coordinateInclusion_apply, adjoint_coordinateInclusion_mul_apply U i r (s, j)]
  have hi : ‖Jiᴴ‖ ≤ 1 :=
    (Matrix.l2_opNorm_conjTranspose Ji).le.trans (norm_coordinateInclusion_le i)
  have hj : ‖Jj‖ ≤ 1 := norm_coordinateInclusion_le j
  calc
    ‖coefficientBlock U i j‖ = ‖Jiᴴ * U * Jj‖ := by rw [hblock]
    _ ≤ ‖Jiᴴ * U‖ * ‖Jj‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Jiᴴ‖ * ‖U‖) * ‖Jj‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ ‖U‖ := by
      calc
        (‖Jiᴴ‖ * ‖U‖) * ‖Jj‖ ≤ (1 * ‖U‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hi (norm_nonneg _)) hj
            (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg _))
        _ = ‖U‖ := by simp

private theorem sum_coefficientBlock_kronecker (U : Matrix (R × A) (R × A) ℂ) :
    (∑ p : A × A, coefficientBlock U p.1 p.2 ⊗ₖ Matrix.single p.1 p.2 (1 : ℂ)) = U := by
  ext ⟨r, i⟩ ⟨s, j⟩
  have h := congrArg (fun M : Matrix A A ℂ => M i j)
    (Matrix.sum_sum_single (fun x y => U (r, x) (s, y)))
  simpa only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    coefficientBlock, Matrix.submatrix_apply, Matrix.single_apply, Matrix.of_apply, mul_ite,
    mul_one, mul_zero] using h

end Blocks

section Compression

variable {A : Type u} {B : Type v} {κ : Type k}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype κ] [DecidableEq κ]

private def sandwich {m n : Type*} [Fintype m] (V : Matrix m n ℂ) :
    Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (mulRightLinearMap n ℂ V).comp (mulLeftLinearMap m ℂ Vᴴ)

/-- The adjoint of the complementary channel in the dilation given by V. -/
private def complementCompression (V : Matrix (B × κ) A ℂ) :
    Matrix κ κ ℂ →ₗ[ℂ] Matrix A A ℂ :=
  (sandwich V).comp (Matrix.kroneckerBilinear (R := ℂ) (1 : Matrix B B ℂ))

private theorem complementCompression_apply (V : Matrix (B × κ) A ℂ) (W : Matrix κ κ ℂ) :
    complementCompression V W = Vᴴ * ((1 : Matrix B B ℂ) ⊗ₖ W) * V :=
  rfl

variable {R : Type w} [Fintype R] [DecidableEq R]

/-- Align the environment operator with the rows of the amplified Kraus column. -/
def referenceOutputOrder (B : Type v) (R : Type w) (κ : Type k) :
    B × (R × κ) ≃ R × (B × κ) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by rintro ⟨b, r, c⟩; rfl
  right_inv := by rintro ⟨r, b, c⟩; rfl

/-- Complementary compression in reference-first coordinates, as in referenceAction. -/
def amplifiedComplementCompression (V : Matrix (B × κ) A ℂ) :
    Matrix (R × κ) (R × κ) ℂ →ₗ[ℂ] Matrix (R × A) (R × A) ℂ :=
  let e := referenceOutputOrder B R κ
  (sandwich ((1 : Matrix R R ℂ) ⊗ₖ V)).comp
    ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
      (Matrix.kroneckerBilinear (R := ℂ) (1 : Matrix B B ℂ)))

private theorem amplifiedComplementCompression_apply (V : Matrix (B × κ) A ℂ)
    (W : Matrix (R × κ) (R × κ) ℂ) :
    amplifiedComplementCompression V W =
      let e := referenceOutputOrder B R κ
      let Vref := (1 : Matrix R R ℂ) ⊗ₖ V
      Vrefᴴ * Matrix.reindex e e ((1 : Matrix B B ℂ) ⊗ₖ W) * Vref :=
  rfl

private theorem amplifiedComplementCompression_kronecker (V : Matrix (B × κ) A ℂ)
    (X : Matrix R R ℂ) (W : Matrix κ κ ℂ) :
    amplifiedComplementCompression V (X ⊗ₖ W) = X ⊗ₖ complementCompression V W := by
  let e := referenceOutputOrder B R κ
  have hreindex : Matrix.reindex e e ((1 : Matrix B B ℂ) ⊗ₖ (X ⊗ₖ W)) =
      X ⊗ₖ ((1 : Matrix B B ℂ) ⊗ₖ W) := by
    ext ⟨r, b, c⟩ ⟨s, d, f⟩
    change (1 : Matrix B B ℂ) b d * (X r s * W c f) =
      X r s * ((1 : Matrix B B ℂ) b d * W c f)
    exact mul_left_comm _ _ _
  rw [amplifiedComplementCompression_apply, complementCompression_apply]
  change ((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ *
      Matrix.reindex e e ((1 : Matrix B B ℂ) ⊗ₖ (X ⊗ₖ W)) * ((1 : Matrix R R ℂ) ⊗ₖ V) =
    X ⊗ₖ (Vᴴ * ((1 : Matrix B B ℂ) ⊗ₖ W) * V)
  rw [hreindex, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- Fixed matrix-unit lifts give a single bound for every finite amplification. -/
private theorem exists_uniform_complement_lift (V : Matrix (B × κ) A ℂ)
    (L : (A × A) → Matrix κ κ ℂ)
    (hL : ∀ p, complementCompression V (L p) = Matrix.single p.1 p.2 (1 : ℂ)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (R : Type w) [Fintype R] [DecidableEq R]
        (U : Matrix (R × A) (R × A) ℂ), ‖U‖ ≤ 1 →
        ∃ W : Matrix (R × κ) (R × κ) ℂ,
          amplifiedComplementCompression V W = U ∧ ‖W‖ ≤ C := by
  refine ⟨max 1 (∑ p, ‖L p‖), le_max_left _ _, ?_⟩
  intro R _ _ U hU
  let W : Matrix (R × κ) (R × κ) ℂ :=
    ∑ p : A × A, coefficientBlock U p.1 p.2 ⊗ₖ L p
  refine ⟨W, ?_, ?_⟩
  · change amplifiedComplementCompression V (∑ p : A × A, coefficientBlock U p.1 p.2 ⊗ₖ L p) = U
    rw [map_sum]
    simp only [amplifiedComplementCompression_kronecker, hL]
    exact sum_coefficientBlock_kronecker U
  · calc
      ‖W‖ ≤ ∑ p : A × A, ‖coefficientBlock U p.1 p.2 ⊗ₖ L p‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p : A × A, ‖L p‖ := by
        apply Finset.sum_le_sum
        intro p _
        calc
          ‖coefficientBlock U p.1 p.2 ⊗ₖ L p‖ ≤ ‖coefficientBlock U p.1 p.2‖ * ‖L p‖ :=
            norm_kronecker_le _ _
          _ ≤ 1 * ‖L p‖ := mul_le_mul_of_nonneg_right
            ((norm_coefficientBlock_le U p.1 p.2).trans hU) (norm_nonneg _)
          _ = ‖L p‖ := one_mul _
      _ ≤ max 1 (∑ p, ‖L p‖) := le_max_right _ _

private theorem complementCompression_kraus_single (K : κ → Matrix B A ℂ) (i j : κ) :
    complementCompression (krausColumn K) (Matrix.single i j (1 : ℂ)) =
      (K i)ᴴ * K j := by
  have hcolumn (b : B) (c : κ) (y : A) :
      (((1 : Matrix B B ℂ) ⊗ₖ Matrix.single i j (1 : ℂ)) * krausColumn K) (b, c) y =
        if i = c then K j b y else 0 := by
    by_cases hc : i = c
    · rw [ite_eq_left hc, Matrix.mul_apply, Finset.sum_eq_single (b, j)]
      · simp [hc, krausColumn]
      · rintro ⟨d, l⟩ _ hne
        by_cases hd : b = d
        · have hl : j ≠ l := fun h => hne (Prod.ext hd.symm h.symm)
          simp [hl]
        · simp [hd]
      · simp
    · rw [ite_eq_right hc, Matrix.mul_apply, Fintype.sum_prod_type]
      simp [hc]
  rw [complementCompression_apply, Matrix.mul_assoc]
  ext x y
  change (∑ p : B × κ, star (K p.2 p.1 x) *
      (((1 : Matrix B B ℂ) ⊗ₖ Matrix.single i j (1 : ℂ)) * krausColumn K) p y) =
    ∑ b : B, star (K i b x) * K j b y
  rw [Fintype.sum_prod_type]
  simp [hcolumn, mul_ite, Finset.sum_ite_eq]

/-- Full complex span of the Kraus products supplies the fixed matrix-unit lifts. -/
theorem exists_uniform_complement_lift_of_full_span (K : κ → Matrix B A ℂ)
    (hspan : Submodule.span ℂ (Set.range fun p : κ × κ => (K p.1)ᴴ * K p.2) = ⊤) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (R : Type w) [Fintype R] [DecidableEq R]
        (U : Matrix (R × A) (R × A) ℂ), ‖U‖ ≤ 1 →
        ∃ W : Matrix (R × κ) (R × κ) ℂ,
          amplifiedComplementCompression (krausColumn K) W = U ∧ ‖W‖ ≤ C := by
  let T := complementCompression (krausColumn K)
  have hle : Submodule.span ℂ (Set.range fun p : κ × κ => (K p.1)ᴴ * K p.2) ≤
      LinearMap.range T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact LinearMap.mem_range.mpr
      ⟨Matrix.single i j (1 : ℂ), complementCompression_kraus_single K i j⟩
  have htop : ⊤ ≤ LinearMap.range T := by simpa only [hspan] using hle
  have hsurj : Function.Surjective T := LinearMap.range_eq_top.mp (top_unique htop)
  let L : (A × A) → Matrix κ κ ℂ :=
    fun p => Classical.choose (hsurj (Matrix.single p.1 p.2 (1 : ℂ)))
  have hL : ∀ p, complementCompression (krausColumn K) (L p) =
      Matrix.single p.1 p.2 (1 : ℂ) :=
    fun p => Classical.choose_spec (hsurj (Matrix.single p.1 p.2 (1 : ℂ)))
  exact exists_uniform_complement_lift (krausColumn K) L hL

end Compression

end

end D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift
