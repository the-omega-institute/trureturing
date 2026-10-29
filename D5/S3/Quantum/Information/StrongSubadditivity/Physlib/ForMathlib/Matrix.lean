/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/Matrix
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/ForMathlib/Matrix.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

@[expose] public section

set_option relaxedAutoImplicit true

open BigOperators
variable {n 𝕜 : Type*}
variable [RCLike 𝕜] [DecidableEq n]
namespace Matrix
open scoped ComplexOrder MatrixOrder

section spectrum_kron

--This is really really ugly, and already *after* trying to clean it up a bit.
set_option maxHeartbeats 7200000

open Kronecker
open scoped Pointwise

private lemma spectrum_prod_complex {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∀ x : 𝕜, x ∈ spectrum 𝕜 (A ⊗ₖ B) → ∃ a ∈ spectrum 𝕜 A, ∃ b ∈ spectrum 𝕜 B, x = a * b := by
  intro x hx
  have h_det : Matrix.det (A ⊗ₖ B - x • 1) = 0 := by
    rw [ spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det ] at hx;
    rw [ ← neg_sub, Matrix.det_neg ]
    simp_all only [isUnit_iff_ne_zero, ne_eq, Decidable.not_not, Fintype.card_prod,
      mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, not_or, false_and, false_or]
    convert hx using 1;
    congr! 1;
    ext ⟨ i, j ⟩ ⟨ i', j' ⟩;
    simp [ Algebra.smul_def ]
  -- Since $A$ and $B$ are Hermitian, they are diagonalizable. Let $P$ and $Q$ be unitary matrices such that $P^*AP$ and $Q^*BQ$ are diagonal.
  obtain ⟨P, hP₁, ⟨D, hD⟩⟩ : ∃ P : Matrix d d 𝕜, P.det ≠ 0 ∧ ∃ D : Matrix d d 𝕜, D.IsDiag ∧ P⁻¹ * A * P = D := by
    refine' ⟨ hA.eigenvectorUnitary, _, Matrix.diagonal ( RCLike.ofReal ∘ hA.eigenvalues ), _, _ ⟩;
    · intro h_det_zero;
      exact absurd h_det_zero <| isUnit_iff_ne_zero.mp <| UnitaryGroup.det_isUnit hA.eigenvectorUnitary
    · exact isDiag_diagonal (RCLike.ofReal ∘ hA.eigenvalues);
    · -- Since $U$ is unitary, $U⁻¹ = U*$, and thus $U⁻¹ * U = I$.
      have h_unitary : (hA.eigenvectorUnitary : Matrix d d 𝕜)⁻¹ = star (hA.eigenvectorUnitary : Matrix d d 𝕜) := by
        rw [ Matrix.inv_eq_left_inv ];
        simp
      -- Substitute h_unitary into the equation.
      rw [h_unitary];
      convert Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary hA using 1
      simp
  obtain ⟨Q, hQ₁, ⟨E, hE⟩⟩ : ∃ Q : Matrix d₂ d₂ 𝕜, Q.det ≠ 0 ∧ ∃ E : Matrix d₂ d₂ 𝕜, E.IsDiag ∧ Q⁻¹ * B * Q = E := by
    have := Matrix.IsHermitian.spectral_theorem hB;
    -- By the spectral theorem, since B is Hermitian, there exists a unitary matrix Q and a diagonal matrix D such that B = Q * D * Q⁻¹.
    obtain ⟨Q, hQ_unitary, D, hD_diag, hQ⟩ : ∃ Q : Matrix d₂ d₂ 𝕜, Q.det ≠ 0 ∧ ∃ D : Matrix d₂ d₂ 𝕜, D.IsDiag ∧ B = Q * D * Q⁻¹ := by
      refine' ⟨ hB.eigenvectorUnitary, _, Matrix.diagonal ( RCLike.ofReal ∘ hB.eigenvalues ), _, _ ⟩;
      · intro h_det_zero;
        -- Since the eigenvector unitary matrix is unitary, its determinant is non-zero.
        have h_unitary_det : ∀ (U : Matrix d₂ d₂ 𝕜), U * star U = 1 → U.det ≠ 0 :=
          fun U hU => Matrix.det_ne_zero_of_right_inverse hU;
        exact h_unitary_det _ ( by simp) h_det_zero;
      · exact isDiag_diagonal (RCLike.ofReal ∘ hB.eigenvalues);
      · convert this using 1;
        rw [ Matrix.inv_eq_left_inv ];
        · simp
          rfl
        · simp only [SetLike.coe_mem, Unitary.star_mul_self_of_mem]
    refine ⟨ Q, hQ_unitary, D, hD_diag, ?_ ⟩
    simp [ hQ, mul_assoc, hQ_unitary, isUnit_iff_ne_zero ];
  -- Then $(P \otimes Q)^{-1}(A \otimes B)(P \otimes Q) = D \otimes E$, where $D$ and $E$ are diagonal matrices.
  have h_diag : (P.kronecker Q)⁻¹ * (A ⊗ₖ B) * (P.kronecker Q) = D ⊗ₖ E := by
    -- Using the properties of the Kronecker product and the fact that $P$ and $Q$ are invertible, we can simplify the expression.
    have h_kronecker : (P.kronecker Q)⁻¹ * (A.kronecker B) * (P.kronecker Q) = (P⁻¹ * A * P).kronecker (Q⁻¹ * B * Q) := by
      have h_kronecker : ∀ (X Y : Matrix d d 𝕜) (Z W : Matrix d₂ d₂ 𝕜), (X.kronecker Z) * (Y.kronecker W) = (X * Y).kronecker (Z * W) := by
        intro X Y Z W; ext i j; simp [ Matrix.mul_apply ] ;
        simp only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
        exact Fintype.sum_prod_type_right _
      rw [Matrix.inv_eq_right_inv, h_kronecker, h_kronecker];
      convert h_kronecker P P⁻¹ Q Q⁻¹ using 1;
      simp [ hP₁, hQ₁, isUnit_iff_ne_zero ];
    aesop;
  -- Since $D$ and $E$ are diagonal matrices, the determinant of $(D \otimes E - xI)$ is the product of the determinants of $(D - xI)$ and $(E - xI)$.
  have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = 0 := by
    have h_det_diag : Matrix.det ((P.kronecker Q)⁻¹ * (A ⊗ₖ B - x • 1) * (P.kronecker Q)) = Matrix.det (D ⊗ₖ E - x • 1) := by
      simp [ ← h_diag, mul_sub, sub_mul ];
      simp [ Matrix.det_kronecker, hP₁, hQ₁ ];
    simp_all [ Matrix.det_mul ];
  -- Since $D$ and $E$ are diagonal matrices, the determinant of $(D \otimes E - xI)$ is the product of the determinants of $(D - xI)$ and $(E - xI)$. Therefore, there must be some $i$ and $j$ such that $D_{ii} * E_{jj} = x$.
  obtain ⟨i, j, hij⟩ : ∃ i : d, ∃ j : d₂, D i i * E j j = x := by
    contrapose! h_det_diag;
    have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = ∏ i : d, ∏ j : d₂, (D i i * E j j - x) := by
      have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = Matrix.det (Matrix.diagonal (fun p : d × d₂ => D p.1 p.1 * E p.2 p.2 - x)) := by
        congr with p q
        simp_all only [ne_eq, kronecker, sub_apply,
          kroneckerMap_apply, smul_apply, smul_eq_mul]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨fst_1, snd_1⟩ := q
        obtain ⟨left, rfl⟩ := hD
        obtain ⟨left_1, rfl⟩ := hE
        simp_all only
        by_cases h : fst = fst_1 <;> by_cases h' : snd = snd_1 <;> simp [ h, h', Matrix.one_apply ];
        · exact Or.inr ( left_1 ( by aesop ) );
        · exact Or.inl ( left h );
        · exact Or.inl ( left h );
      simp_all [ Matrix.det_diagonal ];
      exact Fintype.prod_prod_type fun (x_2 : d × d₂) => D x_2.1 x_2.1 * E x_2.2 x_2.2 - x
    exact h_det_diag.symm ▸ Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero_of_ne <| by solve_by_elim;
  refine' ⟨ D i i, _, E j j, _, _ ⟩
  · simp_all [ spectrum.mem_iff ];
    simp_all [ Matrix.isUnit_iff_isUnit_det ];
    have h_det_diag : Matrix.det (P⁻¹ * (D i i • 1 - A) * P) = 0 := by
      simp_all [ mul_sub, sub_mul, mul_assoc ];
      rw [ Matrix.det_eq_zero_of_row_eq_zero i ]
      intro j_1
      subst hij
      simp_all only [map_mul, sub_apply, smul_apply, smul_eq_mul]
      obtain ⟨left, rfl⟩ := hD
      obtain ⟨left_1, rfl⟩ := hE
      by_cases hij : i = j_1 <;> simp_all [ Matrix.one_apply ];
      exact left hij;
    simp_all [ Matrix.det_mul];
    convert h_det_diag using 1;
    exact congr_arg Matrix.det ( by ext i j; by_cases hi : i = j <;> simp [ hi, Algebra.smul_def ] );
  · simp_all [ spectrum.mem_iff ];
    -- Since $E$ is diagonal, $E j j - B$ is singular, hence not invertible.
    have h_singular : Matrix.det (E j j • 1 - B) = 0 := by
      have h_singular : Matrix.det (Q⁻¹ * (E j j • 1 - B) * Q) = 0 := by
        simp [ mul_sub, sub_mul, hE.2 ];
        rw [ Matrix.det_eq_zero_of_row_eq_zero j ]
        intro j_1
        subst hij
        simp_all only [map_mul, isUnit_iff_ne_zero, ne_eq, not_false_eq_true, nonsing_inv_mul, sub_apply,
          smul_apply, smul_eq_mul]
        obtain ⟨left, rfl⟩ := hD
        obtain ⟨left_1, rfl⟩ := hE
        by_cases h : j = j_1 <;> aesop;
      simp_all [ Matrix.det_mul ];
    simp_all [ Matrix.isUnit_iff_isUnit_det ];
    convert h_singular using 1;
    simp [ Algebra.smul_def ];
  · simp_all [ spectrum.mem_iff ];

private lemma spectrum_prod_le {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    spectrum ℝ (A ⊗ₖ B) ⊆ spectrum ℝ A * spectrum ℝ B := by
  intro x hx
  suffices h : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ B, x = a * b by
    rcases h with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  obtain ⟨_, ha, _, hb, h₁, ⟨a', rfl⟩, ⟨b', rfl⟩⟩ : ∃ a ∈ spectrum 𝕜 A, ∃ b ∈ spectrum 𝕜 B,
      x = a * b ∧
      a ∈ Set.range (algebraMap ℝ 𝕜) ∧ b ∈ Set.range (algebraMap ℝ 𝕜) := by
    obtain ⟨a, ha, b, hb, hx_eq⟩ := spectrum_prod_complex hA hB x (by exact hx);
    have ha' := ha
    have hb' := hb
    rw [hA.spectrum_eq_image_range] at ha
    rw [hB.spectrum_eq_image_range] at hb
    grind
  use a', ha, b', hb
  simp only [RCLike.algebraMap_eq_ofReal] at h₁
  exact_mod_cast h₁

set_option maxHeartbeats 800000
open Kronecker in
open scoped Pointwise in
lemma spectrum_prod {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    spectrum ℝ (A ⊗ₖ B) = spectrum ℝ A * spectrum ℝ B := by
  apply subset_antisymm
  · exact spectrum_prod_le hA hB
  · rintro x ⟨ y, hy, z, hz, rfl ⟩;
    -- Since $y$ is an eigenvalue of $A$ and $z$ is an eigenvalue of $B$, there exist eigenvectors $v$ and $w$ such that $A*v = y*v$ and $B*w = z*w$.
    obtain ⟨v, hv⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ A.mulVec v = y • v := by
      rw [ spectrum.mem_iff ] at hy;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hy;
      simp_all [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all [ sub_mul, Matrix.one_apply, Algebra.algebraMap_eq_smul_one ];
      exact ⟨ this.choose, this.choose_spec.1, fun x => by linear_combination -this.choose_spec.2 x ⟩
    obtain ⟨w, hw⟩ : ∃ w : d₂ → 𝕜, w ≠ 0 ∧ B.mulVec w = z • w := by
      rw [ spectrum.mem_iff ] at hz;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hz;
      simp_all [ Matrix.sub_mulVec ];
      obtain ⟨ w, hw, hw' ⟩ := this; use w; simp_all [ sub_eq_zero, Algebra.algebraMap_eq_smul_one ] ;
      simp_all [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all [ Matrix.one_apply];
    refine' spectrum.mem_iff.mpr _;
    -- Consider the vector $v \otimes w$.
    set v_tensor_w : (d × d₂) → 𝕜 := fun p => v p.1 * w p.2;
    -- We need to show that $v \otimes w$ is an eigenvector of $A \otimes B$ with eigenvalue $yz$.
    have h_eigenvector : (Matrix.kroneckerMap (· * ·) A B).mulVec v_tensor_w = (y * z) • v_tensor_w := by
      ext ⟨ i, j ⟩ ;
      simp [ Matrix.mulVec, dotProduct] at *
      simp [ funext_iff, Matrix.mulVec, dotProduct ] at hv hw ⊢
      rw [ Fintype.sum_prod_type ]
      simp_all only [v_tensor_w]
      obtain ⟨left, right⟩ := hv
      obtain ⟨left_1, right_1⟩ := hw
      -- By separating the sums, we can apply the given equalities.
      have h_separate : ∑ x, ∑ x_1, A i x * B j x_1 * (v x * w x_1) = (∑ x : d, A i x * v x) * (∑ x_1 : d₂, B j x_1 * w x_1) := by
        simp only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      rw [ h_separate, right, right_1 ]
      simp [RCLike.real_smul_eq_coe_mul]
      ring_nf
    -- Since $v \otimes w$ is an eigenvector of $A \otimes B$ with eigenvalue $yz$, we have $(A \otimes B - yzI)(v \otimes w) = 0$.
    have h_eigenvector_zero : ((A ⊗ₖ B) - (y * z) • 1) *ᵥ v_tensor_w = 0 := by
      simp [ h_eigenvector, Matrix.sub_mulVec ];
      simp [ Matrix.mulVec, funext_iff ];
      simp [ Matrix.one_apply, dotProduct ];
    -- Since $v \otimes w$ is non-zero, we have $(A \otimes B - yzI)(v \otimes w) = 0$ implies that $A \otimes B - yzI$ is not invertible.
    have h_not_invertible : ¬IsUnit (A ⊗ₖ B - (y * z) • 1) := by
      simp only [ne_eq, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Decidable.not_not, v_tensor_w] at *
      rw [ ← Matrix.exists_mulVec_eq_zero_iff ]
      refine' ⟨ v_tensor_w, _, h_eigenvector_zero ⟩;
      simp [ funext_iff ] at hv hw ⊢
      obtain ⟨left, right⟩ := hv
      obtain ⟨left_1, right_1⟩ := hw
      exact ⟨left.choose, left_1.choose, mul_ne_zero left.choose_spec left_1.choose_spec⟩
    rw [← IsUnit.neg_iff, neg_sub]
    convert h_not_invertible using 4
    simp [ Algebra.smul_def ]

end spectrum_kron

open ComplexOrder in
open MatrixOrder in
lemma PosDef.zero_lt {n : Type*} [Nonempty n] [Fintype n] {A : Matrix n n ℂ} (hA : A.PosDef) : 0 < A := by
  apply lt_of_le_of_ne
  · replace hA := hA.posSemidef
    rwa [Matrix.nonneg_iff_posSemidef]
  · rintro rfl; exact absurd (hA.diag_pos (i := Classical.arbitrary n)) (by simp)


lemma IsHermitian.spectrum_eq_image_eigenvalues [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    spectrum ℝ A = Finset.univ.image hA.eigenvalues := by
  simpa using hA.spectrum_real_eq_range_eigenvalues

/- This lemma looks "wrong" in the sense that it's specifically about `Fintype.card foo = Finset.card bar`,
why not just use the underlying fact `foo = ↑bar`? It turns out this actually gives annoying issues
with dependent rewrites, given the necessary `Fintype` instance. Using the above theorem for example,
trying `rw [hA.spectrum_eq_image_eigenvalues]` fails because of dependent types. -/
lemma IsHermitian.card_spectrum_eq_image [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
  [Fintype (spectrum ℝ A)] :
    Fintype.card (spectrum ℝ A) = (Finset.univ.image hA.eigenvalues).card := by
  trans (Set.univ.image hA.eigenvalues).toFinset.card
  · symm
    convert Set.toFinset_card _
    rw [Set.image_univ]
    exact Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA
  · simp

section iInf_iSup
namespace IsHermitian

variable {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}

open ComplexOrder

lemma sub_iInf_eignevalues (hA : A.IsHermitian) :
    (A - iInf hA.eigenvalues • 1).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · simpa [ Matrix.IsHermitian, sub_eq_add_neg ] using hA
  · intro x
    have h_eigenvalue : ∀ i, hA.eigenvalues i ≥ iInf hA.eigenvalues := by
      -- By definition of infimum, for any eigenvalue $i$, we have $hA.eigenvalues i \geq iInf hA.eigenvalues$.
      intros i
      apply le_of_forall_le
      intro j a
      exact le_trans a (ciInf_le ( Finite.bddBelow_range hA.eigenvalues ) i );
    -- Since $A$ is Hermitian, we can diagonalize it as $A = Q \Lambda Q^*$, where $Q$ is unitary and $\Lambda$ is diagonal with the eigenvalues on the diagonal.
    obtain ⟨Q, Λ, hQ, hΛ⟩ : ∃ Q : Matrix d d ℂ, ∃ Λ : d → ℂ, Q.conjTranspose * Q = 1 ∧ A = Q * Matrix.diagonal Λ * Q.conjTranspose ∧ ∀ i, Λ i = Matrix.IsHermitian.eigenvalues hA i := by
      have := hA.spectral_theorem;
      refine' ⟨ _, _, _, this, _ ⟩;
      · simp [ ← Matrix.ext_iff ];
        intro i j; rw [ Matrix.mul_apply ] ; simp [ Matrix.one_apply ] ;
        have := hA.eigenvectorBasis.orthonormal;
        rw [ orthonormal_iff_ite ] at this;
        rw [← this i j]
        simp [PiLp.inner_apply, mul_comm]
      · simp
    -- Since $Q$ is unitary, we have $Q^* Q = I$, and thus $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$.
    have h_diag : Q.conjTranspose * (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1) * Q = Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA))) := by
      simp [ hΛ, mul_sub, sub_mul, mul_assoc, hQ ];
      simp [ ← mul_assoc, hQ];
      ext i j ; by_cases hij : i = j <;> aesop;
    -- Since $Q$ is unitary, we have $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$, and thus $x^* (A - \lambda_{\min} I) x = (Q^* x)^* (\Lambda - \lambda_{\min} I) (Q^* x)$.
    have h_quad_form : Star.star x ⬝ᵥ (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1).mulVec x = Star.star (Q.conjTranspose.mulVec x) ⬝ᵥ (Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA)))).mulVec (Q.conjTranspose.mulVec x) := by
      rw [ ← h_diag ];
      simp [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, mul_eq_one_comm.mp hQ];
      simp only [mulVec_conjTranspose, star_star, vecMul_vecMul];
      rw [ ← Matrix.mul_assoc, mul_eq_one_comm.mp hQ, one_mul ];
    simp_all only [ge_iff_le, dotProduct, Pi.star_apply, RCLike.star_def, mulVec, sub_apply,
      smul_apply, Complex.real_smul, conjTranspose_apply, star_sum, star_mul',
      RingHomCompTriple.comp_apply, RingHom.id_apply];
    simp_all only [implies_true, and_self, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, ↓reduceIte];
    -- Since the eigenvalues are real and the sums involving Q and x are complex, the product of a complex number and its conjugate is non-negative.
    have h_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      have h_nonneg : 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * star (∑ x_2, Q x_2 i * star (x x_2)) := by
        exact mul_star_self_nonneg (∑ x_2, Q x_2 i * star (x x_2))
      convert h_nonneg using 1;
      simp [ mul_comm, Finset.mul_sum _ _ _];
    -- Since each term in the sum is a product of a non-negative number and a non-negative eigenvalue difference, the entire sum is non-negative.
    have h_sum_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (((↑(hA.eigenvalues i) : ℂ) - (↑(iInf hA.eigenvalues) : ℂ)) * ∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      specialize h_nonneg i
      simp_all only [mul_assoc, mul_comm, mul_left_comm, RCLike.star_def] ;
      rw [ ← mul_assoc ];
      exact mul_nonneg h_nonneg ( sub_nonneg_of_le <| mod_cast h_eigenvalue i );
    convert! Finset.sum_nonneg fun i _ => h_sum_nonneg i;
    rw [ hΛ.1 ]

lemma iInf_eigenvalues_le_dotProduct_mulVec (hA : A.IsHermitian) (v : d → ℂ) :
    iInf hA.eigenvalues * (star v ⬝ᵥ v) ≤ star v ⬝ᵥ A *ᵥ v := by
  conv_lhs =>
    equals (star v ⬝ᵥ (iInf hA.eigenvalues • 1) *ᵥ v) =>
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mulVec]
      simp [Matrix.one_apply, mul_assoc, mul_left_comm, Finset.mul_sum]
  rw [← sub_nonneg, ← dotProduct_sub, ← Matrix.sub_mulVec]
  replace hA := sub_iInf_eignevalues hA
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA
  exact hA.right v

lemma iInf_eigenvalues_le_of_posSemidef
  (hAB : (B - A).PosSemidef) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues := by
  rcases isEmpty_or_nonempty d
  · simp
  contrapose! hAB
  rw [posSemidef_iff_dotProduct_mulVec]
  simp only [not_and, not_forall]
  intro _
  apply exists_lt_of_ciInf_lt at hAB
  rcases hAB with ⟨i, hi⟩
  use WithLp.ofLp (hB.eigenvectorBasis i)
  simp only [sub_mulVec, dotProduct_sub, sub_nonneg]
  rw [hB.mulVec_eigenvectorBasis i]
  simp only [dotProduct_smul, Complex.real_smul]
  nth_rw 2 [dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  intro h
  replace h := (iInf_eigenvalues_le_dotProduct_mulVec hA _).trans h
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [OrthonormalBasis.inner_eq_one, mul_one, Complex.real_le_real] at h
  order

open MatrixOrder in
lemma iInf_eigenvalues_le (hAB : A ≤ B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues :=
  iInf_eigenvalues_le_of_posSemidef hAB hA hB

open MatrixOrder in
lemma iInf_eigenvalues_smul_one_le (hA : A.IsHermitian) : iInf hA.eigenvalues • 1 ≤ A :=
  (PosSemidef.smul_one_le_of_eigenvalues_iff hA (iInf hA.eigenvalues)).mp
    (ciInf_le (Finite.bddBelow_range _))

end IsHermitian
end iInf_iSup

section matrix_order

--Shortcut instances. Having these around speeds things out considerably, in some cases?
open MatrixOrder

variable {d : Type*} [Fintype d]

lemma _shortcut_posSMulMono : PosSMulMono ℝ (Matrix d d ℂ) :=
  inferInstance

lemma _shortcut_posSmulReflectLE : PosSMulReflectLE ℝ (Matrix d d ℂ) :=
  inferInstance

scoped[MatrixOrder] attribute [instance] Matrix._shortcut_posSMulMono
scoped[MatrixOrder] attribute [instance] Matrix._shortcut_posSmulReflectLE

end matrix_order

open ComplexOrder in
lemma IsHermitian.spectrum_subset_Ici_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x : Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (x - A).PosSemidef) :
    spectrum ℝ x ⊆ Set.Ici (⨅ i, hA.eigenvalues i) := by
  --Thanks Aristotle
  intro μ hμ
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ x.mulVec v = μ • v := by
    have h_singular : ∃ v : d → 𝕜, v ≠ 0 ∧ (μ • 1 - x).mulVec v = 0 := by
      simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq, Decidable.not_not] at hμ
      convert Matrix.exists_mulVec_eq_zero_iff.mpr hμ;
      simp [Algebra.smul_def]
    refine h_singular.imp fun v h ↦ ⟨h.left, ?_⟩
    simp_all [Matrix.sub_mulVec, sub_eq_iff_eq_add, funext_iff, Matrix.mulVec, dotProduct, Matrix.one_apply]
  -- Since $x - A$ is positive semidefinite, for any eigenvalue $\lambda$ of $x$, we have $\lambda \geq \min(\text{eigenvalues of } A)$.
  have h_lower_bound : ∀ (v : d → 𝕜), v ≠ 0 → (star v ⬝ᵥ (x.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
    intro v hv_nonzero
    have h_eigenvalue : (star v ⬝ᵥ (A.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
      have h_expand : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        have h_decomp : A = ∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) := by
          convert Matrix.IsHermitian.spectral_theorem hA using 1;
          ext i j
          simp only [RCLike.star_def, Matrix.smul_of, Matrix.sum_apply, Matrix.of_apply,
            Pi.smul_apply, Matrix.diagonal, Function.comp_apply, Matrix.mul_apply,
            Matrix.IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.star_apply,
            Unitary.conjStarAlgAut_apply]
          simp [ mul_comm, mul_left_comm, Algebra.smul_def ]
          congr! 1
          simp [Algebra.algebraMap_eq_smul_one]
        -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$.
        have h_subst : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star v ⬝ᵥ (Matrix.mulVec (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) v)) := by
          -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$ and use the linearity of matrix multiplication.
          have h_subst : (star v ⬝ᵥ (A.mulVec v)) = (star v ⬝ᵥ ((∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v)) := by
            rw [ ← h_decomp ];
          -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product.
          have h_distribute : (star v ⬝ᵥ (∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) = ∑ i, (star v ⬝ᵥ ((hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) := by
            -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product. This follows from the fact that matrix multiplication is linear.
            have h_distribute : ∀ (M N : Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (M + N).mulVec v = Star.star v ⬝ᵥ M.mulVec v + Star.star v ⬝ᵥ N.mulVec v := by
              simp [ Matrix.add_mulVec, dotProduct_add ];
            -- By induction on the number of terms in the sum, we can apply the distributive property repeatedly.
            have h_induction : ∀ (n : ℕ) (M : Fin n → Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (∑ i, M i).mulVec v = ∑ i, Star.star v ⬝ᵥ (M i).mulVec v := by
              intro n M v
              induction n
              · simp [*]
              · simp [Fin.sum_univ_succ, *]
            convert h_induction ( Fintype.card d ) ( fun i => Matrix.of ( hA.eigenvalues ( Fintype.equivFin d |>.symm i ) • fun j k => hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) j * starRingEnd 𝕜 ( hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) k ) ) ) v using 1;
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
          convert h_distribute using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.of_apply,
            Finset.mul_sum _ _ _, Matrix.smul_apply, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm];
          simp [ Algebra.smul_def ];
        convert h_subst using 2;
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mul_assoc, Matrix.mulVec,
          Matrix.of_apply, mul_eq_mul_left_iff, map_eq_zero];
        simp [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      -- Since $\lambda_i \geq \inf(\text{eigenvalues of } A)$ for all $i$, we can bound each term in the sum.
      have h_bound : ∀ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) ≥ (⨅ i, (hA.eigenvalues i)) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        intro i
        have h_eigenvalue_bound : (hA.eigenvalues i) ≥ (⨅ i, (hA.eigenvalues i)) :=
          ciInf_le (Set.finite_range _).bddBelow _
        -- Since the product of the inner products is real and non-negative, multiplying both sides of the inequality by this product preserves the inequality.
        have h_nonneg : 0 ≤ (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
          -- Since the inner product is conjugate symmetric, we have star v ⬝ᵥ (hA.eigenvectorBasis i) = conjugate(star (hA.eigenvectorBasis i) ⬝ᵥ v).
          have h_conj_symm : star v ⬝ᵥ (hA.eigenvectorBasis i) = star (star (hA.eigenvectorBasis i) ⬝ᵥ v) := by
            simp [ dotProduct, mul_comm];
          rw [ h_conj_symm ];
          exact mul_star_self_nonneg (star (hA.eigenvectorBasis i) ⬝ᵥ v);
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_right ( mod_cast h_eigenvalue_bound ) h_nonneg;
      -- Since $\sum_{i} (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v$, we can factor out $(⨅ i, (hA.eigenvalues i))$ from the sum.
      have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
        have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i) = v := by
          have := hA.eigenvectorBasis.sum_repr (WithLp.toLp 2 v);
          convert this using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm,
            hA.eigenvectorBasis.repr_apply_apply, PiLp.inner_apply, RCLike.inner_apply];
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul]
          have key : ∀ (c : d → 𝕜) (f : d → EuclideanSpace 𝕜 d) (w : d → 𝕜),
              (∑ x, c x • (f x).ofLp = w) ↔ (∑ x, c x • f x = WithLp.toLp 2 w) := by
            intro c f w
            conv_lhs => rw [show ∑ x, c x • (f x).ofLp = (∑ x, c x • f x).ofLp from by
              rw [WithLp.ofLp_sum]; simp [WithLp.ofLp_smul]]
            constructor
            · intro h; apply_fun WithLp.toLp 2 at h; simpa using h
            · intro h; apply_fun WithLp.ofLp at h; simpa using h
          exact key _ _ _
        -- Taking the inner product of both sides of h_sum with star v, we get the desired equality.
        have h_inner : star v ⬝ᵥ (∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
          congr 1
          simp_rw [← WithLp.ofLp_smul, ← WithLp.ofLp_sum, h_sum]
        convert h_inner using 1;
        simp [ dotProduct, Finset.mul_sum _ _ _ ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      rw [ h_expand ];
      refine' le_trans _ ( Finset.sum_le_sum fun i _ => h_bound i );
      simp only [ mul_assoc];
      rw [ ← Finset.mul_sum _ _ _, h_sum ];
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hl
    have := hl.2 v
    simp [Matrix.sub_mulVec] at this
    exact le_trans h_eigenvalue this;
  change (⨅ i, hA.eigenvalues i) ≤ μ
  have := h_lower_bound v hv₁
  simp_all only [ne_eq, star, RCLike.star_def, Matrix.dotProduct_mulVec, ge_iff_le,
    dotProduct_smul];
  simp_all only [dotProduct, mul_comm, RCLike.mul_conj];
  rw [ Algebra.smul_def ] at this;
  -- Since the sum of the squares of the norms of v is positive, we can divide both sides of the inequality by it.
  have h_sum_pos : 0 < ∑ x : d, (‖v x‖ : ℝ) ^ 2 := by
    contrapose! hv₁;
    simp_all only [funext_iff, Pi.zero_apply, not_forall, forall_exists_index, Matrix.mulVec, Pi.smul_apply]
    intro i
    rw [← norm_eq_zero]
    simpa [ sq_nonneg ] using le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ‖v a‖ ) ) ( Finset.mem_univ i ) ) hv₁ ) ( sq_nonneg ( ‖v i‖ ) )
  norm_cast at this;
  nlinarith

open ComplexOrder in
lemma IsHermitian.spectrum_subset_Iic_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x : Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (A - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Iic (⨆ i, hA.eigenvalues i) := by
  have h := spectrum_subset_Ici_of_sub hA.neg (x := -x) ?_
  · rcases isEmpty_or_nonempty d
    · simp
    rw [← spectrum.neg_eq] at h
    intro μ hμ
    specialize h (Set.neg_mem_neg.mpr hμ)
    rw [← Set.mem_neg, Set.neg_Ici] at h
    convert! h
    rw [iInf, iSup, ← spectrum_real_eq_range_eigenvalues, ← spectrum_real_eq_range_eigenvalues]
    rw [← spectrum.neg_eq, csInf_neg ?_ (A.finite_real_spectrum.bddAbove), neg_neg]
    exact ContinuousFunctionalCalculus.spectrum_nonempty _ hA
  · convert hl using 1
    abel

open ComplexOrder in
lemma IsHermitian.spectrum_subset_of_mem_Icc {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A B x : Matrix d d 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
  (hl : (x - A).PosSemidef) (hr : (B - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Icc (⨅ i, hA.eigenvalues i) (⨆ i, hB.eigenvalues i) := by
  rw [← Set.Ici_inter_Iic]
  exact Set.subset_inter (hA.spectrum_subset_Ici_of_sub hl) (hB.spectrum_subset_Iic_of_sub hr)

/--
The right partial trace of a matrix is equal to the left partial trace of the matrix reindexed by swapping the tensor factors.
-/
theorem traceRight_eq_traceLeft_reindex {n m R : Type*} [Fintype m] [AddCommMonoid R]
  (M : Matrix (n × m) (n × m) R) :
    M.traceRight = (M.reindex (.prodComm ..) (.prodComm ..)).traceLeft := by
  rfl

open ComplexOrder in
lemma PosSemidef.trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≠ 0) : 0 < A.trace := by
  apply hA.trace_nonneg.lt_of_ne'
  classical
  rw [hA.left.trace_eq_sum_eigenvalues]
  suffices ∑ i, hA.left.eigenvalues i ≠ 0 from mod_cast this
  rwa [ne_eq, Fintype.sum_eq_zero_iff_of_nonneg hA.eigenvalues_nonneg,
    hA.left.eigenvalues_eq_zero_iff]

section traceLeftRight

variable {m α : Type*} [AddCommGroup α] [Fintype m]
omit [DecidableEq n]

variable {A B : Matrix (m × n) (m × n) α}
@[simp]
lemma traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft := by
  ext : 2
  simp [Matrix.traceLeft, Finset.sum_add_distrib]

@[simp]
lemma traceLeft_neg : (-A).traceLeft = -A.traceLeft := by
  ext : 2; simp [Matrix.traceLeft]

@[simp]
lemma traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  simp [sub_eq_add_neg]

variable {A B : Matrix (n × m) (n × m) α}

@[simp]
lemma traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight := by
  ext : 2
  simp [Matrix.traceRight, Finset.sum_add_distrib]

@[simp]
lemma traceRight_neg : (-A).traceRight = -A.traceRight := by
  ext : 2; simp [Matrix.traceRight]

@[simp]
lemma traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight := by
  simp [sub_eq_add_neg]

variable {R : Type*} [DistribSMul R α]
@[simp]
lemma traceLeft_smul {A : Matrix (m × n) (m × n) α} (r : R) :
    (r • A).traceLeft = r • A.traceLeft := by
  ext : 2; simp [Matrix.traceLeft, ← Finset.smul_sum]

@[simp]
lemma traceRight_smul {A : Matrix (n × m) (n × m) α} (r : R) :
    (r • A).traceRight = r • A.traceRight := by
  ext : 2; simp [Matrix.traceRight, ← Finset.smul_sum]

end traceLeftRight

lemma unitaryGroup_row_norm [Fintype n] (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖U j i‖^2 = 1 := by
  suffices ∑ j, ‖U j i‖^2 = (1 : ℂ) by exact_mod_cast this
  simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    using congr($(U.prop.left) i i)

section finprod

variable {ι : Type*} {d : ι → Type*} [fι : Fintype ι]
variable {R : Type*}

def piProd [CommMonoid R] (A : ∀ i, Matrix (d i) (d i) R) : Matrix (∀ i, d i) (∀ i, d i) R :=
  Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))

variable {A : ∀ i, Matrix (d i) (d i) R}

lemma IsHermitian.piProd [CommSemiring R] [StarRing R] (hA : ∀ i, (A i).IsHermitian) :
    (piProd A).IsHermitian := by
  ext j k
  simp [Matrix.piProd]
  exact Finset.prod_congr rfl fun i _ => by simpa using congr_fun ( congr_fun ( hA i ) ( j i ) ) ( k i ) ;

variable [DecidableEq ι] [∀ i, Fintype (d i)] --[∀ i, DecidableEq (d i)]

lemma trace_piProd [CommSemiring R] :
    (piProd A).trace = ∏ i, (A i).trace := by
  symm
  simp [trace, piProd, Fintype.prod_sum]

open ComplexOrder MatrixOrder in
lemma PosSemidef.piProd [RCLike R] (hA : ∀ i, (A i).PosSemidef) :
    (piProd A).PosSemidef := by
  -- Let B i be the square root of A i. Let BigB be the pi-product of B i. Show that BigB.conjTranspose * BigB equals the pi-product of A i using Fintype.prod_sum. Then use Matrix.PosSemidef.conjTranspose_mul_self to conclude the proof.
  obtain ⟨B, hB⟩ : ∃ B : ∀ i, Matrix (d i) (d i) R, ∀ i, (A i) = B i * star (B i) := by
    -- By definition of positive semi-definite matrices, each $A_i$ can be written as $B_i^* B_i$ for some matrix $B_i$.
    have h_decomp : ∀ i, ∃ B : Matrix (d i) (d i) R, A i = B * star B := by
      intro i
      obtain ⟨B, hB⟩ : ∃ B : Matrix (d i) (d i) R, A i = B.conjTranspose * B := by
        classical
        apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
        exact nonneg_iff_posSemidef.mpr (hA i)
      use B.conjTranspose;
      convert hB using 1;
      simp [ Matrix.star_eq_conjTranspose ];
    exact ⟨ fun i => Classical.choose ( h_decomp i ), fun i => Classical.choose_spec ( h_decomp i ) ⟩;
  have hBigB_conjTranspose_mul_BigB : Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i * star (B i)) (j i) (k i)) = Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i)) * star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i))) := by
    ext j k; simp [ Matrix.mul_apply]
    simp only [Finset.prod_sum, ← Finset.prod_mul_distrib];
    refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
    · simp [ funext_iff ];
    · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  simp_all [Matrix.piProd]
  constructor
  · ext1
    simp [Matrix.mul_apply, mul_comm]
  · intro x
    set y := star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, B i (j i) (k i))) *ᵥ x
    convert dotProduct_star_self_nonneg y using 1
    simp only [dotProduct_mulVec, y];
    simp only [dotProduct, vecMul, Pi.star_apply, RCLike.star_def, mul_comm, star_apply, of_apply,
      star_prod];
    simp only [mul_apply, of_apply, star_apply, star_prod, RCLike.star_def, Finset.mul_sum _ _ _,
      mul_left_comm, mulVec, dotProduct, mul_comm, map_sum, map_mul, map_prod,
      RingHomCompTriple.comp_apply, RingHom.id_apply, mul_assoc];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

end finprod

--TODO: Can this be used for `Matrix.reindex_eq_conj` cleanup?
lemma submatrix_eq_mul_mul {d d₂ d₃ R : Type*} [DecidableEq d] [Fintype d] [Semiring R]
  (A : Matrix d d R) (e : d₂ → d) (f : d₃ → d) :
    A.submatrix e f = (submatrix (α := R) 1 e id : Matrix d₂ d R) * A * (submatrix (α := R) 1 id f) := by
  rw [show id = Equiv.refl d by rfl, Matrix.mul_submatrix_one, Matrix.one_submatrix_mul]
  simp

open scoped Matrix Kronecker in
/--
The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates (for matrices).
-/
lemma kronecker_conj_eq {m n p q α : Type*} [CommSemiring α] [StarRing α] [Fintype m] [Fintype n]
    (A : Matrix m m α) (B : Matrix n n α) (C : Matrix p m α) (D : Matrix q n α) :
    (C ⊗ₖ D) * (A ⊗ₖ B) * (C ⊗ₖ D)ᴴ = (C * A * Cᴴ) ⊗ₖ (D * B * Dᴴ) := by
  rw [← Matrix.mul_kronecker_mul]
  ext1
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, star_mul']
  simp only [← starRingEnd_apply, mul_comm, Finset.mul_sum, mul_left_comm]
  simp only [Finset.sum_mul, mul_assoc, Finset.mul_sum, mul_left_comm]
  rw [Fintype.sum_prod_type_right]

end Matrix
