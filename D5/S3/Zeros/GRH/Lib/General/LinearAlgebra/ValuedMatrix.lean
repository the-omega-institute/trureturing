/- GID: D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.LinearAlgebra.ValuedMatrix. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/ValuedMatrix.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.ValuationPair
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: Polynomials in matrices: adjoints, base change, invertibility, characteristic polynomial
divisibility. Diagonalisation with simple roots; Sylvester's law of inertia. Valuation bounds for
matrix products; GL_n(O) as integral entries with unit determinant. -/

open Finset Algebra ComplexOrder Equiv MatMul Matrix Polynomial Sgn Valued WithZero Module.End

variable {R S n m} [CommRing R] [CommRing S] [Fintype n] {σ : _} [Fintype m] (ψ : R →+* S)
  {c : Matrix m n R} {x Y : Matrix n n R} {σ : _} {g h : Matrix n n ℂ}

lemma star_aeval {A} [StarRing R] [Ring A] [StarRing A] [Algebra R A] [StarModule R A] (x : A) q :
    star (aeval x q) = aeval (star x) (q.map (starRingEnd R)) := by
    simp [aeval_def, eval₂_map, eval₂, commutes, starRingEnd_apply, sum]

lemma map_aeval_matrix (Y : Matrix n n R) z : (aeval Y z).map ψ = aeval (Y.map ψ) (z.map ψ) := by
  induction z using recOnHorner <;> simp [*, algebraMap, Matrix.map_add]

lemma twistedNorm_map_eq_prod p : ∀ z : S[X], twistedNorm (.map σ) p z = ∏ i ∈ range p, z.map (σ ^
  i) := by induction p <;> simp_all [twistedNorm, prod_range_succ', mul_comm]; congr! 2 <;> aesop

lemma aeval_semiconj {y : Matrix m m R} (h : c * x = y * c) (q : R[X]) : c * aeval x q = aeval y q *
    c := by induction q using recOnHorner with simp_all [algebraMap_eq_smul_one, ← c.mul_assoc]

lemma commute_conjTranspose_aeval [StarRing R] (x : type_of% x) [IsStarNormal x] {w z : R[X]} :
  Commute (aeval x w)ᴴ
  (aeval x z) := aeval_semiconj (Commute.star_left (aeval_semiconj (star_comm_self' x) w).symm) _

lemma charpoly_dvd_charpoly_aeval_comp q : Y.charpoly ∣ (aeval Y q).charpoly.comp q := (eval_map
  ..).subst (by simpa [map_aeval_matrix, eval_map, eval_charpoly, ← charpoly_map]
  using! map_dvd detMonoidHom (aeval_dvd (Y.map C) (((q.map C).map C).sub_dvd_eval_sub (C X) X)))

/-- For a square matrix Y over a commutative ring and a polynomial z, the matrix z(Y) is
invertible if and only if z is coprime to the characteristic polynomial of Y. -/
lemma isUnit_aeval_iff_isCoprime {z} : IsUnit (aeval Y z) ↔ IsCoprime Y.charpoly z :=
  ⟨fun _ ↦ by grw [charpoly_dvd_charpoly_aeval_comp z, ← (charpoly _).divX_mul_X_add]; simp_all
  [isUnit_iff_isUnit_det, isCoprime_one_left.of_isCoprime_of_dvd_left, det_eq_sign_charpoly_coeff],
  fun ⟨_, _, e⟩ ↦ .of_mul_eq_one_right _ (by simpa [aeval_self_charpoly] using congr(aeval Y $e))⟩

/-- Let ψ: R → S be an injective ring homomorphism and σ a ring endomorphism of S whose fixed
points lie in the image of ψ. Then every g in GL_n(S) fixed entrywise by σ is the image
under ψ of an element of GL_n(R). -/
lemma exists_gl_map_eq_of_fixed {ψ : R →+* S} (inj : (⇑ψ).Injective) (fix : ∀ x, σ x = x →
  x ∈ ψ.range) {g : GL n S} (h : g.map σ = g) : ∃ k, .map ψ k = g := by
  choose N a using (fix _ congr($h · ·)); choose M b using (fix _ congr($h⁻¹ · ·))
  use .mkOfMulEqOne (of N) (of M) (map_injective inj (by simp; convert g.3 <;> aesop)),
    GeneralLinearGroup.ext a

@[simp] lemma twistedNorm_diagGL (d : n → Sˣ) p : twistedNorm (.map σ) p (diagGL d) =
  diagonal fun i ↦ ∏ l ∈ range p, (σ ^ l) (d i) := by induction p with simp_all [↓twistedNorm_succ',
  twistedNorm, ↓prod_range_succ', pow_succ', mul_comm]

/-- If the characteristic polynomial of a complex square matrix g vanishes at pairwise distinct
numbers x_i, one for each row index i, then g is conjugate by an invertible matrix to the
diagonal matrix with entries x_i. -/
lemma isConj_diagonal_of_isRoot_charpoly {x : n ↪ ℂ} (hg : ∀ i, g.charpoly.IsRoot (x i)) :
  IsConj (diagonal x) g := by
  choose v hv using (g.charpoly_toLin' ▸ hg · |> (hasEigenvalue_iff_isRoot_charpoly ..).2
    |>.exists_hasEigenvector)
  use (linearIndependent_col_iff_isUnit.1 (eigenvectors_linearIndependent' _ _ x.2 v hv)).unit
  ext; simpa [mul_comm] using! congrFun (hv _).apply_eq_smul.symm _

/-- Sylvester's law of inertia: if hᴴ diag(s) h = diag(t) for signs s, t and a complex matrix h,
then some permutation τ has s_{τ(j)} = t_j for all j. -/
lemma sylvester_law_of_inertia {s t} (e : hᴴ * signMatrix s * h = signMatrix t) : ∃ τ : Perm n, ∀ j,
  s (τ j) = t j := by
  by_contra!
  absurd (PosDef.one.posSemidef_add h.posSemidef_conjTranspose_mul_self).det_pos
  rw [← signMatrix_mul_self, ← e, mul_assoc, mul_assoc, ← mul_add, det_mul, mul_comm, det_apply',
    sum_eq_zero] <;> simp [prod_eq_zero_iff]
  peel this; simp_all [signMatrix, field, sq, ← Int.cast_mul]

variable {n : Type*} {F} [Field F] [Valued F ℤᵐ⁰] [Fintype n]

lemma v_matrix_mul_le {m l} {A : Matrix m n F} {B : Matrix n l F} {c d} (hA : ∀ a b, v (A a b) ≤ c)
  (hB : ∀ a b, v (B a b) ≤ d) a b : v ((A * B) a b) ≤ c * d := v.map_sum_le (by grind [mul_le_mul'])

/-- Over a field F with a valuation v into the value group ℤᵐ⁰, an invertible matrix g lies in
GL_n(𝒪_F) if and only if all its entries have valuation at most 1 and v(det g) = 1. -/
lemma mem_intGL_iff_det {g} : g ∈ intGL n 𝒪[F] ↔ (∀ a b, v (g a b) ≤ 1) ∧
    v g.1.det = 1 := have {A} := 𝒪[F].subtype.map_det (n := n) A ▸
    (Valuation.integer.integers v).isUnit_iff_valuation_eq_one
  ⟨fun ⟨k, h⟩ ↦ h ▸ ⟨(k · · |>.2), this.1 (by simp)⟩,
    fun ⟨a, b⟩ ↦ ⟨.mk'' (⟨_, a · ·⟩) (this.2 b), by aesop⟩⟩
