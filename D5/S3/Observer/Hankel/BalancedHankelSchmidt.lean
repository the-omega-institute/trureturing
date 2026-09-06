/- GID: D5/S3/Observer/Hankel/BalancedHankelSchmidt
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/BalancedHankelSchmidt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct a complete finite Schmidt decomposition of the actual infinite Hankel operator from its balanced Gramians. -/

import D5.S3.Observer.Hankel.InfiniteHankelGramian
import D5.S3.Observer.Hankel.BalancedRealizationTransport
import D5.S3.Observer.LinearMemory.HankelGramianSingularValues

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.BalancedHankelSchmidt

open Matrix
open D5.S3.Observer.Hankel.PositiveGramianBalancing
open D5.S3.Observer.Hankel.ExactGramianSeries
open D5.S3.Observer.Hankel.InfiniteHankelGramian
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

variable {ι κ η : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]

private def invRootDiagonal (w : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => (Real.sqrt (w i))⁻¹)

private theorem invRootDiagonal_selfAdjoint (w : ι → ℝ) :
    (invRootDiagonal w)ᴴ = invRootDiagonal w := by simp [invRootDiagonal]

private theorem invRootDiagonal_normalizes (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    invRootDiagonal w * diagonal w * invRootDiagonal w = 1 := by
  rw [invRootDiagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have he : (fun i => (Real.sqrt (w i))⁻¹ * w i * (Real.sqrt (w i))⁻¹) =
      (fun _ : ι => (1 : ℝ)) := by
    funext i
    have hn := ne_of_gt (Real.sqrt_pos.mpr (hw i))
    field_simp [hn]
    nlinarith [Real.sq_sqrt (le_of_lt (hw i))]
  rw [he, diagonal_one]

/-- Normalize actual future trajectories into an isometric finite-state family.
The norm proof uses the true infinite Gramian, not a supplied trajectory norm. -/
def normalizedFuture (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (L : Matrix ι ι ℝ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hL : Lᴴ * observationGramian A C * L = diagonal w) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] Signal κ where
  toLinearMap := ((futureOutput A C hA).comp
    (Matrix.toEuclideanCLM (L * invRootDiagonal w))).toLinearMap
  norm_map' x := by
    have hn : (L * invRootDiagonal w)ᴴ * observationGramian A C *
        (L * invRootDiagonal w) = 1 := by
      calc
        _ = invRootDiagonal w * (Lᴴ * observationGramian A C * L) * invRootDiagonal w := by
          simp only [conjTranspose_mul, invRootDiagonal_selfAdjoint, Matrix.mul_assoc]
        _ = 1 := by rw [hL, invRootDiagonal_normalizes w hw]
    have he := quadratic_congruence (observationGramian A C)
      (L * invRootDiagonal w) (WithLp.ofLp x)
    rw [hn, quadratic_one] at he
    have hs := futureOutput_norm_sq A C hA (Matrix.toEuclideanCLM (L * invRootDiagonal w) x)
    rw [Matrix.ofLp_toEuclideanCLM, ← he] at hs
    have hx : squareSum (WithLp.ofLp x) = ‖x‖ ^ 2 :=
      (EuclideanSpace.real_norm_sq_eq x).symm
    rw [hx] at hs
    nlinarith [norm_nonneg (futureOutput A C hA
      (Matrix.toEuclideanCLM (L * invRootDiagonal w) x)), norm_nonneg x]

/-- Left Schmidt-space isometry, made from actual original-system future outputs. -/
def leftIsometry (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] Signal η :=
  normalizedFuture A C hA b.toOriginal b.weight b.positive b.observability

/-- Right Schmidt-space isometry, made from actual dual-system future outputs. -/
def rightIsometry (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] Signal κ :=
  normalizedFuture Aᴴ Bᴴ (adjoint_power_square_summable A hA) b.fromOriginalᴴ
    b.weight b.positive (by simpa only [conjTranspose_conjTranspose, controlGramian] using b.controllability)

/-- The actual infinite Hankel operator has an isometric diagonal factorization.
This proves the finite Schmidt core for the actual l2-to-l2 operator. -/
theorem hankel_isometric_factorization (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix η ι ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) :
    hankel A B C hA = (leftIsometry A B C hA b).toContinuousLinearMap.comp
      ((Matrix.toEuclideanCLM (diagonal b.weight)).comp
        (rightIsometry A B C hA b).toContinuousLinearMap.adjoint) := by
  let I := invRootDiagonal b.weight
  have hm : (b.toOriginal * I) * (diagonal b.weight * (b.fromOriginalᴴ * I)ᴴ) = 1 := by
    calc
      _ = b.toOriginal * (I * diagonal b.weight * I) * b.fromOriginal := by
        simp only [I, conjTranspose_mul, invRootDiagonal_selfAdjoint,
          conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [invRootDiagonal_normalizes b.weight b.positive, mul_one, b.to_from]
  have ha (M : Matrix ι ι ℝ) :
      Matrix.toEuclideanCLM Mᴴ = (Matrix.toEuclideanCLM M).adjoint :=
    map_star Matrix.toEuclideanCLM M
  have hc := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) hm
  simp only [map_mul, map_one, ha] at hc
  change (Matrix.toEuclideanCLM (b.toOriginal * I)).comp
    ((Matrix.toEuclideanCLM (diagonal b.weight)).comp
      (Matrix.toEuclideanCLM (b.fromOriginalᴴ * I)).adjoint) = 1 at hc
  let O := futureOutput A C hA
  let Z := futureOutput Aᴴ Bᴴ (adjoint_power_square_summable A hA)
  change O.comp Z.adjoint =
    (O.comp (Matrix.toEuclideanCLM (b.toOriginal * I))).comp
      ((Matrix.toEuclideanCLM (diagonal b.weight)).comp
        (Z.comp (Matrix.toEuclideanCLM (b.fromOriginalᴴ * I))).adjoint)
  rw [ContinuousLinearMap.adjoint_comp]
  symm
  calc
    _ = O.comp (((Matrix.toEuclideanCLM (b.toOriginal * I)).comp
        ((Matrix.toEuclideanCLM (diagonal b.weight)).comp
          (Matrix.toEuclideanCLM (b.fromOriginalᴴ * I)).adjoint)).comp Z.adjoint) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = O.comp Z.adjoint := by rw [hc]; rfl

private theorem isometry_adjoint_self {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℝ] F) : V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap = 1 := by
  ext x
  apply ext_inner_left ℝ
  intro y
  change ⟪y, V.toContinuousLinearMap.adjoint (V x)⟫ = ⟪y, x⟫
  rw [ContinuousLinearMap.adjoint_inner_right, V.inner_map_map]

/-- The genuine left singular trajectories. -/
def leftMode (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) (i : ι) : Signal η :=
  leftIsometry A B C hA b (EuclideanSpace.basisFun ι ℝ i)

/-- The genuine right singular input trajectories. -/
def rightMode (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) (i : ι) : Signal κ :=
  rightIsometry A B C hA b (EuclideanSpace.basisFun ι ℝ i)

private theorem mapped_basis_orthonormal {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : EuclideanSpace ℝ ι →ₗᵢ[ℝ] E) :
    Orthonormal ℝ (fun i => V (EuclideanSpace.basisFun ι ℝ i)) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [V.norm_map]
    exact (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i
  · intro i j hij
    rw [V.inner_map_map]
    exact (EuclideanSpace.basisFun ι ℝ).orthonormal.2 hij

/-- Both infinite trajectory families are genuinely orthonormal in their l2 spaces. -/
theorem modes_orthonormal (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) :
    Orthonormal ℝ (leftMode A B C hA b) ∧ Orthonormal ℝ (rightMode A B C hA b) :=
  ⟨mapped_basis_orthonormal _, mapped_basis_orthonormal _⟩

private theorem diagonal_basis (w : ι → ℝ) (i : ι) :
    Matrix.toEuclideanCLM (diagonal w) (EuclideanSpace.basisFun ι ℝ i) =
      w i • EuclideanSpace.basisFun ι ℝ i := by
  simp [EuclideanSpace.basisFun_apply, Matrix.toEuclideanCLM_toLp,
    Matrix.diagonal_mulVec_single, WithLp.toLp_smul]

/-- Forward and adjoint singular-vector equations for every balancing weight. -/
theorem hankel_mode_equations (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) (i : ι) :
    hankel A B C hA (rightMode A B C hA b i) = b.weight i • leftMode A B C hA b i ∧
    (hankel A B C hA).adjoint (leftMode A B C hA b i) = b.weight i • rightMode A B C hA b i := by
  let F := (leftIsometry A B C hA b).toContinuousLinearMap
  let G := (rightIsometry A B C hA b).toContinuousLinearMap
  let D := Matrix.toEuclideanCLM (diagonal b.weight)
  have hF : F.adjoint.comp F = 1 := isometry_adjoint_self _
  have hG : G.adjoint.comp G = 1 := isometry_adjoint_self _
  have hD : D.adjoint = D := by
    have hh := map_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) (diagonal b.weight)
    simpa [Matrix.star_eq_conjTranspose] using hh.symm
  have hf := hankel_isometric_factorization A B C hA b
  change hankel A B C hA = F.comp (D.comp G.adjoint) at hf
  constructor
  · rw [hf]
    change F (D (G.adjoint (G (EuclideanSpace.basisFun ι ℝ i)))) = _
    have hg := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι =>
      L (EuclideanSpace.basisFun ι ℝ i)) hG
    change G.adjoint (G (EuclideanSpace.basisFun ι ℝ i)) = EuclideanSpace.basisFun ι ℝ i at hg
    rw [hg, diagonal_basis, map_smul]
    rfl
  · rw [hf, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hD]
    change G (D (F.adjoint (F (EuclideanSpace.basisFun ι ℝ i)))) = _
    have hg := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι =>
      L (EuclideanSpace.basisFun ι ℝ i)) hF
    change F.adjoint (F (EuclideanSpace.basisFun ι ℝ i)) = EuclideanSpace.basisFun ι ℝ i at hg
    rw [hg, diagonal_basis, map_smul]
    rfl

/-- Complete finite Schmidt expansion for every l2 input, not just a finite window. -/
theorem hankel_schmidt_expansion (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) (u : Signal κ) :
    hankel A B C hA u = ∑ i, (b.weight i * ⟪rightMode A B C hA b i, u⟫) •
      leftMode A B C hA b i := by
  let F := (leftIsometry A B C hA b).toContinuousLinearMap
  let G := (rightIsometry A B C hA b).toContinuousLinearMap
  let D := Matrix.toEuclideanCLM (diagonal b.weight)
  let e := EuclideanSpace.basisFun ι ℝ
  have hx : G.adjoint u = ∑ i, ⟪e i, G.adjoint u⟫ • e i := by
    simpa only [OrthonormalBasis.repr_apply_apply] using (e.sum_repr (G.adjoint u)).symm
  rw [hankel_isometric_factorization]
  change F (D (G.adjoint u)) = _
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, diagonal_basis, map_smul, smul_smul]
  rw [ContinuousLinearMap.adjoint_inner_right]
  change (⟪rightMode A B C hA b i, u⟫ * b.weight i) • leftMode A B C hA b i = _
  rw [mul_comm]

/-- The expansion exhausts all nonzero singular directions: the kernel is
exactly the orthogonal complement of the constructed right singular family. -/
theorem hankel_kernel_iff (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C)) (u : Signal κ) :
    hankel A B C hA u = 0 ↔ ∀ i, ⟪rightMode A B C hA b i, u⟫ = 0 := by
  constructor
  · intro hu i
    have he := (hankel A B C hA).adjoint_inner_left u (leftMode A B C hA b i)
    rw [(hankel_mode_equations A B C hA b i).2, hu, inner_zero_right,
      real_inner_smul_left] at he
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (b.positive i))
  · intro hu
    rw [hankel_schmidt_expansion]
    simp [hu]

/-- No additional nonzero squared singular eigenvalue can occur for the actual
infinite operator. Repeated weights remain represented by orthogonal modes. -/
theorem nonzero_squared_singular_value (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix η ι ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (b : Coordinates (controlGramian A B) (observationGramian A C))
    (u : Signal κ) (hu : u ≠ 0) (lam : ℝ) (hlam : lam ≠ 0)
    (he : (hankel A B C hA).adjoint (hankel A B C hA u) = lam • u) :
    ∃ i, lam = (b.weight i) ^ 2 := by
  have hex : ∃ i, ⟪rightMode A B C hA b i, u⟫ ≠ 0 := by
    by_contra! hh
    have hz := (hankel_kernel_iff A B C hA b u).mpr hh
    have hu0 : lam • u = 0 := he.symm.trans (by rw [hz, map_zero])
    exact hu ((smul_eq_zero.mp hu0).resolve_left hlam)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have hp := congrArg (fun z => ⟪rightMode A B C hA b i, z⟫) he
  rw [ContinuousLinearMap.adjoint_inner_right,
    (hankel_mode_equations A B C hA b i).1, real_inner_smul_left,
    inner_smul_right] at hp
  have hq := (hankel A B C hA).adjoint_inner_left u (leftMode A B C hA b i)
  rw [(hankel_mode_equations A B C hA b i).2, real_inner_smul_left] at hq
  rw [← hq] at hp
  apply mul_right_cancel₀ hi
  nlinarith [hp]

/-- Consume the existing finite Gramian/singular-value theorem with square roots
that have now actually been constructed. This finite core is supplementary to
the separately proved infinite Hankel Schmidt decomposition above. -/
theorem constructed_core_singular_values (P Q : Matrix ι ι ℝ)
    (hP : P.PosDef) (hQ : Q.PosDef) :
    let L := (gramianRoot P).toEuclideanLin
    let O := (gramianRoot Q).toEuclideanLin
    ∃ h : (L.comp ((O.adjoint.comp O).comp L)).IsSymmetric,
      ∀ i : Fin (Fintype.card ι),
        0 < (O.comp L).singularValues i ∧
        (O.comp L).singularValues i = Real.sqrt (h.eigenvalues finrank_euclideanSpace i) := by
  obtain ⟨hp, hps, _⟩ := gramianRoot_spec P hP
  obtain ⟨hq, _, _⟩ := gramianRoot_spec Q hQ
  have hs : (gramianRoot P).toEuclideanLin.adjoint = (gramianRoot P).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hps]
  have hiP : Function.Injective (gramianRoot P).toEuclideanLin := by
    intro x y he
    have hxy := (Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit) (congrArg WithLp.ofLp he)
    ext i
    exact congrFun hxy i
  have hiQ : Function.Injective (gramianRoot Q).toEuclideanLin := by
    intro x y he
    have hxy := (Matrix.mulVec_injective_iff_isUnit.mpr hq.isUnit) (congrArg WithLp.ofLp he)
    ext i
    exact congrFun hxy i
  exact D5.S3.Observer.LinearMemory.HankelGramianSingularValues.hankel_gramian_singular_values
    _ _ hs hiP hiQ (Fintype.card ι) finrank_euclideanSpace

/-- End-to-end Schmidt identification from the original system alone.
The weights are a complete positive singular multiset. No ordering of the
finite index is asserted; a desired truncation order may be chosen by reindexing. -/
theorem constructed_hankel_schmidt {n m p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    let b := D5.S3.Observer.Hankel.BalancedRealizationTransport.systemCoordinates A B C hA hcon hobs
    Orthonormal ℝ (leftMode A B C hA b) ∧
    Orthonormal ℝ (rightMode A B C hA b) ∧
    (∀ i, hankel A B C hA (rightMode A B C hA b i) = b.weight i • leftMode A B C hA b i ∧
      (hankel A B C hA).adjoint (leftMode A B C hA b i) = b.weight i • rightMode A B C hA b i) ∧
    (∀ u : Signal (Fin m), hankel A B C hA u = ∑ i,
      (b.weight i * ⟪rightMode A B C hA b i, u⟫) • leftMode A B C hA b i) ∧
    (∀ u : Signal (Fin m), hankel A B C hA u = 0 ↔ ∀ i, ⟪rightMode A B C hA b i, u⟫ = 0) ∧
    (controlGramian A B * observationGramian A C).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((b.weight i) ^ 2)) := by
  let b := D5.S3.Observer.Hankel.BalancedRealizationTransport.systemCoordinates A B C hA hcon hobs
  exact ⟨(modes_orthonormal A B C hA b).1, (modes_orthonormal A B C hA b).2,
    hankel_mode_equations A B C hA b, hankel_schmidt_expansion A B C hA b,
    hankel_kernel_iff A B C hA b, b.gramian_product_charpoly⟩

#print axioms hankel_isometric_factorization
#print axioms hankel_schmidt_expansion
#print axioms nonzero_squared_singular_value

end D5.S3.Observer.Hankel.BalancedHankelSchmidt
