/- GID: D5/S3/Quantum/Algebra/AuricActualOcticSupport
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticSupport
   mirror-E: none(waiver:symbolic-support-connectivity)
   anchors: []
   utility: none
   digest: Strong connectivity and row-determinant irreducibility for the actual octic operator. -/

import D5.S3.Quantum.Algebra.AuricActualOcticWindow
import D5.S3.Quantum.Algebra.FixedDiagonalDeterminant

/-! Directed support of the original inverse-obstruction operator over coefficient extensions. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Module LinearMap
open scoped TensorProduct

variable {F D : Type*} [Field F] [Field D] [Algebra F D]

section PolynomialCoefficientExtension

open MvPolynomial

variable {K L ι κ : Type*} [Field K] [Field L]
private def extendHom (φ : K →+* L) (e : MvPolynomial ι K ≃ₐ[K] MvPolynomial κ K) :
    MvPolynomial ι L →ₐ[L] MvPolynomial κ L :=
  aeval (fun i => map φ (e (X i)))
private theorem extendPolynomialEquiv_map_aux (φ : K →+* L)
    (e : MvPolynomial ι K ≃ₐ[K] MvPolynomial κ K) (p : MvPolynomial ι K) :
    extendHom φ e (map φ p) = map φ (e p) := by
  have h : (extendHom φ e).toRingHom.comp (map φ) = (map φ).comp e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [extendHom]
    · intro i
      simp [extendHom]
  exact DFunLike.congr_fun h p
private def extendPolynomialEquiv (φ : K →+* L)
    (e : MvPolynomial ι K ≃ₐ[K] MvPolynomial κ K) :
    MvPolynomial ι L ≃ₐ[L] MvPolynomial κ L :=
  AlgEquiv.ofAlgHom (extendHom φ e) (extendHom φ e.symm)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change extendHom φ e (map φ (e.symm (X i))) = X i
      rw [extendPolynomialEquiv_map_aux]
      simp)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change extendHom φ e.symm (map φ (e (X i))) = X i
      rw [extendPolynomialEquiv_map_aux]
      simp)

/-- Extension of coefficients commutes with the extended polynomial equivalence. -/
private theorem extendPolynomialEquiv_map (φ : K →+* L)
    (e : MvPolynomial ι K ≃ₐ[K] MvPolynomial κ K) (p : MvPolynomial ι K) :
    extendPolynomialEquiv φ e (map φ p) = map φ (e p) :=
  extendPolynomialEquiv_map_aux φ e p

end PolynomialCoefficientExtension

section ActualSupport

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [CharZero F] [FiniteDimensional F K] [Normal F K]
variable [Algebra D K] [IsScalarTower F D K]

open Classical in
/-- The same actual inverse-obstruction matrix has strongly connected nonzero support,
including after extension of its coefficients to any field. -/
theorem general43_2_support (L : Type*) [Field L] [Algebra K L]
    (W : Submodule F D) (hD : finrank F D = 8) (hW : finrank F W = 4)
    (hE : {c : D | ∀ w ∈ W, c * w ∈ W} = Set.range (algebraMap F D))
    (a : D) (ha : a ∉ quotientSet W) :
    ∃ e : K ⊗[F] D ≃ₐ[K] ((D →ₐ[F] K) → K),
      (∀ (c : K) (d : D) (σ : D →ₐ[F] K), e (c ⊗ₜ[F] d) σ = c * σ d) ∧
      let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
      let N := LinearMap.toMatrix' n
      (∀ σ τ, Relation.ReflTransGen (fun i j => N i j ≠ 0) σ τ) ∧
      (∀ σ τ, Relation.ReflTransGen (fun i j => algebraMap K L (N i j) ≠ 0) σ τ) ∧
      Irreducible (FixedDiagonalDeterminant.rowMatrix (N.map (algebraMap K L))).det ∧
      Irreducible (FixedDiagonalDeterminant.diagonalMatrix (N.map (algebraMap K L))).det := by
  classical
  obtain ⟨_, e, he, hn⟩ := general43_2_cut_free K W hD hW hE a ha
  let U := (W.baseChange K).map e.toLinearMap
  let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
  let N := LinearMap.toMatrix' n
  change n.comp n = 0 ∧ n.range = U ∧ n.ker = U ∧ N * N = 0 ∧ N.rank = 4 ∧ _ at hn
  obtain ⟨_, hrange, hker, _, _, _, hstrict, _⟩ := hn
  have hΩ : Fintype.card (D →ₐ[F] K) = 8 := by
    apply (AlgHom.card_of_splits F D K _).trans hD
    intro d
    have hh := Normal.splits (inferInstance : Normal F K) (algebraMap D K d)
    rwa [minpoly.algebraMap_eq (algebraMap D K).injective] at hh
  have hU : finrank K U = 4 := by
    dsimp [U]
    rw [LinearEquiv.finrank_map_eq]
    rw [← (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq,
      Module.finrank_baseChange, hW]
  have hcross (S : Finset (D →ₐ[F] K)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty) :
      0 < (N.submatrix (fun i : S => (i : D →ₐ[F] K))
        (fun j : ↥(Sᶜ) => (j : D →ₐ[F] K))).rank := by
    have hl := cross_rank_bound U n hker hrange hΩ hU S
    have hu := hstrict S hs ht
    rw [← crossRank_matrix] at hl
    change S.card + 1 ≤ 2 * rowRank U S at hu
    change 2 * rowRank U S ≤ S.card +
      (N.submatrix (fun i : S => (i : D →ₐ[F] K))
        (fun j : ↥(Sᶜ) => (j : D →ₐ[F] K))).rank at hl
    omega
  have hreach : ∀ σ τ, Relation.ReflTransGen (fun i j => N i j ≠ 0) σ τ := by
    intro σ τ
    by_contra hnot
    let S : Finset (D →ₐ[F] K) := Finset.univ.filter
      (fun i => Relation.ReflTransGen (fun i j => N i j ≠ 0) i τ)
    have hmem (i : D →ₐ[F] K) : i ∈ S ↔
        Relation.ReflTransGen (fun i j => N i j ≠ 0) i τ := by simp [S]
    have hs : S.Nonempty := ⟨τ, (hmem τ).mpr .refl⟩
    have ht : Sᶜ.Nonempty := ⟨σ, Finset.mem_compl.mpr (by simpa [hmem] using hnot)⟩
    have hz : N.submatrix (fun i : ↥(Sᶜ) => (i : D →ₐ[F] K))
        (fun j : ↥(Sᶜᶜ) => (j : D →ₐ[F] K)) = 0 := by
      ext i j
      change N i j = 0
      by_contra hij
      exact (Finset.mem_compl.mp i.property) ((hmem i).mpr
        (Relation.ReflTransGen.head hij ((hmem j).mp (by simpa using j.property))))
    have hh := hcross Sᶜ ht (by simpa using hs)
    rw [hz, Matrix.rank_zero] at hh
    omega
  have hreachL : ∀ σ τ,
      Relation.ReflTransGen (fun i j => algebraMap K L (N i j) ≠ 0) σ τ := by
    intro σ τ
    have hedge : (fun i j => N i j ≠ 0) ≤
        (fun i j => algebraMap K L (N i j) ≠ 0) := by
      intro i j hij hz
      exact hij ((algebraMap K L).injective (by simpa using hz))
    exact Relation.ReflTransGen.mono hedge σ τ (hreach σ τ)
  refine ⟨e, he, hreach, hreachL, ?_⟩
  have hcard : 1 < Fintype.card (D →ₐ[F] K) := by rw [hΩ]; decide
  haveI : Nontrivial (D →ₐ[F] K) := Fintype.one_lt_card_iff_nontrivial.mp hcard
  exact ⟨FixedDiagonalDeterminant.row_determinant_irreducible _ hreachL,
    FixedDiagonalDeterminant.diagonal_determinant_irreducible _ hreachL⟩

open MvPolynomial in
/-- The original multiplication-obstruction polynomial is irreducible after every extension
of the coefficients of the same finite normal splitting field. -/
theorem general43_2_original_polynomial (L : Type*) [Field L] [Algebra K L]
    (W : Submodule F D) (hD : finrank F D = 8) (hW : finrank F W = 4)
    (hE : {c : D | ∀ w ∈ W, c * w ∈ W} = Set.range (algebraMap F D))
    (bD : Basis (Fin 8) F D) (bW : Basis (Fin 4) F W)
    (bQ : Basis (Fin 4) F (D ⧸ W)) (a : D) (ha : a ∉ quotientSet W) :
    Irreducible (map ((algebraMap K L).comp (algebraMap F K))
      (obstructionPolynomial W bD bW bQ)) := by
  classical
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨e, he, hreach, hreachL, hrow, hdiagonal⟩ :=
    general43_2_support K L W hD hW hE a ha
  let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
  let N := LinearMap.toMatrix' n
  let f := obstructionPolynomial W bD bW bQ
  let c := eval₂ (algebraMap F K) (fun i => algebraMap F K (bD.repr a i)) f
  obtain ⟨hc, hn⟩ := original_polynomial_normalization W K hD hW bD bW bQ a ha e
  change c ≠ 0 at hc
  change eval₂Hom (C.comp (algebraMap F K)) (originalAffineCoordinates K bD a e) f =
    C c * (1 + N.map C * Matrix.diagonal (fun σ => X σ)).det at hn
  rw [Matrix.det_one_add_mul_comm] at hn
  let Φ := originalPolynomialEquiv K bD a e
  have hΦ : Φ (map (algebraMap F K) f) = C c * (FixedDiagonalDeterminant.rowMatrix N).det := by
    change aeval (originalAffineCoordinates K bD a e) (map (algebraMap F K) f) = _
    rw [aeval_def, ← eval₂_map_comp_C]
    simpa only [FixedDiagonalDeterminant.rowMatrix, coe_eval₂Hom, map_comp_C] using hn
  let Ψ := extendPolynomialEquiv (algebraMap K L) Φ
  apply (MulEquiv.irreducible_iff Ψ.toMulEquiv).mp
  have hm : map ((algebraMap K L).comp (algebraMap F K)) f =
      map (algebraMap K L) (map (algebraMap F K) f) := by rw [map_map]
  rw [hm]
  change Irreducible (extendPolynomialEquiv (algebraMap K L) Φ
    (map (algebraMap K L) (map (algebraMap F K) f)))
  rw [extendPolynomialEquiv_map, hΦ, map_mul, map_C]
  have hdet : map (algebraMap K L) (FixedDiagonalDeterminant.rowMatrix N).det =
      (FixedDiagonalDeterminant.rowMatrix (N.map (algebraMap K L))).det := by
    rw [RingHom.map_det]
    congr 1
    ext σ τ
    simp [FixedDiagonalDeterminant.rowMatrix, Matrix.diagonal_mul,
      Matrix.one_apply, Matrix.map_apply]
  rw [hdet]
  have hcl : algebraMap K L c ≠ 0 := by
    intro hz
    exact hc ((algebraMap K L).injective (by simpa using hz))
  have hunit : IsUnit (C (algebraMap K L c) : MvPolynomial (D →ₐ[F] K) L) :=
    (isUnit_iff_ne_zero.mpr hcl).map C
  exact (irreducible_isUnit_mul hunit).mpr hrow

end ActualSupport

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
