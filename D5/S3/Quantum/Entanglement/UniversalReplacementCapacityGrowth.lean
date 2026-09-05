/- GID: D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal replacement extracts orthonormal vectors and forces inner capacity growth. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

/- Library search (2026-09-06): no complete D5 or pinned Mathlib replacement-capacity
   theorem was found. The unadmitted physlib channel search hit is handled by local
   proof under rule 11(4). Bind Mathlib's complex polarization, spectral theorem,
   Orthonormal.linearIndependent, and LinearIndependent.fintype_card_le_finrank.
   Literature: Braunstein--Pati (2007), DOI 10.1103/PhysRevLett.98.080502. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

variable {A B R : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [Fintype R] [DecidableEq R]

/-- Equation 55.2: every density input has the same emitted marginal. -/
def UniversalReplacement (W : Matrix (B × R) A ℂ) (tau : DensityState R) : Prop :=
  ∀ rho : DensityState A,
    partialTraceFirst (W * CStarMatrix.ofMatrix.symm rho.val * W.conjTranspose) =
      CStarMatrix.ofMatrix.symm tau.val

private def emission (W : Matrix (B × R) A ℂ) : Matrix A A ℂ →ₗ[ℂ] Matrix R R ℂ where
  toFun rho := partialTraceFirst (W * rho * W.conjTranspose)
  map_add' rho sigma := by
    ext a b
    simp [partialTraceFirst, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c rho := by
    ext a b
    simp [partialTraceFirst, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum]

omit [DecidableEq A] in
private theorem pure_trace (x : EuclideanSpace ℂ A) :
    Matrix.trace (Matrix.vecMulVec (⇑x) (star (⇑x))) = (‖x‖ : ℂ)^2 := by
  rw [Matrix.trace_vecMulVec]
  exact (EuclideanSpace.inner_eq_star_dotProduct x x).symm.trans
    (inner_self_eq_norm_sq_to_K x)

private def pureState (x : EuclideanSpace ℂ A) (hx : ‖x‖ = 1) : DensityState A :=
  ⟨CStarMatrix.ofMatrix (Matrix.vecMulVec (⇑x) (star (⇑x))),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.posSemidef_vecMulVec_self_star (⇑x)).nonneg,
    by change Matrix.trace (Matrix.vecMulVec (⇑x) (star (⇑x))) = 1
       rw [pure_trace, hx]; norm_num⟩

private theorem replacement_pure (W : Matrix (B × R) A ℂ) (tau : DensityState R)
    (h : UniversalReplacement W tau) (x : EuclideanSpace ℂ A) :
    emission W (Matrix.vecMulVec (⇑x) (star (⇑x))) =
      (‖x‖ : ℂ)^2 • CStarMatrix.ofMatrix.symm tau.val := by
  by_cases hx : x = 0
  · subst x
    change partialTraceFirst (W * Matrix.vecMulVec 0 (star 0) * W.conjTranspose) = _
    ext a b
    simp [partialTraceFirst]
  let y : EuclideanSpace ℂ A := (‖x‖ : ℂ)⁻¹ • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have hp := h (pureState y hy)
  change emission W (Matrix.vecMulVec (⇑y) (star (⇑y))) = _ at hp
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have hout : Matrix.vecMulVec (⇑x) (star (⇑x)) =
      (‖x‖ : ℂ)^2 • Matrix.vecMulVec (⇑y) (star (⇑y)) := by
    ext i j
    simp [y, Matrix.vecMulVec_apply, Pi.star_apply]
    field_simp
  rw [hout, map_smul, hp]

private def contract (e : EuclideanSpace ℂ R) :
    EuclideanSpace ℂ (B × R) →ₗ[ℂ] EuclideanSpace ℂ B where
  toFun v := WithLp.toLp 2 (fun b => ∑ r, star (e r) * v (b, r))
  map_add' x y := by ext b; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext b; simp [Finset.mul_sum, mul_left_comm]

private theorem contract_inner (v : EuclideanSpace ℂ (B × R))
    (e f : EuclideanSpace ℂ R) :
    ⟪contract e v, contract f v⟫_ℂ =
      ⟪f, Matrix.toEuclideanLin
        (partialTraceFirst (Matrix.vecMulVec (⇑v) (star (⇑v)))) e⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, contract, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.toLpLin_apply,
    dotProduct, partialTraceFirst, Matrix.vecMulVec_apply, Matrix.mulVec,
    Pi.star_apply, star_sum, star_mul, star_star]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [Fintype R] [DecidableEq R] in
private theorem emission_outer (W : Matrix (B × R) A ℂ) (x : EuclideanSpace ℂ A) :
    emission W (Matrix.vecMulVec (⇑x) (star (⇑x))) =
      partialTraceFirst (Matrix.vecMulVec (⇑(Matrix.toEuclideanLin W x))
        (star (⇑(Matrix.toEuclideanLin W x)))) := by
  change partialTraceFirst (W * Matrix.vecMulVec (⇑x) (star (⇑x)) * W.conjTranspose) = _
  congr 1
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]
  simp only [star_star]
  rfl

private theorem replacement_contract_self (W : Matrix (B × R) A ℂ)
    (tau : DensityState R) (h : UniversalReplacement W tau)
    (e f : EuclideanSpace ℂ R) (x : EuclideanSpace ℂ A) :
    ⟪contract e (Matrix.toEuclideanLin W x),
      contract f (Matrix.toEuclideanLin W x)⟫_ℂ =
      (‖x‖ : ℂ)^2 * ⟪f, Matrix.toEuclideanLin
        (CStarMatrix.ofMatrix.symm tau.val) e⟫_ℂ := by
  rw [contract_inner, ← emission_outer, replacement_pure W tau h x]
  simp [map_smul]

private theorem replacement_contract_cross (W : Matrix (B × R) A ℂ)
    (tau : DensityState R) (h : UniversalReplacement W tau)
    (e f : EuclideanSpace ℂ R) (x y : EuclideanSpace ℂ A) :
    ⟪contract e (Matrix.toEuclideanLin W x),
      contract f (Matrix.toEuclideanLin W y)⟫_ℂ =
      ⟪f, Matrix.toEuclideanLin (CStarMatrix.ofMatrix.symm tau.val) e⟫_ℂ *
        ⟪x, y⟫_ℂ := by
  let S := (contract e).comp (Matrix.toEuclideanLin W)
  let T := (contract f).comp (Matrix.toEuclideanLin W)
  let c := ⟪f, Matrix.toEuclideanLin (CStarMatrix.ofMatrix.symm tau.val) e⟫_ℂ
  -- Complex polarization in ext_inner_map includes the imaginary-phase superpositions.
  have hK : T.adjoint.comp S = star c • LinearMap.id := by
    apply (ext_inner_map _ _).mp
    intro z
    simpa [LinearMap.adjoint_inner_left, S, T, c, inner_smul_left,
      inner_self_eq_norm_sq_to_K, mul_comm] using replacement_contract_self W tau h e f z
  have hc := congrArg (fun K : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A =>
    ⟪K x, y⟫_ℂ) hK
  simpa [LinearMap.adjoint_inner_left, S, T, c, inner_smul_left, mul_comm] using hc

private theorem extraction_orthonormal (W : Matrix (B × R) A ℂ)
    (tau : DensityState R) (h : UniversalReplacement W tau)
    (hPos : (CStarMatrix.ofMatrix.symm tau.val).PosSemidef) :
    let E := hPos.isHermitian.eigenvectorBasis
    let lam := hPos.isHermitian.eigenvalues
    let v : (A × {a : R // lam a ≠ 0}) → EuclideanSpace ℂ B := fun ia =>
      (Real.sqrt (lam ia.2.val) : ℂ)⁻¹ •
        contract (E ia.2.val) (Matrix.toEuclideanLin W (EuclideanSpace.basisFun A ℂ ia.1))
    Orthonormal ℂ v := by
  dsimp only
  apply orthonormal_iff_ite.mpr
  intro ia jb
  rw [inner_smul_left, inner_smul_right, replacement_contract_cross W tau h]
  have heig (a : R) :
      Matrix.toEuclideanLin (CStarMatrix.ofMatrix.symm tau.val)
          (hPos.isHermitian.eigenvectorBasis a) =
        (hPos.isHermitian.eigenvalues a : ℂ) • hPos.isHermitian.eigenvectorBasis a := by
    ext r
    exact congrFun (hPos.isHermitian.mulVec_eigenvectorBasis a) r
  rw [heig, inner_smul_right]
  rw [orthonormal_iff_ite.mp hPos.isHermitian.eigenvectorBasis.orthonormal,
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun A ℂ).orthonormal]
  have ha := hPos.eigenvalues_nonneg ia.2.val
  have hne : (Real.sqrt (hPos.isHermitian.eigenvalues ia.2.val) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ha (Ne.symm ia.2.property))
  by_cases hab : ia.2.val = jb.2.val
  · have hab' : ia.2 = jb.2 := Subtype.ext hab
    by_cases hij : ia.1 = jb.1
    · have heq : ia = jb := Prod.ext hij hab'
      subst jb
      simp only [ite_true, mul_one]
      have hs : (Real.sqrt (hPos.isHermitian.eigenvalues ia.2.val) : ℂ)^2 =
          (hPos.isHermitian.eigenvalues ia.2.val : ℂ) := by
        exact_mod_cast Real.sq_sqrt ha
      rw [← hs]
      field_simp [hne]
      simp [hne]
    · simp [hab, hij, Prod.ext_iff]
  · have hab' : jb.2.val ≠ ia.2.val := Ne.symm hab
    have habSub : ia.2 ≠ jb.2 := fun heq => hab (congrArg Subtype.val heq)
    simp [hab', habSub, Prod.ext_iff]

/-- The exact no-hiding capacity bound (Braunstein--Pati): normalized spectral
contractions form an orthonormal family with card A times rank tau members.
No isometry premise is added: universal trace-one replacement already suffices. -/
theorem universal_replacement_capacity_growth (W : Matrix (B × R) A ℂ)
    (tau : DensityState R) (h : UniversalReplacement W tau) :
    let hPos : (CStarMatrix.ofMatrix.symm tau.val).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm tau.property.1)
    let E := hPos.isHermitian.eigenvectorBasis
    let lam := hPos.isHermitian.eigenvalues
    let v : (A × {a : R // lam a ≠ 0}) → EuclideanSpace ℂ B := fun ia =>
      (Real.sqrt (lam ia.2.val) : ℂ)⁻¹ • WithLp.toLp 2
        (fun b => ∑ r, star (E ia.2.val r) * W (b, r) ia.1)
    Orthonormal ℂ v ∧
      Fintype.card A * Matrix.rank (CStarMatrix.ofMatrix.symm tau.val) ≤ Fintype.card B := by
  classical
  dsimp only
  let hPos : (CStarMatrix.ofMatrix.symm tau.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm tau.property.1)
  have ho := extraction_orthonormal W tau h hPos
  have hd := ho.linearIndependent.fintype_card_le_finrank
  constructor
  · simpa [contract, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply] using ho
  · simpa [Fintype.card_prod, finrank_euclideanSpace,
      ← hPos.isHermitian.rank_eq_card_non_zero_eigs] using hd

#print axioms universal_replacement_capacity_growth

end

end D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
