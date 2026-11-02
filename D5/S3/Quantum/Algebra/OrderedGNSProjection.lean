/- GID: D5/S3/Quantum/Algebra/OrderedGNSProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OrderedGNSProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered comparisons characterize faithful-state matrix conditional expectations. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! # Faithful-state projections and internal positivity tests -/

noncomputable section

namespace D5.S3.Quantum.Algebra.OrderedGNSProjection

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The original complex, ordered matrix-state evaluation. -/
def state (rho x : Matrix n n ℂ) : ℂ := trace (rho * x)

private theorem state_star (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (x : Matrix n n ℂ) : state rho (star x) = star (state rho x) := by
  change trace (rho * xᴴ) = star (trace (rho * x))
  rw [← trace_conjTranspose, conjTranspose_mul, hrho.isHermitian.eq, trace_mul_comm]

private theorem state_nonneg (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    {x : Matrix n n ℂ} (hx : x.PosSemidef) : 0 ≤ (state rho x).re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef hrho.posSemidef hx

private theorem state_square_faithful (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (x : Matrix n n ℂ) (hx : (state rho (star x * x)).re ≤ 0) : x = 0 := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  apply (re_inner_self_nonpos (𝕜 := ℂ)).mp
  change (trace (x * rho * xᴴ)).re ≤ 0
  rw [← trace_mul_cycle rho xᴴ x]
  simpa only [state, star_eq_conjTranspose, mul_assoc] using hx

/-- A faithful state separates the positive cone using compressions internal to
any unital star-subalgebra. -/
theorem positive_of_internal_compressions
    (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (y : Matrix n n ℂ) (hy : y.IsHermitian) (hyA : y ∈ A)
    (htest : ∀ q ∈ A, 0 ≤ (state rho (star q * y * q)).re) :
    y.PosSemidef := by
  letI : IsClosed (A : Set (Matrix n n ℂ)) :=
    A.toSubmodule.closed_of_finiteDimensional
  let f : ℝ → ℝ := fun t => Real.sqrt t⁻
  let q : Matrix n n ℂ := cfc f y
  let z : Matrix n n ℂ := cfc (fun t : ℝ => t⁻) y
  have hqA : q ∈ A := cfc_mem f hyA
  have hq : IsSelfAdjoint q := by
    exact cfc_predicate _ _
  have hz : IsSelfAdjoint z := by
    exact cfc_predicate _ _
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnegcont : Continuous (fun t : ℝ => t⁻) := by fun_prop
  have hprod : star q * y * q = -(star z * z) := by
    rw [hq.star_eq, hz.star_eq]
    change cfc f y * y * cfc f y = -(cfc (fun t : ℝ => t⁻) y *
      cfc (fun t : ℝ => t⁻) y)
    calc
      _ = cfc (fun t => f t * t * f t) y := by
        rw [cfc_mul (fun t => f t * t) f y
          ((hf.mul continuous_id).continuousOn) hf.continuousOn,
          cfc_mul f (fun t => t) y hf.continuousOn continuous_id.continuousOn,
          cfc_id' ℝ y hy.isSelfAdjoint]
      _ = cfc (fun t : ℝ => -(t⁻ * t⁻)) y := by
        apply cfc_congr
        intro t ht
        dsimp [f]
        have hs := Real.mul_self_sqrt (negPart_nonneg t)
        by_cases h : 0 ≤ t
        · simp [negPart_eq_zero.mpr h]
        · have hn : t⁻ = -t := by simp [negPart_def, max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
          rw [hn] at hs ⊢
          nlinarith
      _ = _ := by
        rw [cfc_neg (fun t : ℝ => t⁻ * t⁻) y,
          cfc_mul (fun t : ℝ => t⁻) (fun t : ℝ => t⁻) y
            hnegcont.continuousOn hnegcont.continuousOn]
  have hp := htest q hqA
  rw [hprod] at hp
  have hz0 : z = 0 := state_square_faithful rho hrho z (by simpa [state] using hp)
  have hneg : y⁻ = 0 := by
    change cfcₙ (fun t : ℝ => t⁻) y = 0
    rw [cfcₙ_eq_cfc (hf := hnegcont.continuousOn) (hf0 := by simp)]
    exact hz0
  exact (CFC.negPart_eq_zero_iff y hy.isSelfAdjoint).mp hneg |>.posSemidef

/-- The actual orthogonal projection for the faithful rho-weighted inner product. -/
def projection (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  letI : TopologicalSpace (Matrix n n ℂ) :=
    (rho.toMatrixNormedAddCommGroup hrho).toMetricSpace.toPseudoMetricSpace
      |>.toUniformSpace.toTopologicalSpace
  exact A.toSubmodule.starProjection.toLinearMap

private theorem projection_mem (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (x : Matrix n n ℂ) :
    projection rho hrho A x ∈ A := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  letI : TopologicalSpace (Matrix n n ℂ) :=
    (rho.toMatrixNormedAddCommGroup hrho).toMetricSpace.toPseudoMetricSpace
      |>.toUniformSpace.toTopologicalSpace
  exact A.toSubmodule.starProjection_apply_mem x

private theorem projection_left_comparison (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (x a : Matrix n n ℂ) (ha : a ∈ A) :
    state rho (star a * projection rho hrho A x) = state rho (star a * x) := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  letI : TopologicalSpace (Matrix n n ℂ) :=
    (rho.toMatrixNormedAddCommGroup hrho).toMetricSpace.toPseudoMetricSpace
      |>.toUniformSpace.toTopologicalSpace
  have h := A.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨a, ha⟩ x
  change trace (projection rho hrho A x * rho * aᴴ) = trace (x * rho * aᴴ) at h
  rw [← trace_mul_cycle rho aᴴ (projection rho hrho A x),
    ← trace_mul_cycle rho aᴴ x] at h
  simpa only [state, star_eq_conjTranspose, mul_assoc] using h

private theorem projection_unique (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (x y : Matrix n n ℂ) (hy : y ∈ A)
    (h : ∀ a ∈ A, state rho (star a * y) = state rho (star a * x)) :
    projection rho hrho A x = y := by
  letI := rho.toMatrixNormedAddCommGroup hrho
  letI := rho.toMatrixInnerProductSpace hrho.posSemidef
  letI : TopologicalSpace (Matrix n n ℂ) :=
    (rho.toMatrixNormedAddCommGroup hrho).toMetricSpace.toPseudoMetricSpace
      |>.toUniformSpace.toTopologicalSpace
  apply A.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero hy
  intro a ha
  rw [inner_eq_zero_symm]
  change trace ((x - y) * rho * aᴴ) = 0
  rw [← trace_mul_cycle rho aᴴ (x - y), mul_sub, trace_sub, sub_eq_zero]
  simpa only [state, star_eq_conjTranspose, mul_assoc] using (h a ha).symm

private theorem projection_retract (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (a : Matrix n n ℂ) (ha : a ∈ A) :
    projection rho hrho A a = a :=
  projection_unique rho hrho A a a ha (fun _ _ => rfl)

private theorem projection_left_module (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (b x : Matrix n n ℂ) (hb : b ∈ A) :
    projection rho hrho A (b * x) = b * projection rho hrho A x := by
  apply projection_unique rho hrho A (b * x) _ (A.mul_mem hb (projection_mem rho hrho A x))
  intro a ha
  have h := projection_left_comparison rho hrho A x (star b * a)
    (A.mul_mem (A.star_mem' hb) ha)
  simpa only [star_mul, star_star, mul_assoc] using h

private theorem projection_state (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (x : Matrix n n ℂ) :
    state rho (projection rho hrho A x) = state rho x := by
  simpa only [star_one, one_mul] using projection_left_comparison rho hrho A x 1 A.one_mem

/-- The same-map right comparison, retaining its full complex value. -/
def RightComparison (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) : Prop :=
  ∀ x a, a ∈ A → state rho (projection rho hrho A x * a) = state rho (x * a)

private theorem projection_star_iff (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    RightComparison rho hrho A ↔
      ∀ x, projection rho hrho A (star x) = star (projection rho hrho A x) := by
  constructor
  · intro h x
    apply projection_unique rho hrho A (star x) _ (A.star_mem' (projection_mem rho hrho A x))
    intro a ha
    have hc := congrArg star (h x a ha)
    simpa only [← state_star rho hrho, star_mul] using hc
  · intro h x a ha
    have hc := congrArg star (projection_left_comparison rho hrho A (star x) a
      ha)
    simpa only [← state_star rho hrho, star_mul, star_star, h] using hc

private theorem projection_right_module (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (hs : ∀ x, projection rho hrho A (star x) = star (projection rho hrho A x))
    (x b : Matrix n n ℂ) (hb : b ∈ A) :
    projection rho hrho A (x * b) = projection rho hrho A x * b := by
  have h := congrArg star (projection_left_module rho hrho A (star b) (star x)
    (A.star_mem' hb))
  simpa only [star_mul, star_star, ← hs] using h

private theorem positive_of_bimodule
    (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hrange : ∀ x, E x ∈ A)
    (hstar : ∀ x, E (star x) = star (E x))
    (hstate : ∀ x, state rho (E x) = state rho x)
    (hbimod : ∀ a ∈ A, ∀ b ∈ A, ∀ x, E (a * x * b) = a * E x * b)
    {x : Matrix n n ℂ} (hx : x.PosSemidef) : (E x).PosSemidef := by
  apply positive_of_internal_compressions rho hrho A (E x)
    (show IsSelfAdjoint (E x) from
      by change star (E x) = E x; rw [← hstar x, hx.isHermitian.star_eq]).isHermitian (hrange x)
  intro q hq
  rw [← hbimod (star q) (A.star_mem' hq) q hq x, hstate]
  exact state_nonneg rho hrho (hx.conjTranspose_mul_mul_same q)

section Amplification
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Original matrix blocks, without changing the full matrix carrier. -/
def block (X : Matrix (k × n) (k × n) ℂ) (r s : k) : Matrix n n ℂ :=
  fun i j => X (r, i) (s, j)

private theorem block_mul (X Y : Matrix (k × n) (k × n) ℂ) (r s : k) :
    block (X * Y) r s = ∑ t, block X r t * block Y t s := by
  ext i j
  simp only [block, mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- Entrywise amplification of the same actual matrix map. -/
def amplify (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Matrix (k × n) (k × n) ℂ →ₗ[ℂ] Matrix (k × n) (k × n) ℂ where
  toFun X := fun p q => E (block X p.1 q.1) p.2 q.2
  map_add' X Y := by
    ext ⟨r, i⟩ ⟨s, j⟩
    change E (block X r s + block Y r s) i j = _
    rw [map_add]
    rfl
  map_smul' c X := by
    ext ⟨r, i⟩ ⟨s, j⟩
    change E (c • block X r s) i j = _
    rw [map_smul]
    rfl

/-- The full matrix star-subalgebra M_k(A) in the original product carrier. -/
def amplifiedAlgebra (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    StarSubalgebra ℂ (Matrix (k × n) (k × n) ℂ) where
  carrier := {X | ∀ r s, block X r s ∈ A}
  zero_mem' := by intro r s; exact A.zero_mem
  add_mem' := by
    intro X Y hX hY r s
    exact A.add_mem (hX r s) (hY r s)
  mul_mem' := by
    intro X Y hX hY r s
    rw [block_mul]
    exact A.sum_mem (fun t _ => A.mul_mem (hX r t) (hY t s))
  one_mem' := by
    intro r s
    by_cases h : r = s
    · subst s
      have he : block (1 : Matrix (k × n) (k × n) ℂ) r r = 1 := by
        ext i j
        simp [block, one_apply]
      rw [he]
      exact A.one_mem
    · have he : block (1 : Matrix (k × n) (k × n) ℂ) r s = 0 := by
        ext i j
        simp [block, one_apply, h]
      rw [he]
      exact A.zero_mem
  algebraMap_mem' := by
    intro c r s
    by_cases h : r = s
    · subst s
      convert A.algebraMap_mem c using 1
      ext i j
      simp [block, algebraMap_eq_diagonal, diagonal]
    · have he : block (algebraMap ℂ (Matrix (k × n) (k × n) ℂ) c) r s = 0 := by
        ext i j
        simp [block, algebraMap_eq_diagonal, diagonal, h]
      rw [he]
      exact A.zero_mem
  star_mem' := by
    intro X hX r s
    exact A.star_mem' (hX s r)

private theorem amplify_mem (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (hrange : ∀ x, E x ∈ A)
    (X : Matrix (k × n) (k × n) ℂ) :
    amplify E X ∈ amplifiedAlgebra A := by
  intro r s
  exact hrange (block X r s)

private theorem amplify_star (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hstar : ∀ x, E (star x) = star (E x))
    (X : Matrix (k × n) (k × n) ℂ) :
    amplify E (star X) = star (amplify E X) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change E (star (block X s r)) i j = star (E (block X s r) j i)
  rw [hstar]
  rfl

private theorem amplify_left_module (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hl : ∀ a ∈ A, ∀ x, E (a * x) = a * E x)
    (B X : Matrix (k × n) (k × n) ℂ) (hB : B ∈ amplifiedAlgebra A) :
    amplify E (B * X) = B * amplify E X := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change E (block (B * X) r s) i j = _
  rw [block_mul, map_sum]
  simp_rw [hl _ (hB r _) _]
  simp only [amplify, LinearMap.coe_mk, mul_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, block]
  rfl

private theorem amplify_right_module (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hr : ∀ b ∈ A, ∀ x, E (x * b) = E x * b)
    (X B : Matrix (k × n) (k × n) ℂ) (hB : B ∈ amplifiedAlgebra A) :
    amplify E (X * B) = amplify E X * B := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change E (block (X * B) r s) i j = _
  rw [block_mul, map_sum]
  simp_rw [hr _ (hB _ s) _]
  simp only [amplify, LinearMap.coe_mk, mul_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, block]
  rfl

open scoped Kronecker in
private theorem amplified_state (rho : Matrix n n ℂ)
    (X : Matrix (k × n) (k × n) ℂ) :
    state ((1 : Matrix k k ℂ) ⊗ₖ rho) X = ∑ r, state rho (block X r r) := by
  simp [state, trace, mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    one_apply, block, ite_mul]

open scoped Kronecker in
/-- The normalized faithful density for each nonempty finite amplification. -/
def amplifiedDensity (rho : Matrix n n ℂ) : Matrix (k × n) (k × n) ℂ :=
  (Fintype.card k : ℝ)⁻¹ • ((1 : Matrix k k ℂ) ⊗ₖ rho)

private theorem amplified_normalized_state (rho : Matrix n n ℂ)
    (X : Matrix (k × n) (k × n) ℂ) :
    state (amplifiedDensity rho) X =
      (Fintype.card k : ℝ)⁻¹ • ∑ r, state rho (block X r r) := by
  unfold amplifiedDensity state
  rw [smul_mul_assoc, trace_smul]
  congr 1
  exact amplified_state rho X

open scoped Kronecker in
private theorem amplify_state (rho : Matrix n n ℂ)
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hstate : ∀ x, state rho (E x) = state rho x)
    (X : Matrix (k × n) (k × n) ℂ) :
    state (amplifiedDensity rho) (amplify E X) =
      state (amplifiedDensity rho) X := by
  rw [amplified_normalized_state, amplified_normalized_state]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => hstate (block X r r))

open scoped Kronecker in
private theorem amplify_positive (rho : Matrix n n ℂ) (hrho : rho.PosDef)
    (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hrange : ∀ x, E x ∈ A)
    (hstar : ∀ x, E (star x) = star (E x))
    (hstate : ∀ x, state rho (E x) = state rho x)
    (hl : ∀ a ∈ A, ∀ x, E (a * x) = a * E x)
    (hr : ∀ b ∈ A, ∀ x, E (x * b) = E x * b)
    {X : Matrix (k × n) (k × n) ℂ} (hX : X.PosSemidef) :
    (amplify E X).PosSemidef := by
  by_cases hk : Nonempty k
  · letI := hk
    have hn : 0 < (Fintype.card k : ℝ)⁻¹ := inv_pos.mpr (by
      exact_mod_cast Fintype.card_pos)
    apply positive_of_bimodule (amplifiedDensity rho)
      ((Matrix.PosDef.one.kronecker hrho).smul hn) (amplifiedAlgebra A) (amplify E)
      (amplify_mem A E hrange) (amplify_star E hstar) (amplify_state rho E hstate) _ hX
    intro B hB C hC X
    rw [amplify_right_module A E hr _ _ hC, amplify_left_module A E hl _ _ hB]
  · letI : IsEmpty k := ⟨fun r => hk ⟨r⟩⟩
    have he : amplify E X = 0 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero

private theorem amplify_one (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hu : E 1 = 1) : amplify E (1 : Matrix (k × n) (k × n) ℂ) = 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change E (block 1 r s) i j = _
  by_cases hrs : r = s
  · subst s
    have hb : block (1 : Matrix (k × n) (k × n) ℂ) r r = 1 := by
      ext i j
      simp [block, one_apply]
    rw [hb, hu]
    simp [one_apply]
  · have hb : block (1 : Matrix (k × n) (k × n) ℂ) r s = 0 := by
      ext i j
      simp [block, one_apply, hrs]
    rw [hb, map_zero]
    simp [one_apply, hrs]

end Amplification


private theorem linear_matrix_expansion
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (X : Matrix n n ℂ) :
    E X = ∑ i, ∑ j, X i j • E (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_smul]
  congr 1
  simp [Matrix.smul_single]


private theorem amplify_eq_left_kron
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    {k : Type*} [Fintype k] [DecidableEq k] (X : Matrix (k × n) (k × n) ℂ) :
    amplify E X = PhyslibLeaf.MatrixMap.kron LinearMap.id E X := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change E (block X r s) i j = _
  rw [linear_matrix_expansion, PhyslibLeaf.MatrixMap.kron_def]
  simp [Matrix.sum_apply, Matrix.single, block, ite_and, mul_comm, smul_eq_mul]

private theorem right_kron_eq_amplify_swap
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    {k : Type*} [Fintype k] [DecidableEq k] (X : Matrix (n × k) (n × k) ℂ) :
    PhyslibLeaf.MatrixMap.kron E LinearMap.id X =
      (amplify E (X.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap := by
  ext ⟨i, r⟩ ⟨j, s⟩
  change _ = E (block (X.submatrix Prod.swap Prod.swap) r s) i j
  rw [PhyslibLeaf.MatrixMap.kron_def]
  conv_rhs => rw [linear_matrix_expansion]
  simp [Matrix.sum_apply, Matrix.single, block, Matrix.submatrix_apply,
    ite_and, mul_comm, smul_eq_mul]

/-- The full expectation contract for a map on the original matrix algebra. -/
def Expectation (rho : Matrix n n ℂ) (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  E 1 = 1 ∧
  PhyslibLeaf.MatrixMap.IsCompletelyPositive E ∧
  (PhyslibLeaf.MatrixMap.IsPositive E ∧ ∀ k : ℕ,
    let Ek := PhyslibLeaf.MatrixMap.kron (LinearMap.id :
      Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ) E
    PhyslibLeaf.MatrixMap.IsPositive Ek ∧ Ek 1 = 1 ∧
      ∀ X, state (amplifiedDensity rho) (Ek X) = state (amplifiedDensity rho) X) ∧
  (∀ x, E (E x) = E x) ∧
  Set.range E = (A : Set (Matrix n n ℂ)) ∧
  (∀ x, state rho (E x) = state rho x) ∧
  (∀ a ∈ A, ∀ b ∈ A, ∀ x, E (a * x * b) = a * E x * b)

/-- For the actual faithful-state orthogonal projection, right ordered comparison,
adjoint preservation and the full completely positive expectation contract agree. -/
theorem ordered_gns_characterization
    (rho : Matrix n n ℂ) (hrho : rho.PosDef) (htrace : trace rho = 1)
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    state rho 1 = 1 ∧
    (∀ x, projection rho hrho A x ∈ A) ∧
    (∀ x a, a ∈ A →
      state rho (star a * projection rho hrho A x) = state rho (star a * x)) ∧
    (∀ x y, y ∈ A →
      (∀ a ∈ A, state rho (star a * y) = state rho (star a * x)) →
      y = projection rho hrho A x) ∧
    (RightComparison rho hrho A ↔
      ∀ x, projection rho hrho A (star x) = star (projection rho hrho A x)) ∧
    (RightComparison rho hrho A ↔ Expectation rho A (projection rho hrho A)) := by
  refine ⟨by simpa [state] using htrace, projection_mem rho hrho A,
    projection_left_comparison rho hrho A, ?_, projection_star_iff rho hrho A, ?_⟩
  · intro x y hy h
    exact (projection_unique rho hrho A x y hy h).symm
  · constructor
    · intro hc
      have hs := (projection_star_iff rho hrho A).mp hc
      have hl := projection_left_module rho hrho A
      have hr := projection_right_module rho hrho A hs
      have hpos : ∀ (k : Type) [Fintype k] [DecidableEq k]
          (X : Matrix (k × n) (k × n) ℂ),
          X.PosSemidef → (amplify (projection rho hrho A) X).PosSemidef := by
        intro k _ _ X hX
        exact amplify_positive rho hrho A (projection rho hrho A)
          (projection_mem rho hrho A) hs (projection_state rho hrho A)
          (fun a ha x => hl a x ha) (fun b hb x => hr x b hb) hX
      refine ⟨projection_retract rho hrho A 1 A.one_mem, ?_, ?_,
        (fun x => projection_retract rho hrho A _ (projection_mem rho hrho A x)),
        ?_, projection_state rho hrho A, ?_⟩
      · intro k X hX
        rw [right_kron_eq_amplify_swap]
        exact (hpos (Fin k) _ (hX.submatrix Prod.swap)).submatrix Prod.swap
      · refine ⟨?_, ?_⟩
        · intro x hx
          apply positive_of_bimodule rho hrho A (projection rho hrho A)
            (projection_mem rho hrho A) hs (projection_state rho hrho A) _ hx
          intro a ha b hb z
          rw [hr _ b hb, hl a z ha]
        · intro k
          refine ⟨?_, ?_, ?_⟩
          · intro X hX
            rw [← amplify_eq_left_kron]
            exact hpos (Fin k) X hX
          · rw [← amplify_eq_left_kron]
            exact amplify_one _ (projection_retract rho hrho A 1 A.one_mem)
          · intro X
            rw [← amplify_eq_left_kron]
            exact amplify_state rho _ (projection_state rho hrho A) X
      · ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact projection_mem rho hrho A x
        · intro hy
          exact ⟨y, projection_retract rho hrho A y hy⟩
      · intro a ha b hb x
        rw [hr _ b hb, hl a x ha]
    · intro h x a ha
      have hm := h.2.2.2.2.2.2 1 A.one_mem a ha x
      have hp := h.2.2.2.2.2.1 (x * a)
      simp only [one_mul] at hm
      rw [hm] at hp
      exact hp

end D5.S3.Quantum.Algebra.OrderedGNSProjection
