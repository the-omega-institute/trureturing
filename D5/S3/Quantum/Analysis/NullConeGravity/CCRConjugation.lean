/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real fixed subspaces of conjugations and transport of bounded and Hilbert-Schmidt operators. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import D5.S3.Quantum.Analysis.TraceClass.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt

namespace NullConeGravity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A real-linear isometric involution which conjugates complex scalars. -/
structure RealConjugation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  toLinearIsometryEquiv : H ≃ₗᵢ[ℝ] H
  involutive : Function.Involutive toLinearIsometryEquiv
  map_complex_smul : ∀ (c : ℂ) (h : H),
    toLinearIsometryEquiv (c • h) = star c • toLinearIsometryEquiv h

variable (Γ : RealConjugation H)

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The closed real form of the complex Hilbert space. -/
def realSubspace : Submodule ℝ H where
  carrier := {h | Γ.toLinearIsometryEquiv h = h}
  zero_mem' := map_zero _
  add_mem' := by
    intro x y hx hy
    change Γ.toLinearIsometryEquiv (x+y) = x+y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change Γ.toLinearIsometryEquiv (r • x) = r • x
    rw [map_smul, hx]

theorem realSubspace_isClosed : IsClosed (realSubspace Γ : Set H) :=
  isClosed_eq Γ.toLinearIsometryEquiv.continuous continuous_id

instance realSubspaceInnerProductSpace : InnerProductSpace ℝ (realSubspace Γ) :=
  inferInstanceAs (InnerProductSpace ℝ ↥(realSubspace Γ))

instance realSubspaceComplete [CompleteSpace H] : CompleteSpace (realSubspace Γ) :=
  (realSubspace_isClosed Γ).completeSpace_coe

/-- Projection onto the fixed real space. -/
def realPart (h : H) : H := (2 : ℂ)⁻¹ • (h + Γ.toLinearIsometryEquiv h)

/-- Imaginary coordinate, also in the fixed real space. -/
def imagPart (h : H) : H := (2 * Complex.I)⁻¹ • (h - Γ.toLinearIsometryEquiv h)

theorem realPart_mem (h : H) : realPart Γ h ∈ realSubspace Γ := by
  change Γ.toLinearIsometryEquiv (realPart Γ h) = realPart Γ h
  unfold realPart
  rw [Γ.map_complex_smul, map_add, Γ.involutive h, add_comm (Γ.toLinearIsometryEquiv h)]
  congr 1
  simp

theorem imagPart_mem (h : H) : imagPart Γ h ∈ realSubspace Γ := by
  change Γ.toLinearIsometryEquiv (imagPart Γ h) = imagPart Γ h
  unfold imagPart
  rw [Γ.map_complex_smul, map_sub, Γ.involutive h, ← neg_sub]
  rw [smul_neg, ← neg_smul]
  congr 1
  simp

theorem real_imag_decomposition (h : H) :
    h = realPart Γ h + Complex.I • imagPart Γ h := by
  have hi : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
    field_simp [Complex.I_ne_zero]
  rw [realPart, imagPart, smul_smul, hi, ← smul_add]
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul]

theorem real_imag_unique (h : H) (x y : realSubspace Γ)
    (hh : h = (x : H) + Complex.I • (y : H)) :
    realPart Γ h = x ∧ imagPart Γ h = y := by
  have hx : Γ.toLinearIsometryEquiv (x : H) = x := x.property
  have hy : Γ.toLinearIsometryEquiv (y : H) = y := y.property
  have hi : star Complex.I = -Complex.I := by simp
  have hh' : Γ.toLinearIsometryEquiv h = (x : H) - Complex.I • (y : H) := by
    rw [hh, map_add, Γ.map_complex_smul, hx, hy, hi, neg_smul, sub_eq_add_neg]
  constructor
  · unfold realPart
    rw [hh', hh]
    module
  · unfold imagPart
    rw [hh', hh]
    have hscalar : (2 * Complex.I)⁻¹ * (2 * Complex.I) = 1 :=
      inv_mul_cancel₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    have he : (x : H) + Complex.I • (y : H) - ((x : H) - Complex.I • (y : H)) =
        (2 * Complex.I) • (y : H) := by
      rw [← smul_smul, two_smul]
      abel
    rw [he, smul_smul, hscalar, one_smul]

/-- Antiunitarity reverses the complex inner product. -/
theorem conj_inner (x y : H) :
    ⟪Γ.toLinearIsometryEquiv x, Γ.toLinearIsometryEquiv y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  have hre (u v : H) :
      (⟪Γ.toLinearIsometryEquiv u, Γ.toLinearIsometryEquiv v⟫_ℂ).re =
      (⟪u, v⟫_ℂ).re := Γ.toLinearIsometryEquiv.inner_map_map u v
  apply Complex.ext
  · simpa only [Complex.star_def, Complex.conj_re] using hre x y
  · have hi := hre x (Complex.I • y)
    rw [Γ.map_complex_smul] at hi
    simpa only [Complex.star_def, Complex.conj_im, Complex.conj_re, Complex.I_re,
      Complex.I_im, inner_smul_right, Complex.mul_re, zero_mul, one_mul, neg_one_mul,
      zero_sub, sub_neg_eq_add, zero_add] using hi

theorem real_inner (x y : realSubspace Γ) :
    ⟪(x : H), (y : H)⟫_ℂ = ((⟪x, y⟫_ℝ : ℝ) : ℂ) := by
  have hx : Γ.toLinearIsometryEquiv (x : H) = x := x.property
  have hy : Γ.toLinearIsometryEquiv (y : H) = y := y.property
  have hc := conj_inner Γ (x : H) (y : H)
  rw [hx, hy] at hc
  apply Complex.ext
  · rfl
  · have him := congrArg Complex.im hc
    rw [Complex.star_def, Complex.conj_im] at him
    change (⟪(x : H), (y : H)⟫_ℂ).im = 0
    linarith

theorem norm_sq_decomposition (h : H) :
    ‖h‖ ^ 2 = ‖realPart Γ h‖ ^ 2 + ‖imagPart Γ h‖ ^ 2 := by
  let x : realSubspace Γ := ⟨realPart Γ h, realPart_mem Γ h⟩
  let y : realSubspace Γ := ⟨imagPart Γ h, imagPart_mem Γ h⟩
  have ho : ⟪(x : H), Complex.I • (y : H)⟫_ℝ = 0 := by
    change (⟪(x : H), Complex.I • (y : H)⟫_ℂ).re = 0
    rw [inner_smul_right, real_inner Γ]
    simp [Complex.mul_re]
  calc
    ‖h‖ ^ 2 = ‖(x : H) + Complex.I • (y : H)‖ ^ 2 :=
      congrArg (fun h : H => ‖h‖ ^ 2) (real_imag_decomposition Γ h)
    _ = ‖(x : H)‖ ^ 2 + ‖Complex.I • (y : H)‖ ^ 2 :=
      by simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real ho
    _ = ‖realPart Γ h‖ ^ 2 + ‖imagPart Γ h‖ ^ 2 := by
      simp [x, y, norm_smul]

/-- Conjugate a bounded complex-linear operator by the antiunitary involution. -/
def conjOp (T : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => Γ.toLinearIsometryEquiv (T (Γ.toLinearIsometryEquiv x))
      map_add' := by simp
      map_smul' := by
        intro c x
        simp only [Γ.map_complex_smul, map_smul, star_star, RingHom.id_apply] }
    ‖T‖ (fun x => by simpa using T.le_opNorm (Γ.toLinearIsometryEquiv x))

@[simp]
theorem conjOp_apply (T : H →L[ℂ] H) (h : H) :
    conjOp Γ T h = Γ.toLinearIsometryEquiv (T (Γ.toLinearIsometryEquiv h)) := rfl

theorem conjOp_adjoint [CompleteSpace H] (T : H →L[ℂ] H) :
    (conjOp Γ T).adjoint = conjOp Γ T.adjoint := by
  symm
  apply (eq_adjoint_iff _ _).2
  intro x y
  have hleft := conj_inner Γ (T.adjoint (Γ.toLinearIsometryEquiv x)) (Γ.toLinearIsometryEquiv y)
  have hright := conj_inner Γ (Γ.toLinearIsometryEquiv x) (T (Γ.toLinearIsometryEquiv y))
  rw [Γ.involutive y, adjoint_inner_left] at hleft
  rw [Γ.involutive x] at hright
  simp only [conjOp_apply]
  exact hleft.trans hright.symm

theorem conjOp_comp (S T : H →L[ℂ] H) :
    conjOp Γ (S.comp T) = (conjOp Γ S).comp (conjOp Γ T) := by
  ext x
  simp [Γ.involutive _]

theorem conjOp_nonneg [CompleteSpace H] (T : H →L[ℂ] H) (hT : 0 ≤ T) :
    0 ≤ conjOp Γ T := by
  rw [nonneg_iff_isPositive] at hT ⊢
  rw [isPositive_def']
  constructor
  · rw [IsSelfAdjoint, star_eq_adjoint, conjOp_adjoint, ← star_eq_adjoint, hT.isSelfAdjoint]
  · intro x
    have h := conj_inner Γ (T (Γ.toLinearIsometryEquiv x)) (Γ.toLinearIsometryEquiv x)
    rw [Γ.involutive x] at h
    change 0 ≤ (⟪conjOp Γ T x, x⟫_ℂ).re
    rw [conjOp_apply, h, Complex.star_def, Complex.conj_re]
    exact hT.re_inner_nonneg_left (Γ.toLinearIsometryEquiv x)

/-- Restriction of an operator commuting with the conjugation to the real form. -/
def restrictReal (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h)) :
    realSubspace Γ →L[ℝ] realSubspace Γ :=
  (T.restrictScalars ℝ).restrict (p := realSubspace Γ) (q := realSubspace Γ) fun x hx =>
    show Γ.toLinearIsometryEquiv (T x) = T x by rw [hT, show Γ.toLinearIsometryEquiv x = x from hx]

@[simp]
theorem restrictReal_apply (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (x : realSubspace Γ) : (restrictReal Γ T hT x : H) = T x := rfl

theorem restrictReal_norm (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h)) :
    ‖restrictReal Γ T hT‖ = ‖T‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖(restrictReal Γ T hT x : H)‖ ≤ ‖T‖ * ‖(x : H)‖
    rw [restrictReal_apply]
    exact T.le_opNorm (x : H)
  · apply opNorm_le_bound T (norm_nonneg (restrictReal Γ T hT))
    intro h
    let x : realSubspace Γ := ⟨realPart Γ h, realPart_mem Γ h⟩
    let y : realSubspace Γ := ⟨imagPart Γ h, imagPart_mem Γ h⟩
    let U := restrictReal Γ T hT
    have hparts := real_imag_unique Γ (T h) (U x) (U y) (by
      change T h = T (realPart Γ h) + Complex.I • T (imagPart Γ h)
      conv_lhs => rw [real_imag_decomposition Γ h, map_add, map_smul])
    have hs := norm_sq_decomposition Γ (T h)
    rw [hparts.1, hparts.2] at hs
    have hx := U.le_opNorm x
    have hy := U.le_opNorm y
    have hsqx := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hx
    have hsqy := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hy
    have hh := norm_sq_decomposition Γ h
    change ‖h‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 at hh
    change ‖T h‖ ^ 2 = ‖U x‖ ^ 2 + ‖U y‖ ^ 2 at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
    rw [hs, mul_pow, hh, mul_add]
    rw [mul_pow] at hsqx hsqy
    exact add_le_add hsqx hsqy

theorem adjoint_commutes [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h)) :
    ∀ h, Γ.toLinearIsometryEquiv (T.adjoint h) = T.adjoint (Γ.toLinearIsometryEquiv h) := by
  have hconj : conjOp Γ T = T := by
    ext x
    simp [hT, Γ.involutive _]
  have ha := conjOp_adjoint Γ T
  rw [hconj] at ha
  intro h
  have he := congrArg (fun S : H →L[ℂ] H => S (Γ.toLinearIsometryEquiv h)) ha
  simpa [Γ.involutive h] using he.symm

theorem restrictReal_adjoint [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h)) :
    (restrictReal Γ T hT).adjoint = restrictReal Γ T.adjoint (adjoint_commutes Γ T hT) := by
  symm
  apply (eq_adjoint_iff _ _).2
  intro x y
  change (⟪T.adjoint (x : H), (y : H)⟫_ℂ).re = (⟪(x : H), T (y : H)⟫_ℂ).re
  rw [adjoint_inner_left]

theorem restrictReal_selfAdjoint [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (h : IsSelfAdjoint T) : IsSelfAdjoint (restrictReal Γ T hT) := by
  rw [IsSelfAdjoint, star_eq_adjoint, restrictReal_adjoint]
  ext x
  change T.adjoint (x : H) = T (x : H)
  rw [← star_eq_adjoint, h]

theorem restrictReal_nonneg [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (h : 0 ≤ T) : 0 ≤ restrictReal Γ T hT := by
  rw [nonneg_iff_isPositive] at h ⊢
  rw [isPositive_iff']
  refine ⟨restrictReal_selfAdjoint Γ T hT h.isSelfAdjoint, fun x => ?_⟩
  exact h.re_inner_nonneg_left (x : H)

theorem restrictReal_skewAdjoint [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (h : T.adjoint = -T) : (restrictReal Γ T hT).adjoint = -restrictReal Γ T hT := by
  rw [restrictReal_adjoint]
  ext x
  change T.adjoint (x : H) = -(T (x : H))
  rw [h, neg_apply]

section Basis

variable [CompleteSpace H]
variable {ι : Type*}

/-- A real Hilbert basis extends to a complex one with the same vectors. -/
def complexHilbertBasis (b : HilbertBasis ι ℝ (realSubspace Γ)) : HilbertBasis ι ℂ H := by
  classical
  let v : ι → H := fun i => (b i : H)
  have ho : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪(b i : H), (b j : H)⟫_ℂ = _
    rw [real_inner Γ, orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> simp
  refine HilbertBasis.mkOfOrthogonalEqBot ho (le_antisymm ?_ bot_le)
  intro z hz
  have hv (i : ι) : ⟪v i, z⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hz _ (Submodule.subset_span ⟨i, rfl⟩)
  let x : realSubspace Γ := ⟨realPart Γ z, realPart_mem Γ z⟩
  let y : realSubspace Γ := ⟨imagPart Γ z, imagPart_mem Γ z⟩
  have hcoord (i : ι) :
      ((⟪b i, x⟫_ℝ : ℝ) : ℂ) + Complex.I * ((⟪b i, y⟫_ℝ : ℝ) : ℂ) = 0 := by
    have hi := hv i
    rw [real_imag_decomposition Γ z, inner_add_right, inner_smul_right] at hi
    change ⟪(b i : H), (x : H)⟫_ℂ + Complex.I * ⟪(b i : H), (y : H)⟫_ℂ = 0 at hi
    rwa [real_inner Γ, real_inner Γ] at hi
  have hx : x = 0 := by
    apply b.repr.injective
    ext i
    have hi := congrArg Complex.re (hcoord i)
    simpa [HilbertBasis.repr_apply_apply, Complex.mul_re] using hi
  have hy : y = 0 := by
    apply b.repr.injective
    ext i
    have hi := congrArg Complex.im (hcoord i)
    simpa [HilbertBasis.repr_apply_apply, Complex.mul_im] using hi
  have hz' : z = (x : H) + Complex.I • (y : H) := real_imag_decomposition Γ z
  rw [hx, hy] at hz'
  simp [hz']

@[simp]
theorem complexHilbertBasis_apply (b : HilbertBasis ι ℝ (realSubspace Γ)) (i : ι) :
    complexHilbertBasis Γ b i = (b i : H) := by
  unfold complexHilbertBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem exists_countable_realHilbertBasis [TopologicalSpace.SeparableSpace H] :
    ∃ w : Set (realSubspace Γ), Countable w ∧ Nonempty (HilbertBasis w ℝ (realSubspace Γ)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ (realSubspace Γ)
  let c := complexHilbertBasis Γ b
  let s : w → Set H := fun i => Metric.ball (c i) (1 / 2)
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hdist : dist (c i) (c j) < 1 := by
      have h1 := Metric.mem_ball.mp hzi
      have h2 := Metric.mem_ball.mp hzj
      rw [dist_comm] at h1
      linarith [dist_triangle (c i) z (c j)]
    have horth : ⟪c i, c j⟫_ℝ = 0 := by
      change (⟪c i, c j⟫_ℂ).re = 0
      rw [c.orthonormal.2 hij]
      rfl
    have hsq := norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
    rw [c.orthonormal.1 i, c.orthonormal.1 j, ← dist_eq_norm] at hsq
    nlinarith [dist_nonneg (x := c i) (y := c j)]
  exact ⟨w, hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨c i, Metric.mem_ball_self (by norm_num)⟩), ⟨b⟩⟩

theorem restrictReal_hasSum_hsSq (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (hHS : HilbertSchmidt.IsHilbertSchmidt T) (b : HilbertBasis ι ℝ (realSubspace Γ)) :
    HasSum (fun i => ‖restrictReal Γ T hT (b i)‖ ^ 2) (hsSq T hHS) := by
  let c := complexHilbertBasis Γ b
  let e : ι ≃ Set.range c := Equiv.ofInjective c c.orthonormal.linearIndependent.injective
  have he (i : ι) : ((e i : Set.range c) : H) = c i := rfl
  let v : Set.range c → H := Subtype.val
  have ho : Orthonormal ℂ v := c.orthonormal.toSubtypeRange
  have hd : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [show Set.range v = Set.range c from Subtype.range_coe]
    exact le_of_eq c.dense_span.symm
  let d := HilbertBasis.mk ho hd
  have hsum := HilbertSchmidt.hasSum_norm_sq_apply_of_basis (S := T)
    (exists_hilbertBasis ℂ H).choose_spec.choose d
    (HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis _ _ hHS)
  have hd_apply (i : ι) : d (e i) = (b i : H) := by
    change HilbertBasis.mk ho hd (e i) = _
    rw [HilbertBasis.coe_mk]
    exact (he i).trans (complexHilbertBasis_apply Γ b i)
  have hsum' := e.hasSum_iff.mpr hsum
  change HasSum (fun i => ‖T (d (e i))‖ ^ 2) (hsSq T hHS) at hsum'
  change HasSum (fun i => ‖T (b i : H)‖ ^ 2) (hsSq T hHS)
  simpa only [hd_apply] using hsum'

theorem restrictReal_hsSq (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (hHS : HilbertSchmidt.IsHilbertSchmidt T) (b : HilbertBasis ι ℝ (realSubspace Γ)) :
    (∑' i, ‖restrictReal Γ T hT (b i)‖ ^ 2) = hsSq T hHS :=
  (restrictReal_hasSum_hsSq Γ T hT hHS b).tsum_eq

theorem restrictReal_isCompact (T : H →L[ℂ] H)
    (hT : ∀ h, Γ.toLinearIsometryEquiv (T h) = T (Γ.toLinearIsometryEquiv h))
    (hHS : HilbertSchmidt.IsHilbertSchmidt T) :
    IsCompactOperator (restrictReal Γ T hT) := by
  have h : IsCompactOperator T := HilbertSchmidt.isCompactOperator_of_isHilbertSchmidt hHS
  exact h.restrict (f := (T.restrictScalars ℝ).toLinearMap)
    (fun x hx => show Γ.toLinearIsometryEquiv (T x) = T x by rw [hT, show Γ.toLinearIsometryEquiv x = x from hx])
    (realSubspace_isClosed Γ)

end Basis

/-- The frequency-reflecting conjugation of null-diamond data. -/
def nullDiamondRealConjugation : RealConjugation H4D where
  toLinearIsometryEquiv := nullConj
  involutive := nullConj_involutive
  map_complex_smul := nullConj_smul

end NullConeGravity
