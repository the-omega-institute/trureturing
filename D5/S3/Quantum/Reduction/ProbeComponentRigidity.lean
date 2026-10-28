/- GID: D5/S3/Quantum/Reduction/ProbeComponentRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/ProbeComponentRigidity
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Arbitrary spanning probe families force component-scalar Kraus operators under universal probability preservation. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity

/-!
# Probe-component rigidity

The probe index type is arbitrary. A component is the equivalence closure of
nonzero overlap, and its space is the complex span of the probes in that class.
Universal density-input probability preservation fixes the probe projections
under the dual map. The positive commutator defect then forces every Kraus
operator to commute with them, and nonzero overlap equates the scalar actions.

Mayer--Knill, arXiv:1805.04491v1, Theorem 1 gives the connected rigidity result.
Koashi--Imoto, quant-ph/0101144 gives the broader nondisturbance structure.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Reduction.ProbeComponentRigidity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance

variable {d s J : Type*} [Fintype d] [DecidableEq d] [Fintype s]

/-- Rank-one probe effect. -/
def probe (v : d → ℂ) : Matrix d d ℂ := vecMulVec v (star v)

/-- The nonorthogonality-component relation, with no finite-family assumption. -/
def SameComponent (v : J → d → ℂ) : J → J → Prop :=
  Relation.EqvGen (fun i j => star (v i) ⬝ᵥ v j ≠ 0)

/-- The actual span of one graph component. -/
def componentSpace (v : J → d → ℂ) (j : J) : Submodule ℂ (d → ℂ) :=
  Submodule.span ℂ {x | ∃ i, SameComponent v j i ∧ v i = x}

/-- Matrix action of a canonical channel. -/
def channelMatrix (T : QuantumChannel d d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

private theorem hermitian_density_separation (A : Matrix d d ℂ) (hA : A.IsHermitian)
    (h : ∀ ρ : DensityState d,
      trace (A * CStarMatrix.ofMatrix.symm ρ.1) = 0) : A = 0 := by
  have he (i : d) : hA.eigenvalues i = 0 := by
    let v : d → ℂ := (hA.eigenvectorBasis i).ofLp
    have hv : star v ⬝ᵥ v = 1 := by
      rw [dotProduct_comm]
      change (hA.eigenvectorBasis i).ofLp ⬝ᵥ star (hA.eigenvectorBasis i).ofLp = 1
      rw [← EuclideanSpace.inner_eq_star_dotProduct]
      simp [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.norm_eq_one i]
    have hz := h (pureState v hv)
    change trace (A * probe v) = 0 at hz
    rw [probe, mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at hz
    rw [hA.eigenvalues_eq i]
    exact congrArg Complex.re hz
  rw [hA.spectral_theorem]
  simp [he, Function.comp_def]

private theorem dual_fixed (K : s → Matrix d d ℂ) (P : Matrix d d ℂ)
    (hP : P.IsHermitian)
    (h : ∀ ρ : DensityState d,
      trace (P * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (P * CStarMatrix.ofMatrix.symm ρ.1)) :
    (∑ a, (K a)ᴴ * P * K a) = P := by
  apply sub_eq_zero.mp
  apply hermitian_density_separation _
  · apply IsHermitian.sub _ hP
    apply isSelfAdjoint_sum
    intro a ha
    exact isHermitian_conjTranspose_mul_mul (K a) hP
  · intro ρ
    rw [sub_mul, trace_sub]
    apply sub_eq_zero.mpr
    rw [Matrix.sum_mul, trace_sum]
    have hh := h ρ
    rw [Matrix.mul_sum, trace_sum] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro a ha
    calc
      trace (((K a)ᴴ * P * K a) * CStarMatrix.ofMatrix.symm ρ.1) =
          trace ((K a)ᴴ * (P * K a * CStarMatrix.ofMatrix.symm ρ.1)) := by
        simp only [mul_assoc]
      _ = trace ((P * K a * CStarMatrix.ofMatrix.symm ρ.1) * (K a)ᴴ) :=
        trace_mul_comm _ _
      _ = trace (P * (K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) := by
        simp only [mul_assoc]

private theorem kraus_commutes_projection (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (P : Matrix d d ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hfix : (∑ a, (K a)ᴴ * P * K a) = P) (a : s) :
    K a * P = P * K a := by
  have hs : (∑ b, (K b * P - P * K b)ᴴ * (K b * P - P * K b)) = 0 := by
    calc
      _ = P * (∑ b, (K b)ᴴ * K b) * P -
          P * (∑ b, (K b)ᴴ * P * K b) -
          (∑ b, (K b)ᴴ * P * K b) * P +
          (∑ b, (K b)ᴴ * (P * P) * K b) := by
        simp only [conjTranspose_sub, conjTranspose_mul, hP,
          mul_sub, sub_mul, mul_add, add_mul, Matrix.mul_sum, Matrix.sum_mul,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc]
        abel
      _ = 0 := by rw [hTP, hPP, hfix]; simp [hPP]
  have hn : (0 : s → Matrix d d ℂ) ≤
      (fun b => (K b * P - P * K b)ᴴ * (K b * P - P * K b)) :=
    fun b => (posSemidef_conjTranspose_mul_self _).nonneg
  have hz := (Fintype.sum_eq_zero_iff_of_nonneg hn).mp hs
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp (congrFun hz a))

private theorem probe_idempotent (v : d → ℂ) (hv : star v ⬝ᵥ v = 1) :
    probe v * probe v = probe v := by
  simp [probe, vecMulVec_mul_vecMulVec, hv]

/-- Universal probability preservation forces every represented Kraus operator
    to commute with every probe effect. -/
theorem probability_preserving_kraus_commute (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    ∀ a j, K a * probe (v j) = probe (v j) * K a := by
  intro a j
  exact kraus_commutes_projection K hTP (probe (v j))
    (by simp [probe]) (probe_idempotent _ (hv j))
    (dual_fixed K _ (posSemidef_vecMulVec_self_star _).1 (hprob j)) a

/-- Scalar of one Kraus map on a unit probe. -/
def probeScalar (C : Matrix d d ℂ) (v : d → ℂ) : ℂ := star v ⬝ᵥ (C *ᵥ v)

private theorem probe_mulVec (v x : d → ℂ) :
    probe v *ᵥ x = (star v ⬝ᵥ x) • v := by
  ext i
  simp [probe, vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
    mul_comm, mul_left_comm, mul_assoc]

private theorem probe_eigenvector (C : Matrix d d ℂ) (v : d → ℂ)
    (hv : star v ⬝ᵥ v = 1) (hc : C * probe v = probe v * C) :
    C *ᵥ v = probeScalar C v • v := by
  have h := congrArg (fun M : Matrix d d ℂ => M *ᵥ v) hc
  simpa only [← mulVec_mulVec, probe_mulVec, hv, one_smul,
    probeScalar] using h

private theorem overlap_scalar (C : Matrix d d ℂ) (v w : d → ℂ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hc : C * probe v = probe v * C) (hd : C * probe w = probe w * C)
    (hn : star v ⬝ᵥ w ≠ 0) : probeScalar C v = probeScalar C w := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have h := congrArg (fun M : Matrix d d ℂ => M *ᵥ w) hc
  simp only [← mulVec_mulVec, probe_mulVec, mulVec_smul,
    probe_eigenvector C v hv hc, probe_eigenvector C w hw hd,
    dotProduct_smul, smul_smul] at h
  have he := smul_left_injective ℂ hv0 h
  exact mul_left_cancel₀ hn (by simpa only [mul_comm] using he)

private theorem component_scalar_equal (C : Matrix d d ℂ)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hc : ∀ j, C * probe (v j) = probe (v j) * C)
    {i j : J} (hij : SameComponent v i j) :
    probeScalar C (v i) = probeScalar C (v j) := by
  induction hij with
  | rel i j h => exact overlap_scalar C (v i) (v j) (hv i) (hv j) (hc i) (hc j) h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Scalarity is derived on the full complex span of each arbitrary-family
    graph component, for every Kraus representation. -/
theorem kraus_scalar_on_component (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    ∀ a j x, x ∈ componentSpace v j →
      K a *ᵥ x = probeScalar (K a) (v j) • x := by
  have hc := probability_preserving_kraus_commute K hTP v hv hprob
  intro a j x hx
  have hs : componentSpace v j ≤
      Module.End.eigenspace (K a).mulVecLin (probeScalar (K a) (v j)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change K a *ᵥ v i = _
    rw [probe_eigenvector _ _ (hv i) (hc a i),
      component_scalar_equal _ v hv (hc a) hi]
  exact Module.End.mem_eigenspace_iff.mp (hs hx)

/-- Trace preservation normalizes any finite rectangular Kraus representation
    of the actual canonical channel. -/
theorem kraus_normalized_of_channel {i o : Type*}
    [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]
    (T : QuantumChannel i o) (K : s → Matrix o i ℂ)
    (hK : ∀ X : Matrix i i ℂ, CStarMatrix.ofMatrix.symm
      (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = ∑ a, K a * X * (K a)ᴴ) :
    (∑ a, (K a)ᴴ * K a) = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [one_mul]
  have h := T.trace_preserving (CStarMatrix.ofMatrix X)
  change trace (CStarMatrix.ofMatrix.symm
    (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = trace X at h
  rw [hK, trace_sum] at h
  rw [Matrix.sum_mul, trace_sum]
  convert h using 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_cycle']

/-- The canonical CP supplier transfers component scalarity to every channel;
    complete positivity is the actual all-amplification predicate. -/
theorem channel_component_scalar (T : QuantumChannel d d)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * channelMatrix T (CStarMatrix.ofMatrix.symm ρ.1)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    ∃ K : (d × d) → Matrix d d ℂ,
      (∀ X, channelMatrix T X = ∑ a, K a * X * (K a)ᴴ) ∧
      (∑ a, (K a)ᴴ * K a) = 1 ∧
      ∀ a j x, x ∈ componentSpace v j →
        K a *ᵥ x = probeScalar (K a) (v j) • x := by
  let K := (krausRepresentation T.toCompletelyPositiveMap).1
  have hK : ∀ X, channelMatrix T X = ∑ a, K a * X * (K a)ᴴ :=
    (krausRepresentation T.toCompletelyPositiveMap).2
  have ht := kraus_normalized_of_channel T K hK
  refine ⟨K, hK, ht, kraus_scalar_on_component K ht v hv ?_⟩
  simpa only [← hK] using hprob

private theorem component_top_of_connected (v : J → d → ℂ)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hc : ∀ i j, SameComponent v i j) (j : J) : componentSpace v j = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, hc j i, rfl⟩

/-- A connected spanning family forces the actual channel to be identity on
    every matrix. The pre-existing identity Kraus supplier gives the final
    scalar matrix statement for the same representation. -/
theorem connected_probability_preserving_identity (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hc : ∀ i j, SameComponent v i j) (j : J) (i₀ : d)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    (∀ X : Matrix d d ℂ, (∑ a, K a * X * (K a)ᴴ) = X) ∧
      ∀ a, K a = K a i₀ i₀ • (1 : Matrix d d ℂ) := by
  have hs := kraus_scalar_on_component K hTP v hv hprob
  let coeff : s → ℂ := fun a => probeScalar (K a) (v j)
  have hk (a) : K a = coeff a • (1 : Matrix d d ℂ) := by
    apply ext_iff_mulVec.mpr
    intro x
    simpa only [smul_mulVec, one_mulVec, coeff] using
      hs a j x (by rw [component_top_of_connected v hspan hc j]; trivial)
  have hl : (∑ a, star (coeff a) * coeff a) = 1 := by
    have h := congrArg (fun M : Matrix d d ℂ => M i₀ i₀) hTP
    simp only [hk, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, one_mul, smul_smul, Matrix.sum_apply, Matrix.smul_apply,
      one_apply_eq, smul_eq_mul, mul_one] at h
    simpa only [mul_comm] using h
  have hi (X : Matrix d d ℂ) : (∑ a, K a * X * (K a)ᴴ) = X := by
    simp only [hk, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, one_mul, mul_one, smul_smul]
    rw [← Finset.sum_smul]
    rw [hl, one_smul]
  refine ⟨hi, ?_⟩
  exact D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar K hi i₀

private theorem kraus_inner (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1) (x y : d → ℂ) :
    (∑ a, star (K a *ᵥ x) ⬝ᵥ (K a *ᵥ y)) = star x ⬝ᵥ y := by
  have hp (a) : star (K a *ᵥ x) ⬝ᵥ (K a *ᵥ y) =
      star x ⬝ᵥ (((K a)ᴴ * K a) *ᵥ y) := by
    rw [← mulVec_mulVec, dotProduct_mulVec (star x), ← star_mulVec]
  simp_rw [hp]
  rw [← dotProduct_sum, ← Matrix.sum_mulVec, hTP, one_mulVec]

/-- The actual finite-environment Stinespring linear isometry associated with
    the normalized Kraus family. The environment coordinate is the Kraus index. -/
def krausStinespring (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1) :
    EuclideanSpace ℂ d →ₗᵢ[ℂ] EuclideanSpace ℂ (s × d) := by
  let L : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ (s × d) :=
    { toFun := fun x => WithLp.toLp 2 (fun p => (K p.1 *ᵥ x.ofLp) p.2)
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective
        ext p
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        apply WithLp.ofLp_injective
        ext p
        simp [Matrix.mulVec_smul] }
  exact L.isometryOfInner (by
    intro x y
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, L,
      LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    have h := kraus_inner K hTP x.ofLp y.ofLp
    simpa only [dotProduct, Pi.star_apply, mul_comm] using h)

/-- A finite Stinespring environment is constant on each complete graph
    component and has unit norm. The formula is asserted on every vector in
    the component space, not just its original probe generators. -/
theorem component_stinespring_form (K : s → Matrix d d ℂ)
    (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    (∀ j, (∑ a, star (probeScalar (K a) (v j)) * probeScalar (K a) (v j)) = 1) ∧
    (∀ j x, x ∈ componentSpace v j → ∀ i a,
      (krausStinespring K hTP (WithLp.toLp 2 x)) (a, i) =
        x i * probeScalar (K a) (v j)) := by
  have hs := kraus_scalar_on_component K hTP v hv hprob
  have hm (j) : v j ∈ componentSpace v j :=
    Submodule.subset_span ⟨j, Relation.EqvGen.refl j, rfl⟩
  constructor
  · intro j
    have h := kraus_inner K hTP (v j) (v j)
    simp only [hs _ j _ (hm j), star_smul, smul_dotProduct, dotProduct_smul,
      hv j, smul_eq_mul, mul_one] at h
    simpa only [mul_comm] using h
  · intro j x hx i a
    change (K a *ᵥ x) i = x i * probeScalar (K a) (v j)
    simp only [hs a j x hx, Pi.smul_apply, smul_eq_mul, mul_comm]

#print axioms connected_probability_preserving_identity
#print axioms component_stinespring_form
#print axioms probability_preserving_kraus_commute
#print axioms kraus_scalar_on_component
#print axioms channel_component_scalar
#print axioms kraus_normalized_of_channel
end D5.S3.Quantum.Reduction.ProbeComponentRigidity
