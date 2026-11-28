/- GID: D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit-vector trace distance and the tail criterion for pure product GNS sectors. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Analysis.GNSOrderCoordinates
import D5.S3.QuantumStates.GNSCompatibleStateExtension
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import D5.S3.OperatorAlgebra.VectorStateGNS
import D5.S3.Matrix.QubitProductDistance

/-!
# Pure vector states and product GNS sectors

The finite distance calculation uses the rank-two polynomial of a difference of ray
projections. Its positive square root yields the trace norm, and trace pairing identifies
this norm with the norm of the difference of the two vector-state functionals.

On the common qubit algebra, each reference vacuum is cyclic with scalar commutant.
Finite rotations produce a common Hilbert-space realization when the overlap deficits
are summable. In the divergent case, vacuum projections force all intertwiners to vanish.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Analysis.NullConeGravity.PureGNSExtensionSectors

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.PureState.PureStateHandshake

section FiniteVectorStates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma trace_density_mul (x : ι → ℂ) (A : Matrix ι ι ℂ) :
    (A * rankOneDensity x).trace = star x ⬝ᵥ (A *ᵥ x) := by
  rw [rankOneDensity, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

omit [DecidableEq ι] in
private lemma density_sandwich (x y : ι → ℂ) (hx : star x ⬝ᵥ x = 1) :
    rankOneDensity x * rankOneDensity y * rankOneDensity x =
      (‖star x ⬝ᵥ y‖ ^ 2 : ℝ) • rankOneDensity x := by
  have hconj : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
    simp [dotProduct, Pi.star_apply, mul_comm]
  rw [(pure_state_handshake x hx (rankOneDensity y)).2.1]
  have h : star x ⬝ᵥ (rankOneDensity y *ᵥ x) = ((‖star x ⬝ᵥ y‖ ^ 2 : ℝ) : ℂ) := by
    rw [rankOneDensity, vecMulVec_mulVec, dotProduct_smul]
    change (star x ⬝ᵥ y) * (star y ⬝ᵥ x) = _
    rw [← hconj, mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  rw [h]
  rfl

/-- The trace norm of the difference of two unit-vector density matrices. -/
theorem pure_matrix_traceNorm (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (rankOneDensity ψ.ofLp - rankOneDensity φ.ofLp) =
      2 * Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) := by
  let P := rankOneDensity ψ.ofLp
  let Q := rankOneDensity φ.ofLp
  let X := P - Q
  let d := 1 - ‖inner ℂ ψ φ‖ ^ 2
  have hxy : star ψ.ofLp ⬝ᵥ φ.ofLp = inner ℂ ψ φ := by
    rw [dotProduct_comm]
    rfl
  have hyx : star φ.ofLp ⬝ᵥ ψ.ofLp = inner ℂ φ ψ := by
    rw [dotProduct_comm]
    rfl
  have hself (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) : star v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [dotProduct_comm]
    change inner ℂ v v = 1
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have hp : P * P = P := (pure_state_handshake ψ.ofLp (hself ψ hψ) P).1
  have hq : Q * Q = Q := (pure_state_handshake φ.ofLp (hself φ hφ) Q).1
  have hsymm : ‖inner ℂ φ ψ‖ = ‖inner ℂ ψ φ‖ := norm_inner_symm _ _
  have hpqp : P * Q * P = (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • P := by
    simpa only [P, Q, hxy] using density_sandwich ψ.ofLp φ.ofLp (hself ψ hψ)
  have hqpq : Q * P * Q = (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • Q := by
    simpa only [P, Q, hyx, hsymm] using density_sandwich φ.ofLp ψ.ofLp (hself φ hφ)
  have hc : X * X * X = d • X := by
    change (P - Q) * (P - Q) * (P - Q) = d • (P - Q)
    rw [sub_mul, mul_sub P, mul_sub Q, hp, hq, sub_mul, sub_mul, sub_mul]
    rw [mul_sub P, mul_sub Q, mul_sub (P * Q), mul_sub (Q * P)]
    rw [hp, hq, Matrix.mul_assoc P Q Q, Matrix.mul_assoc Q P P, hp, hq, hpqp, hqpq]
    simp only [d, sub_smul, one_smul, smul_sub]
    abel
  have hX : X.IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star ψ.ofLp).1.sub
      (Matrix.posSemidef_vecMulVec_self_star φ.ofLp).1
  have hXX : (X * X).PosSemidef := by
    simpa only [hX.eq] using X.posSemidef_conjTranspose_mul_self
  have htrp : P.trace = 1 := by
    simpa [P, rankOneDensity, dotProduct_comm] using hself ψ hψ
  have htrq : Q.trace = 1 := by
    simpa [Q, rankOneDensity, dotProduct_comm] using hself φ hφ
  have htrpq : (P * Q).trace = ((‖inner ℂ ψ φ‖ ^ 2 : ℝ) : ℂ) := by
    rw [trace_density_mul]
    change star φ.ofLp ⬝ᵥ (rankOneDensity ψ.ofLp *ᵥ φ.ofLp) = _
    rw [rankOneDensity, vecMulVec_mulVec, dotProduct_smul, hxy, hyx]
    change inner ℂ φ ψ * inner ℂ ψ φ = _
    rw [← inner_conj_symm φ ψ, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have htr : (X * X).trace = ((2 * d : ℝ) : ℂ) := by
    change ((P - Q) * (P - Q)).trace = _
    rw [sub_mul, mul_sub P, mul_sub Q, hp, hq, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, htrp, htrq, Matrix.trace_mul_comm Q P, htrpq]
    push_cast [d]
    ring
  have hd : 0 ≤ d := by
    have hle : ‖inner ℂ ψ φ‖ ≤ 1 := by simpa [hψ, hφ] using norm_inner_le_norm ψ φ
    dsimp [d]
    nlinarith [norm_nonneg (inner ℂ ψ φ)]
  set b := Real.sqrt d with hb
  have hb₂ : b * b = d := Real.mul_self_sqrt hd
  change (CFC.sqrt (Xᴴ * X)).trace.re = 2 * b
  rw [hX.eq]
  by_cases hb₀ : b = 0
  · have hd₀ : d = 0 := by simpa [hb₀] using hb₂.symm
    have hzero : X * X = 0 := hXX.trace_eq_zero_iff.mp (by simp [htr, hd₀])
    simp [hzero, hb₀]
  · have hnonneg : 0 ≤ b⁻¹ • (X * X) := smul_nonneg
      (inv_nonneg.mpr (Real.sqrt_nonneg _)) hXX.nonneg
    have hsq : (b⁻¹ • (X * X)) * (b⁻¹ • (X * X)) = X * X := by
      rw [smul_mul_assoc, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hc,
        smul_mul_assoc, smul_smul, ← hb₂]
      have hs : b⁻¹ * b⁻¹ * (b * b) = 1 := by field_simp
      simp [hs]
    rw [CFC.sqrt_unique hsq hnonneg, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, htr]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← hb₂]
    field_simp

private def traceFunctional (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℂ (Matrix ι ι ℂ)).flip A)

private lemma norm_traceFunctional_of_nonneg (A : Matrix ι ι ℂ) (hA : 0 ≤ A) :
    ‖traceFunctional A‖ = A.trace.re := by
  have hpos : Monotone (traceFunctional A) := by
    apply (monotone_iff_map_nonneg _).mpr
    intro B hB
    let S := CFC.sqrt A
    have hS : Sᴴ = S := (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
    change 0 ≤ (B * A).trace
    rw [← CFC.sqrt_mul_sqrt_self A hA, Matrix.trace_mul_cycle']
    change 0 ≤ (S * (B * S)).trace
    rw [← Matrix.mul_assoc]
    have hSB := (hB.posSemidef.mul_mul_conjTranspose_same S).trace_nonneg
    rwa [hS] at hSB
  have heq := congrArg Complex.re
    (ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp hpos)
  change Complex.re (↑‖traceFunctional A‖) = (1 * A).trace.re at heq
  simpa using heq

set_option maxHeartbeats 500000 in
private lemma norm_traceFunctional_of_hermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖traceFunctional A‖ = traceNorm A := by
  by_cases hi : Nonempty ι
  · have : Nonempty ι := hi
    refine le_antisymm ?_ ?_
    · have hdiff : traceFunctional A =
          traceFunctional (posPart A) - traceFunctional (negPart A) := by
        ext B
        change (B * A).trace = (B * posPart A).trace - (B * negPart A).trace
        rw [← Matrix.trace_sub, ← mul_sub, CFC.posPart_sub_negPart A hA]
      rw [hdiff, trace_norm_jordan_mass A hA]
      calc
        _ ≤ ‖traceFunctional (posPart A)‖ + ‖traceFunctional (negPart A)‖ := norm_sub_le _ _
        _ = _ := by
          rw [norm_traceFunctional_of_nonneg (posPart A) (CFC.posPart_nonneg A),
            norm_traceFunctional_of_nonneg (negPart A) (CFC.negPart_nonneg A)]
    · obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U A).1
      have hnorm : ‖U.val‖ ≤ 1 := (CStarRing.norm_coe_unitary U).le
      rw [← hU]
      exact (Complex.re_le_norm _).trans ((traceFunctional A).unit_le_opNorm U.val hnorm)
  · have : IsEmpty ι := not_nonempty_iff.mp hi
    have hzero : A = 0 := Subsingleton.elim _ _
    subst A
    have hzero : traceFunctional (0 : Matrix ι ι ℂ) = 0 := by
      ext B
      change (B * (0 : Matrix ι ι ℂ)).trace = 0
      simp
    simp [hzero, traceNorm]

/-- The unit-vector expectation as a continuous linear functional on the matrix algebra. -/
def matrixVectorState (ψ : EuclideanSpace ℂ ι) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  traceFunctional (rankOneDensity ψ.ofLp)

/-- The matrix vector-state functional evaluates the inner product with the matrix action. -/
theorem matrixVectorState_apply (ψ : EuclideanSpace ℂ ι) (A : Matrix ι ι ℂ) :
    matrixVectorState ψ A = inner ℂ ψ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A ψ) := by
  change (A * rankOneDensity ψ.ofLp).trace = _
  rw [trace_density_mul, dotProduct_comm,
    ← Matrix.ofLp_toEuclideanCLM]
  rfl

/-- The dual operator norm gives the same pure-state distance as the matrix trace norm. -/
theorem pure_matrix_vectorState_norm (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖matrixVectorState ψ - matrixVectorState φ‖ =
      2 * Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) := by
  have hdiff : matrixVectorState ψ - matrixVectorState φ =
      traceFunctional (rankOneDensity ψ.ofLp - rankOneDensity φ.ofLp) := by
    ext B
    change (B * rankOneDensity ψ.ofLp).trace - (B * rankOneDensity φ.ofLp).trace =
      (B * (rankOneDensity ψ.ofLp - rankOneDensity φ.ofLp)).trace
    rw [mul_sub, Matrix.trace_sub]
  rw [hdiff, norm_traceFunctional_of_hermitian, pure_matrix_traceNorm ψ φ hψ hφ]
  exact (Matrix.posSemidef_vecMulVec_self_star ψ.ofLp).1.sub
    (Matrix.posSemidef_vecMulVec_self_star φ.ofLp).1


end FiniteVectorStates

open scoped InnerProductSpace
open Physicslib4.GNS Omega.OperatorAlgebra.VectorStateGNS

section VectorState

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def vectorState (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (hv : ‖v‖ = 1) : State A :=
  { toContinuousLinearMap := coeffFunctional π v 1
    isPositive := fun a => by
      simpa only [coeffFunctional_apply, one_apply_eq_self,
        vectorFunctional_apply] using
        (vectorFunctional π v).map_nonneg (star_mul_self_nonneg a)
    isNormalized := by
      let L := coeffFunctional π v 1
      have hL (a : A) : L a = inner ℂ v (π a v) := by simp [L]
      have h1 : L 1 = 1 := by
        rw [hL, map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hv]
        simp
      have hm : Monotone L :=
        (monotone_iff_map_nonneg _).mpr fun a ha => by
          rw [hL, ← vectorFunctional_apply]
          exact (vectorFunctional π v).map_nonneg ha
      have hn := congrArg Complex.re
        (ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp hm)
      simpa only [h1, Complex.ofReal_re, Complex.one_re] using hn }

private theorem vectorState_isPure
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (hv : ‖v‖ = 1)
    (hcyc : DenseRange (fun a => π a v)) (hirr : IsIrreducible π) :
    IsPure (vectorState π v hv) := by
  intro L hL hdom
  let f := vectorFunctional π v
  let U := cyclicUnitary π v hcyc
  let V := U.toContinuousLinearEquiv.toContinuousLinearMap
  let W := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let Lp : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ L.toLinearMap (fun a ha => by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    exact hL b)
  have hd : GNSOrderCoordinates.Dominated Lp f := by
    intro a ha
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    have hb := hdom b
    change L (star b * b) ≤ inner ℂ v (π (star b * b) v) at hb
    exact hb
  let T := GNSOrderCoordinates.coordinate Lp f hd
  have hT : ∀ a, Commute T (f.gnsStarAlgHom a) :=
    (GNSOrderCoordinates.coordinate_mem Lp f hd).2.2
  have hU (a : A) (x : f.GNS) : U (f.gnsStarAlgHom a x) = π a (U x) :=
    cyclicUnitary_intertwines π v hcyc a x
  have hcomm (a : A) : π a * (V.comp (T.comp W)) = (V.comp (T.comp W)) * π a := by
    ext x
    change π a (U (T (U.symm x))) = U (T (U.symm (π a x)))
    rw [← hU, ← show f.gnsStarAlgHom a (U.symm x) = U.symm (π a x) by
      apply U.injective
      rw [hU, U.apply_symm_apply, U.apply_symm_apply]]
    exact congrArg U (congrFun (congrArg (fun Q : f.GNS →L[ℂ] f.GNS => ⇑Q) (hT a).eq.symm)
      (U.symm x))
  obtain ⟨t, ht⟩ := hirr (V.comp (T.comp W)) hcomm
  have hscalar (x : f.GNS) : T x = t • x := by
    apply U.injective
    have h := congrFun (congrArg (fun Q : H →L[ℂ] H => ⇑Q) ht) (U x)
    change U (T (U.symm (U x))) = t • U x at h
    rw [U.symm_apply_apply] at h
    exact h.trans (U.map_smul t x).symm
  refine ⟨t, fun a => ?_⟩
  change Lp a = t * inner ℂ v (π a v)
  rw [GNSOrderCoordinates.coordinate_represents Lp f hd, hscalar,
    inner_smul_right]
  congr 1
  rw [← U.inner_map_map, hU]
  have hVac : U (GNSOrderCoordinates.cyclicVector f) = v :=
    cyclicUnitary_vacuum π v hcyc
  rw [hVac]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem cyclic_of_irreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (hv : ‖v‖ = 1) (hirr : IsIrreducible π) : DenseRange (fun a => π a v) := by
  intro x
  let T := InnerProductSpace.rankOne ℂ x v
  have hT : T ∈ (π.range : Set (H →L[ℂ] H)).centralizer.centralizer := by
    change T ∈ gnsVonNeumann π
    rw [gnsVonNeumann_eq_univ_of_isIrreducible hirr]
    exact Set.mem_univ _
  have h := StarSubalgebra.apply_mem_closure_of_mem_centralizer_centralizer π.range hT v
  have hTv : T v = x := by
    rw [show T v = _ from InnerProductSpace.rankOne_apply _ _ _,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [hTv] at h
  apply closure_mono _ h
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨a, rfl⟩

private theorem cyclicUnitary_symm_intertwines
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (hc : DenseRange (fun a => π a v))
    (a : A) (x : H) :
    (cyclicUnitary π v hc).symm (π a x) =
      (vectorFunctional π v).gnsStarAlgHom a ((cyclicUnitary π v hc).symm x) := by
  apply (cyclicUnitary π v hc).injective
  rw [LinearIsometryEquiv.apply_symm_apply, cyclicUnitary_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

private theorem cyclicUnitary_of_expectation
    (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (h : ∀ a, f a = inner ℂ v (π a v)) (hc : DenseRange (fun a => π a v)) :
    ∃ U : f.GNS ≃ₗᵢ[ℂ] H, ∀ a x, U (f.gnsStarAlgHom a x) = π a (U x) := by
  have hf : f = vectorFunctional π v := DFunLike.ext _ _ h
  subst f
  exact ⟨cyclicUnitary π v hc, cyclicUnitary_intertwines π v hc⟩

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Two completed GNS representations are equivalent when a unitary intertwines their actions. -/
def GNSEquivalent (f g : A →ₚ[ℂ] ℂ) : Prop :=
  ∃ U : f.GNS ≃ₗᵢ[ℂ] g.GNS, ∀ a x, U (f.gnsStarAlgHom a x) = g.gnsStarAlgHom a (U x)

/-- Two completed GNS representations are disjoint when every bounded intertwiner is zero. -/
def GNSDisjoint (f g : A →ₚ[ℂ] ℂ) : Prop :=
  ∀ T : f.GNS →L[ℂ] g.GNS,
    (∀ a x, T (f.gnsStarAlgHom a x) = g.gnsStarAlgHom a (T x)) → T = 0

private theorem gnsEquivalent_of_commonRealization (f g : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v w : H)
    (hf : ∀ a, f a = inner ℂ v (π a v)) (hg : ∀ a, g a = inner ℂ w (π a w))
    (hv : DenseRange (fun a => π a v)) (hw : DenseRange (fun a => π a w)) :
    GNSEquivalent f g := by
  obtain ⟨U, hU⟩ := cyclicUnitary_of_expectation f π v hf hv
  obtain ⟨V, hV⟩ := cyclicUnitary_of_expectation g π w hg hw
  refine ⟨U.trans V.symm, fun a x => V.injective ?_⟩
  change V (V.symm (U (f.gnsStarAlgHom a x))) =
    V (g.gnsStarAlgHom a (V.symm (U x)))
  rw [V.apply_symm_apply, hU, hV, V.apply_symm_apply]

private theorem gnsDisjoint_of_disjoint (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : H) (w : K)
    (hv : DenseRange (fun a => π a v)) (hw : DenseRange (fun a => ρ a w))
    (h : ∀ S : H →L[ℂ] K, (∀ a x, S (π a x) = ρ a (S x)) → S = 0) :
    GNSDisjoint (vectorFunctional π v) (vectorFunctional ρ w) := by
  intro T hT
  let U := cyclicUnitary π v hv
  let V := cyclicUnitary ρ w hw
  let S := V.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hs : S = 0 := h S (fun a x => by
    change V (T (U.symm (π a x))) = ρ a (V (T (U.symm x)))
    rw [cyclicUnitary_symm_intertwines π v hv a x, hT, cyclicUnitary_intertwines ρ w hw])
  ext x
  apply V.injective
  have hx := DFunLike.congr_fun hs (U x)
  change V (T (U.symm (U x))) = 0 at hx
  rw [U.symm_apply_apply] at hx
  simpa only [_root_.zero_apply, map_zero] using hx

private theorem not_gnsEquivalent_of_disjoint {f g : A →ₚ[ℂ] ℂ}
    (hf : f 1 = 1) (hd : GNSDisjoint f g) : ¬ GNSEquivalent f g := by
  rintro ⟨U, hU⟩
  let L := U.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : L = 0 := hd L hU
  let v : f.GNS := f.toPreGNS 1
  have hv : ‖v‖ = 1 := (D5.S3.QuantumStates.GNSCompatibleStateExtension.normalized_gns f hf).1
  have hz : U v = 0 := DFunLike.congr_fun hL v
  have he : v = 0 := U.injective (hz.trans (U.map_zero).symm)
  simp [he] at hv

end VectorState

section QubitProductStates

open Filter Omega.QubitProduct Omega.Analysis.TailProducts
open scoped BigOperators

/-- The first normalized vacuum state of the common qubit observable algebra. -/
def firstProductState (r : Overlaps) : State (pairAlgebra r) :=
  vectorState (firstRep r) (basisVector ∅) (norm_basisVector ∅)

/-- The second normalized vacuum state of the common qubit observable algebra. -/
def secondProductState (r : Overlaps) : State (pairAlgebra r) :=
  vectorState (secondRep r) (basisVector ∅) (norm_basisVector ∅)

private theorem first_irreducible (r : Overlaps) : Physicslib4.GNS.IsIrreducible (firstRep r) :=
  first_scalar_commutant r

/-- The two product states are pure on their common norm-closed observable algebra. -/
theorem pure_product_states (r : Overlaps) :
    IsPure (firstProductState r) ∧ IsPure (secondProductState r) :=
  ⟨vectorState_isPure _ _ _ (first_cyclic r) (first_irreducible r),
    vectorState_isPure _ _ _ (second_cyclic r) (second_scalar_commutant r)⟩

private theorem productFunctionals (r : Overlaps) :
    (firstProductState r).toPositiveLinearMap =
      vectorFunctional (firstRep r) (basisVector ∅) ∧
    (secondProductState r).toPositiveLinearMap =
      vectorFunctional (secondRep r) (basisVector ∅) :=
  ⟨DFunLike.ext _ _ (fun _ => rfl), DFunLike.ext _ _ (fun _ => rfl)⟩

private theorem firstFunctional_one (r : Overlaps) :
    (firstProductState r).toPositiveLinearMap 1 = 1 := by
  rw [(productFunctionals r).1, vectorFunctional_apply, map_one, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K, norm_basisVector]
  simp

private theorem summable_equivalent (r : Overlaps) (hs : Summable (fun k => 1 - overlaps r k)) :
    GNSEquivalent (firstProductState r).toPositiveLinearMap
      (secondProductState r).toPositiveLinearMap := by
  obtain ⟨v, hv, he⟩ := equivalent_vacuum r hs
  rw [(productFunctionals r).1, (productFunctionals r).2]
  exact gnsEquivalent_of_commonRealization _ _ (firstRep r) (basisVector ∅) v
    (fun _ => rfl) (fun a => (he a).symm) (first_cyclic r)
    (cyclic_of_irreducible _ _ hv (first_irreducible r))

set_option maxHeartbeats 800000 in
private theorem not_summable_disjoint (r : Overlaps)
    (hs : ¬ Summable (fun k => 1 - overlaps r k)) :
    GNSDisjoint (firstProductState r).toPositiveLinearMap
      (secondProductState r).toPositiveLinearMap := by
  rw [(productFunctionals r).1, (productFunctionals r).2]
  exact gnsDisjoint_of_disjoint _ _ _ _ (first_cyclic r) (second_cyclic r)
    (intertwiner_zero_of_not_summable r hs)

/-- Positive tail products classify unitary equivalence. Vanishing of every tail
classifies disjointness, including sequences with some orthogonal sites. -/
theorem pure_product_gns_dichotomy (r : Overlaps) :
    (GNSEquivalent (firstProductState r).toPositiveLinearMap
        (secondProductState r).toPositiveLinearMap ↔
      Summable (fun k => 1 - overlaps r k)) ∧
    (GNSDisjoint (firstProductState r).toPositiveLinearMap
        (secondProductState r).toPositiveLinearMap ↔
      ∀ s, tailProduct (overlaps r) s = 0) := by
  have htail := all_tail_products_zero_iff (overlaps r) (fun k => (r k).2)
  refine ⟨⟨fun he => ?_, summable_equivalent r⟩, ?_⟩
  · by_contra hn
    exact not_gnsEquivalent_of_disjoint (firstFunctional_one r) (not_summable_disjoint r hn) he
  · rw [htail]
    refine ⟨fun hd hs => ?_, not_summable_disjoint r⟩
    exact not_gnsEquivalent_of_disjoint (firstFunctional_one r) hd (summable_equivalent r hs)


/-- The norm distance on the common qubit algebra is determined by the full
overlap product, which can vanish even in equivalent sectors. -/
theorem pure_product_state_norm (r : Overlaps) :
    ContinuousLinearMap.opNorm (𝕜 := ℂ) (𝕜₂ := ℂ) (E := pairAlgebra r) (F := ℂ)
      ((firstProductState r).toContinuousLinearMap - (secondProductState r).toContinuousLinearMap) =
      2 * Real.sqrt (1 - tailProduct (overlaps r) 0 ^ 2) := by
  let L := (firstProductState r).toContinuousLinearMap -
    (secondProductState r).toContinuousLinearMap
  have hL (a : pairAlgebra r) : L a =
      inner ℂ (basisVector ∅) (firstRep r a (basisVector ∅)) -
      inner ℂ (basisVector ∅) (secondRep r a (basisVector ∅)) := rfl
  change ContinuousLinearMap.opNorm (𝕜 := ℂ) (𝕜₂ := ℂ) (E := pairAlgebra r) (F := ℂ) L = _
  refine le_antisymm ?_ ?_
  · apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ) (E := pairAlgebra r) (F := ℂ)
      L (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    intro a
    rw [hL]
    exact vacuum_distance_upper r a
  · have hp := tailPrefix_tendsto (overlaps r) (fun k => (r k).2) 0
    have hlim := (Real.continuous_sqrt.continuousAt.tendsto.comp ((hp.pow 2).const_sub 1)).const_mul 2
    apply le_of_tendsto' hlim
    intro n
    obtain ⟨a, ha, htest⟩ := finite_distance_test r n
    have hb := ContinuousLinearMap.le_opNorm (𝕜 := ℂ) (𝕜₂ := ℂ) (E := pairAlgebra r) (F := ℂ) L a
    have hn := ContinuousLinearMap.opNorm_nonneg (𝕜 := ℂ) (𝕜₂ := ℂ) (E := pairAlgebra r) (F := ℂ) L
    replace hb := hb.trans (mul_le_of_le_one_right hn ha)
    rwa [hL, htest] at hb

end QubitProductStates


section SectorExamples

open Omega.QubitProduct Omega.Analysis.TailProducts

private def evenDiagonalAmbientAlgebra (r : Overlaps) :
    StarSubalgebra ℂ (Operator × Operator) :=
  (StarAlgebra.adjoin ℂ (Set.range fun a : ℕ × (Bool → ℂ) =>
    (site r (2 * a.1) (Matrix.diagonal a.2) : Operator × Operator))).topologicalClosure

/-- The incoming observables generated by the diagonal matrices at even sites. -/
def evenDiagonalAlgebra (r : Overlaps) : StarSubalgebra ℂ (pairAlgebra r) :=
  (evenDiagonalAmbientAlgebra r).comap (pairAlgebra r).subtype

private theorem evenDiagonal_expectations (r : Overlaps)
    (hr : ∀ k, overlaps r (2 * k) = 1) (a : pairAlgebra r) (ha : a ∈ evenDiagonalAlgebra r) :
    (firstProductState r).toPositiveLinearMap a = (secondProductState r).toPositiveLinearMap a := by
  have hrot : Omega.QubitProduct.rotation 1 = 1 := by
    ext i j
    cases i <;> cases j <;> norm_num [Omega.QubitProduct.rotation, Matrix.one_apply]
  let fst := StarAlgHom.fst ℂ Operator Operator
  let snd := StarAlgHom.snd ℂ Operator Operator
  have hclose : IsClosed (StarAlgHom.equalizer fst snd : Set (Operator × Operator)) :=
    isClosed_eq continuous_fst continuous_snd
  have hagree : evenDiagonalAmbientAlgebra r ≤ StarAlgHom.equalizer fst snd := by
    apply StarSubalgebra.topologicalClosure_minimal _ hclose
    apply StarAlgHom.adjoin_le_equalizer
    rintro _ ⟨⟨k, d⟩, rfl⟩
    change firstRep r (site r (2 * k) (Matrix.diagonal d)) =
      secondRep r (site r (2 * k) (Matrix.diagonal d))
    have hk : (r (2 * k) : ℝ) = 1 := hr k
    simp only [firstRep_site, secondRep_site, hk, hrot, one_mul, star_one, mul_one]
  have hae : firstRep r a = secondRep r a := hagree ha
  rw [(productFunctionals r).1, (productFunctionals r).2, vectorFunctional_apply,
    vectorFunctional_apply, hae]

private theorem product_states_ne_of_orthogonal_site (r : Overlaps) (k : ℕ)
    (hk : overlaps r k = 0) :
    (firstProductState r).toPositiveLinearMap ≠ (secondProductState r).toPositiveLinearMap := by
  intro heq
  have he := congrArg (fun f : pairAlgebra r →ₚ[ℂ] ℂ => f (site r k vacuumMatrix)) heq
  have hr : (r k : ℝ) = 0 := hk
  rw [(productFunctionals r).1, (productFunctionals r).2, vectorFunctional_apply,
    vectorFunctional_apply, firstRep_site, secondRep_site, vacuum_fixed, inner_basisVector_left,
    inner_basisVector_left, localAction_apply] at he
  simp [basisVector_apply, bit, toggle, conjugate_vacuum_diag, hr] at he

/-- A single orthogonal site makes the full product zero in equivalent sectors.
The states remain distinct and agree on the incoming diagonal algebra. -/
theorem one_orthogonal_site_equivalent :
    ∃ r : Overlaps, overlaps r 1 = 0 ∧ (∀ k, k ≠ 1 → overlaps r k = 1) ∧
      tailProduct (overlaps r) 0 = 0 ∧
      GNSEquivalent (firstProductState r).toPositiveLinearMap
        (secondProductState r).toPositiveLinearMap ∧
      (firstProductState r).toPositiveLinearMap ≠ (secondProductState r).toPositiveLinearMap ∧
      ∀ a ∈ evenDiagonalAlgebra r,
        (firstProductState r).toPositiveLinearMap a = (secondProductState r).toPositiveLinearMap a := by
  let r : Overlaps := fun k => ⟨if k = 1 then 0 else 1, by split <;> norm_num⟩
  have hr : ∀ k, overlaps r k = if k = 1 then 0 else 1 := fun _ => rfl
  have hzero : overlaps r 1 = 0 := by simp [hr]
  have hsingle : Summable (fun k => 1 - overlaps r k) := by
    have h := (hasSum_ite_eq (1 : ℕ) (1 : ℝ)).summable
    convert h using 1
    funext k
    by_cases hk : k = 1 <;> simp [hr, hk]
  refine ⟨r, hzero, fun k hk => by simp [hr, hk], ?_,
    (pure_product_gns_dichotomy r).1.mpr hsingle,
    product_states_ne_of_orthogonal_site r 1 hzero, ?_⟩
  · exact (tailProduct_zero_iff (overlaps r) (fun k => (r k).2)).mpr (Or.inl ⟨1, hzero⟩)
  · exact evenDiagonal_expectations r (fun k => by rw [hr, ite_eq_right (by omega)])

/-- Orthogonality at every odd site yields disjoint sectors with identical
restrictions to the incoming diagonal algebra. -/
theorem odd_orthogonal_sites_disjoint :
    ∃ r : Overlaps, (∀ k, overlaps r (2 * k) = 1 ∧ overlaps r (2 * k + 1) = 0) ∧
      GNSDisjoint (firstProductState r).toPositiveLinearMap
        (secondProductState r).toPositiveLinearMap ∧
      (firstProductState r).toPositiveLinearMap ≠ (secondProductState r).toPositiveLinearMap ∧
      ∀ a ∈ evenDiagonalAlgebra r,
        (firstProductState r).toPositiveLinearMap a = (secondProductState r).toPositiveLinearMap a := by
  let r : Overlaps := fun k => ⟨if k % 2 = 0 then 1 else 0, by split <;> norm_num⟩
  have hr : ∀ k, overlaps r k = if k % 2 = 0 then 1 else 0 := fun _ => rfl
  have hparity (k : ℕ) : overlaps r (2 * k) = 1 ∧ overlaps r (2 * k + 1) = 0 := by
    exact ⟨(hr _).trans (ite_eq_left (by omega)), (hr _).trans (ite_eq_right (by omega))⟩
  have hzero (k : ℕ) := (hparity k).2
  have hdiv : ¬ Summable (fun k => 1 - overlaps r k) := by
    intro h
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro i j hij
      dsimp only at hij
      omega
    have hcomp : ((fun k => 1 - overlaps r k) ∘ (fun k : ℕ => 2 * k + 1)) =
        fun _ : ℕ => (1 : ℝ) := by
      funext k
      change 1 - overlaps r (2 * k + 1) = 1
      rw [hzero k, sub_zero]
    have h₁ := hcomp ▸ h.comp_injective hinj
    have hfinite := Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) h₁
    exact @Infinite.not_finite ℕ inferInstance hfinite
  refine ⟨r, hparity, (pure_product_gns_dichotomy r).2.mpr ?_,
    product_states_ne_of_orthogonal_site r 1 (hparity 0).2,
    evenDiagonal_expectations r (fun k => (hparity k).1)⟩
  exact tailProduct_eq_zero_of_not_summable (overlaps r) (fun k => (r k).2) hdiv

end SectorExamples

end D5.S3.Quantum.Analysis.NullConeGravity.PureGNSExtensionSectors
