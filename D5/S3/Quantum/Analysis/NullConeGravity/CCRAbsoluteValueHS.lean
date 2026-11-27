/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert–Schmidt estimates for operator absolute values via compression and dilation. -/

import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.NullConeGravity.CCRConjugation
import D5.S3.Quantum.Analysis.CompactEigenbasis
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import D5.S3.Quantum.Analysis.TraceClass.LogRegularization
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology Polynomial
open Filter ContinuousLinearMap HilbertSchmidt

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRAbsoluteValueHS

open QuarterPowerSqrtHilbertSchmidt

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The positive square root of the adjoint times the operator. -/
def opAbs (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (T.adjoint.comp T)

private theorem abs_eq_cfc (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    opAbs T = cfc (abs : ℝ → ℝ) T := by
  simpa [opAbs, CFC.abs, Real.norm_eq_abs, ContinuousLinearMap.mul_def, star_eq_adjoint] using CFC.abs_eq_cfc_norm T hT

private theorem basis_range {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ∃ (e : ι ≃ Set.range b) (c : HilbertBasis (Set.range b) ℂ H), ∀ i, c (e i) = b i := by
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  let v : Set.range b → H := Subtype.val
  have hspan : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [show Set.range v = Set.range b from Subtype.range_coe, b.dense_span]
  refine ⟨e, HilbertBasis.mk b.orthonormal.toSubtypeRange hspan, fun i => ?_⟩
  rw [HilbertBasis.coe_mk]
  rfl

private theorem basis_hsSum {ι : Type*} (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    HasSum (fun i => ‖A (b i)‖ ^ 2) (hsSq A hA) := by
  obtain ⟨e, c, hc⟩ := basis_range b
  have hs := hasSum_norm_sq_apply_of_basis (S := A)
    (exists_hilbertBasis ℂ H).choose_spec.choose c
    (summable_norm_sq_apply_of_hilbertBasis _ _ hA)
  simpa only [Function.comp_def, hc, hsSq] using e.hasSum_iff.mpr hs

private theorem basis_isHS {ι : Type*} (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (h : Summable (fun i => ‖A (b i)‖ ^ 2)) : IsHilbertSchmidt A := by
  obtain ⟨e, c, hc⟩ := basis_range b
  exact ⟨_, c, e.summable_iff.mp (by simpa only [Function.comp_def, hc] using h)⟩

private theorem hsSq_basis {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {w : Set H} (b : HilbertBasis w ℂ H) : hsSq T hT = ∑' i, ‖T (b i)‖ ^ 2 :=
  (basis_hsSum b hT).tsum_eq.symm

private theorem hsSq_finite_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) :
    hsSq T hT = ∑ i, ‖T (b i)‖ ^ 2 := by
  simpa [tsum_fintype] using (basis_hsSum b.toHilbertBasis hT).tsum_eq.symm

private theorem finite_abs_sub [FiniteDimensional ℂ H] {U V : H →L[ℂ] H}
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V)
    (h : IsHilbertSchmidt (U - V)) :
    ∃ h' : IsHilbertSchmidt (opAbs U - opAbs V), hsSq _ h' ≤ hsSq _ h := by
  let u := (isSelfAdjoint_iff_isSymmetric.mp hU).eigenvectorBasis rfl
  let v := (isSelfAdjoint_iff_isSymmetric.mp hV).eigenvectorBasis rfl
  let a := (isSelfAdjoint_iff_isSymmetric.mp hU).eigenvalues rfl
  let b := (isSelfAdjoint_iff_isSymmetric.mp hV).eigenvalues rfl
  have hu i : U (u i) = (a i : ℂ) • u i :=
    (isSelfAdjoint_iff_isSymmetric.mp hU).apply_eigenvectorBasis rfl i
  have hv j : V (v j) = (b j : ℂ) • v j :=
    (isSelfAdjoint_iff_isSymmetric.mp hV).apply_eigenvectorBasis rfl j
  have hau i : opAbs U (u i) = ((|a i| : ℝ) : ℂ) • u i := by
    rw [abs_eq_cfc _ hU]
    exact QuantumLogEnergy.cfc_apply_eigenvector U hU _ _ (hu i) _ continuous_abs.continuousOn
  have hav j : opAbs V (v j) = ((|b j| : ℝ) : ℂ) • v j := by
    rw [abs_eq_cfc _ hV]
    exact QuantumLogEnergy.cfc_apply_eigenvector V hV _ _ (hv j) _ continuous_abs.continuousOn
  have coeff (A B : H →L[ℂ] H) (hA : A.adjoint = A)
      (i j : Fin (Module.finrank ℂ H)) (s t : ℝ)
      (hi : A (u i) = (s : ℂ) • u i) (hj : B (v j) = (t : ℂ) • v j) :
      ⟪u i, (A - B) (v j)⟫_ℂ = (s - t : ℂ) * ⟪u i, v j⟫_ℂ := by
    rw [sub_apply, inner_sub_right, ← adjoint_inner_left, hA, hi, hj]
    rw [inner_smul_left, inner_smul_right,
      show starRingEnd ℂ (s : ℂ) = (s : ℂ) from Complex.conj_ofReal s, sub_mul]
  refine ⟨basis_isHS v.toHilbertBasis Summable.of_finite, ?_⟩
  rw [hsSq_finite_basis v, hsSq_finite_basis v]
  apply Finset.sum_le_sum
  intro j _
  rw [← u.sum_sq_norm_inner_right, ← u.sum_sq_norm_inner_right]
  apply Finset.sum_le_sum
  intro i _
  rw [coeff _ _ (show (opAbs U).adjoint = opAbs U from
      (CFC.sqrt_nonneg _).isSelfAdjoint) i j _ _ (hau i) (hav j),
    coeff U V hU i j _ _ (hu i) (hv j), norm_mul, norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real]
  exact abs_abs_sub_abs_le_abs_sub _ _

omit [CompleteSpace H] in
private theorem strong_apply {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H}
    {S : H →L[ℂ] H} {M : ℝ} (hM : ∀ i, ‖T i‖ ≤ M)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x)))
    {y : ι → H} {x : H} (hy : Tendsto y l (𝓝 x)) :
    Tendsto (fun i => T i (y i)) l (𝓝 (S x)) := by
  have h₀ := tendsto_iff_norm_sub_tendsto_zero.mp hy
  have hv : Tendsto (fun i => T i (y i - x)) l (𝓝 0) :=
    squeeze_zero_norm (fun i => ((T i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))) (by simpa using h₀.const_mul M)
  simpa only [map_sub, sub_add_cancel, zero_add] using hv.add (hT x)

private theorem strong_abs {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H}
    {S : H →L[ℂ] H} {M : ℝ} (hM : ∀ i, ‖T i‖ ≤ M) (hSM : ‖S‖ ≤ M)
    (hsa : ∀ i, IsSelfAdjoint (T i)) (hS : IsSelfAdjoint S)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => opAbs (T i) x) l (𝓝 (opAbs S x)) := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    have h₀ : ∀ i, opAbs (T i) x = opAbs S x := fun _ => Subsingleton.elim _ _
    simpa only [h₀] using (tendsto_const_nhds (x := opAbs S x) (f := l))
  | inr h =>
    have hpow (n : ℕ) : Tendsto (fun i => (T i ^ n) x) l (𝓝 ((S ^ n) x)) := by
      induction n with
      | zero => simp [tendsto_const_nhds]
      | succ n ih =>
        simpa only [pow_succ', mul_apply_eq_comp] using strong_apply hM hT ih
    have hpoly (q : ℝ[X]) :
        Tendsto (fun i => (Polynomial.aeval (T i) q) x) l (𝓝 ((Polynomial.aeval S q) x)) := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simpa only [map_add, add_apply] using hp.add hq
      | monomial n a =>
        simpa only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, smul_apply] using (hpow n).const_smul a
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ := ε / (4 * (‖x‖ + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨q, hq⟩ :=
      exists_polynomial_near_of_continuousOn (-M) M abs continuous_abs.continuousOn δ hδ
    have happrox (A : H →L[ℂ] H) (ha : IsSelfAdjoint A) (hn : ‖A‖ ≤ M) :
        ‖Polynomial.aeval A q - opAbs A‖ ≤ δ := by
      rw [abs_eq_cfc A ha, ← cfc_polynomial q A ha, ← cfc_sub q.eval abs A]
      apply norm_cfc_le hδ.le
      intro t ht
      have htM : |t| ≤ M := by
        simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem ht).trans hn
      exact (hq t (abs_le.mp htM)).le
    have hb (A : H →L[ℂ] H) (ha : IsSelfAdjoint A) (hn : ‖A‖ ≤ M) :
        dist ((Polynomial.aeval A q) x) (opAbs A x) ≤ ε / 4 := by
      rw [dist_eq_norm, ← sub_apply]
      refine ((Polynomial.aeval A q - opAbs A).le_opNorm x).trans
        ((mul_le_mul_of_nonneg_right (happrox A ha hn) (norm_nonneg _)).trans ?_)
      calc
        δ * ‖x‖ ≤ δ * (‖x‖ + 1) := by gcongr; linarith
        _ = ε / 4 := by dsimp [δ]; field_simp
    filter_upwards [Metric.tendsto_nhds.mp (hpoly q) (ε / 2) (by positivity)] with i hi
    have h₁ := dist_triangle (opAbs (T i) x) ((Polynomial.aeval (T i) q) x) (opAbs S x)
    have h₂ := dist_triangle ((Polynomial.aeval (T i) q) x) ((Polynomial.aeval S q) x) (opAbs S x)
    have h₃ := hb (T i) (hsa i) (hM i)
    have h₄ := hb S hS hSM
    rw [dist_comm] at h₃
    linarith

omit [CompleteSpace H] in
private theorem projection_tendsto {w : Set H} (b : HilbertBasis w ℂ H) (x : H) :
    Tendsto (fun F : Finset w => (TraceClassCompression.finiteSpan b F).starProjection x)
      atTop (𝓝 x) := by
  let y (F : Finset w) := ∑ i ∈ F, b.repr x i • b i
  have hy : Tendsto y atTop (𝓝 x) := b.hasSum_repr x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_iff_norm_sub_tendsto_zero.mp hy)
  intro F
  let U := TraceClassCompression.finiteSpan b F
  have hm : y F ∈ U := Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, hi, rfl⟩)
  rw [norm_sub_rev, ← dist_eq_norm, U.dist_starProjection_eq_infDist, ← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem hm

set_option maxHeartbeats 800000 in
private theorem abs_compression (E : Submodule ℂ H) [CompleteSpace E]
    (A : H →L[ℂ] H) :
    opAbs (E.starProjection * A * E.starProjection) =
      adjointCongr E.subtypeL.adjoint (opAbs (adjointCongr E.subtypeL A)) := by
  let i := E.subtypeL
  have hi (x : E) : i.adjoint (i x) = x := by
    change E.subtypeL.adjoint (E.subtypeL x) = x
    rw [E.adjoint_subtypeL]
    exact E.orthogonalProjectionOnto_mem_subspace_eq_self x
  have hp : E.starProjection = i ∘L i.adjoint := by
    change E.starProjection = E.subtypeL ∘L E.subtypeL.adjoint
    rw [E.adjoint_subtypeL]
    rfl
  let B := adjointCongr i A
  let S := opAbs B
  have hS : S * S = B.adjoint * B :=
    CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg B)
  change CFC.sqrt _ = adjointCongr i.adjoint S
  have hpos : 0 ≤ adjointCongr i.adjoint S :=
    nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp (CFC.sqrt_nonneg
      (B.adjoint.comp B))).adjoint_conj i.adjoint)
  apply CFC.sqrt_unique _ hpos
  have hcomp : E.starProjection * A * E.starProjection = i ∘L B ∘L i.adjoint := by
    rw [hp]
    rfl
  rw [hcomp]
  simp only [adjointCongr, adjoint_adjoint, adjoint_comp]
  ext x
  simp only [mul_apply_eq_comp, comp_apply, hi]
  exact congrArg i (DFunLike.congr_fun hS (i.adjoint x))

private theorem hs_congruence {T : H →L[ℂ] H} (h : IsHilbertSchmidt T)
    (C : K →L[ℂ] H) (hC : ‖C‖ ≤ 1) :
    ∃ h' : IsHilbertSchmidt (adjointCongr C T), hsSq _ h' ≤ hsSq _ h := by
  obtain ⟨h', h'le⟩ := adjointCongr_hsSq_le C h
  refine ⟨h', h'le.trans ?_⟩
  have hn : 0 ≤ hsSq T h := tsum_nonneg fun _ => sq_nonneg _
  simpa using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg C) hC 4) hn

private theorem congruence_sub (C : K →L[ℂ] H) (A B : H →L[ℂ] H) :
    adjointCongr C (A - B) = adjointCongr C A - adjointCongr C B := by
  ext x
  simp [adjointCongr]

private theorem congruence_selfAdjoint (C : K →L[ℂ] H)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) : IsSelfAdjoint (adjointCongr C A) := by
  change (adjointCongr C A).adjoint = adjointCongr C A
  simp [adjointCongr, adjoint_comp, hA.adjoint_eq, comp_assoc]

/-- Absolute value is contractive in Hilbert–Schmidt norm on bounded self-adjoint operators. -/
theorem opAbs_sub_selfAdjoint {U V : H →L[ℂ] H} (hU : IsSelfAdjoint U)
    (hV : IsSelfAdjoint V) (h : IsHilbertSchmidt (U - V)) :
    ∃ h' : IsHilbertSchmidt (opAbs U - opAbs V), hsSq _ h' ≤ hsSq _ h := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let E := TraceClassCompression.finiteSpan b
  let P (F : Finset w) := (E F).starProjection
  let A (F : Finset w) (S : H →L[ℂ] H) := P F * S * P F
  let d (F : Finset w) := opAbs (A F U) - opAbs (A F V)
  let D := opAbs U - opAbs V
  have hbound (F : Finset w) : ∃ hd : IsHilbertSchmidt (d F), hsSq _ hd ≤ hsSq _ h := by
    let i := (E F).subtypeL
    have hi : ‖i‖ ≤ 1 := (E F).norm_subtypeL_le
    obtain ⟨hF, hFle⟩ := hs_congruence h i hi
    rw [congruence_sub] at hF
    obtain ⟨hd, hdle⟩ :=
      finite_abs_sub (congruence_selfAdjoint i U hU) (congruence_selfAdjoint i V hV) hF
    obtain ⟨ho, hole⟩ := hs_congruence hd i.adjoint (by simpa using hi)
    have he : d F = adjointCongr i.adjoint
        (opAbs (adjointCongr i U) - opAbs (adjointCongr i V)) := by
      change opAbs ((E F).starProjection * U * (E F).starProjection) -
        opAbs ((E F).starProjection * V * (E F).starProjection) = _
      rw [abs_compression, abs_compression, congruence_sub]
    simp only [he]
    exact ⟨ho, hole.trans (hdle.trans (by simpa only [congruence_sub] using hFle))⟩
  have hs (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (x : H) :
      Tendsto (fun F => opAbs (A F S) x) atTop (𝓝 (opAbs S x)) := by
    apply strong_abs (M := ‖S‖) _ le_rfl _ hS _ x
    · intro F
      have hp : ‖P F‖ ≤ 1 := (E F).starProjection_norm_le
      calc
        ‖A F S‖ ≤ ‖P F‖ * ‖S‖ * ‖P F‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ ‖S‖ * 1 := by
          gcongr
          simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg S)
        _ = ‖S‖ := mul_one _
    · intro F
      have hp : (P F).adjoint = P F := isSelfAdjoint_starProjection (E F)
      change (P F * S * P F).adjoint = P F * S * P F
      simp [← star_eq_adjoint, star_mul, show star (P F) = P F from hp, hS.star_eq, mul_assoc]
    · intro y
      exact strong_apply (fun F => (E F).starProjection_norm_le)
        (T := P) (S := (1 : H →L[ℂ] H)) (projection_tendsto b)
        (S.continuous.continuousAt.tendsto.comp (projection_tendsto b y))
  have hlim (x : H) : Tendsto (fun F => d F x) atTop (𝓝 (D x)) := (hs U hU x).sub (hs V hV x)
  have hfinite (F : Finset w) : ∑ i ∈ F, ‖D (b i)‖ ^ 2 ≤ hsSq _ h := by
    apply le_of_tendsto' (tendsto_finsetSum (s := F) fun i _ => (hlim (b i)).norm.pow 2)
    intro G
    obtain ⟨hd, hdle⟩ := hbound G
    rw [hsSq_basis hd b] at hdle
    exact ((summable_norm_sq_apply_of_hilbertBasis w b hd).sum_le_tsum F
      (fun _ _ => sq_nonneg _)).trans hdle
  have hD : IsHilbertSchmidt D := ⟨w, b, summable_of_sum_le (fun _ => sq_nonneg _) hfinite⟩
  exact ⟨hD, (hsSq_basis hD b).trans_le (Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite)⟩

private abbrev Double (H : Type*) := WithLp 2 (H × H)

private def doubleEquiv : Double H ≃L[ℂ] H × H :=
  WithLp.prodContinuousLinearEquiv 2 ℂ H H

private def blockDiag (A B : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  doubleEquiv.symm.toContinuousLinearMap ∘L
    ((A ∘L fst ℂ H H).prod (B ∘L snd ℂ H H)) ∘L doubleEquiv.toContinuousLinearMap

/-- The self-adjoint dilation of an operator to the sum of two copies of its Hilbert space. -/
def dilation (Y : H →L[ℂ] H) : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
  doubleEquiv.symm.toContinuousLinearMap ∘L
    ((Y.adjoint ∘L snd ℂ H H).prod (Y ∘L fst ℂ H H)) ∘L doubleEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
private theorem blockDiag_apply (A B : H →L[ℂ] H) (x : Double H) :
    blockDiag A B x = WithLp.toLp 2 (A x.fst, B x.snd) := rfl

private theorem dilation_apply (Y : H →L[ℂ] H) (x : Double H) :
    dilation Y x = WithLp.toLp 2 (Y.adjoint x.snd, Y x.fst) := rfl

/-- Swapping the two coordinates after applying the operator and its adjoint gives a
self-adjoint operator. -/
theorem dilation_isSelfAdjoint (Y : H →L[ℂ] H) : IsSelfAdjoint (dilation Y) := by
  change (dilation Y).adjoint = dilation Y
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [dilation_apply, WithLp.prod_inner_apply]
  simp only [adjoint_inner_left, adjoint_inner_right]
  exact add_comm _ _

/-- The absolute value of the self-adjoint dilation has the two operator absolute values
on its diagonal. -/
theorem opAbs_dilation_apply (Y : H →L[ℂ] H) (x : WithLp 2 (H × H)) :
    opAbs (dilation Y) x = WithLp.toLp 2 (opAbs Y x.fst, opAbs Y.adjoint x.snd) := by
  change opAbs (dilation Y) x = blockDiag (opAbs Y) (opAbs Y.adjoint) x
  suffices opAbs (dilation Y) = blockDiag (opAbs Y) (opAbs Y.adjoint) by rw [this]
  have half_pos (T : H →L[ℂ] H) : 0 ≤ opAbs T := CFC.sqrt_nonneg _
  have half_sq (T : H →L[ℂ] H) : opAbs T * opAbs T = T.adjoint * T :=
    CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)
  have hA := nonneg_iff_isPositive.mp (half_pos Y)
  have hB := nonneg_iff_isPositive.mp (half_pos Y.adjoint)
  unfold opAbs
  change CFC.sqrt ((dilation Y).adjoint * dilation Y) =
    blockDiag (opAbs Y) (opAbs Y.adjoint)
  rw [show (dilation Y).adjoint = dilation Y from dilation_isSelfAdjoint Y]
  apply CFC.sqrt_unique
  · ext x
    simp only [mul_apply_eq_comp, blockDiag_apply, dilation_apply, WithLp.toLp_fst,
      WithLp.toLp_snd]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, half_sq, half_sq, adjoint_adjoint]
    rfl
  · apply nonneg_iff_isPositive.mpr
    refine isPositive_def'.mpr ⟨?_, ?_⟩
    · change (blockDiag (opAbs Y) (opAbs Y.adjoint)).adjoint = _
      ext y
      apply ext_inner_left ℂ
      intro x
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp only [blockDiag_apply, WithLp.prod_inner_apply]
      rw [← adjoint_inner_left (opAbs Y), ← adjoint_inner_left (opAbs Y.adjoint)]
      rw [show (opAbs Y).adjoint = opAbs Y from hA.isSelfAdjoint,
          show (opAbs Y.adjoint).adjoint = opAbs Y.adjoint from hB.isSelfAdjoint]
      rfl
    · intro x
      change 0 ≤ (⟪blockDiag (opAbs Y) (opAbs Y.adjoint) x, x⟫_ℂ).re
      simp only [blockDiag_apply, WithLp.prod_inner_apply, Complex.add_re]
      exact add_nonneg (hA.re_inner_nonneg_left _) (hB.re_inner_nonneg_left _)

private def doubleVector {ι : Type*} (b : HilbertBasis ι ℂ H) : ι ⊕ ι → Double H :=
  Sum.elim (fun i => WithLp.toLp 2 (b i, 0)) (fun i => WithLp.toLp 2 (0, b i))

private def doubleBasis {ι : Type*} (b : HilbertBasis ι ℂ H) : HilbertBasis (ι ⊕ ι) ℂ (Double H) := by
  classical
  apply HilbertBasis.mkOfOrthogonalEqBot (v := doubleVector b)
  · rw [orthonormal_iff_ite]
    intro i j
    cases i <;> cases j <;>
      simp [doubleVector, WithLp.prod_inner_apply, orthonormal_iff_ite.mp b.orthonormal]
  · rw [eq_bot_iff]
    intro x hx
    have h (i : ι ⊕ ι) := (Submodule.mem_orthogonal _ _).mp hx (doubleVector b i)
      (Submodule.subset_span (Set.mem_range_self _))
    have hzero (v : H) (hv : ∀ i, ⟪b i, v⟫_ℂ = 0) : v = 0 := by
      apply b.repr.injective
      ext i
      simp [b.repr_apply_apply, hv]
    have hf : x.fst = 0 := hzero _ fun i => by
      simpa [doubleVector, WithLp.prod_inner_apply] using h (.inl i)
    have hs : x.snd = 0 := hzero _ fun i => by
      simpa [doubleVector, WithLp.prod_inner_apply] using h (.inr i)
    rw [Submodule.mem_bot]
    apply (WithLp.equiv 2 (H × H)).injective
    exact Prod.ext hf hs

private theorem doubleBasis_apply {ι : Type*} (b : HilbertBasis ι ℂ H) (i : ι ⊕ ι) :
    doubleBasis b i = doubleVector b i := by
  unfold doubleBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]


private theorem block_hs {A B : H →L[ℂ] H} (T : Double H →L[ℂ] Double H)
    (hb₁ : ∀ x : H, ‖T (WithLp.toLp 2 (x, 0))‖ = ‖A x‖)
    (hb₂ : ∀ x : H, ‖T (WithLp.toLp 2 (0, x))‖ = ‖B x‖) :
    (IsHilbertSchmidt T ↔ IsHilbertSchmidt A ∧ IsHilbertSchmidt B) ∧
      ∀ (hT : IsHilbertSchmidt T) (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B),
        hsSq T hT = hsSq A hA + hsSq B hB := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let f (i : w ⊕ w) := ‖T (doubleBasis b i)‖ ^ 2
  have hleft : f ∘ Sum.inl = fun i => ‖A (b i)‖ ^ 2 := by
    funext i
    simp [f, doubleBasis_apply, doubleVector, hb₁]
  have hright : f ∘ Sum.inr = fun i => ‖B (b i)‖ ^ 2 := by
    funext i
    simp [f, doubleBasis_apply, doubleVector, hb₂]
  constructor
  · constructor
    · intro hT
      have hs : Summable f := (basis_hsSum (doubleBasis b) hT).summable
      exact ⟨⟨w, b, hleft ▸ hs.comp_injective Sum.inl_injective⟩,
        ⟨w, b, hright ▸ hs.comp_injective Sum.inr_injective⟩⟩
    · rintro ⟨hA, hB⟩
      apply basis_isHS (doubleBasis b)
      exact Summable.sum f (hleft ▸ (basis_hsSum b hA).summable)
        (hright ▸ (basis_hsSum b hB).summable)
  · intro hT hA hB
    have hsum₁ : HasSum (f ∘ Sum.inl) (hsSq A hA) := hleft ▸ basis_hsSum b hA
    have hsum₂ : HasSum (f ∘ Sum.inr) (hsSq B hB) := hright ▸ basis_hsSum b hB
    exact (basis_hsSum (doubleBasis b) hT).unique (hsum₁.sum hsum₂)

private theorem adjoint_hsSq {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hA' : IsHilbertSchmidt A.adjoint) : hsSq A.adjoint hA' = hsSq A hA := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [← (basis_hsSum b hA).tsum_eq]
  exact (basis_hsSum b hA').unique
    (hasSum_norm_sq_apply_eq_adjoint b b (basis_hsSum b hA).summable)

/-- The joint squared Hilbert–Schmidt change of both absolute values is bounded by
twice the squared change of the original operator. -/
theorem opAbs_sub_symmetric {Y₂ Y₁ : H →L[ℂ] H} (h : IsHilbertSchmidt (Y₂ - Y₁)) :
    ∃ (h₁ : IsHilbertSchmidt (opAbs Y₂ - opAbs Y₁))
      (h₂ : IsHilbertSchmidt (opAbs Y₂.adjoint - opAbs Y₁.adjoint)),
      hsSq _ h₁ + hsSq _ h₂ ≤ 2 * hsSq _ h := by
  have hadj : IsHilbertSchmidt (Y₂ - Y₁).adjoint := isHilbertSchmidt_star h
  have hsub : (Y₂ - Y₁).adjoint = Y₂.adjoint - Y₁.adjoint := star_sub _ _
  have hinput := block_hs (A := Y₂ - Y₁) (B := (Y₂ - Y₁).adjoint) (dilation Y₂ - dilation Y₁)
    (fun x => by
      rw [sub_apply, dilation_apply, dilation_apply]
      simp [← WithLp.toLp_sub, WithLp.norm_toLp_snd])
    (fun x => by
      rw [sub_apply, dilation_apply, dilation_apply]
      simp [← WithLp.toLp_sub, WithLp.norm_toLp_fst, hsub])
  have hDil := hinput.1.mpr ⟨h, hadj⟩
  obtain ⟨hAbs, hAbsBound⟩ :=
    opAbs_sub_selfAdjoint (dilation_isSelfAdjoint Y₂) (dilation_isSelfAdjoint Y₁) hDil
  have houtput := block_hs (A := opAbs Y₂ - opAbs Y₁)
    (B := opAbs Y₂.adjoint - opAbs Y₁.adjoint) (opAbs (dilation Y₂) - opAbs (dilation Y₁))
    (fun x => by
      rw [sub_apply, opAbs_dilation_apply, opAbs_dilation_apply]
      simp [← WithLp.toLp_sub, WithLp.norm_toLp_fst])
    (fun x => by
      rw [sub_apply, opAbs_dilation_apply, opAbs_dilation_apply]
      simp [← WithLp.toLp_sub, WithLp.norm_toLp_snd])
  obtain ⟨h₁, h₂⟩ := houtput.1.mp hAbs
  refine ⟨h₁, h₂, ?_⟩
  rwa [houtput.2 hAbs h₁ h₂, hinput.2 hDil h hadj, adjoint_hsSq h hadj, ← two_mul] at hAbsBound

/-- The squared Hilbert–Schmidt change of the absolute value is bounded by twice the
squared change of the original operator. -/
theorem opAbs_sub {Y₂ Y₁ : H →L[ℂ] H} (h : IsHilbertSchmidt (Y₂ - Y₁)) :
    ∃ h' : IsHilbertSchmidt (opAbs Y₂ - opAbs Y₁), hsSq _ h' ≤ 2 * hsSq _ h := by
  obtain ⟨h₁, h₂, hsum⟩ := opAbs_sub_symmetric h
  have h₂nonneg : 0 ≤ hsSq _ h₂ := tsum_nonneg fun _ => sq_nonneg _
  exact ⟨h₁, (le_add_of_nonneg_right h₂nonneg).trans hsum⟩

/-- On the one-dimensional complex Hilbert space, the pair of zero and identity operators
attains equality in the joint estimate, with nonzero input square sum. -/
theorem opAbs_sub_symmetric_sharp :
    ∃ (h : IsHilbertSchmidt ((1 : ℂ →L[ℂ] ℂ) - 0))
      (h₁ : IsHilbertSchmidt (opAbs (1 : ℂ →L[ℂ] ℂ) - opAbs 0))
      (h₂ : IsHilbertSchmidt (opAbs (1 : ℂ →L[ℂ] ℂ).adjoint -
        opAbs (0 : ℂ →L[ℂ] ℂ).adjoint)),
      hsSq _ h = 1 ∧ hsSq _ h₁ + hsSq _ h₂ = 2 := by
  let b := (OrthonormalBasis.singleton Unit ℂ).toHilbertBasis
  have hI : IsHilbertSchmidt (1 : ℂ →L[ℂ] ℂ) :=
    basis_isHS b Summable.of_finite
  have hsq : hsSq _ hI = 1 := by
    rw [← (basis_hsSum b hI).tsum_eq]
    simp [b]
  have hz : opAbs (0 : ℂ →L[ℂ] ℂ) = 0 := by simp [opAbs]
  have ho : opAbs (1 : ℂ →L[ℂ] ℂ) = 1 := by
    change CFC.sqrt (star (1 : ℂ →L[ℂ] ℂ) * 1) = 1
    simp
  have ha₀ : (0 : ℂ →L[ℂ] ℂ).adjoint = 0 := star_zero _
  simpa only [sub_zero, hz, ho, ha₀, adjoint_one] using
    (show ∃ (h h₁ h₂ : IsHilbertSchmidt (1 : ℂ →L[ℂ] ℂ)),
        hsSq _ h = 1 ∧ hsSq _ h₁ + hsSq _ h₂ = 2 from
      ⟨hI, hI, hI, hsq, by rw [hsq]; norm_num⟩)

end D5.S3.Quantum.Analysis.NullConeGravity.CCRAbsoluteValueHS
