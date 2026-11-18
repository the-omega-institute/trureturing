/- GID: D5/S3/Quantum/Divergence/UmegakiConditionalBKM
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiConditionalBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arithmetic inverse residual identity for arbitrary quantum marginals. -/

import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Divergence.UmegakiBKMPath
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry

/-! Subtracting the marginal quadratic form is exactly the quadratic form
of a zero-partial-trace residual. The reference is an arbitrary quantum
matrix factor, with no block-diagonal restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
open D5.S3.Quantum.Divergence.UmegakiKernelContraction
open HilbertSchmidtOperatorSpace
open D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
open D5.S3.Quantum.Divergence.UmegakiBKMPath
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Divergence.LogDerivTrace

namespace D5.S3.Quantum.Divergence.UmegakiConditionalBKM
universe u
variable {R a : Type u} [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a]

private lemma partialTraceRight_arithmetic_embed
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) (u : ℝ) :
    partialTraceRight (arithmetic Z (X ⊗ₖ (1 : Matrix a a ℂ)) u) =
      arithmetic (partialTraceRight Z) X u := by
  ext r s
  simp only [arithmetic, partialTraceRight_add,
    D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul,
    partialTraceRight_mul_embed, partialTraceRight_embed_mul]

/-- The same marginal inverse determines the residual for every correlated
joint matrix and arbitrary complex tangent. -/
def residual (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ) : Matrix (R × a) (R × a) ℂ :=
  H - arithmetic Z ((inverseMatrix (partialTraceRight Z) (partialTraceRight H) u) ⊗ₖ
    (1 : Matrix a a ℂ)) u

lemma residual_partialTrace [Nonempty a]
    (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    partialTraceRight (residual Z H u) = 0 := by
  have hs := partialTraceRight_posDef Z hZ
  have h := arithmetic_inverseMatrix (partialTraceRight Z) (partialTraceRight H) u hs hu
  have hsub (V W : Matrix (R × a) (R × a) ℂ) :
      partialTraceRight (V-W) = partialTraceRight V - partialTraceRight W := by
    ext r s
    simp [partialTraceRight, Finset.sum_sub_distrib]
  rw [residual, hsub, partialTraceRight_arithmetic_embed, h, sub_self]

/-- The joint-minus-marginal form is a single native inverse quadratic form
on the actual zero-partial-trace residual. -/
theorem quadratic_difference_eq_residual [Nonempty a]
    (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q Z H u - q (partialTraceRight Z) (partialTraceRight H) u =
      q Z (residual Z H u) u := by
  let S := partialTraceRight Z
  let J := partialTraceRight H
  let X := inverseMatrix S J u
  let W := X ⊗ₖ (1 : Matrix a a ℂ)
  have hs : S.PosDef := partialTraceRight_posDef Z hZ
  have hreal (A B : Matrix R R ℂ) :
      (Aᴴ * B).trace.re = (Bᴴ * A).trace.re := by
    have h := congrArg Complex.re (Matrix.trace_conjTranspose (Aᴴ * B))
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      map_star, Complex.star_def, Complex.conj_re] using h.symm
  have hpair : (Wᴴ * H).trace.re = q S J u := by
    rw [show W = X ⊗ₖ (1 : Matrix a a ℂ) from rfl, trace_embed_pair, hreal]
    exact (q_eq_trace S J u).symm
  have he : energy Z W u = q S J u := by
    rw [energy, show W = X ⊗ₖ (1 : Matrix a a ℂ) from rfl, trace_embed_pair,
      partialTraceRight_arithmetic_embed]
    exact (q_eq_energy_inverse S J u hs hu).symm
  have h := q_sub_arithmetic Z H W u hZ hu
  change q Z (residual Z H u) u = _ at h
  rw [hpair, he] at h
  linarith

variable {b : Type u} [Fintype b] [DecidableEq b]

private lemma amp_residual (N : QuantumChannel a b)
    (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ) :
    amp N (residual Z H u) = residual (amp N Z) (amp N H) u := by
  have hadd (A B : Matrix (R × a) (R × a) ℂ) :
      amp N (A+B) = amp N A + amp N B := by
    simpa only [neg_smul, one_smul, sub_neg_eq_add] using amp_sub_smul N (-1) A B
  have hp (A : Matrix (R × a) (R × a) ℂ) :
      partialTraceRight (amp N A) = partialTraceRight A := ptr_amp N A
  have hsub (A B : Matrix (R × a) (R × a) ℂ) :
      amp N (A-B) = amp N A - amp N B := by
    simpa only [one_smul] using amp_sub_smul N 1 A B
  simp only [residual, hsub, hp, arithmetic, hadd, amp_smul, amp_mul_embed, amp_embed_mul]

section ArithmeticIntegrability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma arithmetic_inverse_pairing_intervalIntegrable (Z H : Matrix ι ι ℂ)
    (hZ : Z.PosDef) :
    IntervalIntegrable (fun u : ℝ =>
      (inner ℂ (matrixHS H) ((hsArithmeticMap Z u).inverse (matrixHS H))).re)
      volume 0 1 := by
  let U : Matrix ι ι ℂ := hZ.isHermitian.eigenvectorUnitary
  let W := Uᴴ * H * U
  let f := fun (i j : ι) (u : ℝ) => Complex.normSq (W i j) *
    ((1-u) * hZ.isHermitian.eigenvalues i + u * hZ.isHermitian.eigenvalues j)⁻¹
  have hi (i j : ι) : IntervalIntegrable (f i j) volume 0 1 :=
    (affineKernel_integrable _ _ (hZ.eigenvalues_pos i)
      (hZ.eigenvalues_pos j)).const_mul _
  have hs : IntervalIntegrable (∑ i, ∑ j, f i j) volume 0 1 :=
    IntervalIntegrable.sum Finset.univ (fun i _ =>
      IntervalIntegrable.sum Finset.univ (fun j _ => hi i j))
  apply hs.congr
  intro u hu
  have hm : matrixHS H = ofOp ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H) := rfl
  simp only [hm, Finset.sum_apply, f, W, U]
  exact (hs_pair_spectral Z H hZ u (Set.Ioc_subset_Icc_self
      (by simpa only [Set.uIoc_of_le zero_le_one] using hu))).symm

end ArithmeticIntegrability

private lemma bkm_difference_contraction [Nonempty a] [Nonempty b]
    (N : QuantumChannel a b) (c : ℝ) (hN : (act N 1).PosDef)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound N c)
    (Z H : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) :
    ((amp N H)ᴴ * logDeriv (amp N Z) (amp N H)).trace.re -
      ((partialTraceRight (amp N H))ᴴ *
        logDeriv (partialTraceRight (amp N Z)) (partialTraceRight (amp N H))).trace.re ≤
    c * ((Hᴴ * logDeriv Z H).trace.re -
      ((partialTraceRight H)ᴴ * logDeriv (partialTraceRight Z) (partialTraceRight H)).trace.re) := by
  have hT := amp_posDef N hN Z hZ
  have hS := partialTraceRight_posDef Z hZ
  have hST := partialTraceRight_posDef (amp N Z) hT
  have hq {ι : Type u} [Fintype ι] [DecidableEq ι]
      (A B : Matrix ι ι ℂ) (hA : A.PosDef) :
      (Bᴴ * logDeriv A B).trace.re = ∫ u in (0 : ℝ)..1, q A B u :=
    arithmetic_inverse_pairing_eq_logDeriv A B hA
  rw [hq (amp N Z) (amp N H) hT,
    hq (partialTraceRight (amp N Z)) (partialTraceRight (amp N H)) hST,
    hq Z H hZ, hq (partialTraceRight Z) (partialTraceRight H) hS]
  have hi {ι : Type u} [Fintype ι] [DecidableEq ι]
      (A B : Matrix ι ι ℂ) (hA : A.PosDef) :
      IntervalIntegrable (q A B) volume 0 1 :=
    arithmetic_inverse_pairing_intervalIntegrable A B hA
  have hiJM := hi (partialTraceRight Z) (partialTraceRight H) hS
  have hiTM := hi (partialTraceRight (amp N Z)) (partialTraceRight (amp N H)) hST
  have hiJ := hi Z H hZ
  have hiT := hi (amp N Z) (amp N H) hT
  rw [← intervalIntegral.integral_sub hiT hiTM,
    ← intervalIntegral.integral_sub hiJ hiJM, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one (hiT.sub hiTM) ((hiJ.sub hiJM).const_mul c)
  intro u hu
  change q (amp N Z) (amp N H) u - _ ≤ c * (q Z H u - _)
  rw [quadratic_difference_eq_residual _ _ u hT hu,
    quadratic_difference_eq_residual Z H u hZ hu, ← amp_residual]
  exact kernel_contraction N c hN hc hEnd Z (residual Z H u) u hZ
    (residual_partialTrace Z H u hZ hu) hu

section Path
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma logDeriv_reindex (e : ι ≃ κ) (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    logDeriv (Z.reindex e e) (H.reindex e e) = (logDeriv Z H).reindex e e := by
  let F := (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.toContinuousLinearMap
  let f : ℝ → Matrix ι ι ℂ := fun t => (Z + t • 1)⁻¹ * H * (Z + t • 1)⁻¹
  have hf : Integrable f (volume.restrict (Set.Ioi 0)) := logDeriv_integrable Z H hZ
  change _ = F (∫ t in Set.Ioi (0 : ℝ), f t)
  rw [← F.integral_comp_comm hf]
  apply integral_congr_ae
  filter_upwards with t
  change (Z.reindex e e + t • 1)⁻¹ * H.reindex e e * (Z.reindex e e + t • 1)⁻¹ =
    (f t).reindex e e
  have hZt : (Z + t • 1).reindex e e = Z.reindex e e + t • 1 := by
    let E := Matrix.reindexAlgEquiv ℝ ℂ e
    change E (Z + t • 1) = E Z + t • 1
    rw [map_add, map_smul, map_one]
  rw [← hZt, Matrix.inv_reindex]
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  change E ((Z + t • 1)⁻¹) * E H * E ((Z + t • 1)⁻¹) = E (f t)
  simp only [f, map_mul]

private def pathIntegrand (A B : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  (1-t) * (((A-B)ᴴ * logDeriv (B + t • (A-B)) (A-B)).trace.re)

private lemma affine_posDef (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (B + t • (A-B)).PosDef := by
  have he : B + t • (A-B) = t • A + (1-t) • B := by module
  rw [he]
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, zero_smul, sub_zero, one_smul, zero_add]
    exact hB
  · exact (hA.smul h).add_posSemidef (hB.posSemidef.smul (sub_nonneg.mpr ht.2))

private lemma path_integrand_reindex (e : ι ≃ κ)
    (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (A.reindex e e) (B.reindex e e) t = pathIntegrand A B t := by
  have hZ := affine_posDef A B hA hB t ht
  unfold pathIntegrand
  let E := Matrix.reindexAlgEquiv ℝ ℂ e
  change (1-t) * (((E A - E B)ᴴ * logDeriv (E B + t • (E A - E B)) (E A - E B)).trace.re)
    = _
  rw [← map_sub, ← map_smul, ← map_add]
  change (1-t) * ((((A-B).reindex e e)ᴴ *
    logDeriv ((B + t • (A-B)).reindex e e) ((A-B).reindex e e)).trace.re) = _
  rw [logDeriv_reindex e _ _ hZ, Matrix.conjTranspose_reindex]
  change (1-t) * ((E (A-B)ᴴ * E (logDeriv (B + t • (A-B)) (A-B))).trace.re) = _
  rw [← map_mul]
  exact congrArg (fun w : ℂ => (1-t) * w.re) (trace_reindex e _)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma matrix_path (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    IntervalIntegrable (pathIntegrand A B) volume 0 1 ∧
    (A * (CFC.log A - CFC.log B)).trace.re - (A-B).trace.re =
      ∫ t in (0 : ℝ)..1, pathIntegrand A B t := by
  let e := Fintype.equivFin ι
  let Af := A.reindex e e
  let Bf := B.reindex e e
  have hAf : Af.PosDef := hA.submatrix e.symm.injective
  have hBf : Bf.PosDef := hB.submatrix e.symm.injective
  have hHerm := hAf.isHermitian.sub hBf.isHermitian
  have hI (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      pathIntegrand Af Bf t = pathIntegrand A B t :=
    path_integrand_reindex e A B hA hB t (by simpa only [Set.uIcc_of_le zero_le_one] using ht)
  constructor
  · have hi : IntervalIntegrable (pathIntegrand Af Bf) volume 0 1 := by
      change IntervalIntegrable (fun t => (1-t) *
        (((Af-Bf)ᴴ * logDeriv (Bf + t • (Af-Bf)) (Af-Bf)).trace.re)) volume 0 1
      simp only [hHerm.eq]
      exact weighted_bkm_integrable Af Bf hAf hBf
    exact IntervalIntegrable.congr (fun t ht => hI t (Set.uIoc_subset_uIcc ht)) hi
  · have h := relativeEntropy_eq_integral_bkm Af Bf hAf hBf
    rw [show (∫ t in (0 : ℝ)..1,
        (1-t) * ((Af-Bf) * logDeriv (Bf + t • (Af-Bf)) (Af-Bf)).trace.re) =
        ∫ t in (0 : ℝ)..1, pathIntegrand A B t by
      apply intervalIntegral.integral_congr
      intro t ht
      simpa only [pathIntegrand, hHerm.eq] using hI t ht] at h
    rw [show (Af * (CFC.log Af - CFC.log Bf)).trace.re - (Af-Bf).trace.re =
        (A * (CFC.log A - CFC.log B)).trace.re - (A-B).trace.re by
      simp only [Af, Bf, CFC.log, Matrix.cfc_reindex]
      let E := Matrix.reindexAlgEquiv ℝ ℂ e
      change (E A * (E (cfc Real.log A) - E (cfc Real.log B))).trace.re -
        (E A-E B).trace.re = _
      rw [← map_sub, ← map_mul, ← map_sub]
      simp only [E, Matrix.coe_reindexAlgEquiv, trace_reindex]] at h
    exact h

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma density_path (ρ σ : DensityState ι)
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef)
    (hσ : (CStarMatrix.ofMatrix.symm σ.1).PosDef) :
    let A := CStarMatrix.ofMatrix.symm ρ.1
    let B := CStarMatrix.ofMatrix.symm σ.1
    IntervalIntegrable (pathIntegrand A B) volume 0 1 ∧
    extendedQuantumRelativeEntropy ρ σ = ((∫ t in (0 : ℝ)..1, pathIntegrand A B t) : ℝ) := by
  let A := CStarMatrix.ofMatrix.symm ρ.1
  let B := CStarMatrix.ofMatrix.symm σ.1
  obtain ⟨hi,hp⟩ := matrix_path A B hρ hσ
  refine ⟨hi, ?_⟩
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef ρ σ hσ)]
  apply WithTop.coe_eq_coe.mpr
  have hA : A.trace = 1 := ρ.2.2
  have hB : B.trace = 1 := σ.2.2
  rw [Matrix.trace_sub, hA, hB, sub_self, Complex.zero_re, sub_zero] at hp
  have mapLog (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
      CStarMatrix.ofMatrix (CFC.log M) = CFC.log (CStarMatrix.ofMatrix M) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _)
  unfold finiteTraceLogRelativeEntropy
  change (CStarMatrix.ofMatrix A * (CFC.log (CStarMatrix.ofMatrix A) -
    CFC.log (CStarMatrix.ofMatrix B)) : CStarMatrix ι ι ℂ).trace.re = _
  rw [← mapLog A hρ.isHermitian, ← mapLog B hσ.isHermitian]
  exact hp

end Path

/-- A uniform endpoint contraction on the partial-trace kernel contracts
the faithful conditional Umegaki divergence for every finite quantum reference. -/
theorem faithful_conditional_relativeEntropy_contraction
    (N : QuantumChannel a b) (c : ℝ) (hN : (act N 1).PosDef)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound N c)
    (ρ σ : DensityState (R × a))
    (hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosDef)
    (hσ : (CStarMatrix.ofMatrix.symm σ.1).PosDef) :
    finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) -
      finiteTraceLogRelativeEntropy (marginalRight (referenceState N ρ))
        (marginalRight (referenceState N σ)) ≤
    c * (finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)) := by
  haveI : Nonempty (R × a) := state_nonempty ⟨density_posSemidef ρ, ρ.2.2⟩
  haveI : Nonempty (R × b) := state_nonempty
    ⟨density_posSemidef (referenceState N ρ), (referenceState N ρ).2.2⟩
  haveI : Nonempty a := Nonempty.map Prod.snd (inferInstance : Nonempty (R × a))
  haveI : Nonempty b := Nonempty.map Prod.snd (inferInstance : Nonempty (R × b))
  let A := CStarMatrix.ofMatrix.symm ρ.1
  let B := CStarMatrix.ofMatrix.symm σ.1
  have hp (ξ : DensityState (R × a)) (hξ : (CStarMatrix.ofMatrix.symm ξ.1).PosDef) :
      (CStarMatrix.ofMatrix.symm (referenceState N ξ).1).PosDef :=
    amp_posDef N hN _ hξ
  have hm {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
      (ξ : DensityState (R × d)) (hξ : (CStarMatrix.ofMatrix.symm ξ.1).PosDef) :
      (CStarMatrix.ofMatrix.symm (marginalRight ξ).1).PosDef :=
    partialTraceRight_posDef _ hξ
  have hpath {d : Type u} [Fintype d] [DecidableEq d]
      (ξ η : DensityState d) (hξ : (CStarMatrix.ofMatrix.symm ξ.1).PosDef)
      (hη : (CStarMatrix.ofMatrix.symm η.1).PosDef) :
      let X := CStarMatrix.ofMatrix.symm ξ.1
      let Y := CStarMatrix.ofMatrix.symm η.1
      IntervalIntegrable (pathIntegrand X Y) volume 0 1 ∧
      finiteTraceLogRelativeEntropy ξ η = ∫ t in (0 : ℝ)..1, pathIntegrand X Y t := by
    obtain ⟨hi,he⟩ := density_path ξ η hξ hη
    rw [extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef ξ η hη)] at he
    exact ⟨hi, WithTop.coe_eq_coe.mp he⟩
  obtain ⟨hiIn,heIn⟩ := hpath ρ σ hρ hσ
  obtain ⟨hiOut,heOut⟩ := hpath (referenceState N ρ) (referenceState N σ) (hp ρ hρ) (hp σ hσ)
  obtain ⟨hiM,heM⟩ := hpath (marginalRight ρ) (marginalRight σ) (hm ρ hρ) (hm σ hσ)
  obtain ⟨hiTM,heTM⟩ := hpath (marginalRight (referenceState N ρ))
    (marginalRight (referenceState N σ)) (hm _ (hp ρ hρ)) (hm _ (hp σ hσ))
  rw [heIn, heOut, heM, heTM, ← intervalIntegral.integral_sub hiOut hiTM,
    ← intervalIntegral.integral_sub hiIn hiM, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one (hiOut.sub hiTM) ((hiIn.sub hiM).const_mul c)
  intro t ht
  let H := A-B
  let Z := B+t • H
  have hZ : Z.PosDef := affine_posDef A B hρ hσ t ht
  have hTA (X Y : Matrix (R × a) (R × a) ℂ) :
      amp N (X-Y) = amp N X - amp N Y := by simpa only [one_smul] using amp_sub_smul N 1 X Y
  have hPA {d : Type u} [Fintype d] [DecidableEq d] (X Y : Matrix (R × d) (R × d) ℂ) :
      partialTraceRight (X-Y) = partialTraceRight X - partialTraceRight Y := by
    simpa only [ptr, one_smul] using ptr_sub_smul 1 X Y
  have hTZ : amp N Z = amp N B + t • amp N H := by
    have he : Z = B - (-t) • H := by dsimp [Z]; module
    rw [he, amp_sub_smul, neg_smul, sub_neg_eq_add]
  have hPZ {d : Type u} [Fintype d] [DecidableEq d] (X Y : Matrix (R × d) (R × d) ℂ) :
      partialTraceRight (X + t • Y) = partialTraceRight X + t • partialTraceRight Y := by
    rw [partialTraceRight_add, partialTraceRight_smul]
  change pathIntegrand (amp N A) (amp N B) t -
      pathIntegrand (partialTraceRight (amp N A)) (partialTraceRight (amp N B)) t ≤
    c * (pathIntegrand A B t - pathIntegrand (partialTraceRight A) (partialTraceRight B) t)
  have hbkm := bkm_difference_contraction N c hN hc hEnd Z H hZ
  have heH : amp N H = amp N A - amp N B := hTA A B
  have heP : partialTraceRight H = partialTraceRight A - partialTraceRight B := hPA A B
  have hePT : partialTraceRight (amp N H) =
      partialTraceRight (amp N A) - partialTraceRight (amp N B) := by rw [heH, hPA]
  unfold pathIntegrand
  rw [← heH, ← heP, ← hePT, ← hTZ, ← hPZ, ← hTZ, ← hPZ]
  change (1-t) * _ - (1-t) * _ ≤ c * ((1-t) * _ - (1-t) * _)
  convert mul_le_mul_of_nonneg_left hbkm (sub_nonneg.mpr ht.2) using 1 <;> ring

#print axioms faithful_conditional_relativeEntropy_contraction

end D5.S3.Quantum.Divergence.UmegakiConditionalBKM
