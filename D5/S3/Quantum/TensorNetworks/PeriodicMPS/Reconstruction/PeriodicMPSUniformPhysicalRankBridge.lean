/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalRankBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalRankBridge
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Maximal minors describe the critical coordinates of the normalized two-site observation. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformGraphRecovery
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeCriticalMatrix

/-!
# The physical rank criterion in the uniform graph

The literal suffix Gram differential gives the ten raw rows of the chart
observation. Its radial line is the kernel of normalization. On the
nonzero aligned mixed-trace sector, a fixed physical unitary transports rank
to the positive slice, where the five slice derivatives and three rotations
are the columns of the native polynomial matrix.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformPhysicalRankBridge

open Function Matrix MvPolynomial
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology

open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSUniformHardCoreMarginalWitness (Amplitudes pairGram)
open PeriodicMPSAmbiguityDensity (changePhysical pairBasis)
open UniformMPSExpectedDimensionRefutation (traceWord)
open TwoQubitMarginalReflection (Bits Density)
open SevenSiteTraceBase (Word amplitudeOfLength differentiable_amplitudeOfLength)
open PeriodicMPSUniformCompactGraph (Parameters traceChart chartDomain)
open PeriodicMPSUniformGraphRecovery (chartObservation criticalCoordinates)
open PeriodicMPSCompactReadout (Readout readout)
open SevenSitePhysicalRankBridge (Ordinary SlicePoint align unalign unalign_align
  physicalChart_center sliceOrdinary sectionUnitary)
open SevenSitePhysicalRankAssembly (asOrdinary alignedSlice firstTrace fixedChart)
open UniformRankNormalization (ordinaryAmplitude ordinaryRaw ordinaryMass ordinaryMarginal
  finrank_rawReadout_span)
open UniformNativeCriticalMatrix (criticalMatrix ordinaryMarginal_rank_eq_eight_iff_minor)

open private analyticAt_traceChart from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformGraphRecovery
open private join from D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness
open private pairGram_changePhysical_unitary pairGram_scaled ordinaryRaw_actual from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeRotation
open private ordinaryMass_pos ordinaryMarginal_eq_normalizedRaw
  differentiableAt_ordinaryMarginal projectiveMass_eq_ordinaryMass from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformRankNormalization
open private sectionNorm sectionNorm_pos from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private asOrdinary_injective coreOrdinary restoredCore core_firstTrace restoredCore_trace
  fixedChart_core fixedChart_section fixedChart_left_inv firstTrace_inverse analyticAt_fixedChart
  conjugation conjugation_injective trace_conjugation from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly

noncomputable section

/-- Collective unitary equivariance after summing out the literal suffix. -/
theorem suffixGram_changePhysical (m : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A : Fin 2 → Bond) :
    pairGram (m := m) (traceWord 2 2 (2 + m) (changePhysical U.val A)) =
      pairBasis U.val * pairGram (m := m) (traceWord 2 2 (2 + m) A) * (pairBasis U.val)ᴴ :=
  pairGram_changePhysical_unitary m U A

/-- The two terms obtained by differentiating the literal suffix sum over a
real parameter. -/
def suffixGramDifferential {m : ℕ} (a da : Amplitudes m) : Density :=
  fun p q => ∑ w : Word m,
    (da (join p w) * star (a (join q w)) + a (join p w) * star (da (join q w)))

private def entry (i j : Bits) : Density →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i : Density →L[ℝ] (Bits → ℂ))

private theorem differentiableAt_pairGram {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℕ} {a : E → Amplitudes m} {x : E}
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (fun y => pairGram (a y)) x := by
  apply differentiableAt_pi.mpr
  intro p
  apply differentiableAt_pi.mpr
  intro q
  unfold pairGram
  simp only [Complex.star_def, ← Complex.conjCLE_apply]
  fun_prop

/-- The real derivative of a suffix Gram matrix, evaluated on a direction. -/
theorem fderiv_pairGram_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {a : E → Amplitudes m} {x : E} (ha : DifferentiableAt ℝ a x) (v : E) :
    fderiv ℝ (fun y => pairGram (a y)) x v =
      suffixGramDifferential (a x) (fderiv ℝ a x v) := by
  let D := fderiv ℝ a x
  have hword (w : Word (2 + m)) :
      HasFDerivAt (fun y => a y w) ((ContinuousLinearMap.proj w).comp D) x :=
    (ContinuousLinearMap.proj w : Amplitudes m →L[ℝ] ℂ).hasFDerivAt.comp x ha.hasFDerivAt
  have hprod (p q : Bits) (w : Word m) :=
    (hword (join p w)).fun_mul
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x (hword (join q w)))
  ext p q
  have h₁ := (entry p q).hasFDerivAt.comp x (differentiableAt_pairGram ha).hasFDerivAt
  have h₂ := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Word m)))
    (fun w _ => hprod p q w)
  have h := h₁.unique (show HasFDerivAt (entry p q ∘ fun y => pairGram (a y)) _ x from h₂)
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L v) h
  change entry p q (fderiv ℝ (fun y => pairGram (a y)) x v) = _
  rw [show entry p q (fderiv ℝ (fun y => pairGram (a y)) x v) = _ from hv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    suffixGramDifferential, D, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [add_comm]
  exact congrArg (fun z => z + a x (join p w) * star (fderiv ℝ a x v (join q w)))
    (mul_comm (star (a x (join q w))) (fderiv ℝ a x v (join p w)))

private def traceReal : Density →L[ℝ] ℝ :=
  Complex.reCLM.comp (∑ i : Bits, entry i i)

private theorem traceReal_apply (M : Density) : traceReal M = M.trace.re := by
  simp only [traceReal, ContinuousLinearMap.comp_apply, _root_.sum_apply, trace, diag]
  rw [Complex.reCLM_apply]
  exact congrArg Complex.re (Finset.sum_congr rfl fun _ _ => rfl)

/-- The literal trace-word amplitude in the graph's ordinary affine chart. -/
def chartAmplitude (m : ℕ) (u : Parameters) : Amplitudes m :=
  amplitudeOfLength (2 + m) (traceChart u)

private theorem differentiable_chartAmplitude (m : ℕ) : Differentiable ℝ (chartAmplitude m) := by
  exact (differentiable_amplitudeOfLength (𝕜 := ℝ) (2 + m)).comp
    (fun u => (analyticAt_traceChart u).differentiableAt)

/-- The mass and nine Pauli readings of an unnormalized adjacent Gram matrix. -/
def rawRows : Density →L[ℝ] ℝ × Readout :=
  traceReal.prod readout

/-- The ten raw rows in the graph's ordinary chart. -/
def chartRawReadout (m : ℕ) (u : Parameters) : ℝ × Readout :=
  rawRows (pairGram (chartAmplitude m u))

/-- The explicit ten-row real differential before dividing by the mass. -/
def chartRawDifferential (m : ℕ) (u v : Parameters) : ℝ × Readout :=
  rawRows (suffixGramDifferential (chartAmplitude m u) (fderiv ℝ (chartAmplitude m) u v))

private theorem chartAmplitude_eq_ordinary (m : ℕ) (u : Parameters) :
    chartAmplitude m u = ordinaryAmplitude m (asOrdinary u) := rfl

private theorem differentiableAt_chartRawReadout (m : ℕ) (u : Parameters) :
    DifferentiableAt ℝ (chartRawReadout m) u := by
  exact rawRows.differentiableAt.comp u (differentiableAt_pairGram (differentiable_chartAmplitude m u))

theorem fderiv_chartRawReadout_apply (m : ℕ) (u v : Parameters) :
    fderiv ℝ (chartRawReadout m) u v = chartRawDifferential m u v := by
  have ha := differentiable_chartAmplitude m u
  have hg := differentiableAt_pairGram ha
  change fderiv ℝ (rawRows ∘ fun y => pairGram (chartAmplitude m y)) u v = _
  rw [(rawRows.hasFDerivAt.comp u hg.hasFDerivAt).fderiv]
  change rawRows (fderiv ℝ (fun y => pairGram (chartAmplitude m y)) u v) = _
  exact congrArg rawRows (fderiv_pairGram_apply ha v)

theorem chartObservation_eq_normalizedRaw (m : ℕ) (u : Parameters) :
    chartObservation m u = (chartRawReadout m u).1⁻¹ • (chartRawReadout m u).2 := by
  change readout (ordinaryMarginal m (asOrdinary u)) = _
  rw [ordinaryMarginal_eq_normalizedRaw, map_smul]
  simp only [chartRawReadout, rawRows, ContinuousLinearMap.prod_apply, traceReal_apply,
    chartAmplitude_eq_ordinary]
  rfl

private theorem chartRawMass_pos (m : ℕ) (u : Parameters) (hu : u ∈ chartDomain (2 + m)) :
    0 < (chartRawReadout m u).1 := by
  change chartAmplitude m u ≠ 0 at hu
  rw [chartAmplitude_eq_ordinary] at hu
  change 0 < traceReal (pairGram (chartAmplitude m u))
  rw [traceReal_apply, chartAmplitude_eq_ordinary]
  exact ordinaryMass_pos m _ hu

/-- Product rule for the normalized graph readout. Multiplying the derivative
by the mass leaves the raw Pauli differential minus its radial component. -/
theorem mass_smul_fderiv_chartObservation (m : ℕ) (u v : Parameters)
    (hu : u ∈ chartDomain (2 + m)) :
    (chartRawReadout m u).1 • fderiv ℝ (chartObservation m) u v =
      (chartRawDifferential m u v).2 -
        (chartRawDifferential m u v).1 • chartObservation m u := by
  let g := chartObservation m
  let R := chartRawReadout m
  let n : Parameters → ℝ := Prod.fst ∘ R
  let o : Parameters → Readout := Prod.snd ∘ R
  have hR := differentiableAt_chartRawReadout m u
  have hn : DifferentiableAt ℝ n u := hR.fst
  have hg : DifferentiableAt ℝ g u :=
    (PeriodicMPSUniformGraphRecovery.analyticAt_chartObservation hu).differentiableAt
  have hn₀ : n u ≠ 0 := (chartRawMass_pos m u hu).ne'
  have heq : (fun y => n y • g y) =ᶠ[𝓝 u] o :=
    (hn.continuousAt.eventually_ne hn₀).mono fun y hy => by
      change n y • chartObservation m y = o y
      rw [chartObservation_eq_normalizedRaw]
      change n y • (n y)⁻¹ • o y = o y
      rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
  have hprod : n u • fderiv ℝ g u v + fderiv ℝ n u v • g u = fderiv ℝ o u v := by
    rw [← heq.fderiv_eq]
    change _ = fderiv ℝ (n • g) u v
    rw [fderiv_smul hn hg]
    rfl
  have hfst : fderiv ℝ n u v = (chartRawDifferential m u v).1 := by
    change fderiv ℝ (Prod.fst ∘ chartRawReadout m) u v = _
    rw [fderiv_comp u differentiableAt_fst hR, fderiv_fst, ContinuousLinearMap.comp_apply,
      fderiv_chartRawReadout_apply]
    rfl
  have hsnd : fderiv ℝ o u v = (chartRawDifferential m u v).2 := by
    change fderiv ℝ (Prod.snd ∘ chartRawReadout m) u v = _
    rw [fderiv_comp u differentiableAt_snd hR, fderiv_snd, ContinuousLinearMap.comp_apply,
      fderiv_chartRawReadout_apply]
    rfl
  rw [hfst, hsnd] at hprod
  exact eq_sub_of_add_eq hprod

/-- Exactly the real directions whose ten raw differentials are radial
disappear from the normalized nine-Pauli readout. -/
theorem fderiv_chartObservation_eq_zero_iff_radial (m : ℕ) (u v : Parameters)
    (hu : u ∈ chartDomain (2 + m)) :
    fderiv ℝ (chartObservation m) u v = 0 ↔
      ∃ t : ℝ, chartRawDifferential m u v = t • chartRawReadout m u := by
  let R := chartRawReadout m u
  let D := chartRawDifferential m u v
  have hR : R.1 ≠ 0 := (chartRawMass_pos m u hu).ne'
  have hprod := mass_smul_fderiv_chartObservation m u v hu
  change R.1 • _ = D.2 - D.1 • _ at hprod
  rw [chartObservation_eq_normalizedRaw] at hprod
  constructor
  · intro h
    rw [h, smul_zero, eq_comm, sub_eq_zero, smul_smul] at hprod
    refine ⟨D.1 * R.1⁻¹, Prod.ext ?_ hprod⟩
    change D.1 = (D.1 * R.1⁻¹) * R.1
    rw [mul_assoc, inv_mul_cancel₀ hR, mul_one]
  · rintro ⟨t, h⟩
    change D = t • R at h
    have h₁ : D.1 = t * R.1 := congrArg Prod.fst h
    have h₂ : D.2 = t • R.2 := congrArg Prod.snd h
    rw [h₁, h₂, smul_smul, mul_assoc, mul_inv_cancel₀ hR, mul_one, sub_self] at hprod
    exact (smul_eq_zero.mp hprod).resolve_left hR

/-- On the ordinary graph chart, rank loss is the existence of a nonzero
real parameter tangent whose raw differential is radial. -/
theorem mem_criticalCoordinates_iff_radial (m : ℕ) (u : Parameters)
    (hu : u ∈ chartDomain (2 + m)) :
    u ∈ criticalCoordinates m ↔
      ∃ v : Parameters, v ≠ 0 ∧
        ∃ t : ℝ, chartRawDifferential m u v = t • chartRawReadout m u := by
  classical
  change (u ∈ chartDomain (2 + m) ∧ ¬ Injective (fderiv ℝ (chartObservation m) u)) ↔ _
  rw [and_iff_right hu]
  change ¬ Injective (fderiv ℝ (chartObservation m) u).toLinearMap ↔ _
  rw [← (fderiv ℝ (chartObservation m) u).toLinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  push Not
  exact exists_congr fun v => by
    rw [ContinuousLinearMap.coe_coe, fderiv_chartObservation_eq_zero_iff_radial m u v hu, and_comm]

section AlignedSlice

private theorem fixedChart_raw (m : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    ordinaryRaw m (fixedChart U.val p) =
      Complex.normSq ((firstTrace U.val p)⁻¹ ^ (2 + m)) • conjugation U (ordinaryRaw m p) := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  have ha : coreOrdinary A = p := Prod.ext hs (Prod.ext hd (Prod.ext he hk))
  let τ := (changePhysical U.val A 0).trace
  have hτ : τ = firstTrace U.val p := (core_firstTrace _ _ ht).trans (congrArg _ ha)
  let B := restoredCore U.val A
  have hτne : τ ≠ 0 := hτ.symm ▸ hp
  have htB : (B 0).trace = 1 := restoredCore_trace _ _ hτne
  have hb : fixedChart U.val p = coreOrdinary B := by
    rw [← ha, fixedChart_core U.val A ht]
  rw [hb, show ordinaryRaw m (coreOrdinary B) = _ from ordinaryRaw_actual m B htB,
    show ordinaryRaw m p = _ from (congrArg (ordinaryRaw m) ha.symm).trans
      (ordinaryRaw_actual m A ht),
    show B = τ⁻¹ • changePhysical U.val A from rfl, pairGram_scaled, suffixGram_changePhysical]
  rw [Complex.star_def, Complex.mul_conj]
  rw [hτ]
  rfl

private theorem fixedChart_mass (m : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    ordinaryMass m (fixedChart U.val p) =
      Complex.normSq ((firstTrace U.val p)⁻¹ ^ (2 + m)) * ordinaryMass m p := by
  simp only [ordinaryMass, fixedChart_raw m U p hp, Matrix.trace_smul, Complex.smul_re,
    trace_conjugation, smul_eq_mul]

private theorem ordinaryMass_eq_zero_iff (m : ℕ) (p : Ordinary) :
    ordinaryMass m p = 0 ↔ ordinaryAmplitude m p = 0 := by
  constructor
  · intro h
    by_contra ha
    exact (ordinaryMass_pos m p ha).ne' h
  · intro h
    rw [← projectiveMass_eq_ordinaryMass, h]
    simp [PeriodicMPSProjectiveCoordinates.mass]

private theorem fixedChart_marginal (m : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) :
    ordinaryMarginal m (fixedChart U.val p) = conjugation U (ordinaryMarginal m p) := by
  let c := Complex.normSq ((firstTrace U.val p)⁻¹ ^ (2 + m))
  have hc : c ≠ 0 := (Complex.normSq_pos.mpr (pow_ne_zero _ (inv_ne_zero hp))).ne'
  rw [ordinaryMarginal_eq_normalizedRaw, ordinaryMarginal_eq_normalizedRaw,
    fixedChart_mass m U p hp, fixedChart_raw m U p hp, map_smul, smul_smul]
  change ((c * ordinaryMass m p)⁻¹ * c) • _ = _
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- A fixed collective rotation with trace-one restoration preserves injectivity
of the normalized density derivative in both directions. -/
private theorem injective_fderiv_fixedChart_iff
    (m : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Ordinary)
    (hp : firstTrace U.val p ≠ 0) (ha : ordinaryAmplitude m p ≠ 0)
    (hb : ordinaryAmplitude m (fixedChart U.val p) ≠ 0) :
    Injective (fderiv ℝ (ordinaryMarginal m) (fixedChart U.val p)) ↔
      Injective (fderiv ℝ (ordinaryMarginal m) p) := by
  let F := fixedChart U.val
  let G := fixedChart U.valᴴ
  let P := fderiv ℝ F p
  let D := fderiv ℝ (ordinaryMarginal m) p
  let D' := fderiv ℝ (ordinaryMarginal m) (F p)
  have hF : DifferentiableAt ℝ F p := (analyticAt_fixedChart _ _ hp).differentiableAt
  have hG : DifferentiableAt ℝ G (F p) :=
    (analyticAt_fixedChart _ _ (firstTrace_inverse U p hp)).differentiableAt
  have hnear : ∀ᶠ q in 𝓝 p, firstTrace U.val q ≠ 0 := by
    have ht : Continuous (firstTrace U.val) := by unfold firstTrace; fun_prop
    exact ht.continuousAt.eventually_ne hp
  have hInv : G ∘ F =ᶠ[𝓝 p] id :=
    hnear.mono fun q hq => fixedChart_left_inv U q hq
  have hI : (fderiv ℝ G (F p)).comp P = ContinuousLinearMap.id ℝ Ordinary := by
    rw [← fderiv_comp p hG hF, hInv.fderiv_eq, fderiv_id]
  have hi : Injective P := by
    have hleft : LeftInverse (fderiv ℝ G (F p)) P :=
      fun v => congrArg (fun L : Ordinary →L[ℝ] Ordinary => L v) hI
    exact hleft.injective
  have hs : Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (show Injective P.toLinearMap from hi)
  have hCov : ordinaryMarginal m ∘ F =ᶠ[𝓝 p] conjugation U ∘ ordinaryMarginal m :=
    hnear.mono fun q hq => fixedChart_marginal m U q hq
  have hD : D' ∘ P = conjugation U ∘ D := by
    have hL := (differentiableAt_ordinaryMarginal m _ hb).hasFDerivAt.comp p hF.hasFDerivAt
    have hR := (conjugation U).hasFDerivAt.comp p
      (differentiableAt_ordinaryMarginal m p ha).hasFDerivAt
    exact congrArg (fun L : Ordinary →L[ℝ] Density => (L : Ordinary → Density))
      (hL.unique (hR.congr_of_eventuallyEq hCov))
  change Injective D' ↔ Injective D
  constructor
  · intro h
    have hcomp : Injective (conjugation U ∘ D) := hD ▸ h.comp hi
    exact hcomp.of_comp
  · intro h
    have hcomp : Injective (D' ∘ P) := hD.symm ▸ (conjugation_injective U).comp h
    exact hcomp.of_comp_right hs

private theorem alignedSlice_center (p : Ordinary) (hK : (align p).2.2.2 ≠ 0) :
    0 < alignedSlice p 1 ∧
      ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
        firstTrace U.val (sliceOrdinary (alignedSlice p)) ≠ 0 ∧
        fixedChart U.val (sliceOrdinary (alignedSlice p)) = p := by
  let q := align p
  let K := q.2.2.2
  let r := Real.sqrt (Complex.normSq K)
  let l := K / (r : ℂ)
  let x := alignedSlice p
  have hr : 0 < r := Real.sqrt_pos.2 (Complex.normSq_pos.2 hK)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hl : Complex.normSq l = 1 := by
    rw [show l = K / (r : ℂ) from rfl, Complex.normSq_div, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (Complex.normSq_nonneg K),
      div_self (Complex.normSq_pos.2 hK).ne']
  let U := sectionUnitary q.1 l hl
  have ht : firstTrace U.val (sliceOrdinary x) ≠ 0 := by
    rw [sliceOrdinary, physicalChart_center]
    change ((sectionNorm q.1 : ℂ)⁻¹ * 1 + U.val 0 1 * 0) ≠ 0
    simpa using inv_ne_zero (Complex.ofReal_ne_zero.mpr (sectionNorm_pos q.1).ne')
  have hd : (x 0 : ℂ) + Complex.I * (x 3 : ℂ) = q.2.1 := by
    change (q.2.1.re : ℂ) + Complex.I * (q.2.1.im : ℂ) = q.2.1
    rw [mul_comm Complex.I, Complex.re_add_im]
  have he : (x 2 : ℂ) + Complex.I * (x 4 : ℂ) = q.2.2.1 / l ^ 2 := by
    change ((q.2.2.1 / l ^ 2).re : ℂ) + Complex.I * ((q.2.2.1 / l ^ 2).im : ℂ) = _
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hk : l * (x 1 : ℂ) = K := div_mul_cancel₀ _ hrC
  refine ⟨hr, U, ht, ?_⟩
  rw [fixedChart_section q.1 l hl, hd, he, ← mul_div_assoc,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 (div_ne_zero hK hrC)), hk]
  exact unalign_align p

private theorem finrank_ordinary : Module.finrank ℝ Ordinary = 8 := by
  simp [Ordinary, Module.finrank_prod, Complex.finrank_real_complex]

private theorem finrank_range_eq_eight_iff_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Ordinary →L[ℝ] E) :
    Module.finrank ℝ (LinearMap.range D.toLinearMap) = 8 ↔ Injective D := by
  change Module.finrank ℝ (LinearMap.range D.toLinearMap) = 8 ↔ Injective D.toLinearMap
  rw [← D.toLinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have h := D.toLinearMap.finrank_range_add_finrank_ker
  rw [finrank_ordinary] at h
  omega

private theorem injective_fderiv_chartObservation_iff (m : ℕ) (u : Parameters)
    (hu : u ∈ chartDomain (2 + m)) :
    Injective (fderiv ℝ (chartObservation m) u) ↔
      Injective (fderiv ℝ (ordinaryMarginal m) (asOrdinary u)) := by
  have ha : ordinaryAmplitude m (asOrdinary u) ≠ 0 := hu
  have hs : Surjective asOrdinary := by
    rintro ⟨s, d, e, k⟩
    exact ⟨![s, d, e, k], rfl⟩
  have hfun : chartObservation m = (readout ∘ ordinaryMarginal m) ∘ asOrdinary := rfl
  have hd := readout.differentiableAt.comp (asOrdinary u)
    (differentiableAt_ordinaryMarginal m _ ha)
  rw [hfun, fderiv_comp u hd asOrdinary.differentiableAt, ContinuousLinearMap.fderiv]
  change Injective (fderiv ℝ (readout ∘ ordinaryMarginal m) (asOrdinary u) ∘ asOrdinary) ↔ _
  have hcomp : ∀ (f : Ordinary → Readout), Injective (f ∘ asOrdinary) ↔ Injective f :=
    fun f => ⟨fun h => h.of_comp_right hs, fun h => h.comp asOrdinary_injective⟩
  rw [hcomp]
  refine (finrank_range_eq_eight_iff_injective _).symm.trans
    (Iff.trans ?_ (finrank_range_eq_eight_iff_injective _))
  rw [(finrank_rawReadout_span m _ ha).2]

/-- On the nonzero aligned mixed-trace sector, the actual graph is critical
exactly when every maximal minor of the native ten-row physical differential
vanishes. The determinant is evaluated on the positive aligned trace slice. -/
theorem mem_criticalCoordinates_iff_native_minors (m : ℕ) (u : Parameters)
    (hu : u ∈ chartDomain (2 + m)) (hK : (align (asOrdinary u)).2.2.2 ≠ 0) :
    u ∈ criticalCoordinates m ↔
      ∀ deleted : Fin 10, eval (fun i => (alignedSlice (asOrdinary u) i : ℂ))
        ((criticalMatrix m).submatrix deleted.succAbove id).det = 0 := by
  classical
  let p := asOrdinary u
  let x := alignedSlice p
  obtain ⟨hx, U, hτ, hcenter⟩ := alignedSlice_center p hK
  have hp : ordinaryAmplitude m p ≠ 0 := hu
  have hA : ordinaryAmplitude m (sliceOrdinary x) ≠ 0 := by
    intro hz
    have hm := (ordinaryMass_eq_zero_iff m _).mpr hz
    have hc := fixedChart_mass m U (sliceOrdinary x) hτ
    rw [hcenter, hm, mul_zero] at hc
    exact hp ((ordinaryMass_eq_zero_iff m p).mp hc)
  have hRank : Injective (fderiv ℝ (chartObservation m) u) ↔
      ∃ deleted : Fin 10, eval (fun i => (x i : ℂ))
        ((criticalMatrix m).submatrix deleted.succAbove id).det ≠ 0 := by
    rw [injective_fderiv_chartObservation_iff m u hu]
    change Injective (fderiv ℝ (ordinaryMarginal m) p) ↔ _
    rw [← hcenter, injective_fderiv_fixedChart_iff m U (sliceOrdinary x) hτ hA
      (hcenter.symm ▸ hp)]
    exact (finrank_range_eq_eight_iff_injective _).symm.trans
      (ordinaryMarginal_rank_eq_eight_iff_minor m x hx hA)
  change (_ ∧ ¬ Injective (fderiv ℝ (chartObservation m) u)) ↔ _
  rw [and_iff_right hu, hRank]
  push Not
  rfl

/-- A single nonzero evaluated native minor certifies regularity of the
actual normalized graph readout at that period. -/
theorem not_mem_criticalCoordinates_of_native_minor (m : ℕ) (u : Parameters)
    (hu : u ∈ chartDomain (2 + m)) (hK : (align (asOrdinary u)).2.2.2 ≠ 0)
    (deleted : Fin 10)
    (hminor : eval (fun i => (alignedSlice (asOrdinary u) i : ℂ))
      ((criticalMatrix m).submatrix deleted.succAbove id).det ≠ 0) :
    u ∉ criticalCoordinates m :=
  fun hc => hminor ((mem_criticalCoordinates_iff_native_minors m u hu hK).mp hc deleted)

end AlignedSlice

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformPhysicalRankBridge
