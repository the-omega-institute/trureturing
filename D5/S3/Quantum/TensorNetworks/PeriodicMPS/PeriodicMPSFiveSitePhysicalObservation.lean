/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSitePhysicalObservation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSitePhysicalObservation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates]
   utility: none
   digest: Real observation coordinates retain the complete five-site physical marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteLocalGraphs

/-! Hermitian symmetry and cyclic reflection reduce a five-site marginal to
ten real coordinates before fixing its trace. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSitePhysicalObservation

open Matrix hiding gram
open Set PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteTraceChart
  PeriodicMPSFiveSiteSpecialFiber PeriodicMPSFiveSiteNormalization PeriodicMPSFiveSiteJetCoordinates
  PeriodicMPSFiveSiteCompactChart PeriodicMPSFiveSiteCompactSource
open scoped ComplexConjugate Matrix.Norms.Elementwise

open private amplitude entry from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates
open private chart_ne_zero from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart

noncomputable section

abbrev Marginal := Matrix (Fin 4) (Fin 4) ℂ

/-- The nine tangential entries and the corner probability of a raw marginal. -/
def entries (M : Marginal) : Fin 10 → ℝ :=
  ![(M 0 0).re, (M 0 1).re, (M 0 1).im, (M 0 3).re, (M 0 3).im, (M 1 1).re,
    (M 1 2).re, (M 1 3).re, (M 1 3).im, (M 3 3).re]

/-- The reflection of the adjacent binary subsystem interchanges 01 and 10. -/
private def swapBits : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

private def symmetricMarginals : Set Marginal :=
  {M | (∀ i j, M i j = conj (M j i)) ∧
    (∀ i j, M (swapBits i) (swapBits j) = M i j)}

private theorem gram_mem (p : Fin 8 → ℂ) : gram p ∈ symmetricMarginals := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [gram, Matrix.mul_apply, conjTranspose_apply, Complex.star_def, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_comm]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [swapBits, Equiv.swap_apply_def, gram, Matrix.mul_apply, conjTranspose_apply, flatten,
        Fin.sum_univ_succ] <;>
      ring

private theorem scale_mem {M : Marginal} (hM : M ∈ symmetricMarginals) (r : ℝ) :
    r • M ∈ symmetricMarginals := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rw [hM.1 i j]
  · simp only [Matrix.smul_apply, hM.2 i j]

private theorem physical_mem {x : Ambient} (hx : x ∈ source) :
    observation x ∈ symmetricMarginals := by
  obtain ⟨p, hmass, hp⟩ := source_amplitude_projective hx
  have hm : PeriodicMPSProjectiveCoordinates.mass p = 1 := hmass
  have hpn : p ≠ 0 := by
    intro h
    simp [PeriodicMPSProjectiveCoordinates.mass, h] at hm
  have he : x.2 = PeriodicMPSProjectiveCoordinates.projector p := by
    rw [← hp]
    simp [PeriodicMPSProjectiveCoordinates.projector, hm]
  rw [observation_of_projector hpn he, normalizedGram]
  exact scale_mem (gram_mem p) _

private theorem symmetric_eq_of_entries {M N : Marginal} (hM : M ∈ symmetricMarginals)
    (hN : N ∈ symmetricMarginals) (he : entries M = entries N) : M = N := by
  have hv (i : Fin 10) := congrFun he i
  have hre (Q : Marginal) (hQ : Q ∈ symmetricMarginals) (i : Fin 4) : (Q i i).im = 0 := by
    have h := congrArg Complex.im (hQ.1 i i)
    simpa using (show (Q i i).im = 0 by
      rw [Complex.conj_im] at h
      linarith)
  have hpair (Q : Marginal) (hQ : Q ∈ symmetricMarginals) : (Q 1 2).im = 0 := by
    have hs : Q 2 1 = Q 1 2 := hQ.2 1 2
    have h := congrArg Complex.im ((hQ.1 1 2).trans (congrArg conj hs))
    rw [Complex.conj_im] at h
    linarith
  have h00 : M 0 0 = N 0 0 := Complex.ext (hv 0) ((hre M hM 0).trans (hre N hN 0).symm)
  have h01 : M 0 1 = N 0 1 := Complex.ext (hv 1) (hv 2)
  have h03 : M 0 3 = N 0 3 := Complex.ext (hv 3) (hv 4)
  have h11 : M 1 1 = N 1 1 := Complex.ext (hv 5) ((hre M hM 1).trans (hre N hN 1).symm)
  have h12 : M 1 2 = N 1 2 := Complex.ext (hv 6) ((hpair M hM).trans (hpair N hN).symm)
  have h13 : M 1 3 = N 1 3 := Complex.ext (hv 7) (hv 8)
  have h33 : M 3 3 = N 3 3 := Complex.ext (hv 9) ((hre M hM 3).trans (hre N hN 3).symm)
  have hs (Q : Marginal) (hQ : Q ∈ symmetricMarginals) :
      Q 0 2 = Q 0 1 ∧ Q 2 2 = Q 1 1 ∧ Q 2 3 = Q 1 3 :=
    ⟨hQ.2 0 1, hQ.2 1 1, hQ.2 1 3⟩
  have h02 := (hs M hM).1.trans (h01.trans (hs N hN).1.symm)
  have h22 := (hs M hM).2.1.trans (h11.trans (hs N hN).2.1.symm)
  have h23 := (hs M hM).2.2.trans (h13.trans (hs N hN).2.2.symm)
  have flip (i j : Fin 4) (h : M j i = N j i) : M i j = N i j :=
    (hM.1 i j).trans ((congrArg conj h).trans (hN.1 i j).symm)
  ext i j
  fin_cases i <;> fin_cases j <;> first | assumption | exact flip _ _ (by assumption)

/-- The trace-one observation can be stored in nine real numbers. -/
def measured (p : Ambient) : Fin 9 → ℝ :=
  fun j => entries (observation p) j.castSucc

private theorem trace_re_mem {M : Marginal} (hM : M ∈ symmetricMarginals) :
    M.trace.re = (M 0 0).re + 2 * (M 1 1).re + (M 3 3).re := by
  have h : M 2 2 = M 1 1 := hM.2 1 1
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, Complex.add_re, h]
  ring

private theorem observation_trace_one {p : Ambient} (hp : p ∈ source) :
    (observation p).trace.re = 1 := by
  obtain ⟨q, hmass, hq⟩ := source_amplitude_projective hp
  have hm : PeriodicMPSProjectiveCoordinates.mass q = 1 := hmass
  have hqn : q ≠ 0 := by
    intro h
    simp [PeriodicMPSProjectiveCoordinates.mass, h] at hm
  have he : p.2 = PeriodicMPSProjectiveCoordinates.projector q := by
    rw [← hq]
    simp [PeriodicMPSProjectiveCoordinates.projector, hm]
  rw [observation_of_projector hqn he, normalizedGram, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul, ← PeriodicMPSFiveSiteNormalization.mass,
    inv_mul_cancel₀ (mass_positive _ hqn).ne']

/-- View the nine normalized readouts as a continuous real-linear map. -/
def readout : Marginal →L[ℝ] (Fin 9 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    let e (j k : Fin 4) : Marginal →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj k : (Fin 4 → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj j : (Fin 4 → Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ))
    ![Complex.reCLM.comp (e 0 0), Complex.reCLM.comp (e 0 1), Complex.imCLM.comp (e 0 1),
      Complex.reCLM.comp (e 0 3), Complex.imCLM.comp (e 0 3), Complex.reCLM.comp (e 1 1),
      Complex.reCLM.comp (e 1 2), Complex.reCLM.comp (e 1 3), Complex.imCLM.comp (e 1 3)] i)

theorem readout_apply (M : Marginal) (i : Fin 9) : readout M i = entries M i.castSucc := by
  fin_cases i <;> rfl

theorem measured_eq_readout (p : Ambient) : measured p = readout (observation p) := by
  funext i
  exact (readout_apply _ _).symm

/-- Reconstruct the matrix on the trace-one Hermitian reflection subspace. -/
def readoutInverse (v : Fin 9 → ℝ) : Marginal :=
  let a := (v 1 : ℂ) + (v 2 : ℂ) * Complex.I
  let b := (v 3 : ℂ) + (v 4 : ℂ) * Complex.I
  let c := (v 7 : ℂ) + (v 8 : ℂ) * Complex.I
  !![(v 0 : ℂ), a, a, b;
    conj a, (v 5 : ℂ), (v 6 : ℂ), c;
    conj a, (v 6 : ℂ), (v 5 : ℂ), c;
    conj b, conj c, conj c, (1 - (v 0 : ℂ) - 2 * (v 5 : ℂ))]

theorem differentiable_readoutInverse : Differentiable ℝ readoutInverse := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  have hr (k : Fin 9) : Differentiable ℝ (fun v : Fin 9 → ℝ => (v k : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp (differentiable_apply k)
  have hc : Differentiable ℝ (conj : ℂ → ℂ) := Complex.conjCLE.differentiable
  fin_cases i <;> fin_cases j <;> simp [readoutInverse] <;> fun_prop

theorem readoutInverse_readout {p : Ambient} (hp : p ∈ source) :
    readoutInverse (readout (observation p)) = observation p := by
  let M := observation p
  let v := readout M
  have hM := physical_mem hp
  have ht := trace_re_mem hM
  rw [observation_trace_one hp] at ht
  have hM' : readoutInverse v ∈ symmetricMarginals := by
    refine ⟨?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [readoutInverse, map_ofNat]
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [readoutInverse, swapBits, Equiv.swap_apply_def]
  refine symmetric_eq_of_entries hM' hM ?_
  funext i
  have hr (j : Fin 9) : v j = entries M j.castSucc := readout_apply _ _
  fin_cases i <;> simp [entries, readoutInverse, readout_apply, v, M,
    Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im] <;> linarith

/-- Equality of the nine real coordinates is equivalent to equality of the
complete normalized matrix on the compact source. -/
theorem measured_eq_iff {p q : Ambient} (hp : p ∈ source) (hq : q ∈ source) :
    measured p = measured q ↔ observation p = observation q := by
  constructor
  · intro h
    have htrace₁ := trace_re_mem (physical_mem hp)
    have htrace₂ := trace_re_mem (physical_mem hq)
    rw [observation_trace_one hp] at htrace₁
    rw [observation_trace_one hq] at htrace₂
    have h0 : (observation p 0 0).re = (observation q 0 0).re := congrFun h 0
    have h5 : (observation p 1 1).re = (observation q 1 1).re := congrFun h 5
    have h9 : (observation p 3 3).re = (observation q 3 3).re := by linarith
    apply symmetric_eq_of_entries (physical_mem hp) (physical_mem hq)
    funext j
    exact Fin.lastCases h9 (congrFun h) j
  · intro h
    unfold measured
    rw [h]

private def gaussianToComplex : Gaussian ℝ →+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' z w := rfl
  map_mul' z w := by
    apply Complex.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Complex.mul_re,
      Complex.mul_im] <;> ring

private theorem gaussianToComplex_star (z : Gaussian ℝ) :
    gaussianToComplex (star z) = conj (gaussianToComplex z) := by
  apply Complex.ext <;> simp [gaussianToComplex]

/-- Lift eight real chart coordinates to the corresponding four complex parameters. -/
def complexParameter (u : Fin 9 → ℝ) : Fin 4 → ℂ :=
  ![⟨u 0, u 1⟩, ⟨u 2, u 3⟩, ⟨u 4, u 5⟩, ⟨u 6, u 7⟩]

private def rayAmplitude (u : Fin 9 → ℝ) : Fin 8 → ℂ :=
  let q := complexParameter u
  chart (q 3) (q 0) (q 1) 1 (q 2)

private theorem map_chart {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s x y z w : R) :
    f ∘ chart s x y z w = chart (f s) (f x) (f y) (f z) (f w) := by
  funext i
  fin_cases i <;> simp [chart, shear, aligned, map_ofNat]

private theorem gaussian_amplitude (u : Fin 9 → ℝ) :
    gaussianToComplex ∘ amplitude u = rayAmplitude u := by
  rw [amplitude, map_chart, map_one]
  rfl

private theorem gaussian_entry (u : Fin 9 → ℝ) (i j : Fin 4) :
    gaussianToComplex (entry u i j) = (u 8 : ℝ) • gram (rayAmplitude u) i j := by
  have he (a : Fin 4) (b : Fin 8) :
      gaussianToComplex (flatten (amplitude u) a b) = flatten (rayAmplitude u) a b := by
    rw [← gaussian_amplitude]
    fin_cases a <;> fin_cases b <;> rfl
  simp only [entry, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, map_mul, map_sum,
    gaussianToComplex_star, he, Complex.star_def, Complex.real_smul]
  rfl

/-- The polynomial used in the jet computation is the physical raw density with its free gain. -/
theorem raw_eq_entries (u : Fin 9 → ℝ) :
    raw u = entries (u 8 • gram (rayAmplitude u)) := by
  funext j
  fin_cases j <;>
    first
    | exact congrArg Complex.re (gaussian_entry u _ _)
    | exact congrArg Complex.im (gaussian_entry u _ _)

/-- Trace in the ten real coordinates of a raw matrix. -/
def rawTrace (r : Fin 10 → ℝ) : ℝ := r 0 + 2 * r 5 + r 9

/-- Normalization keeps the nine coordinates independent of the trace. -/
def normalizeEntries (r : Fin 10 → ℝ) : Fin 9 → ℝ :=
  fun i => r i.castSucc / rawTrace r

/-- Recover a raw observation given its trace and nine normalized coordinates. -/
def restoreEntries (t : ℝ) (v : Fin 9 → ℝ) : Fin 10 → ℝ :=
  Fin.lastCases (t * (1 - v 0 - 2 * v 5)) (fun i => t * v i)

theorem trace_restore (t : ℝ) (v : Fin 9 → ℝ) : rawTrace (restoreEntries t v) = t := by
  unfold rawTrace restoreEntries
  simp only [show (0 : Fin 10) = (0 : Fin 9).castSucc from rfl,
    show (5 : Fin 10) = (5 : Fin 9).castSucc from rfl,
    show (9 : Fin 10) = Fin.last 9 from rfl, Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

theorem normalize_restore {t : ℝ} (ht : t ≠ 0) (v : Fin 9 → ℝ) :
    normalizeEntries (restoreEntries t v) = v := by
  funext i
  simp only [normalizeEntries, trace_restore, restoreEntries, Fin.lastCases_castSucc]
  exact mul_div_cancel_left₀ _ ht

theorem restore_normalize (r : Fin 10 → ℝ) (h : rawTrace r ≠ 0) :
    restoreEntries (rawTrace r) (normalizeEntries r) = r := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoreEntries, normalizeEntries, Fin.lastCases_last]
    field_simp [h]
    simp only [rawTrace]
    change r 0 + 2 * r 5 + r 9 - r 0 - 2 * r 5 = r 9
    ring
  · simp only [restoreEntries, normalizeEntries, Fin.lastCases_castSucc]
    exact mul_div_cancel₀ _ h

private theorem entries_smul (r : ℝ) (M : Marginal) :
    entries (r • M) = r • entries M := by
  funext i
  fin_cases i <;> simp [entries, Matrix.smul_apply, Complex.smul_re, Complex.smul_im,
    Pi.smul_apply]

theorem raw_trace_eq (u : Fin 9 → ℝ) :
    rawTrace (raw u) = u 8 * PeriodicMPSFiveSiteNormalization.mass (rayAmplitude u) := by
  rw [raw_eq_entries]
  have h := trace_re_mem (scale_mem (gram_mem (rayAmplitude u)) (u 8))
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at h
  exact h.symm

theorem raw_measured_eq (u : Fin 9 → ℝ) (hg : u 8 ≠ 0) :
    normalizeEntries (raw u) =
      measured (affine (complexParameter u 0) (complexParameter u 1)
        (complexParameter u 2) (complexParameter u 3)) := by
  let p := rayAmplitude u
  have hp : p ≠ 0 := chart_ne_zero _ _ _ _
  have hm := (mass_positive p hp).ne'
  have he := observation_of_projector hp
    (x := affine (complexParameter u 0) (complexParameter u 1)
      (complexParameter u 2) (complexParameter u 3)) rfl
  funext i
  unfold normalizeEntries
  rw [raw_trace_eq]
  simp only [raw_eq_entries, measured, he, normalizedGram,
    entries_smul, Pi.smul_apply, smul_eq_mul]
  change (u 8 * entries (gram p) i.castSucc) /
    (u 8 * PeriodicMPSFiveSiteNormalization.mass p) =
      (PeriodicMPSFiveSiteNormalization.mass p)⁻¹ * entries (gram p) i.castSucc
  field_simp

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSitePhysicalObservation
