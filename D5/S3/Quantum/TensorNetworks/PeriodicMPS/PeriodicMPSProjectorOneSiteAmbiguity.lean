/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSOneSiteAmbiguity, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization]
   utility: none
   digest: Generic ambiguity of the trace-one single-site density in the compact projector model. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSOneSiteAmbiguity
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization

/-!
# One-site ambiguity in the compact projector model

For the periodic binary bond-two trace parametrization, see Andrew Critch and
Jason Morton, *Algebraic Geometry of Matrix Product States*, §1 and §3,
SIGMA 10 (2014), 095, doi:10.3842/SIGMA.2014.095. Here the observation is the normalized one-site density
obtained by tracing the same projector used for the adjacent-pair observation.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectorOneSiteAmbiguity

open Set Filter Matrix
open scoped Matrix Kronecker Topology
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_cons)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSOneSiteAmbiguity
  (rawOne defect amplitudeTwo actual_locus_open_dense arbitrarily_close_one_site_collisions)
open PeriodicMPSProjectiveCoordinates (mass mass_pos projector continuousAt_projector)
open PeriodicMPSUniformHardCoreMarginalWitness (Pair Amplitudes pairGram pairGram_traceWord)
open PeriodicMPSUniformHardCoreLocalization
  (StateMatrix twoSiteObservation continuous_twoSiteObservation twoSiteObservation_projector
    actualProjectors)
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

/-- The single-site observation on the same projector space as the adjacent-pair observation. -/
def oneSiteObservation (m : ℕ) (P : StateMatrix m) : Bond :=
  partialTraceRight (twoSiteObservation m P)

private lemma partialTraceRight_smul_real (a : ℝ) (G : Matrix Pair Pair ℂ) :
    partialTraceRight (a • G) = a • partialTraceRight G := by
  ext i j
  simp only [partialTraceRight, Matrix.smul_apply, Finset.smul_sum]

private lemma defect_smul_real (a : ℝ) (G : Matrix Pair Pair ℂ) :
    defect (a • G) = a ^ 2 • defect G := by
  simp only [defect, partialTraceRight_smul_real, smul_kronecker, kronecker_smul,
    ← smul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, smul_sub]

private lemma continuous_partialTraceRight :
    Continuous (partialTraceRight : Matrix Pair Pair ℂ → Bond) :=
  continuous_matrix fun i j => continuous_finsetSum _ fun k _ =>
    (continuous_apply (j, k)).comp (continuous_apply (i, k))

private lemma continuous_defect : Continuous defect := by
  have h : Continuous (fun G : Matrix Pair Pair ℂ =>
      partialTraceRight G ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ partialTraceRight G) :=
    continuous_matrix fun i j =>
      ((continuous_partialTraceRight.matrix_elem i.1 j.1).mul continuous_const).add
        (continuous_const.mul (continuous_partialTraceRight.matrix_elem i.2 j.2))
  exact (h.matrix_mul continuous_id).sub (continuous_id.matrix_mul h)

private lemma continuous_traceWord (n : ℕ) : Continuous (traceWord 2 2 n) := by
  have hw {k : ℕ} (w : Word k) : Continuous (fun A : Fin 2 → Bond => wordMatrix A w) := by
    induction k with
    | zero => simpa [wordMatrix, List.ofFn_zero] using
        (continuous_const : Continuous (fun _ : Fin 2 → Bond => (1 : Bond)))
    | succ k ih =>
      rw [← Fin.cons_self_tail w]
      simp only [wordMatrix_cons]
      exact (continuous_apply (w 0)).matrix_mul (ih (Fin.tail w))
  refine continuous_pi fun w => ?_
  change Continuous (fun A : Fin 2 → Bond => ∑ i : Fin 2, wordMatrix A w i i)
  exact continuous_finsetSum _ fun i _ => (hw w).matrix_elem i i

private lemma trace_pairGram {m : ℕ} (ψ : Amplitudes m) :
    (pairGram ψ).trace = (mass ψ : ℂ) := by
  have hre : (pairGram ψ).trace.re = mass ψ :=
    (PeriodicMPSUniformHardCoreMarginalWitness.mass_eq_trace ψ).symm
  rw [← hre]
  simp only [Matrix.trace, Matrix.diag_apply, pairGram, Complex.star_def, Complex.mul_conj,
    ← Complex.ofReal_sum, Complex.ofReal_re]

private lemma trace_rawOne (r : ℕ) (A : Fin 2 → Bond) :
    (rawOne A r).trace = (mass (traceWord 2 2 (2 + (r + 2)) A) : ℂ) := by
  rw [rawOne, trace_partialTraceRight, ← pairGram_traceWord, trace_pairGram]

private lemma twoSiteObservation_amplitude (r : ℕ) (ψ : Amplitudes (r + 2)) :
    twoSiteObservation (r + 2) (projector ψ) = (mass ψ)⁻¹ • amplitudeTwo r ψ := by
  rw [twoSiteObservation_projector]
  rfl

private lemma twoSiteObservation_raw (r : ℕ) (A : Fin 2 → Bond) :
    twoSiteObservation (r + 2) (projector (traceWord 2 2 (2 + (r + 2)) A)) =
      (mass (traceWord 2 2 (2 + (r + 2)) A))⁻¹ • rawTwo A r :=
  twoSiteObservation_amplitude r _

/-- The single-site observation has trace one throughout the compact model. -/
theorem trace_oneSiteObservation_of_mem_closure (m : ℕ) {P : StateMatrix m}
    (hP : P ∈ closure (actualProjectors m)) : (oneSiteObservation m P).trace = 1 := by
  have hobs : Continuous (oneSiteObservation m) :=
    continuous_partialTraceRight.comp (continuous_twoSiteObservation m)
  have htrace : Continuous (fun Q : StateMatrix m => (oneSiteObservation m Q).trace) :=
    continuous_finsetSum _ fun i _ => hobs.matrix_elem i i
  refine closure_minimal ?_ (isClosed_eq htrace continuous_const) hP
  rintro _ ⟨A, hA, rfl⟩
  change (partialTraceRight (twoSiteObservation m (projector _))).trace = 1
  rw [trace_partialTraceRight, twoSiteObservation_projector, Matrix.trace_smul, trace_pairGram,
    Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (mass_pos _ hA).ne',
    Complex.ofReal_one]

set_option maxHeartbeats 400000 in
/-- At every ring length at least four, the nonzero commutator of the normalized
adjacent-pair observation defines a relatively open dense locus in the compact
projector closure. Each actual projector on that locus is in the relative closure
of the other actual projectors with the same normalized single-site observation. -/
theorem generic_projector_one_site_ambiguity (r : ℕ) :
    let X := closure (actualProjectors (r + 2))
    let G := {P : X | defect (twoSiteObservation (r + 2) P.val) ≠ 0}
    G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      ∀ P ∈ G, P.val ∈ actualProjectors (r + 2) →
        P ∈ closure {Q : X | Q.val ∈ actualProjectors (r + 2) ∧ Q ≠ P ∧
          oneSiteObservation (r + 2) Q.val = oneSiteObservation (r + 2) P.val} := by
  let X := closure (actualProjectors (r + 2))
  let G : Set X := {P | defect (twoSiteObservation (r + 2) P.val) ≠ 0}
  let F := traceWord 2 2 (2 + (r + 2))
  let Y := Set.range F
  let H : Set Y := {ψ | defect (amplitudeTwo r ψ.val) ≠ 0}
  obtain ⟨hne, _, hdense⟩ := actual_locus_open_dense r
  have image_mem (ψ : Y) (hψ : ψ ∈ H) : projector ψ.val ∈ Subtype.val '' G := by
    have hn : ψ.val ≠ 0 := by
      intro hz
      apply hψ
      rw [hz]
      change defect ((0 : Matrix Pair (Word (r + 2)) ℂ) * 0ᴴ) = 0
      simp [defect]
    have ha : projector ψ.val ∈ actualProjectors (r + 2) := by
      obtain ⟨A, hA⟩ := ψ.property
      refine ⟨A, ?_, congrArg projector hA⟩
      change F A ≠ 0
      rwa [hA]
    refine ⟨⟨_, subset_closure ha⟩, ?_, rfl⟩
    change defect (twoSiteObservation (r + 2) (projector ψ.val)) ≠ 0
    rw [twoSiteObservation_amplitude, defect_smul_real]
    exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero (mass_pos _ hn).ne')) hψ
  have hcover : actualProjectors (r + 2) ⊆ closure (Subtype.val '' G) := by
    rintro _ ⟨A, hA, rfl⟩
    let ψ : Y := ⟨F A, A, rfl⟩
    have hv : ContinuousAt (fun χ : Y => χ.val) ψ := continuous_subtype_val.continuousAt
    have hc : ContinuousAt (fun χ : Y => projector χ.val) ψ :=
      (continuousAt_projector (p := ψ.val) hA).comp hv
    have hsubset : (fun χ : Y => projector χ.val) '' H ⊆ Subtype.val '' G := by
      rintro _ ⟨χ, hχ, rfl⟩
      exact image_mem χ hχ
    change projector ψ.val ∈ closure (Subtype.val '' G)
    exact closure_mono hsubset (mem_closure_image (x := ψ) hc (hdense ψ))
  obtain ⟨ψ, hψ⟩ := hne
  obtain ⟨P₀, hP₀, _⟩ := image_mem ψ hψ
  refine ⟨⟨P₀, hP₀⟩, isOpen_ne_fun
    (continuous_defect.comp ((continuous_twoSiteObservation _).comp continuous_subtype_val))
    continuous_const, Subtype.dense_iff.mpr (closure_minimal hcover isClosed_closure), ?_⟩
  intro P hP hactual
  obtain ⟨A, hA, hproj⟩ := hactual
  have hraw : defect (rawTwo A r) ≠ 0 := by
    intro hz
    apply hP
    rw [← hproj, twoSiteObservation_raw, defect_smul_real, hz, smul_zero]
  obtain ⟨B, hB, hB0, hsame, hchange⟩ := arbitrarily_close_one_site_collisions A r hraw
  have hm (t : ℝ) : mass (F (B t)) = mass (F A) := by
    have ht := congrArg Matrix.trace (hsame t)
    rw [trace_rawOne, trace_rawOne] at ht
    exact Complex.ofReal_injective ht
  have hnonzero (t : ℝ) : F (B t) ≠ 0 := by
    intro hz
    have hp := mass_pos (F A) hA
    rw [← hm t, hz] at hp
    simp [mass] at hp
  let C (t : ℝ) : X := ⟨projector (F (B t)), subset_closure ⟨B t, hnonzero t, rfl⟩⟩
  have hC0 : C 0 = P := Subtype.ext (by change projector (F (B 0)) = P.val; rwa [hB0])
  have hlimit : Tendsto C (𝓝 0) (𝓝 P) := by
    rw [← hC0, tendsto_subtype_rng]
    have hFB : ContinuousAt (fun t : ℝ => F (B t)) 0 :=
      ((continuous_traceWord _).comp hB).continuousAt
    exact ContinuousAt.comp' (f := fun t : ℝ => F (B t))
      (continuousAt_projector (hnonzero 0)) hFB
  have hfreq : ∃ᶠ t in 𝓝 (0 : ℝ), rawTwo (B t) r ≠ rawTwo A r := by
    simpa only [Filter.Frequently, Filter.EventuallyEq, not_not] using hchange
  apply mem_closure_iff_frequently.mpr
  apply hlimit.frequently
  refine hfreq.mono fun t ht => ⟨⟨B t, hnonzero t, rfl⟩, ?_, ?_⟩
  · intro he
    have hp := congrArg (fun Q : X => twoSiteObservation (r + 2) Q.val) he
    change twoSiteObservation (r + 2) (projector (F (B t))) =
      twoSiteObservation (r + 2) P.val at hp
    rw [← hproj, twoSiteObservation_raw, twoSiteObservation_raw, hm t] at hp
    exact ht (smul_right_injective _ (inv_ne_zero (mass_pos (F A) hA).ne') hp)
  · change partialTraceRight (twoSiteObservation (r + 2) (projector (F (B t)))) =
      partialTraceRight (twoSiteObservation (r + 2) P.val)
    rw [← hproj, twoSiteObservation_raw, twoSiteObservation_raw, hm t,
      partialTraceRight_smul_real, partialTraceRight_smul_real]
    exact congrArg ((mass (F A))⁻¹ • ·) (hsame t)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectorOneSiteAmbiguity
