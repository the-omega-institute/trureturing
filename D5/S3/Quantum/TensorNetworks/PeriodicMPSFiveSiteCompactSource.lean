/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSource
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSource
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates]
   utility: none
   digest: The projective trace graph gives a compact source covering the actual five-site rays. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteNormalization
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates

/-! The graph retains the trace direction, the squared trace and determinant
pencil, and the resulting amplitude ray. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

open Set
open PeriodicMPSFiveSiteCoordinates PeriodicMPSProjectiveCoordinates
open PeriodicMPSFiveSiteSpecialFiber (gram)
open PeriodicMPSFiveSiteNormalization (normalizedGram mass_positive)

noncomputable section

/-- Trace direction, squared trace and determinant pencil, and necklace ray. -/
abbrev Ambient :=
  (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 6) (Fin 6) ℂ) × Matrix (Fin 8) (Fin 8) ℂ

/-- The invariant trace tuple of a nonzero state. -/
abbrev Inputs := {a : Fin 5 → ℂ | coordinates (a 0) (a 1) (a 2) (a 3) (a 4) ≠ 0}

private def traceDirection (a : Fin 5 → ℂ) : Fin 2 → ℂ := ![a 0, a 1]

private def pencil (a : Fin 5 → ℂ) : Fin 6 → ℂ :=
  ![a 0 ^ 2, a 0 * a 1, a 1 ^ 2, a 2, a 0 * a 1 - a 4, a 3]

private theorem either_trace_ne_zero (a : Inputs) : a.val 0 ≠ 0 ∨ a.val 1 ≠ 0 := by
  by_contra! h
  apply a.property
  funext i
  fin_cases i <;> simp [coordinates, h.1, h.2]

private theorem traceDirection_ne_zero (a : Inputs) : traceDirection a.val ≠ 0 := by
  intro h
  exact (either_trace_ne_zero a).elim
    (fun hn => hn (congrFun h 0)) (fun hn => hn (congrFun h 1))

private theorem pencil_ne_zero (a : Inputs) : pencil a.val ≠ 0 := by
  intro h
  exact (either_trace_ne_zero a).elim
    (fun hn => hn (sq_eq_zero_iff.mp (congrFun h 0)))
    (fun hn => hn (sq_eq_zero_iff.mp (congrFun h 2)))

/-- Point of the ordinary projective trace graph. -/
def ordinary (a : Inputs) : Ambient :=
  ((projector (traceDirection a.val), projector (pencil a.val)),
    projector (coordinates (a.val 0) (a.val 1) (a.val 2) (a.val 3) (a.val 4)))

/-- The compact source is the closure of the ordinary graph in the product
of three complex projective spaces. -/
def source : Set Ambient := closure (range ordinary)

theorem ordinary_mem_source (a : Inputs) : ordinary a ∈ source :=
  subset_closure (mem_range_self a)

theorem source_subset_projective :
    source ⊆ ((projective (ι := Fin 2) ×ˢ projective (ι := Fin 6)) ×ˢ
      projective (ι := Fin 8)) := by
  apply closure_minimal _ ((isCompact_projective.prod isCompact_projective).prod
    isCompact_projective).isClosed
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨projector_mem _ (traceDirection_ne_zero a), projector_mem _ (pencil_ne_zero a)⟩,
    projector_mem _ a.property⟩

theorem source_isCompact : IsCompact source :=
  ((isCompact_projective.prod isCompact_projective).prod isCompact_projective).of_isClosed_subset
    isClosed_closure source_subset_projective

theorem source_amplitude_projective {x : Ambient} (hx : x ∈ source) :
    x.2 ∈ projective :=
  (source_subset_projective hx).2

/-- The linear contraction of a necklace projector to the adjacent two-site
matrix. Repeated suffix terms carry their multiplicities through the sum. -/
def cut (P : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ k : Fin 8, P (flatten id i k) (flatten id j k)

private theorem cut_outer (p : Fin 8 → ℂ) : cut (outer p) = gram p := by
  have h (i : Fin 4) (k : Fin 8) : flatten p i k = p (flatten id i k) := by
    fin_cases i <;> fin_cases k <;> rfl
  ext i j
  simp only [cut, outer, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, h, Complex.star_def]

private theorem cut_scale (P : Matrix (Fin 8) (Fin 8) ℂ) (r : ℝ) :
    cut (r • P) = r • cut P := by
  ext i j
  simp [cut, Matrix.smul_apply, Finset.smul_sum]

private theorem continuous_cut : Continuous cut :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_finsetSum _ fun k _ =>
      (continuous_apply (flatten id j k)).comp (continuous_apply (flatten id i k))

private theorem continuous_cut_mass :
    Continuous (fun P : Matrix (Fin 8) (Fin 8) ℂ => (cut P).trace.re) := by
  have htrace : Continuous (fun P : Matrix (Fin 4) (Fin 4) ℂ => P.trace) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  exact Complex.continuous_re.comp (htrace.comp continuous_cut)

/-- The trace-one observation extends continuously to the compact source. -/
def observation (x : Ambient) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((cut x.2).trace.re)⁻¹ • cut x.2

theorem continuousOn_observation : ContinuousOn observation source := by
  have hpos (x : Ambient) (hx : x ∈ source) : 0 < (cut x.2).trace.re := by
    obtain ⟨p, hm, he⟩ := source_amplitude_projective hx
    have hp : p ≠ 0 := by
      intro hz
      have hm' : mass p = 1 := hm
      simp [mass, hz] at hm'
    rw [← he, cut_outer]
    exact mass_positive _ hp
  exact ((continuous_cut_mass.comp continuous_snd).continuousOn.inv₀
    (fun x hx => (hpos x hx).ne')).smul (continuous_cut.comp continuous_snd).continuousOn

theorem observation_of_projector {x : Ambient} {p : Fin 8 → ℂ} (hp : p ≠ 0)
    (hx : x.2 = projector p) : observation x = normalizedGram p := by
  unfold observation
  rw [hx]
  change ((cut (projector p)).trace.re)⁻¹ • cut (projector p) = normalizedGram p
  rw [projector, cut_scale, cut_outer, Matrix.trace_smul, Complex.smul_re, normalizedGram]
  simp only [smul_eq_mul, mul_inv, smul_smul]
  congr 1
  have hm := (mass_pos p hp).ne'
  rw [mul_right_comm, inv_inv, mul_inv_cancel₀ hm, one_mul]
  rfl

theorem observation_ordinary (a : Inputs) :
    observation (ordinary a) =
      normalizedGram (coordinates (a.val 0) (a.val 1) (a.val 2) (a.val 3) (a.val 4)) :=
  observation_of_projector a.property rfl

/-- Every actual nonzero five-site periodic bond-two state has a lift with the
same adjacent two-site observation. -/
theorem actual_state_lifts
    (A : Fin 2 → PeriodicMPSParentIntersection.Bond)
    (h : UniformMPSExpectedDimensionRefutation.traceWord 2 2 5 A ∘ necklaces ≠ 0) :
    let p := UniformMPSExpectedDimensionRefutation.traceWord 2 2 5 A ∘ necklaces
    ∃ x ∈ source, x.2 = projector p ∧ observation x = normalizedGram p := by
  let a : Fin 5 → ℂ := ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace]
  have ha : coordinates (a 0) (a 1) (a 2) (a 3) (a 4) ≠ 0 := by
    rw [trace_word_necklaces] at h
    exact h
  let u : Inputs := ⟨a, ha⟩
  dsimp only
  rw [trace_word_necklaces]
  exact ⟨ordinary u, ordinary_mem_source u, rfl, observation_ordinary u⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
