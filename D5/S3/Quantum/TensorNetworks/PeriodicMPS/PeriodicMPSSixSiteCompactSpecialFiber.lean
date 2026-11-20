/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSpecialFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSpecialFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional,
     lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialFiber]
   utility: none
   digest: The chosen adjacent marginal has two lifts in the compact trace graph. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialFiber

/-! The two actual lifts exhaust the compact fiber over the chosen observation. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactSpecialFiber

open Set
open PeriodicMPSSixSiteCompactSource PeriodicMPSSixSiteCompactExceptional
open PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal
open PeriodicMPSSixSiteInvariants PeriodicMPSSixSiteSpecialFiber
open PeriodicMPSProjectiveCoordinates
open PeriodicMPSParentIntersection (Bond)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped ComplexConjugate

noncomputable section

/-- Weight-two invariants in the nilpotent chart with mixed trace one. -/
def nilpotentInvariant (x y : ℂ) : Fin 6 → ℂ := ![x, 0, 0, y, 0, 1]

theorem amplitude_nilpotentInvariant (x y : ℂ) :
    amplitude (nilpotentInvariant x y) = nilpotentRay x y := by
  change coordinates x 0 0 y 0 1 = _
  rw [nilpotent_coordinates]
  simp [nilpotentRay, independentSlice]

private theorem nilpotentInvariant_input (x y : ℂ) :
    (nilpotentInvariant x y 1) ^ 2 = nilpotentInvariant x y 0 * nilpotentInvariant x y 2 ∧
      amplitude (nilpotentInvariant x y) ≠ 0 := by
  refine ⟨by simp [nilpotentInvariant], ?_⟩
  rw [amplitude_nilpotentInvariant]
  intro h
  have h9 : (1 : ℂ) = 0 := congrFun h 9
  exact one_ne_zero h9

/-- The compact lift of an actual nilpotent-chart representative. -/
def point (x y : ℂ) : Ambient := graphPoint (nilpotentInvariant x y)

theorem point_mem_source (x y : ℂ) : point x y ∈ source :=
  ordinary_mem_source ⟨nilpotentInvariant x y, nilpotentInvariant_input x y⟩

theorem observation_point (x y : ℂ) :
    observation (point x y) = normalizedGram (nilpotentRay x y) := by
  have h := observation_ordinary ⟨nilpotentInvariant x y, nilpotentInvariant_input x y⟩
  change observation (point x y) = normalizedGram (amplitude (nilpotentInvariant x y)) at h
  rwa [amplitude_nilpotentInvariant] at h

/-- The trace-normalized observation coinciding at the two special lifts. -/
def target : Matrix (Fin 4) (Fin 4) ℂ := normalizedGram (nilpotentRay 1 Complex.I)

private theorem special_gram_entries :
    gram (nilpotentRay 1 Complex.I) 3 3 = 0 ∧
      gram (nilpotentRay 1 Complex.I) 1 1 = 15 ∧
      gram (nilpotentRay 1 Complex.I) 1 2 = 11 := by
  rw [nilpotentRay]
  refine ⟨(independent_gram _ _ _ _ _).2.2.2.2, ?_, ?_⟩
  · rw [(independent_gram _ _ _ _ _).2.2.1]
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, pow_succ]
  · rw [(independent_gram _ _ _ _ _).2.2.2.1]
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, pow_succ]

private theorem target_properties :
    target 3 3 = 0 ∧ target 1 1 ≠ 0 ∧ target 1 1 ≠ target 1 2 := by
  obtain ⟨h₀, h₁, h₂⟩ := special_gram_entries
  have hp : nilpotentRay 1 Complex.I ≠ 0 := by
    intro h
    exact one_ne_zero (show (1 : ℂ) = 0 from congrFun h 9)
  have hr := inv_ne_zero (gram_mass_pos _ hp).ne'
  simp only [target, normalizedGram, Matrix.smul_apply, h₀, h₁, h₂, smul_zero]
  exact ⟨trivial, smul_ne_zero hr (by norm_num),
    fun h => (show (15 : ℂ) ≠ 11 by norm_num) (smul_right_injective ℂ hr h)⟩

private theorem normalized_gain {p : Fin 14 → ℂ} (h : normalizedGram p = target) :
    ((gram (nilpotentRay 1 Complex.I)).trace.re * ((gram p).trace.re)⁻¹) • gram p =
      gram (nilpotentRay 1 Complex.I) := by
  have hp : nilpotentRay 1 Complex.I ≠ 0 := by
    intro hzero
    exact one_ne_zero (show (1 : ℂ) = 0 from congrFun hzero 9)
  change ((gram p).trace.re)⁻¹ • gram p =
    ((gram (nilpotentRay 1 Complex.I)).trace.re)⁻¹ • gram (nilpotentRay 1 Complex.I) at h
  rw [← smul_smul, h, smul_smul, mul_inv_cancel₀ (gram_mass_pos _ hp).ne', one_smul]

private theorem input_over_target (q : Inputs) (h : observation (ordinary q) = target) :
    ordinary q = point 1 Complex.I ∨
      ordinary q = point secondPhase (secondPhase * (-Complex.I)) := by
  obtain ⟨A, hA⟩ := exists_actual_invariants q.val q.property.1
  let p := traceWord 2 2 6 A ∘ necklaces
  have hp : p = amplitude q.val := by
    change traceWord 2 2 6 A ∘ necklaces = amplitude q.val
    rw [← amplitude_invariants, hA]
  have hpne : p ≠ 0 := hp.symm ▸ q.property.2
  have hne : traceWord 2 2 6 A ≠ 0 := by
    intro he
    apply hpne
    funext i
    exact congrFun he (necklaces i)
  have hm : normalizedGram p = target := by
    rw [hp, ← observation_ordinary q]
    exact h
  have hcorner : gram p 3 3 = 0 := by
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 3 3) hm
    rw [target_properties.1] at he
    change ((gram p).trace.re)⁻¹ • gram p 3 3 = 0 at he
    exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero (gram_mass_pos p hpne).ne')
  have hsingle : gram p 1 1 ≠ 0 := by
    intro he
    have hs := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 1 1) hm
    change ((gram p).trace.re)⁻¹ • gram p 1 1 = target 1 1 at hs
    rw [he, smul_zero] at hs
    exact target_properties.2.1 hs.symm
  obtain ⟨hs, he⟩ := trace_det_second_eq_zero A hne hcorner
  let t := (A 0).trace
  let d := (A 0).det
  let k := (A 0 * A 1).trace
  have hp' : p = coordinates (t ^ 2) 0 0 d 0 k := by
    dsimp [p]
    rw [trace_word_necklaces, hs, he, mul_zero, zero_pow (by decide : 2 ≠ 0)]
  have hk : k ≠ 0 := by
    intro hz
    apply hsingle
    rw [hp', nilpotent_coordinates, hz]
    simp [gram, flatten, necklaceTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
  let x := t ^ 2 / k
  let y := d / k
  have hq : q.val = k • nilpotentInvariant x y := by
    rw [← hA]
    funext i
    fin_cases i <;> simp [invariants, nilpotentInvariant, hs, he, x, y, t, d, k,
      Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hk]
  have hray : p = k ^ 3 • nilpotentRay x y := by
    rw [hp, hq, amplitude_scale, amplitude_nilpotentInvariant]
  have hg := normalized_gain hm
  rw [hray, gram_scale, smul_smul] at hg
  have hpoint : ordinary q = point x y := by
    change graphPoint q.val = graphPoint (nilpotentInvariant x y)
    rw [hq, graphPoint_scale _ hk]
  rcases specialChart hg with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl (by simpa only [hx, hy] using hpoint)
  · exact Or.inr (by rw [hpoint, hy, hx])

/-- The entire compact fiber comprises precisely the two stated source points. -/
theorem observation_eq_target_iff {x : Ambient} (hx : x ∈ source) :
    observation x = target ↔
      x = point 1 Complex.I ∨ x = point secondPhase (secondPhase * (-Complex.I)) := by
  constructor
  · intro h
    obtain ⟨q, hq, houter⟩ := source_invariant_projective hx
    have hmass : mass q = 1 := hq
    have hproj : x.1 = projector q := by rw [projector, hmass, inv_one, one_smul, houter]
    have ha : amplitude q ≠ 0 := by
      intro hzero
      have he := exceptional_observation_difference_eq_zero hx hproj hzero
        (by rw [h, target_properties.1])
      rw [h] at he
      exact target_properties.2.2 he
    obtain ⟨j, hj⟩ : ∃ j : Fin 6, q j ≠ 0 := by
      by_contra! hz
      have hzero : q = 0 := funext hz
      simp [hzero, mass] at hmass
    have hquad : q 1 ^ 2 = q 0 * q 2 := by
      have he := source_quadric_column hx j
      rw [← houter] at he
      simp only [outer, mul_pow] at he
      apply mul_right_cancel₀ (pow_ne_zero 2 ((map_ne_zero (starRingEnd ℂ)).2 hj))
      linear_combination he
    have hx' : x = ordinary ⟨q, hquad, ha⟩ := eq_graphPoint_of_amplitude_ne_zero hx hproj ha
    rw [hx'] at h ⊢
    exact input_over_target _ h
  · rintro (rfl | rfl)
    · exact observation_point 1 Complex.I
    · rw [observation_point, normalizedGram, secondPhase_same_gram]
      rfl

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactSpecialFiber
