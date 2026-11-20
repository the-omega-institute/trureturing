/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSource
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSource
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates,
     lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal]
   utility: none
   digest: The compact six-site trace graph carries the normalized adjacent two-site marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal

/-! The first projector records the weight-two tuple `(T, S, U, d, e, k)`
with `S² = T U`. The second records the fourteen cyclic amplitudes.
The compact source is the closure of the graph on the nonvanishing locus. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactSource

open Set
open PeriodicMPSParentIntersection (Bond)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSProjectiveCoordinates PeriodicMPSSixSiteCoordinates
open PeriodicMPSSixSiteMarginal (necklaceTable flatten gram flatten_gram prefixBits)
open scoped ComplexConjugate

noncomputable section

abbrev Ambient := Matrix (Fin 6) (Fin 6) ℂ × Matrix (Fin 14) (Fin 14) ℂ

/-- The weight-two trace invariants of a binary bond-two presentation. -/
def invariants (A : Fin 2 → Bond) : Fin 6 → ℂ :=
  ![(A 0).trace ^ 2, (A 0).trace * (A 1).trace, (A 1).trace ^ 2,
    (A 0).det, (A 1).det, (A 0 * A 1).trace]

theorem invariants_quadric (A : Fin 2 → Bond) :
    invariants A 1 ^ 2 = invariants A 0 * invariants A 2 := by
  change ((A 0).trace * (A 1).trace) ^ 2 = (A 0).trace ^ 2 * (A 1).trace ^ 2
  exact mul_pow _ _ _

private theorem exists_traces (q : Fin 6 → ℂ) (hq : q 1 ^ 2 = q 0 * q 2) :
    ∃ t s : ℂ, t ^ 2 = q 0 ∧ t * s = q 1 ∧ s ^ 2 = q 2 := by
  by_cases h₀ : q 0 = 0
  · have h₁ : q 1 = 0 :=
      sq_eq_zero_iff.mp (by simpa only [h₀, zero_mul] using hq)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (q 2) (n := 2) (by decide)
    exact ⟨0, s, by simp [h₀], by simp [h₁], hs⟩
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (q 0) (n := 2) (by decide)
    have ht₀ : t ≠ 0 := fun h => h₀ (by simpa [h] using ht.symm)
    refine ⟨t, q 1 / t, ht, ?_, ?_⟩
    · rw [mul_comm, div_mul_cancel₀ _ ht₀]
    · rw [div_pow, ht, hq, mul_comm (q 0) (q 2), mul_div_cancel_right₀ _ h₀]

/-- Every representative on the weight-two quadric has an actual presentation. -/
theorem exists_actual_invariants (q : Fin 6 → ℂ) (hq : q 1 ^ 2 = q 0 * q 2) :
    ∃ A : Fin 2 → Bond, invariants A = q := by
  obtain ⟨t, s, ht, hts, hs⟩ := exists_traces q hq
  obtain ⟨A, hA₀, hA₁, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates t s (q 3) (q 4) (q 5)
  refine ⟨A, ?_⟩
  funext i
  fin_cases i <;> simp [invariants, hA₀, hA₁, hd, he, hk, ht, hts, hs]

/-- The cubic amplitude map in the weight-two coordinates. -/
def amplitude (q : Fin 6 → ℂ) : Fin 14 → ℂ :=
  coordinates (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)

theorem amplitude_invariants (A : Fin 2 → Bond) :
    amplitude (invariants A) = traceWord 2 2 6 A ∘ necklaces :=
  (trace_word_necklaces A).symm

theorem amplitude_scale (z : ℂ) (q : Fin 6 → ℂ) :
    amplitude (z • q) = z ^ 3 • amplitude q :=
  coordinates_scale z (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)

private theorem amplitude_zero : amplitude 0 = 0 := by
  funext i
  fin_cases i <;> simp [amplitude, coordinates]

private theorem continuous_amplitude : Continuous amplitude := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> dsimp only [amplitude, coordinates] <;> fun_prop

/-- Nonzero projective inputs with a defined amplitude ray. -/
abbrev Inputs := {q : Fin 6 → ℂ | q 1 ^ 2 = q 0 * q 2 ∧ amplitude q ≠ 0}

/-- Projectors of the invariant tuple and its cubic amplitude. -/
def graphPoint (q : Fin 6 → ℂ) : Ambient := (projector q, projector (amplitude q))

theorem graphPoint_scale (q : Fin 6 → ℂ) {z : ℂ} (hz : z ≠ 0) :
    graphPoint (z • q) = graphPoint q := by
  simp only [graphPoint, amplitude_scale, projector_scale q hz,
    projector_scale (amplitude q) (pow_ne_zero 3 hz)]

/-- Point of the ordinary projective graph. -/
def ordinary (q : Inputs) : Ambient := graphPoint q.val

/-- Compactification in the two projector spaces with coordinate sizes six and fourteen. -/
def source : Set Ambient := closure (range ordinary)

theorem ordinary_mem_source (q : Inputs) : ordinary q ∈ source :=
  subset_closure (mem_range_self q)

theorem source_subset_projective :
    source ⊆ projective (ι := Fin 6) ×ˢ projective (ι := Fin 14) := by
  apply closure_minimal _ (isCompact_projective.prod isCompact_projective).isClosed
  rintro _ ⟨q, rfl⟩
  have hq : q.val ≠ 0 := by
    intro h
    exact q.property.2 ((congrArg amplitude h).trans amplitude_zero)
  exact ⟨projector_mem _ hq, projector_mem _ q.property.2⟩

theorem source_isCompact : IsCompact source :=
  (isCompact_projective.prod isCompact_projective).of_isClosed_subset
    isClosed_closure source_subset_projective

theorem source_invariant_projective {x : Ambient} (hx : x ∈ source) : x.1 ∈ projective :=
  (source_subset_projective hx).1

theorem source_amplitude_projective {x : Ambient} (hx : x ∈ source) : x.2 ∈ projective :=
  (source_subset_projective hx).2

/-- The graph point computed from an actual binary bond-two presentation. -/
def actualPoint (A : Fin 2 → Bond) : Ambient :=
  (projector (invariants A), projector (traceWord 2 2 6 A ∘ necklaces))

theorem actualPoint_eq_graphPoint (A : Fin 2 → Bond) :
    actualPoint A = graphPoint (invariants A) := by
  rw [actualPoint, graphPoint, amplitude_invariants]

/-- Every ordinary point is realized, and the graph includes every nonzero actual amplitude. -/
theorem range_ordinary_eq_actual :
    range ordinary = {x | ∃ A : Fin 2 → Bond,
      traceWord 2 2 6 A ∘ necklaces ≠ 0 ∧ actualPoint A = x} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨A, hA⟩ := exists_actual_invariants q.val q.property.1
    have hp : traceWord 2 2 6 A ∘ necklaces = amplitude q.val := by
      rw [← amplitude_invariants, hA]
    refine ⟨A, ?_, ?_⟩
    · rw [hp]
      exact q.property.2
    · simp only [actualPoint_eq_graphPoint, hA, ordinary]
  · rintro ⟨A, hp, rfl⟩
    refine ⟨⟨invariants A, invariants_quadric A, ?_⟩, (actualPoint_eq_graphPoint A).symm⟩
    rw [amplitude_invariants]
    exact hp

theorem actualPoint_mem_source (A : Fin 2 → Bond) (hp : traceWord 2 2 6 A ∘ necklaces ≠ 0) :
    actualPoint A ∈ source := by
  change actualPoint A ∈ closure (range ordinary)
  refine subset_closure ?_
  rw [range_ordinary_eq_actual]
  exact ⟨A, hp, rfl⟩

/-- Every nonzero point on the traceless plane has a defined cubic ray. -/
theorem amplitude_ne_zero_of_traceless {q : Fin 6 → ℂ} (hq : q ≠ 0)
    (hT : q 0 = 0) (hS : q 1 = 0) (hU : q 2 = 0) : amplitude q ≠ 0 := by
  intro hp
  have hz : coordinates 0 0 0 (q 3) (q 4) (q 5) = 0 := by
    simpa only [amplitude, hT, hS, hU] using hp
  obtain ⟨hd, he, hk⟩ := traceless_eq_zero_iff.mp hz
  apply hq
  funext i
  fin_cases i <;> first | exact hT | exact hS | exact hU | exact hd | exact he | exact hk

private theorem continuous_invariant_column (c : Fin 6) :
    Continuous (fun x : Ambient => fun i => x.1 i c) :=
  continuous_pi fun i =>
    (continuous_apply c).comp ((continuous_apply i).comp continuous_fst)

private theorem continuous_amplitude_entry (k l : Fin 14) :
    Continuous (fun x : Ambient => x.2 k l) :=
  (continuous_apply l).comp ((continuous_apply k).comp continuous_snd)

private theorem projector_column {n : ℕ} (q : Fin n → ℂ) (c : Fin n) :
    (fun i => projector q i c) = ((↑((mass q)⁻¹) : ℂ) * conj (q c)) • q := by
  funext i
  simp only [projector, outer, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Each invariant projector column lies on the weight-two quadric. -/
theorem source_quadric_column {x : Ambient} (hx : x ∈ source) (c : Fin 6) :
    x.1 1 c ^ 2 = x.1 0 c * x.1 2 c := by
  have hcont (i : Fin 6) : Continuous (fun y : Ambient => y.1 i c) :=
    (continuous_apply i).comp (continuous_invariant_column c)
  refine closure_minimal (s := range ordinary)
    (t := {y : Ambient | y.1 1 c ^ 2 = y.1 0 c * y.1 2 c}) ?_
    (isClosed_eq ((hcont 1).pow 2) ((hcont 0).mul (hcont 2))) hx
  rintro _ ⟨q, rfl⟩
  let v : Fin 6 → ℂ := fun i => projector q.val i c
  change v 1 ^ 2 = v 0 * v 2
  have hv : v = ((↑((mass q.val)⁻¹) : ℂ) * conj (q.val c)) • q.val :=
    projector_column q.val c
  rw [hv]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, q.property.1]
  ring

set_option maxHeartbeats 1200000 in
-- Elaborate two continuous compositions in the finite matrix coordinates.
/-- At a compact limit the cubic of an invariant column and each amplitude
column satisfy the projective graph incidence. These equations determine the
amplitude ray wherever the cubic is nonzero. -/
theorem source_amplitude_incidence {x : Ambient} (hx : x ∈ source)
    (c : Fin 6) (i j k : Fin 14) :
    amplitude (fun a => x.1 a c) i * x.2 j k =
      amplitude (fun a => x.1 a c) j * x.2 i k := by
  have hcont (l : Fin 14) :
      Continuous (fun y : Ambient => amplitude (fun a => y.1 a c) l) := by
    change Continuous (((fun p : Fin 14 → ℂ => p l) ∘ amplitude) ∘
      fun y : Ambient => fun a => y.1 a c)
    exact ((continuous_apply l).comp continuous_amplitude).comp (continuous_invariant_column c)
  refine closure_minimal (s := range ordinary)
    (t := {y : Ambient | amplitude (fun a => y.1 a c) i * y.2 j k =
      amplitude (fun a => y.1 a c) j * y.2 i k}) ?_
    (isClosed_eq ((hcont i).mul (continuous_amplitude_entry j k))
      ((hcont j).mul (continuous_amplitude_entry i k))) hx
  rintro _ ⟨q, rfl⟩
  change amplitude (fun a => projector q.val a c) i * projector (amplitude q.val) j k =
    amplitude (fun a => projector q.val a c) j * projector (amplitude q.val) i k
  rw [projector_column, amplitude_scale]
  simp only [projector, outer, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Linear contraction with one term per suffix in the literal six-site table. -/
def cut (P : Matrix (Fin 14) (Fin 14) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ k : Fin 16, P (necklaceTable i k) (necklaceTable j k)

theorem cut_outer (p : Fin 14 → ℂ) : cut (outer p) = gram p := by
  ext i j
  simp only [cut, outer, gram, flatten, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def]

private theorem cut_scale (P : Matrix (Fin 14) (Fin 14) ℂ) (r : ℝ) :
    cut (r • P) = r • cut P := by
  ext i j
  simp [cut, Matrix.smul_apply, Finset.smul_sum]

/-- Every necklace label has a prefix and suffix witness in the literal table. -/
theorem necklaceTable_surjective (n : Fin 14) :
    ∃ i : Fin 4, ∃ k : Fin 16, necklaceTable i k = n := by
  fin_cases n
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 5, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 11, rfl⟩
  · exact ⟨0, 13, rfl⟩
  · exact ⟨0, 15, rfl⟩
  · exact ⟨1, 5, rfl⟩
  · exact ⟨1, 7, rfl⟩
  · exact ⟨1, 11, rfl⟩
  · exact ⟨1, 15, rfl⟩
  · exact ⟨3, 15, rfl⟩

private theorem gram_trace (p : Fin 14 → ℂ) :
    (gram p).trace = (↑(∑ i : Fin 4, ∑ k : Fin 16, Complex.normSq (flatten p i k)) : ℂ) := by
  simp only [gram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Complex.mul_conj _

theorem gram_mass_pos (p : Fin 14 → ℂ) (hp : p ≠ 0) : 0 < (gram p).trace.re := by
  rw [gram_trace, Complex.ofReal_re]
  have hrow (i : Fin 4) : 0 ≤ ∑ k : Fin 16, Complex.normSq (flatten p i k) :=
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hrow i)
  intro hzero
  apply hp
  funext n
  obtain ⟨i, k, hnk⟩ := necklaceTable_surjective n
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrow i)).mp hzero.symm
    i (Finset.mem_univ _)
  have hk := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (flatten p i k))).mp hi k (Finset.mem_univ _)
  change p n = 0
  rw [← hnk]
  exact Complex.normSq_eq_zero.mp hk

/-- The physical normalization denominator is positive at every compact lift. -/
theorem cut_mass_pos {x : Ambient} (hx : x ∈ source) : 0 < (cut x.2).trace.re := by
  obtain ⟨p, hp, he⟩ := source_amplitude_projective hx
  have hne : p ≠ 0 := by
    intro hz
    have hm : mass p = 1 := hp
    simp [mass, hz] at hm
  rw [← he, cut_outer]
  exact gram_mass_pos p hne

private theorem continuous_cut : Continuous cut :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_finsetSum _ fun k _ =>
      (continuous_apply (necklaceTable j k)).comp (continuous_apply (necklaceTable i k))

private theorem continuous_cut_mass :
    Continuous (fun P : Matrix (Fin 14) (Fin 14) ℂ => (cut P).trace.re) := by
  have htrace : Continuous (fun P : Matrix (Fin 4) (Fin 4) ℂ => P.trace) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  exact Complex.continuous_re.comp (htrace.comp continuous_cut)

/-- The adjacent two-site Gram normalized by its physical trace. -/
def normalizedGram (p : Fin 14 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((gram p).trace.re)⁻¹ • gram p

/-- The observation uses only the amplitude projector. -/
def observation (x : Ambient) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((cut x.2).trace.re)⁻¹ • cut x.2

theorem continuousOn_observation : ContinuousOn observation source :=
  ((continuous_cut_mass.comp continuous_snd).continuousOn.inv₀
    (fun _ hx => (cut_mass_pos hx).ne')).smul (continuous_cut.comp continuous_snd).continuousOn

theorem continuous_observation : Continuous (fun x : source => observation x.val) :=
  continuousOn_observation.domRestrict

theorem observation_trace {x : Ambient} (hx : x ∈ source) : (observation x).trace = 1 := by
  obtain ⟨p, _, he⟩ := source_amplitude_projective hx
  have hr : (cut x.2).trace = ↑((cut x.2).trace.re) := by
    rw [← he, cut_outer, gram_trace, Complex.ofReal_re]
  rw [observation, Matrix.trace_smul, Complex.real_smul]
  calc
    (↑(((cut x.2).trace.re)⁻¹) : ℂ) * (cut x.2).trace =
        (↑(((cut x.2).trace.re)⁻¹) : ℂ) * ↑((cut x.2).trace.re) :=
      congrArg (fun z : ℂ => (↑(((cut x.2).trace.re)⁻¹) : ℂ) * z) hr
    _ = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (cut_mass_pos hx).ne', Complex.ofReal_one]

theorem observation_of_projector {x : Ambient} {p : Fin 14 → ℂ} (hp : p ≠ 0)
    (hx : x.2 = projector p) : observation x = normalizedGram p := by
  rw [observation, hx, projector, cut_scale, cut_outer, Matrix.trace_smul, Complex.smul_re,
    normalizedGram]
  simp only [smul_eq_mul, mul_inv, smul_smul]
  congr 1
  rw [mul_right_comm, inv_inv, mul_inv_cancel₀ (mass_pos p hp).ne', one_mul]

theorem observation_ordinary (q : Inputs) :
    observation (ordinary q) = normalizedGram (amplitude q.val) :=
  observation_of_projector q.property.2 rfl

/-- An actual nonzero six-site state lifts with its literal normalized adjacent marginal. -/
theorem actual_state_lifts (A : Fin 2 → Bond) (hne : traceWord 2 2 6 A ≠ 0) :
    let G := (PeriodicMPSTwoSiteAmbiguity.rawTwo A 2).submatrix prefixBits prefixBits
    ∃ x ∈ source, x.1 = projector (invariants A) ∧
      x.2 = projector (traceWord 2 2 6 A ∘ necklaces) ∧
      observation x = (G.trace.re)⁻¹ • G := by
  let p := traceWord 2 2 6 A ∘ necklaces
  have hp : p ≠ 0 := by
    intro hz
    have hs : p = (0 : ℂ) • p := by rw [zero_smul, hz]
    exact hne (by simpa only [zero_smul] using traceWord_smul_of_necklaces A A 0 hs)
  refine ⟨actualPoint A, actualPoint_mem_source A hp, rfl, rfl, ?_⟩
  rw [flatten_gram]
  exact observation_of_projector hp rfl

/-- Away from the base locus the compact graph has the same amplitude as the ordinary graph. -/
theorem eq_graphPoint_of_amplitude_ne_zero {x : Ambient} (hx : x ∈ source) {q : Fin 6 → ℂ}
    (hq : x.1 = projector q) (ha : amplitude q ≠ 0) : x = graphPoint q := by
  have hqne : q ≠ 0 := fun hn => ha ((congrArg amplitude hn).trans amplitude_zero)
  obtain ⟨c, hc⟩ : ∃ c : Fin 6, q c ≠ 0 := by
    by_contra! he
    exact hqne (funext he)
  let z : ℂ := (↑((mass q)⁻¹) : ℂ) * conj (q c)
  have hz : z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (mass_pos q hqne).ne'))
      ((map_ne_zero (starRingEnd ℂ)).2 hc)
  have hcolumn : (fun i => x.1 i c) = z • q := by
    rw [hq]
    exact projector_column q c
  obtain ⟨p, hp, houter⟩ := source_amplitude_projective hx
  have hp_mass : mass p = 1 := hp
  have hpne : p ≠ 0 := by
    intro he
    simp [he, mass] at hp_mass
  obtain ⟨k, hk⟩ : ∃ k : Fin 14, p k ≠ 0 := by
    by_contra! he
    exact hpne (funext he)
  have hcross (i j : Fin 14) : amplitude q i * p j = amplitude q j * p i := by
    have he := source_amplitude_incidence hx c i j k
    rw [hcolumn, amplitude_scale, ← houter] at he
    simp only [outer, Pi.smul_apply, smul_eq_mul] at he
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hz) ((map_ne_zero (starRingEnd ℂ)).2 hk))
    linear_combination he
  obtain ⟨j, hj⟩ : ∃ j : Fin 14, amplitude q j ≠ 0 := by
    by_contra! he
    exact ha (funext he)
  have hpj : p j ≠ 0 := by
    intro he
    have hm := hcross j k
    rw [he, mul_zero] at hm
    exact (mul_ne_zero hj hk) hm
  let a : ℂ := p j / amplitude q j
  have hrep : p = a • amplitude q := by
    funext i
    change p i = (p j / amplitude q j) * amplitude q i
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hj).2
    linear_combination -(hcross i j)
  refine Prod.ext hq ?_
  calc
    x.2 = outer p := houter.symm
    _ = projector p := by rw [projector, hp_mass, inv_one, one_smul]
    _ = projector (amplitude q) := by
      rw [hrep, projector_scale _ (div_ne_zero hpj hj)]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactSource
