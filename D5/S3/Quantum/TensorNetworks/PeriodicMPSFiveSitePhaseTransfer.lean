/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSitePhaseTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSitePhaseTransfer
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource]
   utility: none
   digest: Generic uniqueness on the compact source descends to unit-mass actual states. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
import D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber

/-! Locally around any unit-mass amplitude, a nonzero projector column
chooses a continuous representative through that amplitude. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSitePhaseTransfer

open Set Filter PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCoordinates
  PeriodicMPSProjectiveCoordinates PeriodicMPSCompactFiber
open PeriodicMPSFiveSiteNormalization hiding mass
open UniformMPSExpectedDimensionRefutation
open PeriodicMPSParentIntersection (Bond Word)
open scoped Topology

open private traceDirection pencil from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
open private prefixBits suffixEquiv
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

noncomputable section

abbrev Necklace := Fin 8 → ℂ
abbrev AmplitudeProjector := Matrix (Fin 8) (Fin 8) ℂ
local notation "mass₅" => PeriodicMPSFiveSiteNormalization.mass

/-- The eight necklace coordinates of an actual periodic state. -/
def actual (p : Necklace) : Prop :=
  ∃ A : Fin 2 → Bond, traceWord 2 2 5 A ∘ necklaces = p

/-- Actual five-site amplitudes of mass one, represented by their necklaces. -/
abbrev UnitStates := {p : Necklace // actual p ∧ mass₅ p = 1}

private theorem actual_coordinates (t s d e k : ℂ) : actual (coordinates t s d e k) := by
  obtain ⟨A, h₀, h₁, h₂, h₃, h₄⟩ := exists_trace_coordinates t s d e k
  exact ⟨A, by rw [trace_word_necklaces, h₀, h₁, h₂, h₃, h₄]⟩

private theorem actual_smul {p : Necklace} (hp : actual p) (z : ℂ) : actual (z • p) := by
  obtain ⟨A, rfl⟩ := hp
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq z (n := 5) (by decide)
  rw [trace_word_necklaces, ← hk, ← coordinates_scale]
  exact actual_coordinates _ _ _ _ _

private theorem unit_ne_zero (p : UnitStates) : p.val ≠ 0 := by
  intro h
  have hm := p.property.2
  rw [h] at hm
  have h0 := PeriodicMPSFiveSiteNormalization.mass_scale (0 : Necklace) (0 : ℂ)
  simp at h0
  rw [h0] at hm
  norm_num at hm

private def project (x : source) : AmplitudeProjector := x.val.2

private theorem ordinary_dense :
    Dense (range (fun a : Inputs => (⟨ordinary a, ordinary_mem_source a⟩ : source))) := by
  intro x
  rw [closure_subtype, ← range_comp]
  exact x.property

private theorem observation_eq_of_project {x y : source} (h : project x = project y) :
    observation x.val = observation y.val := by
  unfold observation
  change x.val.2 = y.val.2 at h
  rw [h]

private def column (p : Necklace) (j : Fin 8) (P : AmplitudeProjector) : Necklace :=
  fun i => p j * (P i j / P j j)

private def sectionAt (p : Necklace) (j : Fin 8) (P : AmplitudeProjector) : Necklace :=
  (↑((Real.sqrt (mass₅ (column p j P)))⁻¹ : ℝ) : ℂ) • column p j P

private theorem column_eq_smul (p q : Necklace) (j : Fin 8) (hj : q j ≠ 0) :
    column p j (projector q) = (p j / q j) • q := by
  funext i
  simp only [column, projector_ratio _ _ _ hj, Pi.smul_apply, smul_eq_mul]
  ring

private theorem sectionAt_self (p : UnitStates) (j : Fin 8) (hj : p.val j ≠ 0) :
    sectionAt p.val j (projector p.val) = p.val := by
  simp only [sectionAt, column_eq_smul p.val p.val j hj, div_self hj, one_smul, p.property.2,
    Real.sqrt_one, inv_one, Complex.ofReal_one]

private theorem sectionAt_continuousAt (p : UnitStates) (j : Fin 8) (hj : p.val j ≠ 0) :
    ContinuousAt (sectionAt p.val j) (projector p.val) := by
  have hc : ContinuousAt (column p.val j) (projector p.val) := by
    apply continuousAt_pi.mpr
    intro i
    unfold column
    exact continuousAt_const.mul
      (ContinuousAt.div
        (((continuous_apply j).comp (continuous_apply i)).continuousAt)
        (((continuous_apply j).comp (continuous_apply j)).continuousAt)
        ((projector_diag_ne_zero_iff _ _).2 hj))
  have hm : Continuous mass₅ := by
    change Continuous (fun p : Necklace => mass₅ p)
    simp_rw [mass_eq_sum]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => by
      fin_cases i <;> fin_cases k <;> exact Complex.continuous_normSq.comp (continuous_apply _)
  have hself : column p.val j (projector p.val) = p.val := by
    rw [column_eq_smul _ _ _ hj, div_self hj, one_smul]
  have hn : Real.sqrt (mass₅ (column p.val j (projector p.val))) ≠ 0 := by
    rw [hself, p.property.2, Real.sqrt_one]
    exact one_ne_zero
  have hR : ContinuousAt (fun P => (↑((Real.sqrt (mass₅ (column p.val j P)))⁻¹ : ℝ) : ℂ))
      (projector p.val) :=
    Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuous_sqrt.continuousAt.comp (hm.continuousAt.comp hc)).inv₀ hn)
  exact hR.smul hc

private theorem sectionAt_unit (p : UnitStates) (j : Fin 8) (hj : p.val j ≠ 0)
    {q : Necklace} (hq : actual q) (hqj : q j ≠ 0) :
    actual (sectionAt p.val j (projector q)) ∧
      mass₅ (sectionAt p.val j (projector q)) = 1 ∧
      projector (sectionAt p.val j (projector q)) = projector q := by
  let r := column p.val j (projector q)
  have hsc : r = (p.val j / q j) • q := column_eq_smul _ _ _ hqj
  have hqn : q ≠ 0 := fun e => hqj (congrFun e j)
  have hr : r ≠ 0 := by
    rw [hsc]
    exact smul_ne_zero (div_ne_zero hj hqj) hqn
  let s := Real.sqrt (mass₅ r)
  have hs : s ≠ 0 := (Real.sqrt_pos_of_pos (mass_positive _ hr)).ne'
  have hc : ((s⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hs)
  change actual (((s⁻¹ : ℝ) : ℂ) • r) ∧ mass₅ (((s⁻¹ : ℝ) : ℂ) • r) = 1 ∧
    projector (((s⁻¹ : ℝ) : ℂ) • r) = projector q
  refine ⟨actual_smul (hsc.symm ▸ actual_smul hq _) _, ?_, ?_⟩
  · rw [PeriodicMPSFiveSiteNormalization.mass_scale, Complex.normSq_ofReal, ← pow_two,
      inv_pow, Real.sq_sqrt (mass_positive _ hr).le,
      inv_mul_cancel₀ (mass_positive _ hr).ne']
  · rw [projector_scale _ hc, hsc, projector_scale _ (div_ne_zero hj hqj)]

set_option maxHeartbeats 1000000 in
-- The descent works with three nested subtypes of finite-dimensional spaces.
/-- Open dense singleton-fiber points of the compact observation give open
dense actual unit-mass amplitudes identifiable against all actual competitors. -/
theorem transfer_unitPhase {G : Set source} (hG : IsOpen G) (hD : Dense G)
    (hunique : ∀ x ∈ G, ∀ y : source, observation y.val = observation x.val → y = x) :
    ∃ U : Set UnitStates, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ q : UnitStates, normalizedGram q.val = normalizedGram p.val →
        ∃ z : ℂ, ‖z‖ = 1 ∧ q.val = z • p.val := by
  letI : CompactSpace source := isCompact_iff_compactSpace.mp source_isCompact
  let D := range (fun a : Inputs => (⟨ordinary a, ordinary_mem_source a⟩ : source))
  have hproj : Continuous project := continuous_snd.comp continuous_subtype_val
  obtain ⟨W, hW, hw, hcl⟩ := descend_open_dense hproj hG hD (D := D) ordinary_dense
    (fun x hx y he => hunique x hx y (observation_eq_of_project he) ▸ hx)
  let U : Set UnitStates := {p | projector p.val ∈ W}
  have hpU : IsOpen U := by
    apply hW.preimage
    exact continuous_iff_continuousAt.mpr fun p =>
      (continuousAt_projector (unit_ne_zero p)).comp continuous_subtype_val.continuousAt
  refine ⟨U, hpU, ?_, ?_⟩
  · intro p
    obtain ⟨A, hA⟩ := p.property.1
    obtain ⟨x, hx, he, _⟩ := actual_state_lifts A (hA.symm ▸ unit_ne_zero p)
    rw [hA] at he
    let P := projector p.val
    have hP : P ∈ closure (project '' (G ∩ D)) :=
      hcl ⟨⟨x, hx⟩, he⟩
    have hj : ∃ j, p.val j ≠ 0 := by
      by_contra! h
      exact unit_ne_zero p (funext h)
    obtain ⟨j, hj⟩ := hj
    rw [closure_subtype]
    let S : Set AmplitudeProjector := project '' (G ∩ D)
    let L : Filter AmplitudeProjector := 𝓝[S] P
    haveI : NeBot L := mem_closure_iff_nhdsWithin_neBot.mp hP
    have hl : L ≤ 𝓝 P := nhdsWithin_le_nhds
    have ht₀ : Tendsto (sectionAt p.val j) (𝓝 P) (𝓝 (sectionAt p.val j P)) :=
      (sectionAt_continuousAt p j hj).tendsto
    have heq : 𝓝 (sectionAt p.val j P) = 𝓝 p.val := congrArg nhds (sectionAt_self p j hj)
    have ht : Tendsto (sectionAt p.val j) L (𝓝 p.val) := heq ▸ ht₀.mono_left hl
    have hd₀ : Continuous (fun R : AmplitudeProjector => R j j) :=
      (continuous_apply j).comp (continuous_apply j)
    have hd₁ : P j j ≠ 0 := (projector_diag_ne_zero_iff _ _).2 hj
    have hd₂ : ∀ᶠ R : AmplitudeProjector in 𝓝 P, R j j ≠ 0 :=
      hd₀.continuousAt (isOpen_ne.mem_nhds hd₁)
    have hd : ∀ᶠ R : AmplitudeProjector in L, R j j ≠ 0 := hd₂.filter_mono hl
    have hevent : ∀ᶠ R : AmplitudeProjector in L,
        sectionAt p.val j R ∈ (Subtype.val : UnitStates → Necklace) '' U := by
      have hS : ∀ᶠ R in L, R ∈ S := self_mem_nhdsWithin
      filter_upwards [hS, hd] with R hR hn
      obtain ⟨y, ⟨hy, ⟨u, rfl⟩⟩, rfl⟩ := hR
      let q := coordinates (u.val 0) (u.val 1) (u.val 2) (u.val 3) (u.val 4)
      change projector q j j ≠ 0 at hn
      have hqj : q j ≠ 0 := (projector_diag_ne_zero_iff q j).1 hn
      obtain ⟨ha, hm, hz⟩ := sectionAt_unit p j hj (actual_coordinates _ _ _ _ _) hqj
      refine ⟨⟨_, ha, hm⟩, ?_, rfl⟩
      change projector (sectionAt p.val j (projector q)) ∈ W
      rw [hz]
      have him : projector q ∈ project '' G := mem_image_of_mem project hy
      rw [hw] at him
      exact him.2
    exact mem_closure_of_tendsto ht hevent
  · intro p hp q h
    obtain ⟨A, hA⟩ := p.property.1
    obtain ⟨B, hB⟩ := q.property.1
    obtain ⟨x, hx, hxP, hxO⟩ := actual_state_lifts A (hA.symm ▸ unit_ne_zero p)
    obtain ⟨y, hy, hyP, hyO⟩ := actual_state_lifts B (hB.symm ▸ unit_ne_zero q)
    rw [hA] at hxP hxO
    rw [hB] at hyP hyO
    have hxG : (⟨x, hx⟩ : source) ∈ G := by
      have hh : project (⟨x, hx⟩ : source) ∈ W := by
        change x.2 ∈ W
        rw [hxP]
        exact hp
      have he : project (⟨x, hx⟩ : source) ∈ project '' G :=
        hw.symm ▸ ⟨mem_range_self _, hh⟩
      obtain ⟨x', hx', hh⟩ := he
      exact hunique x' hx' _ (observation_eq_of_project hh.symm) ▸ hx'
    have he := hunique ⟨x, hx⟩ hxG ⟨y, hy⟩ (hyO.trans (h.trans hxO.symm))
    have hP : projector p.val = projector q.val := hxP.symm.trans
      ((congrArg project he).symm.trans hyP)
    obtain ⟨z, _, hz⟩ := eq_smul_of_projector_eq (unit_ne_zero p) hP
    have hm := q.property.2
    rw [hz, PeriodicMPSFiveSiteNormalization.mass_scale, p.property.2, mul_one,
      ← Complex.sq_norm] at hm
    exact ⟨z, by nlinarith [norm_nonneg z], hz⟩

private def wordPair : Fin 4 × Fin 8 ≃ Word 5 :=
  (Equiv.prodCongr (prefixBits.trans (finTwoArrowEquiv (Fin 2)).symm) suffixEquiv).trans
    (Fin.appendEquiv 2 3)

private theorem traceWord_wordPair (A : Fin 2 → Bond) (p : Fin 4 × Fin 8) :
    traceWord 2 2 5 A (wordPair p) =
      flatten (traceWord 2 2 5 A ∘ necklaces) p.1 p.2 :=
  congrFun (congrFun (flatten_necklaces A) p.1) p.2

private def expand (p : Necklace) (w : Word 5) : ℂ :=
  flatten p (wordPair.symm w).1 (wordPair.symm w).2

private theorem expand_traceWord (A : Fin 2 → Bond) :
    expand (traceWord 2 2 5 A ∘ necklaces) = traceWord 2 2 5 A := by
  funext w
  unfold expand
  rw [← traceWord_wordPair A (wordPair.symm w), wordPair.apply_symm_apply]

private theorem flatten_apply (p : Necklace) (i : Fin 4) (j : Fin 8) :
    flatten p i j = p (flatten id i j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- A phase relation on the necklaces is a phase relation on the full amplitude. -/
theorem traceWord_smul_of_necklaces (A B : Fin 2 → Bond) (z : ℂ)
    (h : traceWord 2 2 5 B ∘ necklaces = z • (traceWord 2 2 5 A ∘ necklaces)) :
    traceWord 2 2 5 B = z • traceWord 2 2 5 A := by
  calc
    _ = expand (traceWord 2 2 5 B ∘ necklaces) := (expand_traceWord B).symm
    _ = expand (z • (traceWord 2 2 5 A ∘ necklaces)) := congrArg expand h
    _ = z • expand (traceWord 2 2 5 A ∘ necklaces) := by
      funext w
      simp only [expand, flatten_apply, Pi.smul_apply]
    _ = _ := congrArg (fun p : Word 5 → ℂ => z • p) (expand_traceWord A)

/-- The squared norm of the full amplitude with the standard computational basis. -/
def wordMass (p : Word 5 → ℂ) : ℝ := ∑ w, Complex.normSq (p w)

theorem wordMass_traceWord (A : Fin 2 → Bond) :
    wordMass (traceWord 2 2 5 A) = mass₅ (traceWord 2 2 5 A ∘ necklaces) := by
  rw [wordMass, mass_eq_sum]
  calc
    _ = ∑ p : Fin 4 × Fin 8, Complex.normSq (traceWord 2 2 5 A (wordPair p)) :=
      (Equiv.sum_comp wordPair _).symm
    _ = ∑ p : Fin 4 × Fin 8,
        Complex.normSq (flatten (traceWord 2 2 5 A ∘ necklaces) p.1 p.2) := by
      simp only [traceWord_wordPair]
    _ = _ := Fintype.sum_prod_type _

private theorem gram_eq_of_rawTwo_eq (A B : Fin 2 → Bond)
    (h : PeriodicMPSTwoSiteAmbiguity.rawTwo B 1 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 1) :
    PeriodicMPSFiveSiteSpecialFiber.gram (traceWord 2 2 5 B ∘ necklaces) =
      PeriodicMPSFiveSiteSpecialFiber.gram (traceWord 2 2 5 A ∘ necklaces) := by
  unfold PeriodicMPSFiveSiteSpecialFiber.gram
  rw [← flatten_gram A, ← flatten_gram B, h]

/-- Equal two-site marginals force equal mass for the full amplitudes. -/
theorem wordMass_eq_of_rawTwo_eq (A B : Fin 2 → Bond)
    (h : PeriodicMPSTwoSiteAmbiguity.rawTwo B 1 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 1) :
    wordMass (traceWord 2 2 5 B) = wordMass (traceWord 2 2 5 A) := by
  rw [wordMass_traceWord A, wordMass_traceWord B]
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.trace.re)
    (gram_eq_of_rawTwo_eq A B h)

/-- Equal two-site marginals of unit amplitudes give equal normalized Gram matrices. -/
theorem normalizedGram_eq_of_rawTwo_eq (A B : Fin 2 → Bond)
    (hA : wordMass (traceWord 2 2 5 A) = 1) (hB : wordMass (traceWord 2 2 5 B) = 1)
    (h : PeriodicMPSTwoSiteAmbiguity.rawTwo B 1 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 1) :
    normalizedGram (traceWord 2 2 5 B ∘ necklaces) =
      normalizedGram (traceWord 2 2 5 A ∘ necklaces) := by
  rw [wordMass_traceWord] at hA hB
  simpa only [normalizedGram, hA, hB, inv_one, one_smul] using gram_eq_of_rawTwo_eq A B h

/-- Actual periodic amplitudes in the full computational basis, of mass one. -/
abbrev UnitWordStates :=
  {p : Word 5 → ℂ // (∃ A : Fin 2 → Bond, traceWord 2 2 5 A = p) ∧ wordMass p = 1}

private def toNecklaceState (p : UnitWordStates) : UnitStates := by
  refine ⟨p.val ∘ necklaces, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := p.property.1
    exact ⟨A, congrArg (fun q : Word 5 → ℂ => q ∘ necklaces) hA⟩
  · obtain ⟨A, hA⟩ := p.property.1
    rw [← hA, ← wordMass_traceWord, hA]
    exact p.property.2

private def toWordState (p : UnitStates) : UnitWordStates := by
  refine ⟨expand p.val, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := p.property.1
    exact ⟨A, by rw [← hA, expand_traceWord]⟩
  · obtain ⟨A, hA⟩ := p.property.1
    rw [← hA, expand_traceWord, wordMass_traceWord, hA]
    exact p.property.2

private def unitWordHomeomorph : UnitWordStates ≃ₜ UnitStates where
  toFun := toNecklaceState
  invFun := toWordState
  left_inv p := by
    obtain ⟨A, hA⟩ := p.property.1
    apply Subtype.ext
    change expand (p.val ∘ necklaces) = p.val
    rw [← hA, expand_traceWord]
  right_inv p := by
    obtain ⟨A, hA⟩ := p.property.1
    apply Subtype.ext
    change expand p.val ∘ necklaces = p.val
    rw [← hA, expand_traceWord]
  continuous_toFun := by
    have h : Continuous (fun p : UnitWordStates => p.val ∘ necklaces) := continuous_pi fun i =>
      (continuous_apply (necklaces i)).comp continuous_subtype_val
    exact h.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun p : UnitStates => expand p.val) := by
      apply continuous_pi
      intro w
      change Continuous (fun p : UnitStates => flatten p.val (wordPair.symm w).1 (wordPair.symm w).2)
      simp only [flatten_apply]
      exact (continuous_apply (flatten id (wordPair.symm w).1 (wordPair.symm w).2)).comp
        continuous_subtype_val
    exact h.subtype_mk _

/-- Singleton fibers on a dense open part of the compact source give generic
two-site recovery against all actual unit-mass amplitudes. -/
theorem transfer_rawTwo_unitPhase {G : Set source} (hG : IsOpen G) (hD : Dense G)
    (hunique : ∀ x ∈ G, ∀ y : source, observation y.val = observation x.val → y = x) :
    ∃ U : Set UnitWordStates, IsOpen U ∧ Dense U ∧
      ∀ (A B : Fin 2 → Bond) (hA : wordMass (traceWord 2 2 5 A) = 1)
        (hB : wordMass (traceWord 2 2 5 B) = 1),
        (⟨traceWord 2 2 5 A, ⟨A, rfl⟩, hA⟩ : UnitWordStates) ∈ U →
        PeriodicMPSTwoSiteAmbiguity.rawTwo B 1 = PeriodicMPSTwoSiteAmbiguity.rawTwo A 1 →
          ∃ z : ℂ, ‖z‖ = 1 ∧ traceWord 2 2 5 B = z • traceWord 2 2 5 A := by
  obtain ⟨U, hU, hd, hf⟩ := transfer_unitPhase hG hD hunique
  refine ⟨unitWordHomeomorph ⁻¹' U, hU.preimage unitWordHomeomorph.continuous,
    hd.preimage unitWordHomeomorph.isOpenMap, ?_⟩
  intro A B hA hB hAU hR
  let p : UnitWordStates := ⟨traceWord 2 2 5 A, ⟨A, rfl⟩, hA⟩
  let q : UnitWordStates := ⟨traceWord 2 2 5 B, ⟨B, rfl⟩, hB⟩
  have hN := normalizedGram_eq_of_rawTwo_eq A B hA hB hR
  obtain ⟨z, hz, he⟩ := hf (unitWordHomeomorph p) hAU (unitWordHomeomorph q) hN
  exact ⟨z, hz, traceWord_smul_of_necklaces A B z he⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSitePhaseTransfer
