/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactExceptional
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactExceptional
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteTraceChart]
   utility: none
   digest: Description of all exceptional six-site amplitude projectors over a base point. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteExceptionalMarginal

/-! Exceptional amplitude projectors in the closure of the six-site trace graph. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactExceptional

open Set Filter PeriodicMPSProjectiveCoordinates PeriodicMPSSixSiteCompactSource
  PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteTraceChart
open scoped Topology ComplexConjugate

open private projector_column from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource

noncomputable section

/-- Normalization by the first trace-square entry of the invariant projector. -/
def firstTraceChart (x : Ambient) (i : Fin 6) : ℂ := x.1 i 0 / x.1 0 0

private theorem continuous_invariant_entry (i j : Fin 6) :
    Continuous (fun x : Ambient => x.1 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)

private theorem continuous_amplitude_entry (i j : Fin 14) :
    Continuous (fun x : Ambient => x.2 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)

private theorem continuousAt_firstTraceChart_entry {x : Ambient} (ht : x.1 0 0 ≠ 0)
    (i : Fin 6) : ContinuousAt (fun y => firstTraceChart y i) x :=
  (continuous_invariant_entry i 0).continuousAt.div
    (continuous_invariant_entry 0 0).continuousAt ht

private theorem firstTraceChart_amplitude {x : Ambient} (hx : x ∈ source)
    (ht : x.1 0 0 ≠ 0) :
    amplitude (firstTraceChart x) = coordinates 1 (firstTraceChart x 1)
      (firstTraceChart x 1 ^ 2) (firstTraceChart x 3) (firstTraceChart x 4)
      (firstTraceChart x 5) := by
  have h₀ : firstTraceChart x 0 = 1 := div_self ht
  have h₂ : firstTraceChart x 2 = firstTraceChart x 1 ^ 2 := by
    change x.1 2 0 / x.1 0 0 = (x.1 1 0 / x.1 0 0) ^ 2
    rw [div_pow, source_quadric_column hx 0, pow_two, mul_div_mul_left _ _ ht]
  unfold amplitude
  rw [h₀, h₂]

/-- Second determinant after subtracting `s` times the first trace generator. -/
def normalE (s d e k : ℂ) : ℂ := e - s * (s - k) + s ^ 2 * d

/-- Mixed trace after subtracting `s` times the first trace generator. -/
def normalK (s d k : ℂ) : ℂ := k - s * (1 - 2 * d)

private theorem shear_unshear (s : ℂ) (p : Fin 14 → ℂ) : shear s (shear (-s) p) = p := by
  rw [shear_add, add_neg_cancel, shear_zero]

private theorem shear_zero_vector (s : ℂ) : shear s (0 : Fin 14 → ℂ) = 0 := by
  simpa only [zero_smul] using shear_smul s 0 (0 : Fin 14 → ℂ)

private theorem shear_ne_zero (s : ℂ) {p : Fin 14 → ℂ} (hp : p ≠ 0) : shear s p ≠ 0 := by
  intro h
  apply hp
  have hi := shear_unshear (-s) p
  rw [neg_neg, h, shear_zero_vector] at hi
  exact hi.symm

/-- Exact normal factorization in the first trace chart, including all higher-order terms. -/
theorem align_coordinates (s d e k : ℂ) :
    shear (-s) (coordinates 1 s (s ^ 2) d e k) =
      lift d (normalE s d e k) (normalK s d k)
        ![vacuum d, normalK s d k, normalE s d e k] := by
  have hE : normalE s d e k - s * normalK s d k + s ^ 2 * d = e := by
    unfold normalE normalK
    ring
  have hK : normalK s d k + s * (1 - 2 * d) = k := by
    unfold normalK
    ring
  have h := shear_aligned s d (normalE s d e k) (normalK s d k)
  rw [hE, hK] at h
  rw [← h, shear_add, neg_add_cancel, shear_zero, lift_coordinates]

private def kFactor (d : ℂ) : ℂ := d ^ 2 - 3 * d + 1

private def eFactor (d : ℂ) : ℂ := -(2 * d ^ 2 - 4 * d + 1)

private def recoverNormal (d : ℂ) (p : Fin 14 → ℂ) : Fin 3 → ℂ :=
  ![p 0, p 1 / kFactor d, p 2 / eFactor d]

private theorem recoverNormal_lift {d : ℂ} (hk : kFactor d ≠ 0) (he : eFactor d ≠ 0)
    (E K : ℂ) (z : Fin 3 → ℂ) : recoverNormal d (lift d E K z) = z := by
  funext i
  fin_cases i
  · rfl
  · change (kFactor d * z 1) / kFactor d = z 1
    rw [mul_comm, mul_div_cancel_right₀ _ hk]
  · change (eFactor d * z 2) / eFactor d = z 2
    rw [mul_comm, mul_div_cancel_right₀ _ he]

private def alignedColumn (x : Ambient) (j : Fin 14) : Fin 14 → ℂ :=
  shear (-firstTraceChart x 1) (fun i => x.2 i j)

set_option maxHeartbeats 900000 in
-- Check continuity of each of the fourteen polynomial shear components.
private theorem continuousAt_alignedColumn {x : Ambient} (ht : x.1 0 0 ≠ 0) (j : Fin 14) :
    ContinuousAt (fun y => alignedColumn y j) x := by
  have hs := continuousAt_firstTraceChart_entry ht 1
  have hp (i : Fin 14) : ContinuousAt (fun y : Ambient => y.2 i j) x :=
    (continuous_amplitude_entry i j).continuousAt
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> dsimp only [alignedColumn, shear] <;> fun_prop

private def fittedColumn (x : Ambient) (j : Fin 14) : Fin 14 → ℂ :=
  let q := firstTraceChart x
  lift (q 3) (normalE (q 1) (q 3) (q 4) (q 5)) (normalK (q 1) (q 3) (q 5))
    (recoverNormal (q 3) (alignedColumn x j))

private theorem ordinary_column_factorization (u : Inputs) (ht : (ordinary u).1 0 0 ≠ 0)
    (hk : kFactor (firstTraceChart (ordinary u) 3) ≠ 0)
    (he : eFactor (firstTraceChart (ordinary u) 3) ≠ 0) (j : Fin 14) :
    alignedColumn (ordinary u) j = fittedColumn (ordinary u) j := by
  let q := firstTraceChart (ordinary u)
  have hu : u.val 0 ≠ 0 := (projector_diag_ne_zero_iff u.val 0).mp ht
  have hq : u.val 0 • q = u.val := by
    funext i
    change u.val 0 * (projector u.val i 0 / projector u.val 0 0) = u.val i
    rw [projector_ratio _ _ _ hu, mul_comm, div_mul_cancel₀ _ hu]
  have ha : amplitude u.val = u.val 0 ^ 3 • amplitude q := by
    rw [← amplitude_scale, hq]
  have halign : shear (-q 1) (amplitude q) =
      lift (q 3) (normalE (q 1) (q 3) (q 4) (q 5)) (normalK (q 1) (q 3) (q 5))
        ![vacuum (q 3), normalK (q 1) (q 3) (q 5), normalE (q 1) (q 3) (q 4) (q 5)] := by
    rw [show amplitude q = _ from firstTraceChart_amplitude (ordinary_mem_source u) ht,
      align_coordinates]
  let a := amplitude u.val
  let g : ℂ := (↑((mass a)⁻¹) : ℂ) * conj (a j)
  have hcol : alignedColumn (ordinary u) j =
      lift (q 3) (normalE (q 1) (q 3) (q 4) (q 5)) (normalK (q 1) (q 3) (q 5))
        ((g * u.val 0 ^ 3) •
          ![vacuum (q 3), normalK (q 1) (q 3) (q 5), normalE (q 1) (q 3) (q 4) (q 5)]) := by
    change shear (-q 1) (fun i => projector a i j) = _
    rw [projector_column]
    change shear (-q 1) (g • a) = _
    calc
      _ = shear (-q 1) (g • (u.val 0 ^ 3 • amplitude q)) :=
        congrArg (fun b => shear (-q 1) (g • b)) ha
      _ = _ := by rw [shear_smul, shear_smul, halign, smul_smul, lift_smul]
  change alignedColumn (ordinary u) j =
    lift (q 3) (normalE (q 1) (q 3) (q 4) (q 5)) (normalK (q 1) (q 3) (q 5))
      (recoverNormal (q 3) (alignedColumn (ordinary u) j))
  rw [hcol, recoverNormal_lift hk he]

private theorem continuousAt_kFactor {x : Ambient} (ht : x.1 0 0 ≠ 0) :
    ContinuousAt (fun y => kFactor (firstTraceChart y 3)) x := by
  have hd := continuousAt_firstTraceChart_entry ht 3
  unfold kFactor
  fun_prop

private theorem continuousAt_eFactor {x : Ambient} (ht : x.1 0 0 ≠ 0) :
    ContinuousAt (fun y => eFactor (firstTraceChart y 3)) x := by
  have hd := continuousAt_firstTraceChart_entry ht 3
  unfold eFactor
  fun_prop

set_option maxHeartbeats 900000 in
-- Check continuity of the fourteen fitted components after dividing by the controlling factors.
private theorem continuousAt_fittedColumn {x : Ambient} (ht : x.1 0 0 ≠ 0)
    (hk : kFactor (firstTraceChart x 3) ≠ 0) (he : eFactor (firstTraceChart x 3) ≠ 0)
    (j : Fin 14) : ContinuousAt (fun y => fittedColumn y j) x := by
  have hq (i : Fin 6) := continuousAt_firstTraceChart_entry ht i
  have hp (i : Fin 14) : ContinuousAt (fun y => alignedColumn y j i) x :=
    (continuous_apply i).continuousAt.comp (continuousAt_alignedColumn ht j)
  have hE : ContinuousAt (fun y => normalE (firstTraceChart y 1) (firstTraceChart y 3)
      (firstTraceChart y 4) (firstTraceChart y 5)) x := by
    unfold normalE
    fun_prop
  have hK : ContinuousAt (fun y => normalK (firstTraceChart y 1) (firstTraceChart y 3)
      (firstTraceChart y 5)) x := by
    unfold normalK
    fun_prop
  have hz (i : Fin 3) :
      ContinuousAt (fun y => recoverNormal (firstTraceChart y 3) (alignedColumn y j) i) x := by
    fin_cases i
    · exact hp 0
    · exact (hp 1).div (continuousAt_kFactor ht) hk
    · exact (hp 2).div (continuousAt_eFactor ht) he
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> dsimp only [fittedColumn, lift] <;> fun_prop

/-- The identity for the unsheared column persists on the compact graph on the open
locus where the trace-square entry and both controlling factors are nonzero. -/
private theorem compact_column_factorization {x : Ambient} (hx : x ∈ source)
    (ht : x.1 0 0 ≠ 0) (hk : kFactor (firstTraceChart x 3) ≠ 0)
    (he : eFactor (firstTraceChart x 3) ≠ 0) (j : Fin 14) :
    alignedColumn x j = fittedColumn x j := by
  let _ : NeBot (𝓝[range ordinary] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have ht' : ∀ᶠ y : Ambient in 𝓝[range ordinary] x, y.1 0 0 ≠ 0 :=
    nhdsWithin_le_nhds ((continuous_invariant_entry 0 0).continuousAt (isOpen_ne.mem_nhds ht))
  have hk' : ∀ᶠ y : Ambient in 𝓝[range ordinary] x, kFactor (firstTraceChart y 3) ≠ 0 :=
    nhdsWithin_le_nhds (continuousAt_kFactor ht (isOpen_ne.mem_nhds hk))
  have he' : ∀ᶠ y : Ambient in 𝓝[range ordinary] x, eFactor (firstTraceChart y 3) ≠ 0 :=
    nhdsWithin_le_nhds (continuousAt_eFactor ht (isOpen_ne.mem_nhds he))
  have hEq : (fun y => alignedColumn y j) =ᶠ[𝓝[range ordinary] x] fun y => fittedColumn y j := by
    filter_upwards [self_mem_nhdsWithin, ht', hk', he'] with y hy hyt hyk hye
    obtain ⟨u, rfl⟩ := hy
    exact ordinary_column_factorization u hyt hyk hye j
  exact tendsto_nhds_unique_of_eventuallyEq (continuousAt_alignedColumn ht j).continuousWithinAt
    (continuousAt_fittedColumn ht hk he j).continuousWithinAt hEq

private theorem exists_projective_column {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ}
    (hP : P ∈ projective) : ∃ j, P j j ≠ 0 ∧ P = projector (fun i => P i j) := by
  obtain ⟨p, hp, houter⟩ := hP
  have hm : mass p = 1 := hp
  have hne : p ≠ 0 := by
    intro h
    simp [h, mass] at hm
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  have h : P = projector p := by rw [projector, hm, inv_one, one_smul, houter]
  have ha : (↑((mass p)⁻¹) : ℂ) * conj (p j) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (mass_pos p hne).ne'))
      ((map_ne_zero (starRingEnd ℂ)).2 hj)
  refine ⟨j, ?_, ?_⟩
  · rw [h]
    exact (projector_diag_ne_zero_iff p j).2 hj
  · have he : (fun i => P i j) = ((↑((mass p)⁻¹) : ℂ) * conj (p j)) • p := by
      rw [h]
      funext i
      simp only [projector, outer, Matrix.smul_apply, Complex.real_smul,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, projector_scale _ ha]
    exact h

/-- In the first trace chart, every compact amplitude above a base point is a
projective normal lift. The same column is used throughout the closure argument. -/
theorem firstChart_exceptional {x : Ambient} (hx : x ∈ source) (ht : x.1 0 0 ≠ 0)
    (hbase : amplitude (firstTraceChart x) = 0) :
    vacuum (firstTraceChart x 3) = 0 ∧
      ∃ z : Fin 3 → ℂ, z ≠ 0 ∧
        x.2 = projector (shear (firstTraceChart x 1) (lift (firstTraceChart x 3) 0 0 z)) := by
  let q := firstTraceChart x
  rw [firstTraceChart_amplitude hx ht] at hbase
  obtain ⟨hd, he, hk⟩ := chart_eq_zero_iff.mp hbase
  have hE : normalE (q 1) (q 3) (q 4) (q 5) = 0 := by
    dsimp [normalE, q]
    rw [he, hk]
    ring
  have hK : normalK (q 1) (q 3) (q 5) = 0 := by
    dsimp [normalK, q]
    rw [hk]
    ring
  obtain ⟨hc, hb⟩ := controlling_factors_ne hd
  obtain ⟨j, hj, hproj⟩ := exists_projective_column (source_amplitude_projective hx)
  let z := recoverNormal (q 3) (alignedColumn x j)
  have hfit := compact_column_factorization hx ht hc (neg_ne_zero.mpr hb) j
  change alignedColumn x j = lift (q 3) (normalE (q 1) (q 3) (q 4) (q 5))
    (normalK (q 1) (q 3) (q 5)) z at hfit
  rw [hE, hK] at hfit
  have hcol : (fun i => x.2 i j) = shear (q 1) (lift (q 3) 0 0 z) := by
    rw [← hfit, alignedColumn]
    exact (shear_unshear _ _).symm
  refine ⟨hd, z, ?_, hproj.trans (congrArg projector hcol)⟩
  intro hz
  have hzero : lift (q 3) 0 0 (0 : Fin 3 → ℂ) = 0 := by
    simpa only [zero_smul] using lift_smul (q 3) 0 0 0 (0 : Fin 3 → ℂ)
  rw [hz, hzero, shear_zero_vector] at hcol
  exact hj (congrFun hcol j)

private def invariantSwapIndex : Fin 6 → Fin 6 := ![2, 1, 0, 4, 3, 5]

private theorem invariantSwapIndex_involutive : Function.Involutive invariantSwapIndex := by
  intro i
  fin_cases i <;> decide

private theorem swappedIndex_involutive : Function.Involutive swappedIndex := by
  intro i
  fin_cases i <;> decide

private def invariantSwap : Fin 6 ≃ Fin 6 where
  toFun := invariantSwapIndex
  invFun := invariantSwapIndex
  left_inv := invariantSwapIndex_involutive
  right_inv := invariantSwapIndex_involutive

private def amplitudeSwap : Fin 14 ≃ Fin 14 where
  toFun := swappedIndex
  invFun := swappedIndex
  left_inv := swappedIndex_involutive
  right_inv := swappedIndex_involutive

private def permuteMatrix {ι : Type*} (σ : ι ≃ ι) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => P (σ i) (σ j)

private theorem projector_permute {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (p : ι → ℂ) :
    permuteMatrix σ (projector p) = projector (p ∘ σ) := by
  have hm : mass (p ∘ σ) = mass p := σ.sum_comp fun i => Complex.normSq (p i)
  ext i j
  simp only [permuteMatrix, projector, hm, outer, Matrix.smul_apply, Function.comp_apply]

private theorem amplitude_swap (q : Fin 6 → ℂ) :
    amplitude (q ∘ invariantSwap) = amplitude q ∘ swappedIndex :=
  coordinates_swap (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)

private theorem swapped_amplitude_ne_zero {p : Fin 14 → ℂ} (hp : p ≠ 0) :
    p ∘ swappedIndex ≠ 0 := by
  intro h
  apply hp
  funext i
  have hi := congrFun h (swappedIndex i)
  change p (swappedIndex (swappedIndex i)) = 0 at hi
  rwa [swappedIndex_involutive i] at hi

private def swapInput (u : Inputs) : Inputs :=
  ⟨u.val ∘ invariantSwap, by
    constructor
    · change u.val 1 ^ 2 = u.val 2 * u.val 0
      exact u.property.1.trans (mul_comm _ _)
    · rw [amplitude_swap]
      exact swapped_amplitude_ne_zero u.property.2⟩

/-- Simultaneous physical symbol exchange on the invariant and amplitude projectors. -/
def swapPoint (x : Ambient) : Ambient :=
  (permuteMatrix invariantSwap x.1, permuteMatrix amplitudeSwap x.2)

private theorem continuous_swapPoint : Continuous swapPoint := by
  unfold swapPoint
  exact (continuous_pi fun i => continuous_pi fun j =>
    continuous_invariant_entry (invariantSwap i) (invariantSwap j)).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        continuous_amplitude_entry (amplitudeSwap i) (amplitudeSwap j))

private theorem swapPoint_ordinary (u : Inputs) :
    swapPoint (ordinary u) = ordinary (swapInput u) := by
  change (permuteMatrix invariantSwap (projector u.val),
    permuteMatrix amplitudeSwap (projector (amplitude u.val))) =
      (projector (u.val ∘ invariantSwap), projector (amplitude (u.val ∘ invariantSwap)))
  rw [projector_permute, projector_permute, amplitude_swap]
  rfl

/-- Symbol exchange preserves the compact graph. -/
theorem swapPoint_mem_source {x : Ambient} (hx : x ∈ source) : swapPoint x ∈ source := by
  have hmap : MapsTo swapPoint (range ordinary) (range ordinary) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨swapInput u, (swapPoint_ordinary u).symm⟩
  exact hmap.closure continuous_swapPoint hx

/-- The second trace chart uses the coordinates after physical symbol exchange. -/
def secondTraceChart (x : Ambient) : Fin 6 → ℂ := firstTraceChart (swapPoint x)

/-- In the second trace chart the compact amplitude is the symbol exchange of
the first-chart normal lift in the exchanged coordinates. -/
theorem secondChart_exceptional {x : Ambient} (hx : x ∈ source) (ht : x.1 2 2 ≠ 0)
    (hbase : amplitude (secondTraceChart x) = 0) :
    vacuum (secondTraceChart x 3) = 0 ∧
      ∃ z : Fin 3 → ℂ, z ≠ 0 ∧
        x.2 = projector (shear (secondTraceChart x 1) (lift (secondTraceChart x 3) 0 0 z) ∘
          swappedIndex) := by
  have ht' : (swapPoint x).1 0 0 ≠ 0 := ht
  obtain ⟨hd, z, hz, hproj⟩ := firstChart_exceptional (swapPoint_mem_source hx) ht' hbase
  let p := shear (secondTraceChart x 1) (lift (secondTraceChart x 3) 0 0 z)
  refine ⟨hd, z, hz, ?_⟩
  have h := congrArg (permuteMatrix amplitudeSwap) hproj
  change permuteMatrix amplitudeSwap (permuteMatrix amplitudeSwap x.2) =
    permuteMatrix amplitudeSwap (projector p) at h
  have hswap : permuteMatrix amplitudeSwap (permuteMatrix amplitudeSwap x.2) = x.2 := by
    ext i j
    change x.2 (swappedIndex (swappedIndex i)) (swappedIndex (swappedIndex j)) = x.2 i j
    rw [swappedIndex_involutive i, swappedIndex_involutive j]
  rw [hswap, projector_permute] at h
  exact h

private theorem firstTraceChart_of_projector {x : Ambient} {q : Fin 6 → ℂ}
    (h : x.1 = projector q) (ht : q 0 ≠ 0) : firstTraceChart x = (q 0)⁻¹ • q := by
  funext i
  change x.1 i 0 / x.1 0 0 = (q 0)⁻¹ * q i
  rw [h, projector_ratio _ _ _ ht, div_eq_inv_mul]

private theorem firstTraceChart_base {x : Ambient} {q : Fin 6 → ℂ} (h : x.1 = projector q)
    (ht : q 0 ≠ 0) (ha : amplitude q = 0) : amplitude (firstTraceChart x) = 0 := by
  rw [firstTraceChart_of_projector h ht, amplitude_scale, ha, smul_zero]

/-- Every base point has a nonzero trace-square coordinate, so the two
trace charts exhaust the exceptional fibers of the compact source. -/
theorem exceptional_amplitude {x : Ambient} {q : Fin 6 → ℂ} (hx : x ∈ source)
    (hq : x.1 = projector q) (hbase : amplitude q = 0) :
    ∃ (s d : ℂ) (z : Fin 3 → ℂ), vacuum d = 0 ∧ z ≠ 0 ∧
      (x.2 = projector (shear s (lift d 0 0 z)) ∨
        x.2 = projector (shear s (lift d 0 0 z) ∘ swappedIndex)) := by
  by_cases ht : q 0 = 0
  · obtain ⟨j, hj, _⟩ := exists_projective_column (source_invariant_projective hx)
    have hqj : q j ≠ 0 := by
      apply (projector_diag_ne_zero_iff q j).mp
      simpa only [hq] using hj
    have hu : q 2 ≠ 0 := by
      intro hu
      have hp₀ : x.1 0 j = 0 := by
        rw [hq]
        simp [projector, outer, ht, Matrix.smul_apply]
      have hsq := source_quadric_column hx j
      rw [hp₀, zero_mul] at hsq
      have hp₁ := sq_eq_zero_iff.mp hsq
      have hr := projector_ratio q 1 j hqj
      rw [← hq, hp₁, zero_div] at hr
      have hs : q 1 = 0 := (div_eq_zero_iff.mp hr.symm).resolve_right hqj
      exact amplitude_ne_zero_of_traceless (fun h => hqj (congrFun h j)) ht hs hu hbase
    have hdiag : x.1 2 2 ≠ 0 := by
      rw [hq]
      exact (projector_diag_ne_zero_iff q 2).mpr hu
    have hswap : (swapPoint x).1 = projector (q ∘ invariantSwap) := by
      change permuteMatrix invariantSwap x.1 = _
      rw [hq, projector_permute]
    have hampl : amplitude (q ∘ invariantSwap) = 0 := by
      rw [amplitude_swap, hbase]
      rfl
    obtain ⟨hd, z, hz, hproj⟩ := secondChart_exceptional hx hdiag
      (firstTraceChart_base hswap hu hampl)
    exact ⟨secondTraceChart x 1, secondTraceChart x 3, z, hd, hz, Or.inr hproj⟩
  · have hdiag : x.1 0 0 ≠ 0 := by
      rw [hq]
      exact (projector_diag_ne_zero_iff q 0).mpr ht
    obtain ⟨hd, z, hz, hproj⟩ := firstChart_exceptional hx hdiag (firstTraceChart_base hq ht hbase)
    exact ⟨firstTraceChart x 1, firstTraceChart x 3, z, hd, hz, Or.inl hproj⟩

/-- At a compact base lift, a zero adjacent-ones weight forces the singleton
diagonal and exchange entries to coincide. -/
theorem exceptional_observation_difference_eq_zero {x : Ambient} {q : Fin 6 → ℂ}
    (hx : x ∈ source) (hq : x.1 = projector q) (hbase : amplitude q = 0)
    (hcorner : observation x 3 3 = 0) : observation x 1 1 = observation x 1 2 := by
  obtain ⟨s, d, z, hd, hz, hproj⟩ := exceptional_amplitude hx hq hbase
  let p := shear s (lift d 0 0 z)
  have hp : p ≠ 0 := shear_ne_zero s (lift_ne_zero_of_vacuum hd hz)
  have hgram {v : Fin 14 → ℂ} (hv : v ≠ 0) (hP : x.2 = projector v) :
      PeriodicMPSSixSiteMarginal.gram v 3 3 = 0 := by
    have h := hcorner
    rw [observation_of_projector hv hP] at h
    simp only [normalizedGram, Matrix.smul_apply, Complex.real_smul] at h
    exact (mul_eq_zero.mp h).resolve_left
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (gram_mass_pos v hv).ne'))
  rcases hproj with hP | hP
  · have h := PeriodicMPSSixSiteExceptionalMarginal.firstChart_difference_eq_zero hd hz
      (hgram hp hP)
    rw [observation_of_projector hp hP]
    simp only [normalizedGram, Matrix.smul_apply]
    rw [h]
  · exact (PeriodicMPSSixSiteExceptionalMarginal.secondChart_corner_ne_zero hd hz
      (hgram (swapped_amplitude_ne_zero hp) hP)).elim

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCompactExceptional
