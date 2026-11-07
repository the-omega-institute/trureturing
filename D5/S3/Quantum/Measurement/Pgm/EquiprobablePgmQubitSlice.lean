/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmQubitSlice
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmQubitSlice
   mirror-E: none(waiver:universal-slice-proof)
   anchors: []
   utility: none
   digest: A complete small-parameter mixed-qubit PGM failure interval. -/

import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmLoading
import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity
import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison

/-!
The qubit construction and symmetric calculations are credited to Hyunho Cha
by the anonymous mechanism manuscript and the Haobo Ma–Wenlin Zhang new note.
The latter alone carries CC BY 4.0. The universal closed cutoff 1/55 is
sufficient, not asserted optimal; t=0 is excluded from the physical family.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmQubitSlice
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison (symmetric_scores inverse_sqrt_two)
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity (pgmEffects pgm_support)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

def states (t : ℝ) := rho (1 - t ^ 2) (t / 2) (1 - 10 * t ^ 2)

private theorem domain (t : ℝ) (ht : 0 < t) (hhi : t ≤ 1 / 55) :
    0 < 1 - t ^ 2 ∧ 1 - t ^ 2 < 1 ∧
      0 < 1 - 10 * t ^ 2 ∧ 1 - 10 * t ^ 2 < 1 ∧
      0 < (1 - t ^ 2) * (1 - (1 - t ^ 2)) - (t / 2) ^ 2 ∧
      |(1 - 10 * t ^ 2) - (1 - t ^ 2)| ≤ t / 2 ∧
      0 < 1 - 4 * t ^ 2 := by
  have hsq := pow_le_pow_left₀ ht.le hhi 2
  norm_num at hsq
  have hp : 0 < t ^ 2 := sq_pos_of_pos ht
  have hdet := mul_pos hp (show 0 < 3 / 4 - t ^ 2 by linarith)
  refine ⟨by linarith, by linarith, by linarith, by linarith, by nlinarith, ?_, by linarith⟩
  rw [abs_of_nonpos (by nlinarith : (1 - 10 * t ^ 2) - (1 - t ^ 2) ≤ 0)]
  nlinarith

private theorem scores (t : ℝ) (ht : 0 < t) (hhi : t ≤ 1 / 55) :
    pgmScore (states t) {0, 1} - 1 / 3 = t / (6 * Real.sqrt (1 - t ^ 2)) ∧
    pgmScore (states t) Finset.univ - 1 / 3 =
      t / (18 * Real.sqrt (1 - 4 * t ^ 2)) + 3 * t ^ 2 / (2 * (1 - 4 * t ^ 2)) := by
  obtain ⟨ha, ha1, hc, hc1, hd, hload, hv⟩ := domain t ht hhi
  have hs := symmetric_scores (1 - t ^ 2) (t / 2) (1 - 10 * t ^ 2) ha ha1 hc hc1
  have hq : (1 - t ^ 2) * (1 - (1 - t ^ 2)) = t ^ 2 * (1 - t ^ 2) := by ring
  have hD : (2 * (1 - t ^ 2) + (1 - 10 * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - 10 * t ^ 2)) = (6 * t) ^ 2 * (1 - 4 * t ^ 2) := by ring
  have hqroot : Real.sqrt ((1 - t ^ 2) * (1 - (1 - t ^ 2))) =
      t * Real.sqrt (1 - t ^ 2) := by
    rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have hDroot : Real.sqrt ((2 * (1 - t ^ 2) + (1 - 10 * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - 10 * t ^ 2))) =
        6 * t * Real.sqrt (1 - 4 * t ^ 2) := by
    rw [hD, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  change (pgmScore (rho _ _ _) _ - 1 / 3 = _) ∧ _
  constructor
  · rw [hs.1, hqroot]
    field_simp
    ring
  · change pgmScore (rho _ _ _) Finset.univ - 1 / 3 = _
    rw [hs.2, hDroot, hD]
    field_simp
    ring

/-- Every parameter in the entire stated interval is a strictly positive mixed
qubit ensemble, with unique two-active optimum and a certified strict PGM gap. -/
theorem family (t : ℝ) (ht : 0 < t) (hhi : t ≤ 1 / 55) :
    (∀ i, (states t i).PosDef ∧ trace (states t i) = 1) ∧
    finitePOVM pairPovm ∧
    (∀ E, finitePOVM E →
      ((∀ F, finitePOVM F → success (states t) F ≤ success (states t) E) ↔ E = pairPovm)) ∧
    success (states t) pairPovm = (1 + t) / 3 ∧
    pgmScore (states t) {0, 1} - 1 / 3 = t / (6 * Real.sqrt (1 - t ^ 2)) ∧
    pgmScore (states t) Finset.univ - 1 / 3 =
      t / (18 * Real.sqrt (1 - 4 * t ^ 2)) + 3 * t ^ 2 / (2 * (1 - 4 * t ^ 2)) ∧
    t * (1 - 54 * t - 12 * t ^ 2) / (18 * (1 - 4 * t ^ 2)) ≤
      (pgmScore (states t) {0, 1} - 1 / 3) -
        2 * (pgmScore (states t) Finset.univ - 1 / 3) ∧
    0 < t * (1 - 54 * t - 12 * t ^ 2) / (18 * (1 - 4 * t ^ 2)) := by
  obtain ⟨ha, ha1, hc, hc1, hd, hload, hv⟩ := domain t ht hhi
  have hopt := pair_classification (1 - t ^ 2) (t / 2) (1 - 10 * t ^ 2)
    (by positivity) hload
  have hs := scores t ht hhi
  refine ⟨states_posDef _ _ _ ha hc hc1 hd, hopt.1, hopt.2.2, ?_, hs.1, hs.2, ?_, ?_⟩
  · change success (rho _ _ _) pairPovm = _
    rw [hopt.2.1]; ring
  · rw [hs.1, hs.2]
    have hS : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr ha
    have hV : 0 < Real.sqrt (1 - 4 * t ^ 2) := Real.sqrt_pos.mpr hv
    have hS1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
      nlinarith [Real.sq_sqrt ha.le, sq_nonneg t]
    have hVlow : 1 - 4 * t ^ 2 ≤ Real.sqrt (1 - 4 * t ^ 2) := by
      nlinarith [Real.sq_sqrt hv.le, sq_nonneg (Real.sqrt (1 - 4 * t ^ 2) - 1)]
    have hA : t / 6 ≤ t / (6 * Real.sqrt (1 - t ^ 2)) := by
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
      nlinarith
    have hP : t / (18 * Real.sqrt (1 - 4 * t ^ 2)) ≤ t / (18 * (1 - 4 * t ^ 2)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hid : t / 6 - 2 * (t / (18 * (1 - 4 * t ^ 2)) +
        3 * t ^ 2 / (2 * (1 - 4 * t ^ 2))) =
        t * (1 - 54 * t - 12 * t ^ 2) / (18 * (1 - 4 * t ^ 2)) := by
      field_simp <;> ring_nf <;>
        field_simp [show 1 - t ^ 2 * 4 ≠ 0 by linarith] <;> ring
    linarith
  · have hsq := pow_le_pow_left₀ ht.le hhi 2
    norm_num at hsq
    have hpoly : 43 / 3025 ≤ 1 - 54 * t - 12 * t ^ 2 := by linarith
    exact div_pos (mul_pos ht (by linarith)) (by positivity)

open Filter Topology in
private theorem small_parameters : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 / 55 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 55)).filter_mono nhdsWithin_le_nhds]
    with t ht hhi
  exact ⟨ht, hhi.le⟩

open Filter Topology Asymptotics in
private theorem cubic_remainder (r : ℝ → ℝ) (hr : ContinuousAt r 0) :
    (fun t : ℝ => t ^ 3 * r t) =O[𝓝[>] 0] (fun t => t ^ 3) := by
  simpa only [mul_one] using (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝[>] 0)).mul
    ((hr.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ)

open Filter Topology Asymptotics in
/-- Complete cubic-order expansions of the actual centered scores and gap,
with centered ratio tending to three and raw ratio tending to one. -/
theorem asymptotics :
    (fun t : ℝ => (pgmScore (states t) {0, 1} - 1 / 3) - t / 6)
      =O[𝓝[>] 0] (fun t => t ^ 3) ∧
    (fun t : ℝ => (pgmScore (states t) Finset.univ - 1 / 3) - t / 18 - 3 * t ^ 2 / 2)
      =O[𝓝[>] 0] (fun t => t ^ 3) ∧
    (fun t : ℝ => (pgmScore (states t) {0, 1} - 1 / 3) -
      2 * (pgmScore (states t) Finset.univ - 1 / 3) - t / 18 + 3 * t ^ 2)
      =O[𝓝[>] 0] (fun t => t ^ 3) ∧
    Tendsto (fun t : ℝ => (pgmScore (states t) {0, 1} - 1 / 3) /
      (pgmScore (states t) Finset.univ - 1 / 3)) (𝓝[>] 0) (𝓝 3) ∧
    Tendsto (fun t : ℝ => pgmScore (states t) {0, 1} /
      pgmScore (states t) Finset.univ) (𝓝[>] 0) (𝓝 1) := by
  let rA : ℝ → ℝ := fun t => 1 /
    (6 * Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)))
  let rP : ℝ → ℝ := fun t => 2 /
    (9 * Real.sqrt (1 - 4 * t ^ 2) * (1 + Real.sqrt (1 - 4 * t ^ 2))) +
      6 * t / (1 - 4 * t ^ 2)
  have hcA : ContinuousAt rA 0 := by dsimp [rA]; fun_prop (disch := norm_num)
  have hcP : ContinuousAt rP 0 := by dsimp [rP]; fun_prop (disch := norm_num)
  have hAe : (fun t : ℝ => t ^ 3 * rA t) =ᶠ[𝓝[>] 0]
      (fun t => (pgmScore (states t) {0, 1} - 1 / 3) - t / 6) := by
    filter_upwards [small_parameters] with t ht
    have ha := (domain t ht.1 ht.2).1
    rw [(scores t ht.1 ht.2).1]
    calc
      _ = (t / 6) * (t ^ 2 / (Real.sqrt (1 - t ^ 2) *
          (1 + Real.sqrt (1 - t ^ 2)))) := by dsimp [rA]; field_simp <;> ring
      _ = (t / 6) * (1 / Real.sqrt (1 - t ^ 2) - 1) := by
        rw [inverse_sqrt_residual (t ^ 2) ha]
      _ = _ := by ring
  have hPe : (fun t : ℝ => t ^ 3 * rP t) =ᶠ[𝓝[>] 0]
      (fun t => (pgmScore (states t) Finset.univ - 1 / 3) - t / 18 - 3 * t ^ 2 / 2) := by
    filter_upwards [small_parameters] with t ht
    have hv := (domain t ht.1 ht.2).2.2.2.2.2.2
    rw [(scores t ht.1 ht.2).2]
    have hr := inverse_sqrt_residual (4 * t ^ 2) hv
    have hd : 1 / (1 - 4 * t ^ 2) - 1 = 4 * t ^ 2 / (1 - 4 * t ^ 2) := by
      field_simp; ring
    calc
      _ = (t / 18) * (4 * t ^ 2 /
          (Real.sqrt (1 - 4 * t ^ 2) * (1 + Real.sqrt (1 - 4 * t ^ 2)))) +
          (3 * t ^ 2 / 2) * (4 * t ^ 2 / (1 - 4 * t ^ 2)) := by dsimp [rP]; field_simp <;> ring
      _ = (t / 18) * (1 / Real.sqrt (1 - 4 * t ^ 2) - 1) +
          (3 * t ^ 2 / 2) * (1 / (1 - 4 * t ^ 2) - 1) := by rw [hr, hd]
      _ = _ := by field_simp <;> ring
  have hA := (cubic_remainder rA hcA).congr' hAe EventuallyEq.rfl
  have hP := (cubic_remainder rP hcP).congr' hPe EventuallyEq.rfl
  refine ⟨hA, hP, ?_, ?_, ?_⟩
  · have hD := hA.sub (hP.const_mul_left (2 : ℝ))
    convert hD using 1
    funext t
    ring
  · let f : ℝ → ℝ := fun t => (1 / (6 * Real.sqrt (1 - t ^ 2))) /
      (1 / (18 * Real.sqrt (1 - 4 * t ^ 2)) + 3 * t / (2 * (1 - 4 * t ^ 2)))
    have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop (disch := norm_num)
    have he : f =ᶠ[𝓝[>] 0] (fun t => (pgmScore (states t) {0, 1} - 1 / 3) /
        (pgmScore (states t) Finset.univ - 1 / 3)) := by
      filter_upwards [small_parameters] with t ht
      rw [(scores t ht.1 ht.2).1, (scores t ht.1 ht.2).2]
      dsimp [f]
      have hn : t / (6 * Real.sqrt (1 - t ^ 2)) =
          t * (1 / (6 * Real.sqrt (1 - t ^ 2))) := by ring
      have hd : t / (18 * Real.sqrt (1 - 4 * t ^ 2)) +
          3 * t ^ 2 / (2 * (1 - 4 * t ^ 2)) =
          t * (1 / (18 * Real.sqrt (1 - 4 * t ^ 2)) +
            3 * t / (2 * (1 - 4 * t ^ 2))) := by ring
      rw [hn, hd, mul_div_mul_left _ _ ht.1.ne']
    apply Tendsto.congr' he
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num [f]
  · let f : ℝ → ℝ := fun t => (1 / 3 + t / (6 * Real.sqrt (1 - t ^ 2))) /
      (1 / 3 + t / (18 * Real.sqrt (1 - 4 * t ^ 2)) +
        3 * t ^ 2 / (2 * (1 - 4 * t ^ 2)))
    have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop (disch := norm_num)
    have he : f =ᶠ[𝓝[>] 0] (fun t => pgmScore (states t) {0, 1} /
        pgmScore (states t) Finset.univ) := by
      filter_upwards [small_parameters] with t ht
      have ha := (scores t ht.1 ht.2).1
      have hp := (scores t ht.1 ht.2).2
      have ha' : pgmScore (states t) {0, 1} = 1 / 3 + t / (6 * Real.sqrt (1 - t ^ 2)) := by linarith
      have hp' : pgmScore (states t) Finset.univ = 1 / 3 + t / (18 * Real.sqrt (1 - 4 * t ^ 2)) +
          3 * t ^ 2 / (2 * (1 - 4 * t ^ 2)) := by linarith
      rw [ha', hp']
    apply Tendsto.congr' he
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num [f]

/-- The restricted original-prior PGM effects in the original qubit basis. -/
def restrictedEffects (t : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![(1 / 2 : ℂ), ((1 / (4 * Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ);
       ((1 / (4 * Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ), (1 / 2 : ℂ)],
    !![(1 / 2 : ℂ), ((-1 / (4 * Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ);
       ((-1 / (4 * Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ), (1 / 2 : ℂ)], 0]

/-- The full actual PGM sends exactly five sixths of the weak basis direction
into the third label, independently of the positive parameter. -/
def fullEffects (t : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![(((1 - t ^ 2) / (3 * (1 - 4 * t ^ 2)) : ℝ) : ℂ),
       ((1 / (12 * Real.sqrt (1 - 4 * t ^ 2)) : ℝ) : ℂ);
       ((1 / (12 * Real.sqrt (1 - 4 * t ^ 2)) : ℝ) : ℂ), (1 / 12 : ℂ)],
    !![(((1 - t ^ 2) / (3 * (1 - 4 * t ^ 2)) : ℝ) : ℂ),
       ((-1 / (12 * Real.sqrt (1 - 4 * t ^ 2)) : ℝ) : ℂ);
       ((-1 / (12 * Real.sqrt (1 - 4 * t ^ 2)) : ℝ) : ℂ), (1 / 12 : ℂ)],
    diagonal ![(((1 - 10 * t ^ 2) / (3 * (1 - 4 * t ^ 2)) : ℝ) : ℂ), (5 / 6 : ℂ)]]

private theorem sandwich_entries (a b c x y : ℝ) :
    diagonal ![(x : ℂ), (y : ℂ)] *
      ((1 / 3 : ℂ) • !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)]) *
      diagonal ![(x : ℂ), (y : ℂ)] =
    !![((a * x ^ 2 / 3 : ℝ) : ℂ), ((b * (x * y) / 3 : ℝ) : ℂ);
       ((b * (x * y) / 3 : ℝ) : ℂ), ((c * y ^ 2 / 3 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring

set_option maxHeartbeats 800000 in
-- Exact CFC evaluation expands both three-effect families and their matrix entries.
/-- These displayed effects are equal to the actual CFC effects, and both
families are actual POVMs. The zero third restricted effect is included. -/
theorem pgm_effects (t : ℝ) (ht : 0 < t) (hhi : t ≤ 1 / 55) :
    pgmEffects (states t) {0, 1} = restrictedEffects t ∧
    pgmEffects (states t) Finset.univ = fullEffects t ∧
    finitePOVM (restrictedEffects t) ∧ finitePOVM (fullEffects t) := by
  obtain ⟨ha, ha1, hc, hc1, hd, hload, hv⟩ := domain t ht hhi
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsA : ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (t : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt ha.le
  have hsV : ((Real.sqrt (1 - 4 * t ^ 2) : ℝ) : ℂ) ^ 2 = 1 - 4 * (t : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt hv.le
  have hnV : 1 - (t : ℂ) ^ 2 * 4 ≠ 0 := by
    exact_mod_cast (show 1 - t ^ 2 * 4 ≠ 0 by nlinarith)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hSA : (∑ j ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • states t j) =
      diagonal ![((2 * (1 - t ^ 2) / 3 : ℝ) : ℂ), ((2 * t ^ 2 / 3 : ℝ) : ℂ)] := by
    rw [Finset.sum_pair (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [states, rho] <;> push_cast <;> ring
  have hS : (∑ j : Fin 3, (1 / (3 : ℂ)) • states t j) =
      diagonal ![((1 - 4 * t ^ 2 : ℝ) : ℂ), ((4 * t ^ 2 : ℝ) : ℂ)] := by
    rw [Fin.sum_univ_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [states, rho] <;> push_cast <;> ring
  let aa : Fin 3 → ℝ := ![1 - t ^ 2, 1 - t ^ 2, 1 - 10 * t ^ 2]
  let bb : Fin 3 → ℝ := ![t / 2, -t / 2, 0]
  let cc : Fin 3 → ℝ := ![t ^ 2, t ^ 2, 10 * t ^ 2]
  have hρ (i : Fin 3) : states t i =
      !![(aa i : ℂ), (bb i : ℂ); (bb i : ℂ), (cc i : ℂ)] := by
    fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
      simp [states, rho, aa, bb, cc] <;> push_cast <;> ring
  have hEA : pgmEffects (states t) {0, 1} = restrictedEffects t := by
    funext i
    fin_cases i
    · unfold pgmEffects
      norm_num only [Finset.mem_insert, Finset.mem_singleton, true_or, ↓reduceIte, Nat.cast_ofNat]
      rw [hSA, inverse_sqrt_two _ _ (by positivity) (by positivity)]
      change diagonal _ * ((1 / 3 : ℂ) • !![_, _; _, _]) * diagonal _ = _
      rw [sandwich_entries]
      ext x y
      fin_cases x <;> fin_cases y <;> simp [restrictedEffects] <;> push_cast <;> field_simp [htC] <;>
        simp only [hs2, hs3, hsA, hsV, Real.sqrt_sq ht.le] <;> push_cast <;> ring
    · unfold pgmEffects
      norm_num only [Finset.mem_insert, Finset.mem_singleton, false_or, ↓reduceIte, Nat.cast_ofNat]
      rw [hSA, inverse_sqrt_two _ _ (by positivity) (by positivity)]
      change diagonal _ * ((1 / 3 : ℂ) • !![_, _; _, _]) * diagonal _ = _
      rw [sandwich_entries]
      ext x y
      fin_cases x <;> fin_cases y <;> simp [restrictedEffects] <;> push_cast <;> field_simp [htC] <;>
        simp only [hs2, hs3, hsA, hsV, Real.sqrt_sq ht.le] <;> push_cast <;> ring
    · norm_num [pgmEffects, restrictedEffects]
  have hEP : pgmEffects (states t) Finset.univ = fullEffects t := by
    funext i
    unfold pgmEffects
    simp only [Finset.mem_univ, if_true, Nat.cast_ofNat]
    rw [hS, inverse_sqrt_two _ _ hv.le (by positivity), hρ i, sandwich_entries]
    fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
      simp [fullEffects, aa, bb, cc] <;> push_cast <;> field_simp [htC, hnV] <;>
      simp only [hs2, hs3, hsA, hsV, Real.sqrt_sq ht.le] <;> push_cast <;> norm_num <;> ring_nf <;> simp
  have hpsd : ∀ i, (states t i).PosSemidef := fun i => (family t ht hhi).1 i |>.1.posSemidef
  have hPA := (pgm_support (states t) hpsd {0, 1}).2.2.1
  have hPP := (pgm_support (states t) hpsd Finset.univ).2.2.1
  rw [hEA] at hPA
  rw [hEP] at hPP
  refine ⟨hEA, hEP, ⟨hPA, ?_⟩, ⟨hPP, ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [restrictedEffects, Fin.sum_univ_three, Matrix.one_apply] <;> field_simp <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [fullEffects, Fin.sum_univ_three, Matrix.one_apply] <;>
      push_cast <;> field_simp [hnV] <;> ring_nf <;> field_simp [hnV] <;> ring


end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmQubitSlice

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
