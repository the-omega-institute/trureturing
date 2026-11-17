/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmCommuting
   mirror-E: none(waiver:universal-commuting-proof)
   anchors: []
   utility: none
   digest: Commuting five-state control with every-optimum support activity. -/

import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import D5.S3.Quantum.Reduction.IsometricCompression

/-!
The commuting construction and symmetric scores are credited to Hyunho Cha
in the anonymous mechanism and the Haobo Ma–Wenlin Zhang note (4 November
2026). CC BY 4.0 applies only to the new note. The new content is the whole
interval and every actual optimum on the five-dimensional joint support;
an unused ambient kernel cannot impose a label on every POVM completion.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmCommuting
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity (diagonal_score)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- Common coordinate 0, rare coordinates 1..4, labels 0..3 and omitted label 4. -/
def population (ε : ℝ) (i x : Fin 5) : ℝ :=
  if i = 4 then if x = 0 then 1 - 2 * ε else ε / 2
  else if x = 0 then 1 - ε else if x.val = i.val + 1 then ε else 0

def states (ε : ℝ) (i : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal (fun x => (population ε i x : ℂ))

/-- Every choice of common-coordinate allocation yields a diagonal POVM. -/
def effects (w : Fin 5 → ℝ) (i : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal (fun x => if x = 0 then (w i : ℂ) else if x.val = i.val + 1 then 1 else 0)

private def dual (ε : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal (fun x => if x = 0 then ((1 - ε) / 5 : ℝ) else (ε / 5 : ℝ))

private theorem population_nonneg (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    ∀ i x, 0 ≤ population ε i x := by
  intro i x
  unfold population
  split_ifs <;> linarith

private theorem effects_povm (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : finitePOVM (effects w) := by
  constructor
  · intro i
    apply Matrix.PosSemidef.diagonal
    intro x
    change (0 : ℂ) ≤ if x = 0 then (w i : ℂ) else if x.val = i.val + 1 then 1 else 0
    split_ifs
    · exact_mod_cast hw i
    · norm_num
    · norm_num
  · ext x y
    fin_cases x <;> fin_cases y <;>
      simp [effects, Fin.sum_univ_succ, Matrix.one_apply]
    have hs : w 0 + w 1 + w 2 + w 3 + w 4 = 1 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hsum
    have hc := congrArg Complex.ofReal hs
    simpa [add_assoc] using hc

private theorem effects_score (ε : ℝ) (w : Fin 5 → ℝ) (hzero : w 4 = 0)
    (hsum : ∑ i, w i = 1) : success (states ε) (effects w) = (1 + 3 * ε) / 5 := by
  have hs : w 0 + w 1 + w 2 + w 3 = 1 := by
    simpa [Fin.sum_univ_succ, hzero, add_assoc] using hsum
  simp [success, states, effects, population, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, hzero]
  push_cast at hs ⊢
  linear_combination ((1 - ε) / 5) * hs

private theorem slack_form (ε : ℝ) (i : Fin 5) :
    dual ε - (1 / (5 : ℂ)) • states ε i =
      diagonal (fun x => (((if x = 0 then (1 - ε) / 5 else ε / 5) -
        population ε i x / 5 : ℝ) : ℂ)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [dual, states, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_apply_eq, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  · simp [dual, states, Matrix.diagonal_apply, hxy]

private theorem dual_slacks (ε : ℝ) (hε : 0 < ε) :
    ∀ i, (dual ε - (1 / (5 : ℂ)) • states ε i).PosSemidef := by
  intro i
  rw [slack_form]
  apply Matrix.PosSemidef.diagonal
  intro x
  change (0 : ℂ) ≤ _
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Complex.ofReal_re]
    unfold population
    split_ifs <;> linarith
  · simp

private theorem dual_trace (ε : ℝ) : (trace (dual ε)).re = (1 + 3 * ε) / 5 := by
  simp [dual, trace, Fin.sum_univ_succ]
  ring

/-- Every optimum has the same four active labels on the joint support,
although the optimum itself is nonunique. No restriction to diagonal competing
POVMs is made: E ranges over all complex effects. -/
theorem every_optimum (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    (∀ i, (states ε i).PosSemidef ∧ trace (states ε i) = 1) ∧
    (∀ i j, Commute (states ε i) (states ε j)) ∧
    ∃ E₀, finitePOVM E₀ ∧ success (states ε) E₀ = (1 + 3 * ε) / 5 ∧
      ∀ E, finitePOVM E →
        (∀ F, finitePOVM F → success (states ε) F ≤ success (states ε) E) →
          success (states ε) E = (1 + 3 * ε) / 5 ∧
          Finset.univ.filter (fun i => E i ≠ 0) = {0, 1, 2, 3} := by
  let w : Fin 5 → ℝ := fun i => if i = 0 then 1 else 0
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> norm_num
  have hsum : ∑ i, w i = 1 := by simp [w]
  have hzero : w 4 = 0 := by norm_num [w]
  have hE₀ := effects_povm w hw hsum
  have hscore₀ := effects_score ε w hzero hsum
  refine ⟨?_, ?_, effects w, hE₀, hscore₀, ?_⟩
  · intro i
    refine ⟨Matrix.PosSemidef.diagonal (fun x => by
      change (0 : ℂ) ≤ (population ε i x : ℂ)
      exact_mod_cast population_nonneg ε hε hhi i x), ?_⟩
    fin_cases i <;> simp [states, population, trace, Fin.sum_univ_succ] <;> ring
  · intro i j
    change states ε i * states ε j = states ε j * states ε i
    simp only [states, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact mul_comm _ _
  · intro E hE hopt
    have hle := dual_bound (states ε) E (dual ε) hE (dual_slacks ε hε)
    have hge := hopt (effects w) hE₀
    rw [dual_trace] at hle
    have heq : success (states ε) E = (1 + 3 * ε) / 5 := by linarith
    refine ⟨heq, ?_⟩
    have hprod := complementary_products (states ε) E (dual ε) hE
      (dual_slacks ε hε) (by rw [dual_trace]; exact heq)
    have hrow (i x y : Fin 5) :
        (((if x = 0 then (1 - ε) / 5 else ε / 5) - population ε i x / 5 : ℝ) : ℂ) *
          E i x y = 0 := by
      have hp := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M x y) (hprod i)
      norm_num only [Nat.cast_ofNat] at hp
      rw [slack_form] at hp
      simpa only [Matrix.diagonal_mul, Matrix.zero_apply] using hp
    have hE4 : E 4 = 0 := by
      ext x y
      have hr := hrow 4 x y
      have hc : ((if x = 0 then (1 - ε) / 5 else ε / 5) - population ε 4 x / 5 : ℝ) ≠ 0 := by
        unfold population
        split_ifs <;> norm_num at * <;> linarith
      exact (mul_eq_zero.mp hr).resolve_left (by exact_mod_cast hc)
    have hactive (i : Fin 5) (hi : i ≠ 4) : E i ≠ 0 := by
      let x : Fin 5 := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hother (j : Fin 5) (hj : j ≠ i) : E j x x = 0 := by
        by_cases hj4 : j = 4
        · simp [hj4, hE4]
        · have hr := hrow j x x
          have hx0 : x ≠ 0 := by
            intro he
            have hv := congrArg Fin.val he
            dsimp [x] at hv
            omega
          have hxi : x.val ≠ j.val + 1 := by
            intro h; apply hj; apply Fin.ext; dsimp [x] at h; omega
          have hc : ((if x = 0 then (1 - ε) / 5 else ε / 5) - population ε j x / 5 : ℝ) ≠ 0 := by
            simpa only [population, if_neg hj4, if_neg hx0, if_neg hxi,
              zero_div, sub_zero] using div_ne_zero hε.ne' (by norm_num : (5 : ℝ) ≠ 0)
          exact (mul_eq_zero.mp hr).resolve_left (by exact_mod_cast hc)
      have hs := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M x x) hE.2
      have hone : E i x x = 1 := by
        have hs' : (∑ j, E j x x) = 1 := by
          simpa only [Matrix.sum_apply, Matrix.one_apply_eq] using hs
        rw [Finset.sum_eq_single i] at hs'
        · exact hs'
        · intro j _ hj
          exact hother j hj
        · simp
      intro hz
      rw [hz] at hone
      norm_num at hone
    ext i
    fin_cases i <;> simp [hE4, hactive 0 (by decide), hactive 1 (by decide),
      hactive 2 (by decide), hactive 3 (by decide)]

/-- Exact actual PGM scores and the strict gap on the complete open interval. -/
theorem scores_and_gap (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    pgmScore (states ε) {0, 1, 2, 3} = (1 + 3 * ε) / 5 ∧
    pgmScore (states ε) Finset.univ =
      1 / 5 + 32 * ε / 75 + 4 * ε ^ 2 / (25 * (5 - 6 * ε)) ∧
    3 * (pgmScore (states ε) {0, 1, 2, 3} - 1 / 5) -
      4 * (pgmScore (states ε) Finset.univ - 1 / 5) =
        ε * (7 - 18 * ε) / (15 * (5 - 6 * ε)) ∧
    0 < 3 * (pgmScore (states ε) {0, 1, 2, 3} - 1 / 5) -
      4 * (pgmScore (states ε) Finset.univ - 1 / 5) := by
  have hε1 : 1 - ε ≠ 0 := by linarith
  have hden : 5 - 6 * ε ≠ 0 := by linarith
  have hpA := diagonal_score (by decide : 0 < 5) (population ε)
    (population_nonneg ε hε hhi) {0, 1, 2, 3}
  have hp := diagonal_score (by decide : 0 < 5) (population ε)
    (population_nonneg ε hε hhi) Finset.univ
  have hA : pgmScore (states ε) {0, 1, 2, 3} = (1 + 3 * ε) / 5 := by
    rw [show pgmScore (states ε) _ = _ from hpA]
    norm_num [population, Fin.sum_univ_succ]
    field_simp <;> ring_nf <;>
      field_simp [show 5 - ε * 6 ≠ 0 by linarith] <;> ring
  have hP : pgmScore (states ε) Finset.univ =
      1 / 5 + 32 * ε / 75 + 4 * ε ^ 2 / (25 * (5 - 6 * ε)) := by
    rw [show pgmScore (states ε) _ = _ from hp]
    norm_num [population, Fin.sum_univ_succ]
    field_simp <;> ring_nf <;>
      field_simp [show 5 - ε * 6 ≠ 0 by linarith] <;> ring
  have hgap : 3 * (pgmScore (states ε) {0, 1, 2, 3} - 1 / 5) -
      4 * (pgmScore (states ε) Finset.univ - 1 / 5) =
      ε * (7 - 18 * ε) / (15 * (5 - 6 * ε)) := by
    rw [hA, hP]
    field_simp <;> ring_nf <;>
      field_simp [show 5 - ε * 6 ≠ 0 by linarith] <;> ring
  refine ⟨hA, hP, hgap, ?_⟩
  rw [hgap]
  exact div_pos (mul_pos hε (by linarith)) (by linarith)

/-- Two distinct actual optimal POVMs realize the common-coordinate tie. -/
theorem nonunique (ε : ℝ) (hε : 0 < ε) :
    ∃ E F : Fin 5 → Matrix (Fin 5) (Fin 5) ℂ,
      E ≠ F ∧ finitePOVM E ∧ finitePOVM F ∧
      (∀ G, finitePOVM G → success (states ε) G ≤ success (states ε) E) ∧
      (∀ G, finitePOVM G → success (states ε) G ≤ success (states ε) F) := by
  let w : Fin 5 → ℝ := fun i => if i = 0 then 1 else 0
  let v : Fin 5 → ℝ := fun i => if i = 1 then 1 else 0
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> norm_num
  have hv : ∀ i, 0 ≤ v i := by intro i; dsimp [v]; split_ifs <;> norm_num
  have hsw : ∑ i, w i = 1 := by simp [w]
  have hsv : ∑ i, v i = 1 := by simp [v]
  refine ⟨effects w, effects v, ?_, effects_povm w hw hsw, effects_povm v hv hsv, ?_, ?_⟩
  · intro h
    have he := congrArg (fun E : Fin 5 → Matrix (Fin 5) (Fin 5) ℂ => E 0 0 0) h
    norm_num [effects, w, v] at he
  · intro G hG
    rw [effects_score ε w (by norm_num [w]) hsw, ← dual_trace]
    exact dual_bound _ _ _ hG (dual_slacks ε hε)
  · intro G hG
    rw [effects_score ε v (by norm_num [v]) hsv, ← dual_trace]
    exact dual_bound _ _ _ hG (dual_slacks ε hε)

open Filter Topology in
/-- The exact ratio limit belongs to the actual CFC scores on the joint support. -/
theorem centered_ratio_limit :
    Tendsto (fun ε : ℝ => (pgmScore (states ε) Finset.univ - 1 / 5) /
      (pgmScore (states ε) {0, 1, 2, 3} - 1 / 5)) (𝓝[>] 0) (𝓝 (32 / 45)) := by
  let f : ℝ → ℝ := fun ε => 32 / 45 + 4 * ε / (15 * (5 - 6 * ε))
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop (disch := norm_num)
  have he : f =ᶠ[𝓝[>] 0] (fun ε : ℝ => (pgmScore (states ε) Finset.univ - 1 / 5) /
      (pgmScore (states ε) {0, 1, 2, 3} - 1 / 5)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 7 / 18)).filter_mono nhdsWithin_le_nhds]
      with ε hε hhi
    obtain ⟨hA, hP, -⟩ := scores_and_gap ε hε hhi
    rw [hA, hP]
    have hε0 : ε ≠ 0 := ne_of_gt hε
    dsimp [f]
    field_simp [hε0] <;> ring_nf <;> field_simp [hε0] <;> ring
  apply Tendsto.congr' he
  simpa [f] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The four selected physical density matrices each have exactly rank two. -/
theorem selected_ranks (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    ∀ i : Fin 4, (states ε (Fin.castLE (by decide) i)).rank = 2 := by
  intro i
  have h0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h1 : (1 - (ε : ℂ)) ≠ 0 := by
    have : (1 - ε : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hu : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  fin_cases i <;>
    norm_num [states, Matrix.rank_diagonal, Fintype.card_subtype, hu, Finset.filter_insert, Finset.filter_singleton, population,
      h0, h1, hε.ne', show 1 - ε ≠ 0 by linarith]

/-- The physical five-dimensional model fills its joint spectral support.
This identifies the support to be compressed when padding the model. -/
theorem joint_support (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport
      (∑ i, (1 / (5 : ℂ)) • states ε i) = 1 := by
  let s : Fin 5 → ℝ := fun x => if x = 0 then (5 - 6 * ε) / 5 else 3 * ε / 10
  have hs : (∑ i, (1 / (5 : ℂ)) • states ε i) = diagonal (fun x => (s x : ℂ)) := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [states, population, s, Matrix.sum_apply, Fin.sum_univ_succ] <;> ring
  have hn (x : Fin 5) : s x ≠ 0 := by
    dsimp [s]
    split_ifs <;> linarith
  rw [hs, D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [hn]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hxy]


/-- The fixed inclusion of the five joint-support coordinates into dimension eight. -/
def supportInclusion : Fin 5 → Fin 8 := Fin.castLE (by decide)

private def supportFrame : Matrix (Fin 8) (Fin 5) ℂ :=
  (1 : Matrix (Fin 8) (Fin 8) ℂ).submatrix id supportInclusion

/-- Actual states padded by zero on the three unused ambient coordinates. -/
def embeddedStates (ε : ℝ) (i : Fin 5) : Matrix (Fin 8) (Fin 8) ℂ :=
  supportFrame * states ε i * supportFrameᴴ

private theorem compression_eq (M : Matrix (Fin 8) (Fin 8) ℂ) :
    D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame M =
      M.submatrix supportInclusion supportInclusion := by
  unfold D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame
  simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix (Fin 8) (Fin 8) ℂ).submatrix supportInclusion (Equiv.refl _) *
    M * (1 : Matrix (Fin 8) (Fin 8) ℂ).submatrix (Equiv.refl _) supportInclusion = _
  rw [Matrix.one_submatrix_mul supportInclusion (Equiv.refl _) M,
    Matrix.mul_submatrix_one (Equiv.refl _) supportInclusion]
  rfl

private theorem frame_isometry : supportFrameᴴ * supportFrame = 1 := by
  calc
    supportFrameᴴ * supportFrame =
        D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame 1 := by
          simp [D5.S3.Quantum.Reduction.IsometricCompression.compress]
    _ = 1 := by
      rw [compression_eq]
      exact Matrix.submatrix_one supportInclusion (by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Fin 8 => x.val) hij)

private theorem embedded_success (ε : ℝ) (E : Fin 5 → Matrix (Fin 8) (Fin 8) ℂ) :
    success (embeddedStates ε) E = success (states ε)
      (fun i => (E i).submatrix supportInclusion supportInclusion) := by
  unfold success
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← compression_eq]
  simp only [embeddedStates, Matrix.smul_mul, trace_smul]
  congr 2
  calc
    trace (supportFrame * states ε i * supportFrameᴴ * E i) =
        trace (supportFrame * (states ε i * (supportFrameᴴ * E i))) := by
          simp only [Matrix.mul_assoc]
    _ = trace ((states ε i * (supportFrameᴴ * E i)) * supportFrame) :=
      Matrix.trace_mul_comm _ _
    _ = trace (states ε i *
        D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame (E i)) := by
      simp only [D5.S3.Quantum.Reduction.IsometricCompression.compress, Matrix.mul_assoc]

private theorem compressed_povm (E : Fin 5 → Matrix (Fin 8) (Fin 8) ℂ)
    (hE : finitePOVM E) :
    finitePOVM (fun i => (E i).submatrix supportInclusion supportInclusion) := by
  refine ⟨fun i => (hE.1 i).submatrix _, ?_⟩
  ext x y
  have hs := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ =>
    M (supportInclusion x) (supportInclusion y)) hE.2
  simpa only [Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.one_apply, supportInclusion, Fin.castLE_inj] using hs

private theorem lifted_povm (G : Fin 5 → Matrix (Fin 5) (Fin 5) ℂ) (hG : finitePOVM G) :
    ∃ H : Fin 5 → Matrix (Fin 8) (Fin 8) ℂ,
      finitePOVM H ∧ (fun i => (H i).submatrix supportInclusion supportInclusion) = G := by
  let P := supportFrame * supportFrameᴴ
  let K : Matrix (Fin 8) (Fin 8) ℂ := 1 - P
  have hP : P = diagonal (fun x : Fin 8 => if x.val < 5 then 1 else 0) := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      norm_num [P, supportFrame, supportInclusion, Matrix.mul_apply,
        Matrix.one_apply, Fin.sum_univ_succ]
  have hK : K.PosSemidef := by
    have he : K = diagonal (fun x : Fin 8 => if x.val < 5 then 0 else 1) := by
      ext x y
      rw [show K = 1 - P from rfl, hP]
      by_cases hxy : x = y
      · subst y; simp; split_ifs <;> norm_num
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hxy]
    rw [he]
    apply Matrix.PosSemidef.diagonal
    intro x
    change (0 : ℂ) ≤ (if x.val < 5 then 0 else 1)
    split_ifs <;> norm_num
  have hGK (A : Matrix (Fin 5) (Fin 5) ℂ) :
      D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame
        (supportFrame * A * supportFrameᴴ) = A := by
    unfold D5.S3.Quantum.Reduction.IsometricCompression.compress
    rw [← Matrix.mul_assoc supportFrameᴴ (supportFrame * A) supportFrameᴴ,
      ← Matrix.mul_assoc supportFrameᴴ supportFrame A, frame_isometry,
      Matrix.one_mul, Matrix.mul_assoc, frame_isometry, Matrix.mul_one]
  have hK0 : D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame K = 0 := by
    change supportFrameᴴ * (1 - supportFrame * supportFrameᴴ) * supportFrame = 0
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, frame_isometry]
    have hh := hGK (1 : Matrix (Fin 5) (Fin 5) ℂ)
    simpa [D5.S3.Quantum.Reduction.IsometricCompression.compress] using
      congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ => 1 - A) hh
  let H : Fin 5 → Matrix (Fin 8) (Fin 8) ℂ := fun i =>
    supportFrame * G i * supportFrameᴴ + if i = 0 then K else 0
  refine ⟨H, ⟨?_, ?_⟩, ?_⟩
  · intro i
    apply ((hG.1 i).mul_mul_conjTranspose_same supportFrame).add
    split_ifs
    · exact hK
    · exact Matrix.PosSemidef.zero
  · change (∑ i, (supportFrame * G i * supportFrameᴴ + if i = 0 then K else 0)) = 1
    rw [Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum, hG.2]
    simp [K, P]
  · funext i
    rw [← compression_eq]
    change supportFrameᴴ * (supportFrame * G i * supportFrameᴴ +
      if i = 0 then K else 0) * supportFrame = G i
    rw [Matrix.mul_add, Matrix.add_mul]
    change D5.S3.Quantum.Reduction.IsometricCompression.compress supportFrame
      (supportFrame * G i * supportFrameᴴ) + _ = G i
    rw [hGK]
    split_ifs
    · rw [show supportFrameᴴ * K * supportFrame = 0 from hK0, add_zero]
    · simp

/-- Ambient dimension eight retains the exact five-dimensional support model.
Every ambient optimum has the four specified active labels after compression;
no assertion is made about effects living only on the unused kernel. -/
theorem dimension_eight_optima (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    (∀ i, (embeddedStates ε i).PosSemidef ∧ trace (embeddedStates ε i) = 1) ∧
    (∃ E₀, finitePOVM E₀ ∧
      (∀ F, finitePOVM F → success (embeddedStates ε) F ≤ success (embeddedStates ε) E₀)) ∧
    (∀ E, finitePOVM E →
      (∀ F, finitePOVM F → success (embeddedStates ε) F ≤ success (embeddedStates ε) E) →
      success (embeddedStates ε) E = (1 + 3 * ε) / 5 ∧
        Finset.univ.filter (fun i =>
          (E i).submatrix supportInclusion supportInclusion ≠ 0) = {0, 1, 2, 3}) := by
  obtain ⟨hstates, hcomm, E₀, hpovm, hscore, hall⟩ := every_optimum ε hε hhi
  obtain ⟨H₀, hH₀, hc₀⟩ := lifted_povm E₀ hpovm
  refine ⟨?_, ⟨H₀, hH₀, ?_⟩, ?_⟩
  · intro i
    refine ⟨(hstates i).1.mul_mul_conjTranspose_same supportFrame, ?_⟩
    rw [embeddedStates, Matrix.trace_mul_cycle, frame_isometry, Matrix.one_mul]
    exact (hstates i).2
  · intro F hF
    rw [embedded_success, embedded_success, hc₀, hscore, ← dual_trace]
    exact dual_bound _ _ _ (compressed_povm F hF) (dual_slacks ε hε)
  · intro E hE hopt
    have hp := compressed_povm E hE
    have ho : ∀ G, finitePOVM G → success (states ε) G ≤
        success (states ε) (fun i => (E i).submatrix supportInclusion supportInclusion) := by
      intro G hG
      obtain ⟨H, hH, hc⟩ := lifted_povm G hG
      have hb := hopt H hH
      rw [embedded_success, embedded_success, hc] at hb
      exact hb
    have ht := hall _ hp ho
    rw [embedded_success]
    exact ht

private def population8 (ε : ℝ) (i : Fin 5) (x : Fin 8) : ℝ :=
  if hx : x.val < 5 then population ε i ⟨x.val, hx⟩ else 0

set_option maxHeartbeats 2000000 in
-- The fixed 5-by-8-by-8 entry calculation expands the finite zero padding.
private theorem embedded_diagonal (ε : ℝ) (i : Fin 5) :
    embeddedStates ε i = diagonal (fun x => (population8 ε i x : ℂ)) := by
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [embeddedStates, supportFrame, supportInclusion, states, population8,
      population, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- Exact eight-coordinate support, rank and CFC sums exceed the default budget.
/-- The embedding has the actual rank-five spectral support and exactly the
same original-prior PGM scores, with Moore-Penrose zero action on its kernel. -/
theorem dimension_eight_support_and_scores (ε : ℝ) (hε : 0 < ε) (hhi : ε < 7 / 18) :
    D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport
      (∑ i, (1 / (5 : ℂ)) • embeddedStates ε i) =
        diagonal (fun x : Fin 8 => if x.val < 5 then 1 else 0) ∧
    (∀ i : Fin 4, (embeddedStates ε (Fin.castLE (by decide) i)).rank = 2) ∧
    pgmScore (embeddedStates ε) {0, 1, 2, 3} = (1 + 3 * ε) / 5 ∧
    pgmScore (embeddedStates ε) Finset.univ =
      1 / 5 + 32 * ε / 75 + 4 * ε ^ 2 / (25 * (5 - 6 * ε)) := by
  let mass : Fin 8 → ℝ := fun x =>
    if x = 0 then (5 - 6 * ε) / 5 else if x.val < 5 then 3 * ε / 10 else 0
  have hstates : embeddedStates ε = fun i => diagonal (fun x => (population8 ε i x : ℂ)) :=
    funext (embedded_diagonal ε)
  have havg : (∑ i, (1 / (5 : ℂ)) • embeddedStates ε i) =
      diagonal (fun x => (mass x : ℂ)) := by
    rw [hstates]
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [mass, population8, population, Matrix.sum_apply, Fin.sum_univ_succ] <;>
      push_cast <;> ring
  have hp8 : ∀ i x, 0 ≤ population8 ε i x := by
    intro i x
    dsimp [population8]
    split_ifs
    · exact population_nonneg ε hε hhi _ _
    · norm_num
  have hε1 : 1 - ε ≠ 0 := by linarith
  have hden : 5 - 6 * ε ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [havg, D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport,
      D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [mass, show (5 - 6 * ε) / 5 ≠ 0 by positivity,
        show 3 * ε / 10 ≠ 0 by positivity]
  · intro i
    have h0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have h1 : (1 - (ε : ℂ)) ≠ 0 := by exact_mod_cast hε1
    rw [embedded_diagonal]
    have hu : (Finset.univ : Finset (Fin 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
    fin_cases i <;>
      norm_num [Matrix.rank_diagonal, Fintype.card_subtype, hu, Finset.filter_insert, Finset.filter_singleton, population8,
        population, h0, h1, hε.ne', hε1]
  · rw [hstates, diagonal_score (by decide : 0 < 5) (population8 ε) hp8 {0, 1, 2, 3}]
    norm_num [population8, population, Fin.sum_univ_succ]
    field_simp <;> ring_nf <;>
      field_simp [show 5 - ε * 6 ≠ 0 by linarith] <;> ring
  · rw [hstates, diagonal_score (by decide : 0 < 5) (population8 ε) hp8 Finset.univ]
    norm_num [population8, population, Fin.sum_univ_succ]
    field_simp <;> ring_nf <;>
      field_simp [show 5 - ε * 6 ≠ 0 by linarith] <;> ring


end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmCommuting

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
