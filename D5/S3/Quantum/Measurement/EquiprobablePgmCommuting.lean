/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmCommuting
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmCommuting
   mirror-E: none(waiver:universal-commuting-proof)
   anchors: []
   utility: none
   digest: Commuting five-state control with every-optimum support activity. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric

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
namespace D5.S3.Quantum.Measurement.EquiprobablePgmCommuting
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity (diagonal_score)
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

end D5.S3.Quantum.Measurement.EquiprobablePgmCommuting

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
