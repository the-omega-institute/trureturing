/- GID: D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope
   generality: I
   mirror-B: D5/B/S3/Observer/TraceFibers/ThreeActionModulusEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-action words reduce to seven coefficient shapes, and the two non-dominated shapes cross once. -/

import D5.S3.Observer.TraceFibers.FixedFiberPairModulus
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

noncomputable section

namespace D5.S3.Observer.TraceFibers.ThreeActionModulusEnvelope

open D5.S3.Observer.TraceFibers.FixedFiberPairModulus

private def shape (w : List Action) : ℝ × ℝ :=
  (wordMatrix w 1 1 - wordMatrix w 0 0, wordMatrix w 1 0)

private theorem short_word_shapes (w : List Action) (hw : w.length ≤ 3) :
    shape w = (0, 0) ∨ shape w = (0, 1) ∨ shape w = (1, 1) ∨
      shape w = (0, 2) ∨ shape w = (-1, 1) ∨ shape w = (2, 1) ∨
      shape w = (2, 2) := by
  cases w with
  | nil =>
      simp [shape, wordMatrix]
  | cons a w =>
      cases w with
      | nil =>
          cases a <;>
            norm_num [shape, wordMatrix, actionMatrix,
              GoldenCoding.GoldenModularStandardPair.goldenModularStep,
              HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
              Matrix.mul_apply, Fin.sum_univ_two]
      | cons b w =>
          cases w with
          | nil =>
              cases a <;> cases b <;>
                norm_num [shape, wordMatrix, actionMatrix,
                  GoldenCoding.GoldenModularStandardPair.goldenModularStep,
                  HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
                  Matrix.mul_apply, Fin.sum_univ_two]
          | cons c w =>
              cases w with
              | nil =>
                  cases a <;> cases b <;> cases c <;>
                    norm_num [shape, wordMatrix, actionMatrix,
                      GoldenCoding.GoldenModularStandardPair.goldenModularStep,
                      HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
                      Matrix.mul_apply, Fin.sum_univ_two]
              | cons d w =>
                  simp only [List.length_cons, Nat.reduceAdd] at hw
                  omega

private def phiS (r h d : ℝ) : ℝ := (2 - h) * d + d ^ 2 / r

private def phiA (r h d : ℝ) : ℝ := (2 - 2 * h) * d + 2 * d ^ 2 / r

private theorem finite_envelope_facts
    (k : ℕ) (h x r τ : ℝ)
    (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hx : x = (k + h) * r) (hτ : 0 ≤ τ) :
    let τstar := 2 * r * h
    let dstar := r * h
    let ts := (k + 2) * x
    let ta := 2 * (k + 1) * x
    τstar = 2 * dstar ∧ 0 < τstar ∧ τstar < ts ∧ ts < ta ∧
    (∀ d, phiA r h d - phiS r h d = d * (d / r - h)) ∧
    (∀ w : List Action, w.length ≤ 3 →
      shape w = (0, 0) ∨ shape w = (0, 1) ∨ shape w = (1, 1) ∨
        shape w = (0, 2) ∨ shape w = (-1, 1) ∨ shape w = (2, 1) ∨
        shape w = (2, 2)) := by
  dsimp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hxp : 0 < x := by rw [hx]; positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hks : (0 : ℝ) < k + 1 := by positivity
  have hts : 0 < (k + 2) * x := by positivity
  have hta : 0 < 2 * (k + 1) * x := by positivity
  have hcross : 2 * r * h = 2 * (r * h) := by ring
  have hlt1 : 2 * r * h < (k + 2) * x := by
    rw [hx]
    nlinarith
  have hlt2 : (k + 2) * x < 2 * (k + 1) * x := by
    nlinarith
  refine ⟨hcross, by positivity, hlt1, hlt2, ?_, ?_⟩
  · intro d
    dsimp [phiS, phiA]
    ring
  · intro w hw
    exact short_word_shapes w hw

private theorem scalar_formula_of_result
    (upper : Bool) (executed continuation : List Action) (k : ℕ)
    (x ζ τ : ℝ) (hx : 0 < x) (hζ : 0 < ζ) (hk : 1 ≤ k)
    (hexecuted : wordMatrix executed = secondMatrix upper k)
    (he : 0 < (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
      else (wordMatrix continuation * wordMatrix executed) 0 1))
    (hμ : 0 ≤ |(wordMatrix continuation * wordMatrix executed) 1 1 -
      (wordMatrix continuation * wordMatrix executed) 0 0| -
      (if upper then (wordMatrix continuation * wordMatrix executed) 1 0
        else (wordMatrix continuation * wordMatrix executed) 0 1) / ζ * x)
    (hτ : 0 ≤ τ) :
    let B := wordMatrix continuation * wordMatrix executed
    let e := if upper then B 1 0 else B 0 1
    let D := B 1 1 - B 0 0
    let α := e / ζ
    let μ := |D| - α * x
    scalarModulus upper x ζ B τ =
      min x ((Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)) := by
  have hres := result upper executed continuation k x ζ τ hx hζ hk hexecuted hτ he hμ
  dsimp only at hres
  rcases hres with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscalar, _, _, _⟩
  exact hscalar

/-- The finite word classification and the fixed-fiber scalar interface share
    one conclusion; the entry hypotheses identify the two displayed words with
    their corresponding cumulative matrices. -/
theorem three_action_modulus_envelope
    (k : ℕ) (h x r τ : ℝ) (executed : List Action)
    (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hx : x = (k + h) * r) (hτ : 0 ≤ τ)
    (hexecuted : wordMatrix executed = secondMatrix true k)
    (hS_e : (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 0 = 1)
    (hS_D : |(wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.exchange, Action.advance] *
        wordMatrix executed) 0 0| = k + 2)
    (hA_e : (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 0 = 2)
    (hA_D : |(wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 1 -
      (wordMatrix [Action.advance, Action.advance, Action.advance] *
        wordMatrix executed) 0 0| = 2 * k + 2) :
    let τstar := 2 * r * h
    let dstar := r * h
    let ts := (k + 2) * x
    let ta := 2 * (k + 1) * x
    τstar = 2 * dstar ∧ 0 < τstar ∧ τstar < ts ∧ ts < ta ∧
    (∀ d, phiA r h d - phiS r h d = d * (d / r - h)) ∧
    (∀ w : List Action, w.length ≤ 3 →
      shape w = (0, 0) ∨ shape w = (0, 1) ∨ shape w = (1, 1) ∨
        shape w = (0, 2) ∨ shape w = (-1, 1) ∨ shape w = (2, 1) ∨
        shape w = (2, 2)) ∧
    scalarModulus true x r
        (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) τ =
      min x ((Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) / (2 / r)) ∧
    scalarModulus true x r
        (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) τ =
      min x ((Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) / (4 / r)) := by
  dsimp
  have hbase := finite_envelope_facts k h x r τ hk hh hh1 hr hx hτ
  have hxpos : 0 < x := by rw [hx]; positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hS_e_pos : 0 < (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 0 := by rw [hS_e]; norm_num
  have hA_e_pos : 0 < (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 0 := by rw [hA_e]; norm_num
  have hS_mu : 0 ≤ |(wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 1 - (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 0 0| - (wordMatrix [Action.advance, Action.exchange, Action.advance] *
      wordMatrix executed) 1 0 / r * x := by
    rw [hS_D, hS_e, hx]
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    field_simp
    nlinarith
  have hA_mu : 0 ≤ |(wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 1 - (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 0 0| - (wordMatrix [Action.advance, Action.advance, Action.advance] *
      wordMatrix executed) 1 0 / r * x := by
    rw [hA_D, hA_e, hx]
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    field_simp
    nlinarith
  have hS := scalar_formula_of_result true executed
    [Action.advance, Action.exchange, Action.advance] k x r τ hxpos hr hk hexecuted hS_e_pos hS_mu hτ
  have hA := scalar_formula_of_result true executed
    [Action.advance, Action.advance, Action.advance] k x r τ hxpos hr hk hexecuted hA_e_pos hA_mu hτ
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hbase.2.2.2.2.1,
    hbase.2.2.2.2.2, ?_, ?_⟩
  · dsimp at hS
    have hlinear : (k : ℝ) + 2 - 1 / r * x = 2 - h := by
      rw [hx]
      field_simp [hr0]
      ring
    have hroot :
        (Real.sqrt (((k : ℝ) + 2 - 1 / r * x) ^ 2 + 4 * (1 / r) * τ) -
          ((k : ℝ) + 2 - 1 / r * x)) / (2 * (1 / r)) =
        (Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) / (2 / r) := by
      rw [hlinear]
      have hrad : (2 - h) ^ 2 + 4 * (1 / r) * τ =
          (2 - h) ^ 2 + 4 * τ / r := by
        field_simp [hr0] <;> ring
      rw [hrad]
      field_simp [hr0] <;> ring
    calc
      scalarModulus true x r
          (wordMatrix [Action.advance, Action.exchange, Action.advance] * wordMatrix executed) τ =
        min x ((Real.sqrt (((k : ℝ) + 2 - 1 / r * x) ^ 2 + 4 * (1 / r) * τ) -
          ((k : ℝ) + 2 - 1 / r * x)) / (2 * (1 / r))) := by
            simpa [hS_e, hS_D] using hS
      _ = min x ((Real.sqrt ((2 - h) ^ 2 + 4 * τ / r) - (2 - h)) /
          (2 / r)) := by
            rw [hroot]
  · dsimp at hA
    have hlinear : 2 * (k : ℝ) + 2 - 2 / r * x = 2 - 2 * h := by
      rw [hx]
      field_simp [hr0]
      ring
    have hroot :
        (Real.sqrt ((2 * (k : ℝ) + 2 - 2 / r * x) ^ 2 + 4 * (2 / r) * τ) -
          (2 * (k : ℝ) + 2 - 2 / r * x)) / (2 * (2 / r)) =
      (Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) / (4 / r) := by
      rw [hlinear]
      have hrad : (2 - 2 * h) ^ 2 + 4 * (2 / r) * τ =
          (2 - 2 * h) ^ 2 + 8 * τ / r := by
        field_simp [hr0] <;> ring
      rw [hrad]
      field_simp [hr0] <;> ring
    calc
      scalarModulus true x r
          (wordMatrix [Action.advance, Action.advance, Action.advance] * wordMatrix executed) τ =
        min x ((Real.sqrt ((2 * (k : ℝ) + 2 - 2 / r * x) ^ 2 + 4 * (2 / r) * τ) -
          (2 * (k : ℝ) + 2 - 2 / r * x)) / (2 * (2 / r))) := by
            simpa [hA_e, hA_D] using hA
      _ = min x ((Real.sqrt ((2 - 2 * h) ^ 2 + 8 * τ / r) - (2 - 2 * h)) /
          (4 / r)) := by
            rw [hroot]

end D5.S3.Observer.TraceFibers.ThreeActionModulusEnvelope
