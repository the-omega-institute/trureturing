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

def shape (w : List Action) : ℝ × ℝ :=
  (wordMatrix w 1 1 - wordMatrix w 0 0, wordMatrix w 1 0)

theorem short_word_shapes (w : List Action) (hw : w.length ≤ 3) :
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

def root (μ α τ : ℝ) : ℝ :=
  (Real.sqrt (μ ^ 2 + 4 * α * τ) - μ) / (2 * α)

def clipped (x μ α τ : ℝ) : ℝ := min x (root μ α τ)

def omegaS (x r h τ : ℝ) : ℝ := clipped x (2 - h) (1 / r) τ

def omegaA (x r h τ : ℝ) : ℝ := clipped x (2 - 2 * h) (2 / r) τ

def phiS (r h d : ℝ) : ℝ := (2 - h) * d + d ^ 2 / r

def phiA (r h d : ℝ) : ℝ := (2 - 2 * h) * d + 2 * d ^ 2 / r

theorem root_equation (μ α τ : ℝ) (hα : 0 < α) (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) :
    0 ≤ root μ α τ ∧ μ * root μ α τ + α * (root μ α τ) ^ 2 = τ := by
  dsimp [root]
  have hrad : 0 ≤ μ ^ 2 + 4 * α * τ := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (μ ^ 2 + 4 * α * τ)
  have hm : μ ≤ Real.sqrt (μ ^ 2 + 4 * α * τ) := by
    nlinarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hm) (by positivity)
  · field_simp
    nlinarith

theorem three_action_modulus_envelope
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

end D5.S3.Observer.TraceFibers.ThreeActionModulusEnvelope
