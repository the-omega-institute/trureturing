/- GID: D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Biased trine qubit measurements have the conjectured triplewise threshold. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

namespace D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold

/-- Index `i : Fin 3` denotes source index `i + 1`; the coordinates are ordered x,y,z. -/
def trineDir (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (![![-1 / 2, 0, Real.sqrt 3 / 2],
    ![-1 / 2, 0, -Real.sqrt 3 / 2], ![1, 0, 0]] i)

/-- The source's first family, with `true` denoting outcome +1 and `false` outcome -1. -/
def trineEffect (b η : ℝ) (k : Fin 3) (x : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • scalarB (1 + sgn x * b) ((η * sgn x) • trineDir k)

/-- A single eight-outcome POVM has all six specified binary marginals. -/
def TriplewiseJointlyMeasurable (b η : ℝ) : Prop :=
  ∃ g : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ, IsPOVM g ∧
    ∀ k x, ∑ s with s k = x, g s = trineEffect b η k x

/-- The three cases of the conjectured threshold, including both central endpoints. -/
def trineThreshold (b : ℝ) : ℝ :=
  if b < -1 / 3 then 1 + b else if b ≤ 1 / 3 then 2 / 3 else 1 - b

private lemma trine_source (k : Fin 3) :
    trineDir k = WithLp.toLp 2
      ![Real.cos (2 * ((k.val : ℝ) + 1) * Real.pi / 3), 0,
        Real.sin (2 * ((k.val : ℝ) + 1) * Real.pi / 3)] := by
  sorry

private lemma trine_norm (k : Fin 3) : ‖trineDir k‖ = 1 := by
  sorry

private lemma trine_sum : ∑ k : Fin 3, trineDir k = 0 := by
  sorry

private lemma sign_sum_bound (s : Fin 3 → Bool) :
    ‖∑ k : Fin 3, sgn (s k) • trineDir k‖ ≤ 2 := by
  sorry

private lemma necessity_certificate (b η : ℝ)
    (h : TriplewiseJointlyMeasurable b η) : 3 * η ≤ 2 := by
  sorry

private lemma necessity (b η : ℝ) (hd : |b| ≤ 1 - η)
    (h : TriplewiseJointlyMeasurable b η) : η ≤ trineThreshold b := by
  have hc := necessity_certificate b η h
  unfold trineThreshold
  split_ifs <;> have ha := abs_le.mp (show |b| ≤ 1 - η from hd) <;> linarith

private lemma parent_central (b η : ℝ) (hb : -(1 / 3 : ℝ) ≤ b)
    (hb1 : b ≤ 1 / 3) (hη : 0 ≤ η) (hη1 : η ≤ 2 / 3) :
    TriplewiseJointlyMeasurable b η := by
  sorry

private lemma parent_positive (b η : ℝ) (hb : 1 / 3 ≤ b) (hb1 : b ≤ 1)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 - b) : TriplewiseJointlyMeasurable b η := by
  sorry

private lemma parent_negative (b η : ℝ) (hb : -1 ≤ b) (hb1 : b ≤ -(1 / 3 : ℝ))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 + b) : TriplewiseJointlyMeasurable b η := by
  sorry

/-- The exact triplewise joint-measurability threshold on the source parameter domain. -/
theorem result : ∀ b η : ℝ, -1 ≤ b → b ≤ 1 → 0 ≤ η → η ≤ 1 →
    |b| ≤ 1 - η → (TriplewiseJointlyMeasurable b η ↔ η ≤ trineThreshold b) := by
  intro b η hb hb1 hη _ hd
  constructor
  · exact necessity b η hd
  · intro ht
    unfold trineThreshold at ht
    split_ifs at ht with hn hp
    · exact parent_negative b η hb hn.le hη ht
    · exact parent_central b η (le_of_not_gt hn) hp hη ht
    · exact parent_positive b η (le_of_not_ge hp).le hb1 hη ht

end D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
