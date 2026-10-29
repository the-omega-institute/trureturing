/- GID: D5/S3/Combinatorics/CDSO/LocalizationBootstrap
   generality: G
   mirror-B: none (unfrozen StageA)
   mirror-E: none (unfrozen StageA)
   anchors: [e490b7d8797e6096790170dd4511d3d933e712051ce382fddb8658a6eca5c41b]
   utility: none
   digest: Actual-array definitions and the faithful full statement of CDSO Lemma 13.5.
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.CDSO.LocalizationBootstrap

noncomputable section

abbrev Label (a h : ℕ) := Fin (a + 1 + h)

abbrev NonemptyType (a h : ℕ) := {T : Finset (Label a h) // T.Nonempty}

instance nonemptyTypeFintype (a h : ℕ) : Fintype (NonemptyType a h) :=
  Fintype.ofFinite _

instance nonemptyTypeDecidableEq (a h : ℕ) : DecidableEq (NonemptyType a h) :=
  Classical.decEq _

def cardValue {a h : ℕ} (T : NonemptyType a h) : ℝ := T.1.card

def marginal {a h : ℕ} (mass : NonemptyType a h → ℝ) (i : Label a h) : ℝ :=
  ∑ T : NonemptyType a h, if i ∈ T.1 then mass T else 0

def meanCard {a h : ℕ} (mass : NonemptyType a h → ℝ) : ℝ :=
  ∑ T : NonemptyType a h, mass T * cardValue T

structure JointArray (a h : ℕ) where
  mass : NonemptyType a h → ℝ
  mass_nonneg : ∀ T, 0 ≤ mass T
  mass_sum : ∑ T, mass T = 1
  marginal_pos : ∀ i, 0 < marginal mass i
  mean_card_eq : meanCard mass = a

namespace JointArray

variable {a h : ℕ} (x : JointArray a h)

def y (i : Label a h) : ℝ := marginal x.mass i

structure TailChoice where
  D : Finset (Label a h)
  card_eq : D.card = h
  nonempty : D.Nonempty
  smallest : ∀ j ∈ D, ∀ i ∉ D, y x j ≤ y x i

def K (T : NonemptyType a h) : ℝ := cardValue T

def H : ℝ :=
  ∑ T : NonemptyType a h, x.mass T *
    ((K T) ^ 2 * ∑ i ∈ T.1, (y x i)⁻¹ ^ 2)

def d : ℝ := H x - a * (a + 1) ^ 2

def tailSum (D : Finset (Label a h)) : ℝ := ∑ j ∈ D, y x j

def delta (D : TailChoice x) : ℝ := D.D.sup' D.nonempty (fun j => y x j)

def tailCount (D : TailChoice x) (T : NonemptyType a h) : ℕ := (T.1 ∩ D.D).card

def coreCount (D : TailChoice x) (T : NonemptyType a h) : ℕ := (T.1 \ D.D).card

def tailEventMass (D : TailChoice x) : ℝ :=
  ∑ T : NonemptyType a h, if 0 < tailCount x D T then x.mass T else 0

def tailEnergy (D : TailChoice x) : ℝ :=
  ∑ T : NonemptyType a h, if 0 < tailCount x D T then
      x.mass T * ((K T) ^ 2 * ∑ j ∈ T.1 ∩ D.D, (y x j)⁻¹ ^ 2) else 0

end JointArray

abbrev IndexAtLeast4 := {a : ℕ // 4 ≤ a}

def scale (a : IndexAtLeast4) (q : ℝ) : ℝ := Real.rpow (a : ℝ) q

def EventuallyAtLeast (P : IndexAtLeast4 → Prop) : Prop := ∀ᶠ a in atTop, P a

def FullLowerChain (h : ℕ) (M : ℝ)
    (x : ∀ a : IndexAtLeast4, JointArray a h)
    (D : ∀ a : IndexAtLeast4, (x a).TailChoice) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 0 < N ∧ EventuallyAtLeast (fun a =>
    JointArray.d (x a) ≥
        JointArray.tailEnergy (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a) ∧
    JointArray.tailEnergy (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a) ≥
        ((h : ℝ)^2) / JointArray.tailEventMass (x a) (D a) +
          (2 * (a : ℝ)^3 - C * (a : ℝ)^2) *
            JointArray.tailEventMass (x a) (D a))

def Lemma135Statement (h : ℕ) (M : ℝ) : Prop :=
  2 ≤ h ∧ 0 < M →
  ∀ (x : ∀ a : IndexAtLeast4, JointArray a h)
    (D : ∀ a : IndexAtLeast4, (x a).TailChoice),
    EventuallyAtLeast (fun a => JointArray.d (x a) ≤ M * scale a (3 / 2 : ℝ)) →
      Tendsto (fun a => JointArray.delta (x a) (D a)) atTop (𝓝 0) ∧
      (∃ Cp Cu CH N : ℝ, 0 < Cp ∧ 0 < Cu ∧ 0 < CH ∧ 0 < N ∧
        EventuallyAtLeast (fun a =>
          JointArray.tailEventMass (x a) (D a) ≤ Cp * scale a (-3 / 2 : ℝ) ∧
          JointArray.tailSum (x a) (D a).D ≤ Cu * scale a (-3 / 2 : ℝ) ∧
          JointArray.tailEnergy (x a) (D a) ≤ CH * scale a (3 / 2 : ℝ))) ∧
      FullLowerChain h M x D

def Lemma134ProducerStatement (a h : ℕ) : Prop :=
  4 ≤ a → 2 ≤ h → ∀ (x : JointArray a h)
    (D : (x).TailChoice),
      let C := Finset.univ \ D.D
      let u := JointArray.tailSum x D.D
      let δ := JointArray.delta x D
      δ ≤ JointArray.tailEventMass x D ∧
      JointArray.tailEventMass x D ≤ u ∧ u ≤ h * JointArray.tailEventMass x D ∧
      (∀ i ∈ C, δ ≤ JointArray.y x i) ∧ u / (h : ℝ) ≤ δ

end

end D5.S3.Combinatorics.CDSO.LocalizationBootstrap
