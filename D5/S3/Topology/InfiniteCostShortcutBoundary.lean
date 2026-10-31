/- GID: D5/S3/Topology/InfiniteCostShortcutBoundary
   generality: G
   mirror-B: D5/B/S3/Topology/InfiniteCostShortcutBoundary
   mirror-E: none(waiver:finite-counterexample)
   anchors: []
   utility: none
   digest: A two-point extended metric separates infinite paid cost from a zero-cost self-gluing shortcut. -/

/- Escape audit unfinished for the five public boundary theorems: https://github.com/the-omega-institute/trureturing/issues/24553. No declared_validated registration is claimed. -/

import D5.S3.Topology.FiniteOrbitChainMetric
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal Topology

namespace D5.S3.Topology.InfiniteCostShortcutBoundary

private def twoPointEDist (x y : Bool) : ℝ≥0∞ := if x = y then 0 else ⊤

private theorem twoPoint_edist_self (x : Bool) : twoPointEDist x x = 0 := by
  simp [twoPointEDist]

private theorem twoPoint_edist_comm (x y : Bool) :
    twoPointEDist x y = twoPointEDist y x := by
  simp [twoPointEDist, eq_comm]

private theorem twoPoint_edist_triangle (x y z : Bool) :
    twoPointEDist x z ≤ twoPointEDist x y + twoPointEDist y z := by
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> simp [twoPointEDist, hxy, hyz]

private noncomputable instance : EMetricSpace Bool :=
  { PseudoEMetricSpace.ofEDist twoPointEDist twoPoint_edist_self
      twoPoint_edist_comm twoPoint_edist_triangle with
    eq_of_edist_eq_zero := by
      intro x y h
      by_contra hxy
      change (if x = y then 0 else ⊤) = 0 at h
      simp [hxy] at h }

private theorem twoPoint_edist_false_true : edist false true = ⊤ := by
  change twoPointEDist false true = ⊤
  simp [twoPointEDist]

private theorem twoPoint_edist_true_false : edist true false = ⊤ := by
  change twoPointEDist true false = ⊤
  simp [twoPointEDist]

private theorem twoPoint_edist_eq_zero_iff {x y : Bool} :
    edist x y = 0 ↔ x = y := by
  change twoPointEDist x y = 0 ↔ x = y
  simp [twoPointEDist]

private def noGeneratorDatum :
    FiniteOrbitChainMetric.Datum Unit Empty (fun _ : Unit => Bool) where
  src := fun j => Empty.elim j
  dst := fun j => Empty.elim j
  dom := fun j => Empty.elim j
  ran := fun j => Empty.elim j
  iso := fun j => Empty.elim j
  closed_dom := fun j => Empty.elim j
  closed_ran := fun j => Empty.elim j

private def selfGlueDatum :
    FiniteOrbitChainMetric.Datum Unit Unit (fun _ : Unit => Bool) where
  src := fun _ => ()
  dst := fun _ => ()
  dom := fun _ => {false}
  ran := fun _ => {true}
  iso := fun _ =>
    IsometryEquiv.mk'
      (fun _ : ({false} : Set Bool) => (⟨true, by simp⟩ : ({true} : Set Bool)))
      (fun _ : ({true} : Set Bool) => (⟨false, by simp⟩ : ({false} : Set Bool)))
      (by intro x; apply Subsingleton.elim)
      (by intro x y; have h : x = y := Subsingleton.elim _ _; subst y; simp)
  closed_dom := by simp
  closed_ran := by simp

private abbrev point (b : Bool) : Sigma (fun _ : Unit => Bool) := ⟨(), b⟩

private theorem noGenerator_chain_endpoint
    {a b : Sigma (fun _ : Unit => Bool)} {t : ℝ≥0∞}
    (h : noGeneratorDatum.Chain a b t) :
    a.2 = b.2 ∨ t = ⊤ := by
  induction h with
  | nil => exact Or.inl rfl
  | @move _ x y t h ih =>
      rcases ih with hxy | ht
      · by_cases hsame : x = y
        · left
          simpa [hsame] using hxy
        · right
          change t + twoPointEDist x y = ⊤
          simp [twoPointEDist, hsame]
      · right
        simp [ht]
  | @forward j x t h ih => exact Empty.elim j
  | @backward j x t h ih => exact Empty.elim j

theorem no_generator_distance_infinite :
    noGeneratorDatum.distance (point false) (point true) = ⊤ := by
  apply top_unique
  rw [FiniteOrbitChainMetric.Datum.distance]
  refine le_iInf (fun t => le_iInf (fun h => ?_))
  rcases noGenerator_chain_endpoint h with hsame | ht
  · have : false = true := by simpa using hsame
    cases this
  · exact le_of_eq ht.symm

theorem no_generator_finite_chain_exists :
    ∃ t : ℝ≥0∞, noGeneratorDatum.Chain (point false) (point true) t := by
  refine ⟨edist false true, ?_⟩
  simpa only [point, zero_add] using
    (FiniteOrbitChainMetric.Datum.Chain.move false true
      (FiniteOrbitChainMetric.Datum.Chain.nil (G := noGeneratorDatum)))

private theorem selfGlue_zero_chain :
    selfGlueDatum.Chain (point false) (point true) 0 := by
  let x : selfGlueDatum.dom () := ⟨false, by simp [selfGlueDatum]⟩
  have hval : (selfGlueDatum.iso () x).val = true := by
    change true = true
    rfl
  simpa [point, hval] using
    (FiniteOrbitChainMetric.Datum.Chain.forward () x
      (FiniteOrbitChainMetric.Datum.Chain.nil (G := selfGlueDatum)))

theorem self_glue_distance_zero :
    selfGlueDatum.distance (point false) (point true) = 0 := by
  apply le_antisymm
  · exact iInf₂_le 0 selfGlue_zero_chain
  · exact bot_le

theorem self_glue_orbits_finite :
    ∀ a : Sigma (fun _ : Unit => Bool),
      Set.Finite {b : Sigma (fun _ : Unit => Bool) | selfGlueDatum.Rel a b} := by
  intro a
  exact Set.Finite.subset Set.finite_univ (by intro b _; exact Set.mem_univ b)

theorem no_generator_orbits_finite :
    ∀ a : Sigma (fun _ : Unit => Bool),
      Set.Finite {b : Sigma (fun _ : Unit => Bool) | noGeneratorDatum.Rel a b} := by
  intro a
  exact Set.Finite.subset Set.finite_univ (by intro b _; exact Set.mem_univ b)

end D5.S3.Topology.InfiniteCostShortcutBoundary
