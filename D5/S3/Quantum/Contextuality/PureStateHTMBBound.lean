/- GID: D5/S3/Quantum/Contextuality/PureStateHTMBBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/PureStateHTMBBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pure preparations obey the two-trit HTMB noncontextuality bound. -/

import D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace
open D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity (projector)

namespace D5.S3.Quantum.Contextuality.PureStateHTMBBound

/-- The average probability of correctly guessing one of the two uniformly chosen trits. -/
def htmbValue {d : ℕ} (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 18) * ∑ x, ((projector (ψ x) * m x.1).trace.re +
    (projector (ψ x) * n x.2).trace.re)

/-- Pure preparations satisfying both parity equivalences cannot violate the HTMB inequality. -/
def claim : Prop :=
  ∀ (d : ℕ) (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ),
    (∀ x, ‖ψ x‖ = 1) →
    ((∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) →
    ((∀ b, (n b).PosSemidef) ∧ ∑ b, n b = 1) →
    (∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k),
        projector (ψ x) =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0),
        projector (ψ x)) →
    htmbValue ψ m n ≤ 2 / 3

private theorem additive_form {d : ℕ}
    (p : ZMod 3 × ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k), p x =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0), p x)
    (i j : ZMod 3) : p (i, j) = p (i, 0) + p (0, j) - p (0, 0) := by
  sorry

private theorem projector_difference_span {d : ℕ}
    (a b c e : EuclideanSpace ℂ (Fin d))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (he : ‖e‖ = 1)
    (h : projector a - projector b = projector c - projector e)
    (hne : projector c - projector e ≠ 0) :
    a ∈ Submodule.span ℂ ({c, e} : Set (EuclideanSpace ℂ (Fin d))) ∧
    b ∈ Submodule.span ℂ ({c, e} : Set (EuclideanSpace ℂ (Fin d))) := by
  sorry

private theorem discrimination_bound {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ∀ b, ‖v b‖ = 1)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1)
    (s : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (hs : Module.finrank ℂ s ≤ 2)
    (hvs : ∀ b, v b ∈ s) :
    ∑ b, (projector (v b) * m b).trace.re ≤ 2 := by
  sorry

private theorem effect_bound {d : ℕ}
    (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1)
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) (b : ZMod 3) :
    0 ≤ (projector v * m b).trace.re ∧ (projector v * m b).trace.re ≤ 1 := by
  sorry

private theorem discrimination_three {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ∀ b, ‖v b‖ = 1)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) :
    ∑ b, (projector (v b) * m b).trace.re ≤ 3 := by
  calc
    _ ≤ ∑ _b : ZMod 3, (1 : ℝ) :=
      Finset.sum_le_sum fun b _ => (effect_bound (v b) (hv b) m hm b).2
    _ = 3 := by norm_num

private theorem constant_discrimination {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ‖v 0‖ = 1) (hm : ∑ b, m b = 1)
    (h : ∀ b, projector (v b) = projector (v 0)) :
    ∑ b, (projector (v b) * m b).trace.re = 1 := by
  sorry

private theorem value_reduction {d : ℕ}
    (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hψ : ∀ x, ‖ψ x‖ = 1) (hm : ∑ b, m b = 1) (hn : ∑ b, n b = 1)
    (hadd : ∀ i j, projector (ψ (i, j)) =
      projector (ψ (i, 0)) + projector (ψ (0, j)) - projector (ψ (0, 0))) :
    htmbValue ψ m n = (1 / 6) *
      ((∑ i, (projector (ψ (i, 0)) * m i).trace.re) +
       (∑ j, (projector (ψ (0, j)) * n j).trace.re)) := by
  sorry

private theorem cross_in_plane {d : ℕ}
    (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (hψ : ∀ x, ‖ψ x‖ = 1)
    (hadd : ∀ i j, projector (ψ (i, j)) =
      projector (ψ (i, 0)) + projector (ψ (0, j)) - projector (ψ (0, 0)))
    (i j : ZMod 3)
    (hi : projector (ψ (i, 0)) ≠ projector (ψ (0, 0)))
    (hj : projector (ψ (0, j)) ≠ projector (ψ (0, 0))) :
    ∃ s : Submodule ℂ (EuclideanSpace ℂ (Fin d)), Module.finrank ℂ s ≤ 2 ∧
      (∀ k, ψ (k, 0) ∈ s) ∧ (∀ k, ψ (0, k) ∈ s) := by
  sorry

/-- The pure-state HTMB conjecture of Tavakoli, Zambrini Cruzeiro, Uola and Abbott. -/
theorem result : claim := by
  intro d ψ m n hψ hm hn hequiv
  have hadd := additive_form (fun x => projector (ψ x)) hequiv
  rw [value_reduction ψ m n hψ hm.2 hn.2 hadd]
  have hcol := discrimination_three (fun i => ψ (i, 0)) m (fun i => hψ (i, 0)) hm
  have hrow := discrimination_three (fun j => ψ (0, j)) n (fun j => hψ (0, j)) hn
  by_cases hc : ∀ i, projector (ψ (i, 0)) = projector (ψ (0, 0))
  · have h := constant_discrimination (fun i => ψ (i, 0)) m (hψ (0, 0)) hm.2 hc
    linarith
  by_cases hr : ∀ j, projector (ψ (0, j)) = projector (ψ (0, 0))
  · have h := constant_discrimination (fun j => ψ (0, j)) n (hψ (0, 0)) hn.2 hr
    linarith
  push_neg at hc hr
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, hj⟩ := hr
  obtain ⟨s, hs, hcs, hrs⟩ := cross_in_plane ψ hψ hadd i j hi hj
  have htwo_col := discrimination_bound (fun i => ψ (i, 0)) m
    (fun i => hψ (i, 0)) hm s hs hcs
  have htwo_row := discrimination_bound (fun j => ψ (0, j)) n
    (fun j => hψ (0, j)) hn s hs hrs
  linarith

end D5.S3.Quantum.Contextuality.PureStateHTMBBound
