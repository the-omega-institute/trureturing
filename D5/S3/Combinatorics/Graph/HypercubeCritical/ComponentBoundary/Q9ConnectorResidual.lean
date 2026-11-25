/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ConnectorResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ConnectorResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two even dimer neighbours force a residual two transverse flips from a connector. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! The intended application is the normalized order-ninety cylinder for
Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2, with majority dimers in even
projected parity. Cubic degree gives an odd singleton connector a third actual
transverse neighbour besides its two dimer neighbours. The signed sum row at
that even singleton is nonzero, whereas the prescribed dimer-driven contact
row vanishes there. Agreement at the connector forces the discrepancy to occur
two distinct flips away. The dimer description, contact equation, and initial
agreement are hypotheses supplied by the chart. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ConnectorResidual

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_flip IsSwitching)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9SignedAxialFold (signedWord gaugeLayer paritySign paritySign_flip transverse signed_fold)
open private flip_cons_zero flip_cons_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

attribute [local instance] Classical.propDecidable

/-- The two dimer directions and the absent axial mate leave a lateral neighbour
in the actual support. Its even row detects the odd residual, and agreement
at the starting connector forces the two transverse directions to be distinct. -/
theorem residual_at_connector {C : Finset (Q 9)} {s : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) (d c : Q 8 → ℤ) {x : Q 8} {b : Bool}
    (hxOdd : paritySign x = -1)
    (hx : Fin.cons b x ∈ C) (hxMate : Fin.cons (!b) x ∉ C)
    (hDimer : ∀ y, d y ≠ 0 ↔
      paritySign y = 1 ∧ Fin.cons true y ∈ C ∧ Fin.cons false y ∈ C)
    (hTwo : (univ.filter fun i : Fin 8 => d (BalancedCriticalSpectrum.flip x i) ≠ 0).card = 2)
    (hChart : ∀ y, paritySign y = 1 → transverse c y = 4 * d y)
    (hContact : (gaugeLayer (signedWord C s) true + gaugeLayer (signedWord C s) false) x = c x) :
    let g := gaugeLayer (signedWord C s) true + gaugeLayer (signedWord C s) false
    ∃ i j : Fin 8, i ≠ j ∧ Fin.cons b (BalancedCriticalSpectrum.flip x i) ∈ C ∧
      d (BalancedCriticalSpectrum.flip x i) = 0 ∧
      paritySign (BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x i) j) = -1 ∧
      g (BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x i) j) ≠
        c (BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x i) j) := by
  intro g
  let occupied := directions C (Fin.cons b x)
  let dimerDirections :=
    (univ.filter fun i : Fin 8 => d (BalancedCriticalSpectrum.flip x i) ≠ 0).image
      (Fin.succ : Fin 8 → Fin 9)
  have hOccupied : occupied.card = 3 := regular_directions C hr hx
  have hDimers : dimerDirections.card = 2 := by
    dsimp only [dimerDirections]
    rw [card_image_of_injective _ (Fin.succ_injective 8), hTwo]
  have hCard : dimerDirections.card < occupied.card := by
    simpa only [hDimers, hOccupied] using Nat.lt_succ_self 2
  obtain ⟨k, hk, hkOff⟩ := exists_mem_notMem_of_card_lt_card hCard
  have hkMem := (mem_directions C (Fin.cons b x) k).mp hk
  have hkNonaxial : k ≠ 0 := by
    intro hkZero
    subst k
    exact hxMate (by simpa only [flip_cons_zero] using hkMem)
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hkNonaxial
  let y := flip x i
  have hy : Fin.cons b y ∈ C := by
    simpa only [y, flip_cons_succ] using hkMem
  have hyDimer : d y = 0 := by
    by_contra hn
    have hi : i ∈ univ.filter (fun k : Fin 8 => d (BalancedCriticalSpectrum.flip x k) ≠ 0) :=
      mem_filter.mpr ⟨mem_univ i, hn⟩
    exact hkOff (mem_image.mpr ⟨i, hi, rfl⟩)
  have hyEven : paritySign y = 1 := by
    simp only [y, paritySign_flip, hxOdd, neg_neg]
  have hyMate : Fin.cons (!b) y ∉ C := by
    intro hm
    have hBoth : Fin.cons true y ∈ C ∧ Fin.cons false y ∈ C := by
      cases b
      · exact ⟨hm, hy⟩
      · exact ⟨hy, hm⟩
    exact (hDimer y).mpr ⟨hyEven, hBoth⟩ hyDimer
  have hValue : signedWord C s (Fin.cons b y) ≠ 0 := by
    by_cases h : s (Fin.cons b y) = 1 <;> simp [signedWord, hy, h]
  have hMissing : signedWord C s (Fin.cons (!b) y) = 0 := by
    simp [signedWord, hyMate]
  have hSum : g y ≠ 0 := by
    cases b <;> simp only [Bool.not_false, Bool.not_true] at hMissing <;>
      simpa [g, gaugeLayer, hyEven, hMissing] using hValue
  have hFold := (signed_fold hr hs y).1
  change transverse g y = (3 - paritySign y) * g y at hFold
  rw [hyEven] at hFold
  change transverse g y = 2 * g y at hFold
  obtain ⟨j, hj⟩ : ∃ j : Fin 8, g (flip y j) ≠ c (flip y j) := by
    by_contra! hAgree
    apply mul_ne_zero (by decide : (2 : ℤ) ≠ 0) hSum
    calc
      2 * g y = transverse g y := hFold.symm
      _ = transverse c y := by
        unfold transverse
        exact sum_congr rfl (fun j _ => by rw [hAgree j])
      _ = 0 := by rw [hChart y hyEven, hyDimer, mul_zero]
  have hij : i ≠ j := by
    intro hEq
    apply hj
    simpa only [y, ← hEq, BalancedCriticalSpectrum.flip_flip] using hContact
  have hjOdd : paritySign (flip y j) = -1 := by
    rw [paritySign_flip, hyEven]
  exact ⟨i, j, hij, hy, hyDimer, hjOdd, hj⟩

#print axioms residual_at_connector

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ConnectorResidual
