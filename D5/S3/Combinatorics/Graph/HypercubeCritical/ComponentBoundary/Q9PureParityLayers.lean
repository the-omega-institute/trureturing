/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Single-parity axial fibres force a cubic component into adjacent weight layers by XOR translation. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CrossWitnessTotal
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Adjacent Hamming layers for components with single-parity axial fibres

Translate by the vector of transverse parities. Along every selected edge
from original even parity to original odd parity, the translated weight
increases by one. The difference between translated weight and original
parity is therefore constant on an actual connected component.

This applies to the cubic component supports of the weighted Huang kernel
blocks for Hong–Wu–Xia, §7, Problem 2.
[arXiv:2610.09483v1](https://arxiv.org/html/2610.09483v1#Thmproblem2)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureParityLayers

open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges flip)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9IsotropicHuang (parity)
open Q9OccupiedFibreParity (doubleFibres occupied_fibre_identity)
open Q9WeightedSaturation (xorTranslate)
open TwoBalancedComponents (componentFinset mem_componentFinset)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private dropAxis mem_double_projected_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CrossWitnessTotal
open private projectedVertices card_projectedVertices doubleFibres_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence
open private trueDirections weight_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
open private translate_flip translate_translate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
open private translate_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap

private theorem parity_split (x : Q 9) (i : Fin 9) :
    parity x = Bool.xor (x i) (cubeParity (dropAxis i x)) := by
  change (∑ j : Fin 9, x j) = x i + ∑ j : Fin 8, x (i.succAbove j)
  exact Fin.sum_univ_succAbove x i

private theorem translated_axis_bit {S : Finset (Q 9)} {t x : Q 9} {i : Fin 9}
    (hpure : (doubleFibres S i (!(t i))).card = 0) (hx : x ∈ S)
    (hy : flip x i ∈ S) : xorTranslate t x i = parity x := by
  have hp : cubeParity (dropAxis i x) = t i := by
    by_contra hne
    have hz := (mem_double_projected_iff S i (!(t i)) x).mpr
      ⟨⟨hx, hy⟩, Bool.eq_not_of_ne hne⟩
    exact (notMem_empty _) (card_eq_zero.mp hpure ▸ hz)
  rw [parity_split x i, hp]
  exact Bool.xor_comm _ _

private theorem translated_weight_bounds {S : Finset (Q 9)} {t x : Q 9}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hpure : ∀ i : Fin 9, (doubleFibres S i (!(t i))).card = 0) (hx : x ∈ S) :
    (parity x = false → booleanWeight (xorTranslate t x) + 3 ≤ 9) ∧
    (parity x = true → 3 ≤ booleanWeight (xorTranslate t x)) := by
  classical
  have hc := regular_directions S hr hx
  have hbit (i : Fin 9) (hi : i ∈ directions S x) : xorTranslate t x i = parity x :=
    translated_axis_bit (t := t) (hpure i) hx ((mem_directions S x i).mp hi)
  constructor
  · intro hp
    have hsub : directions S x ⊆ univ \ trueDirections (xorTranslate t x) := by
      intro i hi
      simp only [trueDirections, mem_sdiff, mem_univ, mem_filter, true_and]
      rw [hbit i hi, hp]
      decide
    have hcard := card_le_card hsub
    rw [hc, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at hcard
    change 3 ≤ 9 - booleanWeight (xorTranslate t x) at hcard
    omega
  · intro hp
    have hsub : directions S x ⊆ trueDirections (xorTranslate t x) := by
      intro i hi
      simp only [trueDirections, mem_filter, mem_univ, true_and]
      exact (hbit i hi).trans hp
    have hcard := card_le_card hsub
    rw [hc] at hcard
    exact hcard

open Classical in
/-- A cubic component with all paired fibres in one transverse parity per axis
is carried by that parity vector to consecutive Hamming layers. Original even
vertices go to layer `k` and original odd vertices go to layer `k + 1`.
The graph isomorphism acts by the same translation on every vertex. -/
theorem exists_translate_adjacent_layers (U : Finset (Q 9))
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (hr : ((hypercube 9).induce (componentFinset U C : Set (Q 9))).IsRegularOfDegree 3)
    (hpure : ∀ i : Fin 9, ∃ p : Bool, (doubleFibres (componentFinset U C) i (!p)).card = 0) :
    ∃ (t : Q 9) (k : ℕ), 2 ≤ k ∧ k ≤ 6 ∧
      (∀ i : Fin 9, (doubleFibres (componentFinset U C) i (!(t i))).card = 0) ∧
      (∀ x ∈ componentFinset U C, booleanWeight (xorTranslate t x) = k + (parity x).toNat) ∧
      ∃ e : ((hypercube 9).induce (componentFinset U C : Set (Q 9))) ≃g
          ((hypercube 9).induce ((componentFinset U C).image (xorTranslate t) : Set (Q 9))),
        ∀ x, (e x).val = xorTranslate t x.val := by
  classical
  let S := componentFinset U C
  let G := (hypercube 9).induce (U : Set (Q 9))
  choose t ht using hpure
  let height (x : Q 9) := booleanWeight (xorTranslate t x) - (parity x).toNat
  have hstep {x : Q 9} {i : Fin 9} (hx : x ∈ S) (hy : flip x i ∈ S) :
      height x = height (flip x i) := by
    have hbit := translated_axis_bit (t := t) (ht i) hx hy
    have hpar : parity (flip x i) = !parity x := parity_flip x i
    have hflip : xorTranslate t (flip x i) = flip (xorTranslate t x) i := translate_flip t x i
    dsimp only [height]
    rw [hpar, hflip, weight_flip, hbit]
    cases hp : parity x <;> simp [hp, Bool.toNat]
  obtain ⟨root, hroot⟩ := C.nonempty_supp
  let k := height root.val
  have hconst {v : (U : Set (Q 9))} (hv : Relation.ReflTransGen G.Adj root v) :
      v ∈ C.supp ∧ height v.val = k := by
    induction hv with
    | refl => exact ⟨hroot, rfl⟩
    | @tail u v _ hadj ih =>
      have hvC := C.mem_supp_of_adj_mem_supp ih.1 hadj
      have huS : u.val ∈ S := (mem_componentFinset U C _).mpr ⟨u.property, ih.1⟩
      have hvS : v.val ∈ S := (mem_componentFinset U C _).mpr ⟨v.property, hvC⟩
      obtain ⟨i, hi⟩ := adjacent_exists_flip
        (show (hypercube 9).Adj u.val v.val from hadj)
      have hiS : flip u.val i ∈ S := by rwa [← hi]
      refine ⟨hvC, ?_⟩
      rw [hi]
      exact (hstep huS hiS).symm.trans ih.2
  have hweight (x : Q 9) (hx : x ∈ S) :
      booleanWeight (xorTranslate t x) = k + (parity x).toNat := by
    obtain ⟨hxU, hxC⟩ := (mem_componentFinset U C x).mp hx
    let v : (U : Set (Q 9)) := ⟨x, hxU⟩
    have hreach : G.Reachable root v := C.reachable_of_mem_supp hroot hxC
    have h := (hconst ((reachable_iff_reflTransGen root v).mp hreach)).2
    change booleanWeight (xorTranslate t x) - (parity x).toNat = k at h
    cases hp : parity x
    · simpa [hp, Bool.toNat] using h
    · have hlo := (translated_weight_bounds (t := t) hr ht hx).2 hp
      simp only [hp] at h
      change booleanWeight (xorTranslate t x) - 1 = k at h
      change booleanWeight (xorTranslate t x) = k + 1
      omega
  have hrootS : root.val ∈ S := (mem_componentFinset U C _).mpr ⟨root.property, hroot⟩
  have hdirs := regular_directions S hr hrootS
  obtain ⟨i, hi⟩ : (directions S root.val).Nonempty := card_pos.mp (by omega)
  have hmateS := (mem_directions S root.val i).mp hi
  have hmate : parity (flip root.val i) = !parity root.val := parity_flip root.val i
  have hparities : (∃ x ∈ S, parity x = false) ∧ (∃ x ∈ S, parity x = true) := by
    cases hp : parity root.val
    · exact ⟨⟨root.val, hrootS, hp⟩, flip root.val i, hmateS, by simpa [hp] using hmate⟩
    · exact ⟨⟨flip root.val i, hmateS, by simpa [hp] using hmate⟩, root.val, hrootS, hp⟩
  obtain ⟨⟨x, hx, hxe⟩, y, hy, hyo⟩ := hparities
  have hupper := (translated_weight_bounds (t := t) hr ht hx).1 hxe
  have hlower := (translated_weight_bounds (t := t) hr ht hy).2 hyo
  rw [hweight x hx, hxe] at hupper
  rw [hweight y hy, hyo] at hlower
  change k + 0 + 3 ≤ 9 at hupper
  change 3 ≤ k + 1 at hlower
  let e : (hypercube 9) ≃g (hypercube 9) :=
    { toEquiv := ⟨xorTranslate t, xorTranslate t, translate_translate t, translate_translate t⟩
      map_rel_iff' := by
        intro x y
        exact translate_adj (a := t) (x := x) (y := y) }
  have he : Set.BijOn e (S : Set (Q 9)) (S.image (xorTranslate t) : Set (Q 9)) := by
    rw [coe_image]
    have hinv : Function.Involutive (xorTranslate t) := translate_translate t
    exact hinv.injective.bijOn_image
  exact ⟨t, k, by omega, by omega, ht, hweight, e.induce he, fun _ => rfl⟩

/-- The projected vertex count, which counts each double fibre twice. -/
theorem projected_vertex_identity {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (a : Fin 9) (p : Bool) :
    3 * (projectedVertices S a p).card =
      8 * directionEdges S a + 2 * (doubleFibres S a p).card := by
  have hocc := occupied_fibre_identity hr hb a p
  have hpart := doubleFibres_partition S a p
  rw [card_projectedVertices]
  omega

/-- At eleven or more double fibres of one parity out of twelve, all twelve
have that parity. -/
theorem doubleFibres_eq_twelve_of_ge_eleven {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (a : Fin 9) (p : Bool)
    (hm : directionEdges S a = 12) (hp : 11 ≤ (doubleFibres S a p).card) :
    (doubleFibres S a p).card = 12 ∧ (doubleFibres S a (!p)).card = 0 := by
  have hcount := projected_vertex_identity hr hb a p
  have hpart := doubleFibres_partition S a p
  rw [hm] at hcount hpart
  by_cases h : (doubleFibres S a p).card = 11 <;> omega

/-- At nine or more double fibres of one parity out of thirteen, the two
parity classes have sizes eleven and two. -/
theorem doubleFibres_eq_eleven_of_thirteen_of_ge_nine {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (a : Fin 9) (p : Bool)
    (hm : directionEdges S a = 13) (hp : 9 ≤ (doubleFibres S a p).card) :
    (doubleFibres S a p).card = 11 ∧ (doubleFibres S a (!p)).card = 2 := by
  have hcount := projected_vertex_identity hr hb a p
  have hpart := doubleFibres_partition S a p
  rw [hm] at hcount hpart
  have hcases : (doubleFibres S a p).card = 9 ∨ (doubleFibres S a p).card = 10 ∨
      (doubleFibres S a p).card = 11 ∨ (doubleFibres S a p).card = 12 ∨
      (doubleFibres S a p).card = 13 := by omega
  rcases hcases with h | h | h | h | h <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PureParityLayers
