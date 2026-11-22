/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The endpoint sums on three order-nine blocks biject onto the 108-element label group. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineAssembly
import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineFinite

/-! The endpoint sums for three blocks of size nine.
The midpoint and half-difference reduction follows the canonical nine-block proof.
The remaining checks are on the four radii and their binary patterns. -/

namespace TransversalNine

open AffineNine
open AffineNineFinite (F9 Bits ι)

abbrev TripleLabels := F9 × ZMod 3 × Bits

private def bits (a t : ZMod 3) : Bits :=
  (if a = t then 1 else 0, if a = t + 1 then 1 else 0)

/-- The vertex label on a triple of blocks, using the canonical model of the nine-element field. -/
def vertexLabel (t : ZMod 3) (x : F9) : TripleLabels :=
  (x, t / 2 + (x ^ 2).im, bits x.re t)

/-- The actual endpoint sum on the unordered edges of three disjoint complete graphs. -/
def edgeLabel (e : ZMod 3 × Edge F9) : TripleLabels :=
  Sym2.lift ⟨fun x y => vertexLabel e.1 x + vertexLabel e.1 y, fun _ _ => add_comm _ _⟩ e.2.1

private def radius : Fin 4 → F9 := ![ι, 1, 1 + ι, 1 - ι]

private theorem radius_ne_zero : ∀ k, radius k ≠ 0 := by decide

private theorem radius_representative : ∀ r : F9, r ≠ 0 →
    ∃ k, r = radius k ∨ r = -radius k := by decide

private def radiusBits (u : ZMod 3) (k : Fin 4) : Bits :=
  if k = 0 then (0, 0) else (if u = 0 then 0 else 1, if u = 1 then 0 else 1)

private theorem bits_endpoints : ∀ (a t : ZMod 3) (k : Fin 4),
    bits (a + (radius k).re) t + bits (a - (radius k).re) t = radiusBits (a - t) k := by
  decide

private def pattern (u : ZMod 3) (k : Fin 4) : Bits :=
  radiusBits (u + (2 * radius k ^ 2).im) k

private theorem pattern_injective : ∀ (u : ZMod 3) (j k : Fin 4),
    pattern u j = pattern u k → j = k := by decide

private theorem pattern_surjective : ∀ (u : ZMod 3) (b : Bits),
    ∃ k, pattern u k = b := by decide

private def baseline (c : F9) (d : ZMod 3) : ZMod 3 := d - (2 * (c / 2) ^ 2).im

private def blockAt (c : F9) (d : ZMod 3) (k : Fin 4) : ZMod 3 :=
  baseline c d - (2 * radius k ^ 2).im

private theorem endpoint_ne (h r : F9) (hr : r ≠ 0) : h + r ≠ h - r := by
  intro he
  have hz : (2 : F9) * r = 0 := by linear_combination he
  exact (mul_ne_zero AffineNineFinite.two_ne_zero hr) hz

private def edgeAt (c : F9) (d : ZMod 3) (k : Fin 4) : ZMod 3 × Edge F9 :=
  (blockAt c d k, edge (c / 2 + radius k) (c / 2 - radius k) (endpoint_ne _ _ (radius_ne_zero k)))

private theorem edgeLabel_edgeAt (c : F9) (d : ZMod 3) (k : Fin 4) :
    edgeLabel (edgeAt c d k) = (c, d, pattern ((c / 2).re - baseline c d) k) := by
  have hsum : c / 2 + radius k + (c / 2 - radius k) = c := by
    field_simp [AffineNineFinite.two_ne_zero]
    ring
  have hsquares : (c / 2 + radius k) ^ 2 + (c / 2 - radius k) ^ 2 =
      2 * (c / 2) ^ 2 + 2 * radius k ^ 2 := by ring
  change vertexLabel (blockAt c d k) (c / 2 + radius k) +
    vertexLabel (blockAt c d k) (c / 2 - radius k) = _
  refine Prod.ext hsum (Prod.ext ?_ ?_)
  · change blockAt c d k / 2 + ((c / 2 + radius k) ^ 2).im +
        (blockAt c d k / 2 + ((c / 2 - radius k) ^ 2).im) = d
    have ht (t : ZMod 3) : t / 2 + t / 2 = t := by
      rw [← two_mul, mul_comm, div_mul_cancel₀ _ (by decide : (2 : ZMod 3) ≠ 0)]
    rw [show ∀ a b c : ZMod 3, a + b + (a + c) = (a + a) + (b + c) from
      fun a b c => by ring, ht, ← QuadraticAlgebra.im_add, hsquares, QuadraticAlgebra.im_add]
    unfold blockAt baseline
    ring
  · change bits (c / 2 + radius k).re (blockAt c d k) +
        bits (c / 2 - radius k).re (blockAt c d k) = _
    rw [QuadraticAlgebra.re_add, QuadraticAlgebra.re_sub, bits_endpoints]
    unfold pattern blockAt
    congr 1
    ring

set_option maxHeartbeats 600000 in
private theorem edgeAt_surjective (e : ZMod 3 × Edge F9) :
    ∃ (c : F9) (d : ZMod 3) (k : Fin 4), edgeAt c d k = e := by
  obtain ⟨t, e⟩ := e
  induction e using Edge.inductionOn with
  | _ x y hxy =>
    let c := x + y
    let d := t + ((x ^ 2) + (y ^ 2)).im
    let r := (x - y) / 2
    have hr : r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxy) AffineNineFinite.two_ne_zero
    have hx : c / 2 + r = x := by dsimp [c, r]; field_simp [AffineNineFinite.two_ne_zero]; ring
    have hy : c / 2 - r = y := by dsimp [c, r]; field_simp [AffineNineFinite.two_ne_zero]; ring
    have hsquares : x ^ 2 + y ^ 2 = 2 * (c / 2) ^ 2 + 2 * r ^ 2 := by
      rw [← hx, ← hy]
      ring
    have ht : baseline c d - (2 * r ^ 2).im = t := by
      unfold baseline
      dsimp only [d]
      rw [hsquares, QuadraticAlgebra.im_add]
      ring
    obtain ⟨k, hk | hk⟩ := radius_representative r hr
    · refine ⟨c, d, k, Prod.ext (by simpa only [edgeAt, blockAt, hk] using ht) ?_⟩
      apply Subtype.ext
      change s(c / 2 + radius k, c / 2 - radius k) = s(x, y)
      rw [← hk, hx, hy]
    · refine ⟨c, d, k, Prod.ext (by simpa only [edgeAt, blockAt, hk, even_two.neg_pow] using ht) ?_⟩
      apply Subtype.ext
      change s(c / 2 + radius k, c / 2 - radius k) = s(x, y)
      have hneg : radius k = -r := by rw [hk, neg_neg]
      rw [hneg, ← sub_eq_add_neg, sub_neg_eq_add, hx, hy, Sym2.eq_swap]

/-- Every element of the 108-element label group occurs on exactly one unordered edge. -/
theorem edgeLabel_bijective : Function.Bijective edgeLabel := by
  constructor
  · intro e e' he
    obtain ⟨c, d, k, rfl⟩ := edgeAt_surjective e
    obtain ⟨c', d', k', rfl⟩ := edgeAt_surjective e'
    simp only [edgeLabel_edgeAt, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, hk⟩ := he
    rw [pattern_injective _ _ _ hk]
  · rintro ⟨c, d, b⟩
    obtain ⟨k, hk⟩ := pattern_surjective ((c / 2).re - baseline c d) b
    exact ⟨edgeAt c d k, by rw [edgeLabel_edgeAt, hk]⟩

noncomputable def tripleLabeling : EdgeLabeling F9 (ZMod 3) TripleLabels where
  label := vertexLabel
  edgeEquiv := Equiv.ofBijective edgeLabel edgeLabel_bijective
  edgeEquiv_apply _ _ _ _ := rfl

theorem card_tripleLabels : Fintype.card TripleLabels = 108 := by
  simp [AffineNineFinite.card_f9, TripleLabels, Bits]

#print axioms edgeLabel_bijective
#print axioms tripleLabeling

end TransversalNine
