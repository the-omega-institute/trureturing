/- GID: D5/S3/Arith/GoldenConicStationaryChart
   generality: G
   mirror-B: none(waiver:all-moduli-unit-norm-charts)
   mirror-E: none(waiver:exact-inverse-and-cubic-nilpotent-phase)
   anchors: []
   digest: An exact golden norm chart has a unique inverse and a non-flat quadratic normal phase. -/

import D5.S3.Arith.GoldenApparition
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenConicStationaryChart

open D5.S3.Arith.GoldenApparition

/-- The actual golden norm, in the existing modular golden-coordinate carrier. -/
def normForm {M : ℕ} (z : GoldenMod M) : ZMod M :=
  z.a ^ 2 + z.a * z.b - z.b ^ 2

/-- A tangent whose norm is minus five times the original norm. -/
def tangent {M : ℕ} (z : GoldenMod M) : GoldenMod M :=
  ⟨z.a - 2 * z.b, -(2 * z.a + z.b)⟩

/-- The chart with an explicitly certified denominator inverse.
There is no division by a nonunit in a composite residue ring. -/
def chart {M : ℕ} (z : GoldenMod M) (t d : ZMod M) : GoldenMod M :=
  ⟨d * ((1 + 5 * t ^ 2) * z.a + 2 * t * (tangent z).a),
   d * ((1 + 5 * t ^ 2) * z.b + 2 * t * (tangent z).b)⟩

/-- Radial coefficient, when half=1/2 and invc=1/normForm(z). -/
def radial {M : ℕ} (z w : GoldenMod M) (half invc : ZMod M) : ZMod M :=
  half * invc * ((2 * z.a + z.b) * w.a + (z.a - 2 * z.b) * w.b)

/-- Tangential coefficient in the basis (z,tangent z). -/
def transverse {M : ℕ} (z w : GoldenMod M) (half invc : ZMod M) : ZMod M :=
  half * invc * (z.b * w.a - z.a * w.b)

/-- Exact norm preservation, inverse chart, and the normal phase at a cubic-nilpotent
parameter. The theorem uses the actual GoldenMod carrier at an arbitrary modulus.
At M=p^(2*r+1), r>=1, parameters divisible by p^r have cube zero, so the last
clause supplies the quadratic Gauss phase missed by first-order truncation.
The inverse clause covers every norm point for which its displayed radial
coordinate plus one is a unit; this includes the whole residue ball about z. -/
theorem result {M : ℕ} (z : GoldenMod M) (half invc : ZMod M)
    (hhalf : 2 * half = 1) (hc : normForm z * invc = 1) :
    (∀ t d : ZMod M, d * (1 - 5 * t ^ 2) = 1 →
      normForm (chart z t d) = normForm z ∧
      ∀ lam : ZMod M,
        lam * (2 * z.a + z.b) * (chart z t d).a +
          lam * (z.a - 2 * z.b) * (chart z t d).b =
        2 * lam * normForm z + 20 * lam * normForm z * t ^ 2 * d) ∧
    (∀ w : GoldenMod M, normForm w = normForm z →
      ∀ e : ZMod M, e * (1 + radial z w half invc) = 1 →
        ((1 + radial z w half invc) * half) *
          (1 - 5 * (transverse z w half invc * e) ^ 2) = 1 ∧
        chart z (transverse z w half invc * e)
          ((1 + radial z w half invc) * half) = w ∧
        ∀ t d : ZMod M, d * (1 - 5 * t ^ 2) = 1 →
          chart z t d = w → t = transverse z w half invc * e) ∧
    (∀ t : ZMod M, t ^ 3 = 0 →
      chart z t (1 + 5 * t ^ 2) =
        (⟨(1 + 10 * t ^ 2) * z.a + 2 * t * (tangent z).a,
          (1 + 10 * t ^ 2) * z.b + 2 * t * (tangent z).b⟩ : GoldenMod M) ∧
      normForm (chart z t (1 + 5 * t ^ 2)) = normForm z ∧
      ∀ lam : ZMod M,
        lam * (2 * z.a + z.b) * (chart z t (1 + 5 * t ^ 2)).a +
          lam * (z.a - 2 * z.b) * (chart z t (1 + 5 * t ^ 2)).b =
        2 * lam * normForm z + 20 * lam * normForm z * t ^ 2) := by
  have hforward : ∀ t d : ZMod M, d * (1 - 5 * t ^ 2) = 1 →
      normForm (chart z t d) = normForm z ∧
      ∀ lam : ZMod M,
        lam * (2 * z.a + z.b) * (chart z t d).a +
          lam * (z.a - 2 * z.b) * (chart z t d).b =
        2 * lam * normForm z + 20 * lam * normForm z * t ^ 2 * d := by
    intro t d hd
    constructor
    · calc
        normForm (chart z t d) = normForm z * (d * (1 - 5 * t ^ 2)) ^ 2 := by
          dsimp [normForm, chart, tangent]
          ring
        _ = normForm z := by rw [hd]; ring
    · intro lam
      calc
        _ = 2 * lam * normForm z * (d * (1 - 5 * t ^ 2)) +
              20 * lam * normForm z * t ^ 2 * d := by
          dsimp [chart, tangent, normForm]
          ring
        _ = _ := by rw [hd]; ring
  refine ⟨hforward, ?_, ?_⟩
  · intro w hw e he
    let A := radial z w half invc
    let B := transverse z w half invc
    change e * (1 + A) = 1 at he
    change ((1 + A) * half) * (1 - 5 * (B * e) ^ 2) = 1 ∧
      chart z (B * e) ((1 + A) * half) = w ∧
      ∀ t d : ZMod M, d * (1 - 5 * t ^ 2) = 1 → chart z t d = w → t = B * e
    have hi : (2 * normForm z) * (half * invc) = 1 := by
      calc
        _ = (2 * half) * (normForm z * invc) := by ring
        _ = 1 := by rw [hhalf, hc]; ring
    have hx : A * z.a + B * (tangent z).a = w.a := by
      calc
        _ = ((2 * normForm z) * (half * invc)) * w.a := by
          dsimp [A, B, radial, transverse, normForm, tangent]
          ring
        _ = w.a := by rw [hi]; ring
    have hy : A * z.b + B * (tangent z).b = w.b := by
      calc
        _ = ((2 * normForm z) * (half * invc)) * w.b := by
          dsimp [A, B, radial, transverse, normForm, tangent]
          ring
        _ = w.b := by rw [hi]; ring
    have hnorm : normForm w = normForm z * (A ^ 2 - 5 * B ^ 2) := by
      calc
        normForm w = normForm (⟨A * z.a + B * (tangent z).a,
            A * z.b + B * (tangent z).b⟩ : GoldenMod M) := by rw [hx, hy]
        _ = _ := by dsimp [normForm, tangent]; ring
    have hAB : A ^ 2 - 5 * B ^ 2 = 1 := by
      calc
        _ = (normForm z * invc) * (A ^ 2 - 5 * B ^ 2) := by rw [hc]; ring
        _ = invc * (normForm z * (A ^ 2 - 5 * B ^ 2)) := by ring
        _ = invc * normForm w := by rw [hnorm]
        _ = 1 := by rw [hw]; simpa only [mul_comm] using hc
    have hsmall : 1 - 5 * (B * e) ^ 2 = 2 * e := by
      linear_combination e ^ 2 * hAB - (1 + (A - 1) * e) * he
    have hd : ((1 + A) * half) * (1 - 5 * (B * e) ^ 2) = 1 := by
      calc
        _ = (2 * half) * (e * (1 + A)) := by rw [hsmall]; ring
        _ = 1 := by rw [hhalf, he]; ring
    have htwo : 2 * ((1 + A) * half) = 1 + A := by
      calc
        _ = (1 + A) * (2 * half) := by ring
        _ = 1 + A := by rw [hhalf]; ring
    have ha : ((1 + A) * half) * (1 + 5 * (B * e) ^ 2) = A := by
      linear_combination htwo - hd
    have hb : 2 * ((1 + A) * half) * (B * e) = B := by
      calc
        _ = B * (e * (1 + A)) := by rw [htwo]; ring
        _ = B := by rw [he]; ring
    refine ⟨hd, ?_, ?_⟩
    · apply GoldenMod.ext
      · change ((1 + A) * half) *
          ((1 + 5 * (B * e) ^ 2) * z.a + 2 * (B * e) * (tangent z).a) = w.a
        calc
          _ = (((1 + A) * half) * (1 + 5 * (B * e) ^ 2)) * z.a +
              (2 * ((1 + A) * half) * (B * e)) * (tangent z).a := by ring
          _ = w.a := by rw [ha, hb]; exact hx
      · change ((1 + A) * half) *
          ((1 + 5 * (B * e) ^ 2) * z.b + 2 * (B * e) * (tangent z).b) = w.b
        calc
          _ = (((1 + A) * half) * (1 + 5 * (B * e) ^ 2)) * z.b +
              (2 * ((1 + A) * half) * (B * e)) * (tangent z).b := by ring
          _ = w.b := by rw [ha, hb]; exact hy
    · intro t d hden hchart
      have hA : A = d * (1 + 5 * t ^ 2) := by
        change radial z w half invc = _
        rw [← hchart]
        calc
          _ = ((2 * normForm z) * (half * invc)) * (d * (1 + 5 * t ^ 2)) := by
            dsimp [radial, chart, tangent, normForm]
            ring
          _ = _ := by rw [hi]; ring
      have hB : B = 2 * d * t := by
        change transverse z w half invc = _
        rw [← hchart]
        calc
          _ = ((2 * normForm z) * (half * invc)) * (2 * d * t) := by
            dsimp [transverse, chart, tangent, normForm]
            ring
          _ = _ := by rw [hi]; ring
      have hrel : (1 + A) * t = B := by
        rw [hA, hB]
        linear_combination -t * hden
      calc
        t = (e * (1 + A)) * t := by rw [he]; ring
        _ = e * B := by rw [mul_assoc, hrel]
        _ = B * e := by ring
  · intro t ht
    have hfour : t ^ 4 = 0 := by
      calc
        t ^ 4 = t * t ^ 3 := by ring
        _ = 0 := by rw [ht]; ring
    have hd : (1 + 5 * t ^ 2) * (1 - 5 * t ^ 2) = 1 := by
      linear_combination -25 * hfour
    refine ⟨?_, (hforward t (1 + 5 * t ^ 2) hd).1, ?_⟩
    · apply GoldenMod.ext
      · change (1 + 5 * t ^ 2) *
          ((1 + 5 * t ^ 2) * z.a + 2 * t * (tangent z).a) =
          (1 + 10 * t ^ 2) * z.a + 2 * t * (tangent z).a
        linear_combination (25 * z.a * t + 10 * (tangent z).a) * ht
      · change (1 + 5 * t ^ 2) *
          ((1 + 5 * t ^ 2) * z.b + 2 * t * (tangent z).b) =
          (1 + 10 * t ^ 2) * z.b + 2 * t * (tangent z).b
        linear_combination (25 * z.b * t + 10 * (tangent z).b) * ht
    · intro lam
      calc
        _ = 2 * lam * normForm z + 20 * lam * normForm z * t ^ 2 *
              (1 + 5 * t ^ 2) := (hforward t (1 + 5 * t ^ 2) hd).2 lam
        _ = _ := by linear_combination (100 * lam * normForm z) * hfour

end D5.S3.Arith.GoldenConicStationaryChart
