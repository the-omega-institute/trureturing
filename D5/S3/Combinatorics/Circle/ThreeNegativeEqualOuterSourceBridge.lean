/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge
   mirror-E: none(waiver:consumed-module-boundary-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed source facts across the module and legacy import boundary. -/
module
import all D5.S3.Combinatorics.Circle.ThreeBitSource
public import D5.S3.Combinatorics.Circle.SourceWidth
public import D5.S3.Combinatorics.Circle.DyadicPrefix

/-! Source facts consumed by the complete equal-outer marked joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterSourceBridge
open SourceWidth

public theorem source_zero (k t : ℕ) (hk : 3 ≤ k) :
    ((List.range k).map (fun i => centered (modulus k) ((2 : ℤ) ^ i * t))).sum = 0 :=
  ThreeBitSource.source_zero k t hk

public theorem actual_source_chains (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 2 ≤ z) :
    let P : ℤ := 2 ^ x
    let Q : ℤ := 2 ^ y
    let R : ℤ := 2 ^ z
    let N := modulus (x + y + z)
    let u := 1 + P + P * Q
    let v := 1 + R + R * P
    let w := 1 + Q + Q * R
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
    (1 ≤ u ∧ u < N) ∧ (1 ≤ v ∧ v < N) ∧ (1 ≤ w ∧ w < N) ∧
      (R * u = N + v ∧ Q * v = N + w ∧ P * w = N + u) ∧
      (∀ e < z, f e = if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2) ∧
      (∀ e < y, f (z + e) = if e + 1 < y then (2 : ℤ) ^ e * v else -(N - w) / 2) ∧
      (∀ e < x, f (z + y + e) = if e + 1 < x then (2 : ℤ) ^ e * w else -(N - u) / 2) :=
  ThreeBitSource.actual_source_chains x y z hx hy hz

public theorem physical_schedule {α : Type*} (f : α → ℤ) (labels F Q G : List α)
    (av aw au : α) (Av Aw Au C : ℤ)
    (hperm : (F ++ av :: Q ++ aw :: G ++ [au]).Perm labels)
    (hAv : f av = -Av) (hAw : f aw = -Aw) (hAu : f au = -Au)
    (hAv0 : 0 ≤ Av) (hAw0 : 0 ≤ Aw) (hAuC : 0 ≤ Au ∧ Au ≤ C)
    (hFpos : ∀ i ∈ F, 0 ≤ f i) (hQpos : ∀ i ∈ Q, 0 ≤ f i)
    (hGpos : ∀ i ∈ G, 0 ≤ f i)
    (hFmass : Av ≤ (F.map f).sum ∧ (F.map f).sum ≤ C)
    (hQmass : Aw ≤ (F.map f).sum - Av + (Q.map f).sum ∧
      (F.map f).sum - Av + (Q.map f).sum ≤ C)
    (htotal : (labels.map f).sum = 0) :
    InStrip f C 0 (F ++ av :: Q ++ aw :: G ++ [au]) :=
  ThreeBitSource.physical_schedule f labels F Q G av aw au Av Aw Au C
    hperm hAv hAw hAu hAv0 hAw0 hAuC hFpos hQpos hGpos hFmass hQmass htotal

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterSourceBridge
