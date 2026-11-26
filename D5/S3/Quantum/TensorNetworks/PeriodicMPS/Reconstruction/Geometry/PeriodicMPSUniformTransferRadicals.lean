/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferRadicals
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferRadicals
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Two-radical coordinates for the trace-aligned mixed-transfer fiber. -/
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Two-radical coordinates for the trace-aligned mixed-transfer fiber

This formalizes the coordinate change from the repository's horizontal
four-weight support separation argument.

The coefficient equations are those of `X⁴ − X³ + a X² − b X + c` in
`PeriodicMPSUniformTransferSpectrum.braFirst_charpoly_trace_aligned` and its
ket-first counterpart. Here the variables are the four split determinant
coordinates at fixed `a`, `b`, `c`, `U`, and `k`.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferRadicals

variable {K : Type*} [Field K]

/-- The literal coefficient fiber, with `d * db` fixed to `U`. The last three
equations use the fixed values of `U` and `b` in the quartic formulas. -/
@[ext]
structure CoordinateFiber (K : Type*) [Field K] (a b c U k : K) where
  d : K
  db : K
  e : K
  eb : K
  prod_eq : d * db = U
  coeff_a : d + db - 2 * (U + e * eb) - k ^ 2 = a
  coeff_b : U - e * eb = b
  coeff_c : b ^ 2 + k ^ 2 * (d + eb) * (db + e) = c

/-- The sum `L` of the first two determinant coordinates. -/
def sumD (a b U k : K) : K := a + 4 * U - 2 * b + k ^ 2

/-- The sum `W` of the scaled second determinant coordinates. -/
def sumScaledE (b c U k : K) : K := (c - b ^ 2) / k ^ 2 - 2 * U + b

/-- The discriminant for the first difference. -/
def deltaD (a b U k : K) : K := sumD a b U k ^ 2 - 4 * U

/-- The discriminant for the scaled second difference. -/
def deltaS (b c U k : K) : K := sumScaledE b c U k ^ 2 - 4 * (U * (U - b))

/-- Solutions of the two independent square equations over the coefficient field. -/
@[ext]
structure RadicalFiber (K : Type*) [Field K] (a b c U k : K) where
  x : K
  y : K
  x_sq : x ^ 2 = deltaD a b U k
  y_sq : y ^ 2 = deltaS b c U k

variable {a b c U k : K}

private theorem CoordinateFiber.sum_d (p : CoordinateFiber K a b c U k) :
    p.d + p.db = sumD a b U k := by
  unfold sumD
  linear_combination p.coeff_a - 2 * p.coeff_b

private theorem CoordinateFiber.sum_scaled_e (p : CoordinateFiber K a b c U k) (hk : k ≠ 0) :
    p.d * p.e + p.db * p.eb = sumScaledE b c U k := by
  have hcross : (p.d + p.eb) * (p.db + p.e) = (c - b ^ 2) / k ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hk)).2
    linear_combination p.coeff_c
  unfold sumScaledE
  rw [← hcross]
  linear_combination -p.prod_eq + p.coeff_b

/-- Take the determinant difference and the difference of the scaled second
determinants. -/
def CoordinateFiber.toRadical (p : CoordinateFiber K a b c U k) (hk : k ≠ 0) :
    RadicalFiber K a b c U k where
  x := p.d - p.db
  y := p.d * p.e - p.db * p.eb
  x_sq := by
    rw [deltaD, ← p.sum_d]
    linear_combination -4 * p.prod_eq
  y_sq := by
    rw [deltaS, ← p.sum_scaled_e hk]
    linear_combination (-4 * (p.e * p.eb)) * p.prod_eq + 4 * U * p.coeff_b

private theorem half_pair (s t v : K) (htwo : (2 : K) ≠ 0)
    (ht : t ^ 2 = s ^ 2 - 4 * v) :
    (s + t) / 2 + (s - t) / 2 = s ∧
      (s + t) / 2 - (s - t) / 2 = t ∧
      (s + t) / 2 * ((s - t) / 2) = v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← add_div]
    apply (div_eq_iff htwo).2
    ring
  · rw [← sub_div]
    apply (div_eq_iff htwo).2
    ring
  · rw [← mul_div_mul_comm]
    apply (div_eq_iff (mul_ne_zero htwo htwo)).2
    linear_combination -ht

private theorem mul_reconstruct {d db U : K} (hU : U ≠ 0) (hprod : d * db = U) (z : K) :
    d * (z * db / (2 * U)) = z / 2 := by
  have hnum : d * (z * db) = z * U := by
    rw [← hprod]
    ring
  rw [← mul_div_assoc, hnum, mul_div_mul_comm, div_self hU, mul_one]

/-- Reconstruct the four determinants and verify the three coefficient equations. -/
def RadicalFiber.toCoordinates (r : RadicalFiber K a b c U k)
    (htwo : (2 : K) ≠ 0) (hU : U ≠ 0) (hk : k ≠ 0) : CoordinateFiber K a b c U k := by
  let L := sumD a b U k
  let W := sumScaledE b c U k
  let d := (L + r.x) / 2
  let db := (L - r.x) / 2
  let e := (W + r.y) * db / (2 * U)
  let eb := (W - r.y) * d / (2 * U)
  obtain ⟨hdSum, _, hprod⟩ := half_pair L r.x U htwo r.x_sq
  obtain ⟨heSum, _, heProd⟩ := half_pair W r.y (U * (U - b)) htwo r.y_sq
  have he : d * e = (W + r.y) / 2 := mul_reconstruct hU hprod _
  have heb : db * eb = (W - r.y) / 2 := mul_reconstruct hU ((mul_comm db d).trans hprod) _
  have hV : e * eb = U - b := by
    apply mul_left_cancel₀ hU
    calc
      U * (e * eb) = (d * e) * (db * eb) := by rw [← hprod]; ring
      _ = U * (U - b) := by rw [he, heb, heProd]
  have hcross : (d + eb) * (db + e) = (c - b ^ 2) / k ^ 2 := by
    calc
      (d + eb) * (db + e) = d * db + e * eb + (d * e + db * eb) := by ring
      _ = (c - b ^ 2) / k ^ 2 := by
        rw [hprod, hV, he, heb, heSum]
        dsimp only [W, sumScaledE]
        ring
  refine ⟨d, db, e, eb, hprod, ?_, ?_, ?_⟩
  · rw [show d + db = L from hdSum, hV]
    dsimp only [L, sumD]
    ring
  · rw [hV]
    ring
  · calc
      b ^ 2 + k ^ 2 * (d + eb) * (db + e) =
          b ^ 2 + ((d + eb) * (db + e)) * k ^ 2 := by ring
      _ = c := by
        rw [hcross, div_mul_cancel₀ _ (pow_ne_zero 2 hk)]
        ring

/-- The literal fixed-coefficient fiber is equivalent to the two-radical fiber.
The map is defined also when either or both radicals vanish. -/
def coordinateEquivRadical (a b c U k : K) (htwo : (2 : K) ≠ 0)
    (hU : U ≠ 0) (hk : k ≠ 0) : CoordinateFiber K a b c U k ≃ RadicalFiber K a b c U k where
  toFun p := p.toRadical hk
  invFun r := r.toCoordinates htwo hU hk
  left_inv p := by
    let q := (p.toRadical hk).toCoordinates htwo hU hk
    have hd : q.d = p.d := by
      change (sumD a b U k + (p.d - p.db)) / 2 = p.d
      rw [← p.sum_d]
      apply (div_eq_iff htwo).2
      ring
    have hdb : q.db = p.db := by
      change (sumD a b U k - (p.d - p.db)) / 2 = p.db
      rw [← p.sum_d]
      apply (div_eq_iff htwo).2
      ring
    change q = p
    apply CoordinateFiber.ext hd hdb
    · change (sumScaledE b c U k + (p.d * p.e - p.db * p.eb)) * q.db / (2 * U) = p.e
      rw [hdb, ← p.sum_scaled_e hk]
      apply (div_eq_iff (mul_ne_zero htwo hU)).2
      linear_combination (2 * p.e) * p.prod_eq
    · change (sumScaledE b c U k - (p.d * p.e - p.db * p.eb)) * q.d / (2 * U) = p.eb
      rw [hd, ← p.sum_scaled_e hk]
      apply (div_eq_iff (mul_ne_zero htwo hU)).2
      linear_combination (2 * p.eb) * p.prod_eq
  right_inv r := by
    let p := r.toCoordinates htwo hU hk
    let W := sumScaledE b c U k
    obtain ⟨_, hx, _⟩ := half_pair (sumD a b U k) r.x U htwo r.x_sq
    obtain ⟨_, hyDiff, _⟩ := half_pair W r.y (U * (U - b)) htwo r.y_sq
    have he : p.d * p.e = (W + r.y) / 2 := mul_reconstruct hU p.prod_eq _
    have heb : p.db * p.eb = (W - r.y) / 2 :=
      mul_reconstruct hU ((mul_comm p.db p.d).trans p.prod_eq) _
    change p.toRadical hk = r
    apply RadicalFiber.ext
    · exact hx
    · change p.d * p.e - p.db * p.eb = r.y
      rw [he, heb]
      exact hyDiff

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferRadicals
