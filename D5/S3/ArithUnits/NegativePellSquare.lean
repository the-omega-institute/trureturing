/- GID: D5/S3/ArithUnits/NegativePellSquare
   generality: G
   mirror-B: D5/B/S3/ArithUnits/NegativePellSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A negative-Pell norm-minus-one element squares to an explicit Pell unit. -/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.ArithUnits.NegativePellSquare

/-- For every integer `j`, the element `6j + sqrt(36j^2 + 1)` has norm minus one.
Its square has the displayed coordinates and norm one, making the negative-Pell element's
square an explicit Pell unit. -/
theorem negative_pell_square_unit (j : ℤ) :
    let d : ℤ := 36 * j ^ 2 + 1
    let u : ℤ√d := ⟨6 * j, 1⟩
    u.norm = -1 ∧
      u ^ 2 = ⟨72 * j ^ 2 + 1, 12 * j⟩ ∧
      (u ^ 2).norm = 1 := by
  dsimp only
  have hnorm : Zsqrtd.norm (⟨6 * j, 1⟩ : ℤ√(36 * j ^ 2 + 1)) = -1 := by
    simp only [Zsqrtd.norm]
    ring
  have hsquare :
      (⟨6 * j, 1⟩ : ℤ√(36 * j ^ 2 + 1)) ^ 2 =
        ⟨72 * j ^ 2 + 1, 12 * j⟩ := by
    apply Zsqrtd.ext <;> simp only [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
    · ring
    · ring
  refine ⟨hnorm, hsquare, ?_⟩
  calc
    Zsqrtd.norm ((⟨6 * j, 1⟩ : ℤ√(36 * j ^ 2 + 1)) ^ 2) =
        Zsqrtd.norm (⟨6 * j, 1⟩ : ℤ√(36 * j ^ 2 + 1)) ^ 2 :=
      Zsqrtd.normMonoidHom.map_pow _ _
    _ = 1 := by rw [hnorm]; norm_num

end D5.S3.ArithUnits.NegativePellSquare
