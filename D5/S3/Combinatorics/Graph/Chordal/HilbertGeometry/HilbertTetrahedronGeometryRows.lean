/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertGeometry/HilbertTetrahedronGeometryRows
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar row estimates for a three-vertex face. -/

import OmegaBuild.Commands
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

compile_only_with_mathlib

/-! Omega original.

 Scalar row estimates for a three-vertex face.  The proof uses polynomial
dual multipliers, including the factorization controlling their total weight.
All boundary cases, including zero weights and zero row lower bound, are included. -/

namespace HilbertTetrahedronGeometry

lemma weighted_rows_ordered {a b c x y z L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : b ≤ a) (hbc : c ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hL : 0 ≤ L)
    (h₁ : L ≤ b*x+c*y) (h₂ : L ≤ a*x+c*z) (h₃ : L ≤ a*y+b*z) :
    4*L ≤ (a+b+c)*(x+y+z) := by
  by_cases hb0 : b = 0
  · have hc0 : c = 0 := by linarith
    subst b; subst c
    have hL0 : L = 0 := by linarith
    rw [hL0]
    simpa using mul_nonneg ha (add_nonneg (add_nonneg hx hy) hz)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hapos : 0 < a := hbpos.trans_le hab
  have hs : 0 < a+b+c := by positivity
  by_cases hdom : b+c ≤ a
  · have hm : 0 ≤ b-c := sub_nonneg.mpr hbc
    have hdual : L*(a+b-c) ≤ a*b*(x+y+z) := by
      have hfirst := mul_le_mul_of_nonneg_left h₁ ha
      have hthird := mul_le_mul_of_nonneg_left h₃ hm
      have hrest : 0 ≤ b*(a-b+c)*z := by
        apply mul_nonneg _ hz
        apply mul_nonneg hb
        linarith
      nlinarith
    have hfactor : 4*(a*b) ≤ (a+b+c)*(a+b-c) := by
      have hf : (a+b+c)*(a+b-c)-4*a*b = (a-b-c)*(a-b+c) := by ring
      have hp : 0 ≤ (a-b-c)*(a-b+c) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hfinal : (a*b)*(4*L) ≤ (a*b)*((a+b+c)*(x+y+z)) := by
      calc
        _ ≤ L*((a+b+c)*(a+b-c)) := by nlinarith [mul_le_mul_of_nonneg_left hfactor hL]
        _ = (a+b+c)*(L*(a+b-c)) := by ring
        _ ≤ (a+b+c)*(a*b*(x+y+z)) := mul_le_mul_of_nonneg_left hdual hs.le
        _ = _ := by ring
    exact le_of_mul_le_mul_left hfinal (mul_pos hapos hbpos)
  · have hcpos : 0 < c := by linarith
    have hA : 0 ≤ a*(b+c-a) := mul_nonneg ha (by linarith)
    have hB : 0 ≤ b*(a+c-b) := mul_nonneg hb (by linarith)
    have hC : 0 ≤ c*(a+b-c) := mul_nonneg hc (by linarith)
    let M := a*(b+c-a)+b*(a+c-b)+c*(a+b-c)
    have hdual : L*M ≤ (2*a*b*c)*(x+y+z) := by
      have hfirst := mul_le_mul_of_nonneg_left h₁ hA
      have hsecond := mul_le_mul_of_nonneg_left h₂ hB
      have hthird := mul_le_mul_of_nonneg_left h₃ hC
      dsimp [M]
      nlinarith
    have hfactor : 4*(2*a*b*c) ≤ (a+b+c)*M := by
      have hf : (a+b+c)*M-8*a*b*c =
          (b+c-a)*(a+c-b)*(a+b-c) := by dsimp [M]; ring
      have hp : 0 ≤ (b+c-a)*(a+c-b)*(a+b-c) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    have hfinal : (2*a*b*c)*(4*L) ≤ (2*a*b*c)*((a+b+c)*(x+y+z)) := by
      calc
        _ ≤ L*((a+b+c)*M) := by nlinarith [mul_le_mul_of_nonneg_left hfactor hL]
        _ = (a+b+c)*(L*M) := by ring
        _ ≤ (a+b+c)*((2*a*b*c)*(x+y+z)) := mul_le_mul_of_nonneg_left hdual hs.le
        _ = _ := by ring
    exact le_of_mul_le_mul_left hfinal (by positivity : 0 < 2*a*b*c)

/-- The weighted-row inequality (11), in a denominator-free form. -/
theorem weighted_rows {a b c x y z L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hL : 0 ≤ L)
    (h₁ : L ≤ b*x+c*y) (h₂ : L ≤ a*x+c*z) (h₃ : L ≤ a*y+b*z) :
    4*L ≤ (a+b+c)*(x+y+z) := by
  rcases le_total b a with hba | hab
  · rcases le_total c b with hcb | hbc
    · exact weighted_rows_ordered ha hb hc hba hcb hx hy hz hL h₁ h₂ h₃
    · rcases le_total c a with hca | hac
      · have h := weighted_rows_ordered ha hc hb hca hbc hy hx hz hL
          (by linarith [h₁]) (by linarith [h₃]) (by linarith [h₂])
        nlinarith [h]
      · have h := weighted_rows_ordered hc ha hb hac hba hy hz hx hL
          (by linarith [h₃]) (by linarith [h₁]) (by linarith [h₂])
        nlinarith [h]
  · rcases le_total c a with hca | hac
    · have h := weighted_rows_ordered hb ha hc hab hca hx hz hy hL
        (by linarith [h₂]) (by linarith [h₁]) (by linarith [h₃])
      nlinarith [h]
    · rcases le_total c b with hcb | hbc
      · have h := weighted_rows_ordered hb hc ha hcb hac hz hx hy hL
          (by linarith [h₂]) (by linarith [h₃]) (by linarith [h₁])
        nlinarith [h]
      · have h := weighted_rows_ordered hc hb ha hbc hab hz hy hx hL
          (by linarith [h₃]) (by linarith [h₂]) (by linarith [h₁])
        nlinarith [h]

/-- A face with spherical weighted rows has the sharp low-radius energy bound.
The upper bound on the omitted weight is supplied separately, allowing scalar
slack adjustment of a candidate inside the enclosing sphere. -/
theorem low_face_rows {a b c d x y z q B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_hd : 0 ≤ d)
    (hs : a+b+c+d = 1) (hB : 0 < B) (hq : 0 < q)
    (hquarter : B ≤ 4*q) (hhalf : 2*q ≤ B)
    (homit : 2*q ≤ B*(1-d))
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h₁ : 2*q-d*B ≤ b*x+c*y)
    (h₂ : 2*q-d*B ≤ a*x+c*z)
    (h₃ : 2*q-d*B ≤ a*y+b*z) :
    8*B*q-2*B^2 ≤ q*(x+y+z) := by
  have hL : 0 ≤ 2*q-d*B := by nlinarith
  have hrow := weighted_rows ha hb hc hx hy hz hL h₁ h₂ h₃
  have hspos : 0 < a+b+c := by nlinarith
  have hfactor : 0 ≤ (B-2*q)*(B*(1-d)-2*q) :=
    mul_nonneg (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hrow hq.le
  have hsid : a+b+c = 1-d := by linarith
  have htarget : (a+b+c)*(8*B*q-2*B^2) ≤ (a+b+c)*(q*(x+y+z)) := by
    rw [hsid] at hmul ⊢
    nlinarith only [hmul, hfactor]
  exact le_of_mul_le_mul_left htarget hspos

end HilbertTetrahedronGeometry
