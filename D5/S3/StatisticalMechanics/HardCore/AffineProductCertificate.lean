/- GID: D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/AffineProductCertificate
   mirror-E: none(waiver:exact-rational-to-real-certificate)
   anchors: []
   digest: Exact clamped product certificates imply affine hard-core message inequalities. -/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.AffineProductCertificate

open scoped BigOperators

private theorem four_product_le_one (z : Fin 4 → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hs : (∑ i, z i) ≤ 4) : (∏ i, z i) ≤ 1 := by
  have hp : 0 ≤ ∏ i, z i := Finset.prod_nonneg (fun i _ => hz i)
  have hm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin 4))
    (fun _ => (1 : ℝ)) z (by intro i _; norm_num) (by norm_num)
    (fun i _ => hz i)
  have hroot : (∏ i, z i) ^ (1 / 4 : ℝ) ≤ 1 := by
    norm_num at hm
    exact hm.trans (by linarith)
  have hfour := pow_le_pow_left₀ (Real.rpow_nonneg hp _) hroot 4
  have he : ((∏ i, z i) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = ∏ i, z i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    norm_num
  simpa only [he, one_pow] using hfour

private theorem clamp_sign (L a r t x : ℝ) (ht : 0 < t) (hr : 0 < r)
    (hx : L ≤ x ∧ x ≤ 1)
    (hc : (r = L ∧ t ≤ a * r) ∨ (r = 1 ∧ a * r ≤ t) ∨ a * r = t) :
    (x - r) * (1 / r - a / t) ≤ 0 := by
  have he : 1 / r - a / t = (t - a * r) / (r * t) := by
    field_simp [ne_of_gt hr, ne_of_gt ht]
    <;> ring
  rw [he]
  rcases hc with ⟨hL, hle⟩ | ⟨hU, hle⟩ | heq
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_pos hr ht).le)
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (div_nonneg (by linarith) (mul_pos hr ht).le)
  · simp [heq]

/-- A rationally checkable clamped stationary point is a global upper bound
for the product times the affine residual. The proof uses four-term AM-GM,
including the residual as the fourth factor; it does not assume convexity of
the original polynomial or trust a numerical stationary-point computation. -/
theorem clipped_product_bound (L C t : ℝ) (a r x : Fin 3 → ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hr : ∀ i, L ≤ r i ∧ r i ≤ 1) (hx : ∀ i, L ≤ x i ∧ x i ≤ 1)
    (hbal : C = t + ∑ i, a i * r i)
    (hc : ∀ i, (r i = L ∧ t ≤ a i * r i) ∨
      (r i = 1 ∧ a i * r i ≤ t) ∨ a i * r i = t) :
    (∏ i, x i) * (C - ∑ i, a i * x i) ≤ t * ∏ i, r i := by
  have hrp (i) : 0 < r i := hL.trans_le (hr i).1
  have hxp (i) : 0 < x i := hL.trans_le (hx i).1
  have hpr : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hrp i)
  have hpx : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => (hxp i).le)
  by_cases hS : 0 ≤ C - ∑ i, a i * x i
  · let z : Fin 4 → ℝ := ![(C - ∑ i, a i * x i) / t,
      x 0 / r 0, x 1 / r 1, x 2 / r 2]
    have hz : ∀ i, 0 ≤ z i := by
      intro i
      fin_cases i
      · simpa [z] using div_nonneg hS ht.le
      · simpa [z] using (div_pos (hxp 0) (hrp 0)).le
      · simpa [z] using (div_pos (hxp 1) (hrp 1)).le
      · simpa [z] using (div_pos (hxp 2) (hrp 2)).le
    have hsum : (∑ i, (x i - r i) * (1 / r i - a i / t)) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => clamp_sign L (a i) (r i) t (x i)
        ht (hrp i) (hx i) (hc i))
    have hid : (∑ i, z i) = 4 + ∑ i, (x i - r i) * (1 / r i - a i / t) := by
      dsimp [z]
      rw [hbal]
      simp [Fin.sum_univ_succ]
      field_simp [ne_of_gt ht, ne_of_gt (hrp 0), ne_of_gt (hrp 1),
        ne_of_gt (hrp 2)] <;> ring
    have hzsum : (∑ i, z i) ≤ 4 := by rw [hid]; linarith
    have hm := mul_le_mul_of_nonneg_right (four_product_le_one z hz hzsum)
      (mul_pos ht hpr).le
    have hmul : (∏ i, z i) * (t * ∏ i, r i) =
        (∏ i, x i) * (C - ∑ i, a i * x i) := by
      simp [z, Fin.prod_univ_succ, Fin.sum_univ_succ]
      field_simp [ne_of_gt ht, ne_of_gt (hrp 0), ne_of_gt (hrp 1),
        ne_of_gt (hrp 2)] <;> ring
    simpa only [hmul, one_mul] using hm
  · exact (mul_nonpos_of_nonneg_of_nonpos hpx (lt_of_not_ge hS).le).trans
      (mul_pos ht hpr).le

/-- Data only. Its validity is checked separately in exact rational arithmetic. -/
structure ClipWitness where
  level : ℚ
  reference : Fin 3 → ℚ

/-- Finite rational obligations for a global affine-message polynomial margin.
The `none` case certifies an everywhere nonnegative residual contribution. -/
def CheckedRow (L cap gamma margin ap bp : ℚ) (a b : Fin 3 → ℚ)
    (w : Option ClipWitness) : Prop :=
  (∀ i, 0 ≤ a i) ∧
  match w with
  | none => (∑ i, b i) - gamma * bp ≤ L * ∑ i, a i ∧
      margin ≤ gamma * (bp - ap)
  | some c => 0 < c.level ∧
      (∀ i, L ≤ c.reference i ∧ c.reference i ≤ 1) ∧
      (∑ i, b i) - gamma * bp = c.level + ∑ i, a i * c.reference i ∧
      (∀ i, (c.reference i = L ∧ c.level ≤ a i * c.reference i) ∨
        (c.reference i = 1 ∧ a i * c.reference i ≤ c.level) ∨
        a i * c.reference i = c.level) ∧
      margin ≤ gamma * (bp - ap) - cap * c.level * ∏ i, c.reference i

instance (L cap gamma margin ap bp : ℚ) (a b : Fin 3 → ℚ)
    (w : Option ClipWitness) : Decidable (CheckedRow L cap gamma margin ap bp a b w) := by
  unfold CheckedRow
  cases w <;> infer_instance

/-- Transfer exact rational checks to every real point of the entire box and
every smaller nonnegative activity. No grid sampling or supplied real bound
appears in this endpoint. -/
theorem checked_row_sound (L cap gamma margin ap bp : ℚ) (a b : Fin 3 → ℚ)
    (w : Option ClipWitness) (hL : 0 < L)
    (hcheck : CheckedRow L cap gamma margin ap bp a b w)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ (cap : ℝ))
    (x : Fin 3 → ℝ) (hx : ∀ i, (L : ℝ) ≤ x i ∧ x i ≤ 1) :
    (margin : ℝ) ≤ (gamma : ℝ) * ((bp : ℝ) - (ap : ℝ)) +
      lam * (∏ i, x i) * ((gamma : ℝ) * (bp : ℝ) - (∑ i, (b i : ℝ)) +
        ∑ i, (a i : ℝ) * x i) := by
  let C : ℝ := (∑ i, (b i : ℝ)) - (gamma : ℝ) * (bp : ℝ)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have ha (i) : (0 : ℝ) ≤ a i := by exact_mod_cast hcheck.1 i
  have hpx : 0 ≤ ∏ i, x i :=
    Finset.prod_nonneg (fun i _ => (hLR.trans_le (hx i).1).le)
  have hbound : (margin : ℝ) ≤ (gamma : ℝ) * ((bp : ℝ) - (ap : ℝ)) -
      lam * ((∏ i, x i) * (C - ∑ i, (a i : ℝ) * x i)) := by
    cases w with
    | none =>
        rcases hcheck.2 with ⟨hC, hmargin⟩
        have hCR : C ≤ (L : ℝ) * ∑ i, (a i : ℝ) := by
          dsimp [C]
          exact_mod_cast hC
        have hMR : (margin : ℝ) ≤ (gamma : ℝ) * ((bp : ℝ) - (ap : ℝ)) := by
          exact_mod_cast hmargin
        have hs : (L : ℝ) * (∑ i, (a i : ℝ)) ≤ ∑ i, (a i : ℝ) * x i := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun i _ => by
            nlinarith [mul_le_mul_of_nonneg_left (hx i).1 (ha i)])
        have hn : lam * ((∏ i, x i) * (C - ∑ i, (a i : ℝ) * x i)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam.1
            (mul_nonpos_of_nonneg_of_nonpos hpx (by linarith))
        linarith
    | some c =>
        rcases hcheck.2 with ⟨ht, hr, hb, hc, hm⟩
        have htR : (0 : ℝ) < c.level := by exact_mod_cast ht
        have hrR (i) : (L : ℝ) ≤ c.reference i ∧ (c.reference i : ℝ) ≤ 1 := by
          exact_mod_cast hr i
        have hbR : C = (c.level : ℝ) + ∑ i, (a i : ℝ) * (c.reference i : ℝ) := by
          dsimp [C]
          exact_mod_cast hb
        have hcR (i) : ((c.reference i : ℝ) = (L : ℝ) ∧
            (c.level : ℝ) ≤ (a i : ℝ) * (c.reference i : ℝ)) ∨
            ((c.reference i : ℝ) = 1 ∧
              (a i : ℝ) * (c.reference i : ℝ) ≤ (c.level : ℝ)) ∨
            (a i : ℝ) * (c.reference i : ℝ) = (c.level : ℝ) := by
          exact_mod_cast hc i
        have he := clipped_product_bound (L : ℝ) C (c.level : ℝ)
          (fun i => (a i : ℝ)) (fun i => (c.reference i : ℝ)) x
          hLR htR hrR hx hbR hcR
        have hpref : 0 ≤ (c.level : ℝ) * ∏ i, (c.reference i : ℝ) := by
          exact mul_nonneg htR.le (Finset.prod_nonneg
            (fun i _ => (hLR.trans_le (hrR i).1).le))
        have hmul := (mul_le_mul_of_nonneg_left he hlam.1).trans
          (mul_le_mul_of_nonneg_right hlam.2 hpref)
        have hmR : (margin : ℝ) ≤ (gamma : ℝ) * ((bp : ℝ) - (ap : ℝ)) -
            (cap : ℝ) * (c.level : ℝ) * ∏ i, (c.reference i : ℝ) := by
          exact_mod_cast hm
        nlinarith
  dsimp [C] at hbound
  convert hbound using 1 <;> ring

#print axioms clipped_product_bound
#print axioms checked_row_sound

end D5.S3.StatisticalMechanics.HardCore.AffineProductCertificate
