/- GID: D5/S3/Combinatorics/Graph/HilbertTriangleInsertionAlgebra
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scalar certificates for three-neighbor Hilbert insertion. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

compile_only_with_mathlib

/-! Omega original.

 Exact scalar certificates for three-neighbor Hilbert insertion. -/

namespace HilbertTriangleInsertion

noncomputable section

def R : ℝ := 259 / 200
def C : ℝ := 23 / 5
def B : ℝ := (R + 1) ^ 2
def allowance (s : ℝ) : ℝ := C - R ^ 2 + (2 / 3) * s
def numerator (s : ℝ) : ℝ :=
  (6 * B - C - 2 - s) * allowance s - 2 * B ^ 2
def certificate (s : ℝ) : ℝ :=
  numerator s ^ 2 - 4 * C * (2 + s) * allowance s ^ 2
def smallCertificate (t : ℝ) : ℝ :=
  (4 * B - (R + t) ^ 2) * allowance (t ^ 2) - 2 * B ^ 2

/-- A constrained pair bounds the variance, without contact assumptions. -/
lemma one_edge_variance {a b c x y z q D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (hx : 0 ≤ x) (hxD : x ≤ D) (hyD : y ≤ D) (hzD : z ≤ D)
    (_hD : 0 ≤ D) (hq : q = a * b * x + b * c * y + c * a * z) :
    q * (4 * D - x) ≤ D ^ 2 := by
  have hpair : 4 * a * b ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hcap : q ≤ a * b * x + c * (a + b) * D := by
    nlinarith [mul_nonneg (mul_nonneg hb hc) (sub_nonneg.mpr hyD),
      mul_nonneg (mul_nonneg hc ha) (sub_nonneg.mpr hzD)]
  have hc' : c = 1 - (a + b) := by linarith
  rw [hc'] at hcap
  have hquad : 4 * q ≤ 4 * D * (a + b) - (4 * D - x) * (a + b) ^ 2 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hpair)]
  have hd : 0 ≤ 4 * D - x := by linarith
  have hh := mul_nonneg hd (sub_nonneg.mpr hquad)
  nlinarith [sq_nonneg ((4 * D - x) * (a + b) - 2 * D)]

/-- Above the half-diameter radius, all three contacts have positive mass. -/
lemma weights_positive {a b c x y z q D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (hxD : x ≤ D) (hyD : y ≤ D) (hzD : z ≤ D) (hD : 0 ≤ D)
    (hq : q = a * b * x + b * c * y + c * a * z) (hlarge : D / 4 < q) :
    0 < a ∧ 0 < b ∧ 0 < c := by
  have first {a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hs : a + b + c = 1) (hy : y ≤ D)
      (hq : q = a * b * x + b * c * y + c * a * z) : 0 < a := by
    by_contra hn
    have he : a = 0 := le_antisymm (le_of_not_gt hn) ha
    subst a
    have hp : b * c ≤ 1 / 4 := by nlinarith [sq_nonneg (b - c)]
    nlinarith [mul_nonneg (mul_nonneg hb hc) (sub_nonneg.mpr hy),
      mul_nonneg hD (sub_nonneg.mpr hp)]
  exact ⟨first (x := x) (y := y) (z := z) ha hb hc hs hyD hq,
    first (x := y) (y := z) (z := x) hb hc ha (by linarith) hzD (by nlinarith [hq]),
    first (x := z) (y := x) (z := y) hc ha hb (by linarith) hxD (by nlinarith [hq])⟩

/-- Contact deficits yield the sharp sum-of-squared-sides radius bound. -/
lemma contact_sum_bound {a b c x y z q D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (hx : x ≤ D) (hy : y ≤ D) (hz : z ≤ D) (_hD : 0 ≤ D)
    (h0 : b * x + c * z = 2 * q)
    (h1 : a * x + c * y = 2 * q)
    (h2 : a * z + b * y = 2 * q) :
    q * (6 * D - (x + y + z)) ≤ D ^ 2 := by
  have hsD : D * a + D * b + D * c = D := by
    nlinarith [congrArg (fun v : ℝ => D * v) hs]
  have hwa : D * a ≤ D - 2 * q := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hx),
      mul_nonneg hc (sub_nonneg.mpr hz)]
  have hwb : D * b ≤ D - 2 * q := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx),
      mul_nonneg hc (sub_nonneg.mpr hy)]
  have hwc : D * c ≤ D - 2 * q := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hz),
      mul_nonneg hb (sub_nonneg.mpr hy)]
  have hab : 2 * q ≤ D * (a + b) := by nlinarith
  have hbc : 2 * q ≤ D * (b + c) := by nlinarith
  have hca : 2 * q ≤ D * (c + a) := by nlinarith
  have he : (a + b) * (D - x) + (b + c) * (D - y) +
      (c + a) * (D - z) = 2 * D - 6 * q := by nlinarith
  have hxy := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hab)
  have hyz := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hbc)
  have hzx := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hca)
  nlinarith [congrArg (fun v : ℝ => D * v) he]

lemma smallCertificate_nonneg {t : ℝ} (hlo : 0 ≤ t) (hhi : t ≤ (1 / 5 : ℝ)) :
    0 ≤ smallCertificate t := by
  have hleft : 0 ≤ t - 0 := sub_nonneg.mpr hlo
  have hright : 0 ≤ (1 / 5 : ℝ) - t := sub_nonneg.mpr hhi
  have he : smallCertificate t =
    (382887279 / 512000 : ℝ) * ((1 / 5 : ℝ) - t) ^ 4 +
      (52351839 / 25600 : ℝ) * (t - 0) ^ 1 * ((1 / 5 : ℝ) - t) ^ 3 +
      (1457764639 / 768000 : ℝ) * (t - 0) ^ 2 * ((1 / 5 : ℝ) - t) ^ 2 +
      (247278521 / 384000 : ℝ) * (t - 0) ^ 3 * ((1 / 5 : ℝ) - t) ^ 1 +
      (65009309 / 1536000 : ℝ) * (t - 0) ^ 4 := by
    unfold smallCertificate
    dsimp [certificate, numerator, allowance, B, R, C]
    ring
  rw [he]
  positivity

lemma numerator_nonneg {t : ℝ} (hlo : (1 / 25 : ℝ) ≤ t) (hhi : t ≤ 1) :
    0 ≤ numerator t := by
  have hleft : 0 ≤ t - (1 / 25 : ℝ) := sub_nonneg.mpr hlo
  have hright : 0 ≤ 1 - t := sub_nonneg.mpr hhi
  have he : numerator t =
    (10887775817 / 552960000 : ℝ) * (1 - t) ^ 2 +
      (14831011817 / 276480000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 1 * (1 - t) ^ 1 +
      (18405607817 / 552960000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 2 := by
    unfold numerator
    dsimp [certificate, numerator, allowance, B, R, C]
    ring
  rw [he]
  positivity

lemma certificate_nonneg {t : ℝ} (hlo : (1 / 25 : ℝ) ≤ t) (hhi : t ≤ 1) :
    0 ≤ certificate t := by
  have hleft : 0 ≤ t - (1 / 25 : ℝ) := sub_nonneg.mpr hlo
  have hright : 0 ≤ 1 - t := sub_nonneg.mpr hhi
  have he : certificate t =
    (975694755748417489 / 305764761600000000 : ℝ) * (1 - t) ^ 4 +
      (17322553976822629489 / 76441190400000000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 1 * (1 - t) ^ 3 +
      (37773642277247881489 / 50960793600000000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 2 * (1 - t) ^ 2 +
      (60224159441984173489 / 76441190400000000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 3 * (1 - t) ^ 1 +
      (82705200705591505489 / 305764761600000000 : ℝ) * (t - (1 / 25 : ℝ)) ^ 4 := by
    unfold certificate
    dsimp [certificate, numerator, allowance, B, R, C]
    ring
  rw [he]
  positivity

/-- A rational upper bound suffices for the radius comparison. -/
lemma side_sum_cap {t k S : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 ≤ k) (hk2 : k ^ 2 = C * (2 + t ^ 2))
    (hS : S ≤ C + 2 + t ^ 2 + 2 * k) : S ≤ 1503 / 100 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hkbound : k ≤ 743 / 200 := by dsimp [C] at hk2; nlinarith
  dsimp [C] at hS
  linarith

lemma radius_closure {q S : ℝ} (hq : 0 ≤ q)
    (hS : S ≤ 1503 / 100)
    (hbound : B / 4 < q → q * (6 * B - S) ≤ B ^ 2) : q ≤ R ^ 2 := by
  by_cases hsmall : q ≤ B / 4
  · dsimp [B, R] at *; linarith
  · have hh := hbound (lt_of_not_ge hsmall)
    have hm := mul_nonneg hq (sub_nonneg.mpr hS)
    dsimp [B, R] at *
    nlinarith

/-- The two exact certificates close the child invariant. -/
lemma child_closure {q t k S : ℝ} (hq : 0 ≤ q)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 ≤ k) (hk2 : k ^ 2 = C * (2 + t ^ 2))
    (hS : S ≤ C + 2 + t ^ 2 + 2 * k)
    (hsum : B / 4 < q → q * (6 * B - S) ≤ B ^ 2)
    (hedge : q * (4 * B - (R + t) ^ 2) ≤ B ^ 2) :
    R ^ 2 + 2 * q - (2 / 3) * t ^ 2 ≤ C := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hA : 0 < allowance (t ^ 2) := by
    dsimp [allowance, C, R]; positivity
  by_cases hsmall : q ≤ B / 4
  · dsimp [B, R, C] at *; nlinarith [sq_nonneg t]
  have hqsum := hsum (lt_of_not_ge hsmall)
  have hScap := side_sum_cap ht ht1 hk hk2 hS
  have hden : 0 < 6 * B - (C + 2 + t ^ 2 + 2 * k) := by
    have := side_sum_cap ht ht1 hk hk2 (le_refl (C + 2 + t ^ 2 + 2 * k))
    dsimp [B, R] at *; linarith
  have hqden : q * (6 * B - (C + 2 + t ^ 2 + 2 * k)) ≤ B ^ 2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hS)]
  by_cases htlo : t ≤ 1 / 5
  · have hp := smallCertificate_nonneg ht htlo
    have hd : 0 < 4 * B - (R + t) ^ 2 := by
      dsimp [B, R]; nlinarith
    have hh : (4 * B - (R + t) ^ 2) *
        (allowance (t ^ 2) - 2 * q) ≥ 0 := by
      dsimp [smallCertificate] at hp
      nlinarith
    have ha := nonneg_of_mul_nonneg_right hh hd
    dsimp [allowance] at ha
    linarith
  · have hlo : 1 / 25 ≤ t ^ 2 := by nlinarith [lt_of_not_ge htlo]
    have hn := numerator_nonneg hlo ht2
    have hp := certificate_nonneg hlo ht2
    have hsq : (2 * k * allowance (t ^ 2)) ^ 2 =
        4 * C * (2 + t ^ 2) * allowance (t ^ 2) ^ 2 := by
      calc
        _ = 4 * k ^ 2 * allowance (t ^ 2) ^ 2 := by ring
        _ = _ := by rw [hk2]; ring
    have hka : 0 ≤ 2 * k * allowance (t ^ 2) := by positivity
    have hnka : 2 * k * allowance (t ^ 2) ≤ numerator (t ^ 2) := by
      dsimp [certificate] at hp
      nlinarith
    have hh : (6 * B - (C + 2 + t ^ 2 + 2 * k)) *
        (allowance (t ^ 2) - 2 * q) ≥ 0 := by
      dsimp [numerator] at hnka
      nlinarith
    have ha := nonneg_of_mul_nonneg_right hh hden
    dsimp [allowance] at ha
    linarith

/-- The numerical obligations for the shared three-candidate placement proof. -/
structure NumericalClosure (R C : ℝ) : Prop where
  radius_nonneg : 0 ≤ R
  invariant_ge_three : 3 ≤ C
  repeated_triangle : 2 * R ^ 2 ≤ C
  tetrahedron_cap : 6 * R ^ 2 ≤ 11
  radius : ∀ {q t k S : ℝ}, 0 ≤ q → 0 ≤ t → t ≤ 1 →
    0 ≤ k → k ^ 2 = C * (2 + t ^ 2) → S ≤ C + 2 + t ^ 2 + 2 * k →
    ((R + 1) ^ 2 / 4 < q → q * (6 * (R + 1) ^ 2 - S) ≤ ((R + 1) ^ 2) ^ 2) →
    q ≤ R ^ 2
  child : ∀ {q t k S : ℝ}, 0 ≤ q → 0 ≤ t → t ≤ 1 →
    0 ≤ k → k ^ 2 = C * (2 + t ^ 2) → S ≤ C + 2 + t ^ 2 + 2 * k →
    ((R + 1) ^ 2 / 4 < q → q * (6 * (R + 1) ^ 2 - S) ≤ ((R + 1) ^ 2) ^ 2) →
    q * (4 * (R + 1) ^ 2 - (R + t) ^ 2) ≤ ((R + 1) ^ 2) ^ 2 →
    R ^ 2 + 2 * q - (2 / 3) * t ^ 2 ≤ C

/-- The sharp two-piece scalar estimates instantiate the shared placement rule. -/
theorem sharp_closure : NumericalClosure R C where
  radius_nonneg := by norm_num [R]
  invariant_ge_three := by norm_num [C]
  repeated_triangle := by norm_num [R, C]
  tetrahedron_cap := by norm_num [R]
  radius := fun hq ht ht1 hk hk2 hS hsum =>
    radius_closure hq (side_sum_cap ht ht1 hk hk2 hS) hsum
  child := child_closure

namespace ZeroSplit

/-- Independent one-interval constants, with the `93/20` triangle invariant. -/
def R : ℝ := 13 / 10
def C : ℝ := 93 / 20
def B : ℝ := (R + 1) ^ 2
def allowance (s : ℝ) : ℝ := C - R ^ 2 + (2 / 3) * s
def numerator (s : ℝ) : ℝ :=
  (6 * B - C - 2 - s) * allowance s - 2 * B ^ 2
def certificate (s : ℝ) : ℝ :=
  numerator s ^ 2 - 4 * C * (2 + s) * allowance s ^ 2

/-- Homogenization of the supplied degree-two Möbius certificate. -/
lemma numerator_eq (s : ℝ) : numerator s =
    (156991 / 5000 : ℝ) * s ^ 2 +
    (377723 / 7500 : ℝ) * s * (1 - s) +
    (91491 / 5000 : ℝ) * (1 - s) ^ 2 := by
  dsimp [numerator, allowance, B, R, C]
  ring

/-- Homogenization of the supplied degree-four Möbius certificate. -/
lemma certificate_eq (s : ℝ) : certificate s =
    (6298142081 / 25000000 : ℝ) * s ^ 4 +
    (13901223493 / 18750000 : ℝ) * s ^ 3 * (1 - s) +
    (79945181687 / 112500000 : ℝ) * s ^ 2 * (1 - s) ^ 2 +
    (1434994331 / 6250000 : ℝ) * s * (1 - s) ^ 3 +
    (222315081 / 25000000 : ℝ) * (1 - s) ^ 4 := by
  dsimp [certificate, numerator, allowance, B, R, C]
  ring

lemma numerator_nonneg {s : ℝ} (hlo : 0 ≤ s) (hhi : s ≤ 1) :
    0 ≤ numerator s := by
  have hright : 0 ≤ 1 - s := sub_nonneg.mpr hhi
  rw [numerator_eq]
  positivity

lemma certificate_nonneg {s : ℝ} (hlo : 0 ≤ s) (hhi : s ≤ 1) :
    0 ≤ certificate s := by
  have hright : 0 ≤ 1 - s := sub_nonneg.mpr hhi
  rw [certificate_eq]
  positivity

/-- A rational cap on the exact square-root side-sum bound. -/
lemma side_sum_cap {t k S : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 ≤ k) (hk2 : k ^ 2 = C * (2 + t ^ 2))
    (hS : S ≤ C + 2 + t ^ 2 + 2 * k) : S ≤ 378 / 25 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hkbound : k ≤ 747 / 200 := by dsimp [C] at hk2; nlinarith
  dsimp [C] at hS
  linarith

lemma radius_closure {q S : ℝ} (hq : 0 ≤ q) (hS : S ≤ 378 / 25)
    (hbound : B / 4 < q → q * (6 * B - S) ≤ B ^ 2) : q ≤ R ^ 2 := by
  by_cases hsmall : q ≤ B / 4
  · dsimp [B, R] at *; linarith
  · have hh := hbound (lt_of_not_ge hsmall)
    have hm := mul_nonneg hq (sub_nonneg.mpr hS)
    dsimp [B, R] at *
    nlinarith

/-- A single certificate range `0 ≤ t² ≤ 1` closes the triangle invariant.
Only the geometric half-diameter radius alternative is distinguished. -/
lemma child_closure {q t k S : ℝ} (hq : 0 ≤ q)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hk : 0 ≤ k) (hk2 : k ^ 2 = C * (2 + t ^ 2))
    (hS : S ≤ C + 2 + t ^ 2 + 2 * k)
    (hsum : B / 4 < q → q * (6 * B - S) ≤ B ^ 2) :
    R ^ 2 + 2 * q - (2 / 3) * t ^ 2 ≤ C := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hA : 0 < allowance (t ^ 2) := by
    dsimp [allowance, C, R]; positivity
  by_cases hsmall : q ≤ B / 4
  · dsimp [B, R, C] at *; nlinarith [sq_nonneg t]
  have hqsum := hsum (lt_of_not_ge hsmall)
  have hden : 0 < 6 * B - (C + 2 + t ^ 2 + 2 * k) := by
    have := side_sum_cap ht ht1 hk hk2 (le_refl (C + 2 + t ^ 2 + 2 * k))
    dsimp [B, R] at *; linarith
  have hqden : q * (6 * B - (C + 2 + t ^ 2 + 2 * k)) ≤ B ^ 2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hS)]
  have hn := numerator_nonneg (sq_nonneg t) ht2
  have hp := certificate_nonneg (sq_nonneg t) ht2
  have hsq : (2 * k * allowance (t ^ 2)) ^ 2 =
      4 * C * (2 + t ^ 2) * allowance (t ^ 2) ^ 2 := by
    calc
      _ = 4 * k ^ 2 * allowance (t ^ 2) ^ 2 := by ring
      _ = _ := by rw [hk2]; ring
  have hka : 0 ≤ 2 * k * allowance (t ^ 2) := by positivity
  have hnka : 2 * k * allowance (t ^ 2) ≤ numerator (t ^ 2) := by
    dsimp [certificate] at hp
    nlinarith
  have hh : (6 * B - (C + 2 + t ^ 2 + 2 * k)) *
      (allowance (t ^ 2) - 2 * q) ≥ 0 := by
    dsimp [numerator] at hnka
    nlinarith
  have ha := nonneg_of_mul_nonneg_right hh hden
  dsimp [allowance] at ha
  linarith

/-- The independent `13/10` numerical closure uses no short-edge certificate. -/
theorem closure : NumericalClosure R C where
  radius_nonneg := by norm_num [R]
  invariant_ge_three := by norm_num [C]
  repeated_triangle := by norm_num [R, C]
  tetrahedron_cap := by norm_num [R]
  radius := fun hq ht ht1 hk hk2 hS hsum =>
    radius_closure hq (side_sum_cap ht ht1 hk hk2 hS) hsum
  child := fun hq ht ht1 hk hk2 hS hsum _ => child_closure hq ht ht1 hk hk2 hS hsum

end ZeroSplit

end
end HilbertTriangleInsertion
