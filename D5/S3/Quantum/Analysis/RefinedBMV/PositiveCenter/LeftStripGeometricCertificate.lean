/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certified boxes and their cover of the moderate left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricModels
import Batteries.Tactic.OpenPrivate

/-! Certified boxes for the geometric scalar on the left strip. -/

namespace RefinedBMV.PositiveCenter

noncomputable section

namespace LocalTaylor

open RefinedBMV.PositiveCenter.SmallCorner
open RefinedBMV.PositiveCenter.SmallCorner.RoundedInterval

open private Index Coordinates Model monomial unitBox Models Models.cons range range_sound
  const_sound Enclosure Enclosure.mk Enclosure.model Enclosure.value Enclosure.sound enclosureArithmetic
  modelArithmetic Arithmetic.scalar scalar_value scalar_model realScalar_eq
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricModels

private abbrev Endpoints := ℚ × ℚ

private def midpoint (B : Endpoints) : ℚ := (B.1+B.2)/2

private def radius (B : Endpoints) : ℚ := (B.2-B.1)/2

private def inputModel (B : Endpoints) (i : Index) : Model :=
  [(i, point (radius B)), ((0,0,0), point (midpoint B))]

private def unit {B : Endpoints} (x : ℝ) : ℝ := (x-(midpoint B : ℝ))/(radius B : ℝ)

private def InBox (B : Endpoints) (x : ℝ) : Prop := (B.1 : ℝ) ≤ x ∧ x ≤ (B.2 : ℝ)

private theorem radius_pos {B : Endpoints} (hB : B.1 < B.2) : (0 : ℝ) < (radius B : ℝ) := by
  have hb : 0 < radius B := div_pos (sub_pos.mpr hB) (by norm_num)
  exact_mod_cast hb

private theorem unit_abs_le {B : Endpoints} {x : ℝ} (hB : B.1 < B.2) (hx : InBox B x) :
    |unit (B := B) x| ≤ 1 := by
  unfold unit
  rw [abs_div, abs_of_pos (radius_pos hB), div_le_iff₀ (radius_pos hB), one_mul]
  obtain ⟨hl, hh⟩ := hx
  apply abs_le.mpr
  push_cast [midpoint, radius]
  exact ⟨by linarith, by linarith⟩

private theorem input_sound {B : Endpoints} (hB : B.1 < B.2) (x : ℝ)
    {u : Coordinates} {i : Index} (hi : monomial u i = unit (B := B) x) :
    Models u (inputModel B i) x := by
  have hx : (radius B : ℝ)*monomial u i + (midpoint B : ℝ) = x := by
    rw [hi, unit]
    field_simp [(radius_pos hB).ne']
    ring
  rw [← hx]
  exact Models.cons (encloses_point _) (const_sound _)

private abbrev Box := Endpoints × Endpoints × Endpoints

private def check (B : Box) : Bool :=
  match Arithmetic.scalar modelArithmetic (some (inputModel B.1 (1,0,0)))
      (some (inputModel B.2.1 (0,1,0))) (some (inputModel B.2.2 (0,0,1))) with
  | some P => decide (0 < (range P).lower)
  | none => false

private theorem check_sound {B : Box} {p : ℕ} (hp : 0 < p) {a d : ℝ}
    (hd₀ : 0 < d) (hv : 0 < d+a)
    (hH : InBox B.1 (3/(p : ℝ))) (hA : InBox B.2.1 a) (hD : InBox B.2.2 d)
    (hw : B.1.1 < B.1.2 ∧ B.2.1.1 < B.2.1.2 ∧ B.2.2.1 < B.2.2.2)
    (hc : check B = true) : 0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  let h : ℝ := 3/(p : ℝ)
  let u : Coordinates := (unit (B := B.1) h, unit (B := B.2.1) a, unit (B := B.2.2) d)
  have hu : unitBox u := ⟨unit_abs_le hw.1 hH, unit_abs_le hw.2.1 hA, unit_abs_le hw.2.2 hD⟩
  let H : Enclosure u := Enclosure.mk h (some (inputModel B.1 (1,0,0))) (fun P hP ↦ by
    cases hP
    exact input_sound hw.1 h (by simp [u, monomial]))
  let A : Enclosure u := Enclosure.mk a (some (inputModel B.2.1 (0,1,0))) (fun P hP ↦ by
    cases hP
    exact input_sound hw.2.1 a (by simp [u, monomial]))
  let D : Enclosure u := Enclosure.mk d (some (inputModel B.2.2 (0,0,1))) (fun P hP ↦ by
    cases hP
    exact input_sound hw.2.2 d (by simp [u, monomial]))
  let S := Arithmetic.scalar (enclosureArithmetic hu) H A D
  have he := scalar_model hu H A D
  change Enclosure.model S = _ at he
  unfold check at hc
  rw [← show Enclosure.model S = _ from he] at hc
  cases hS : Enclosure.model S with
  | none => simp [hS] at hc
  | some P =>
    have hl : (0 : ℚ) < (range P).lower := by simpa [hS] using hc
    have hbound := (range_sound hu (Enclosure.sound S P hS)).1
    have hc' : (0 : ℝ) < ((range P).lower : ℝ) := by exact_mod_cast hl
    have hs : Enclosure.value S = _ := (scalar_value hu H A D).trans (realScalar_eq hp hd₀ hv)
    exact hs ▸ hc'.trans_le hbound

private def leftHalf (B : Endpoints) : Endpoints := (B.1, midpoint B)
private def rightHalf (B : Endpoints) : Endpoints := (midpoint B, B.2)

private theorem inHalf {B : Endpoints} {x : ℝ} (hx : InBox B x) :
    InBox (leftHalf B) x ∨ InBox (rightHalf B) x := by
  rcases le_total x (midpoint B : ℝ) with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

private def validWidth (B : Box) : Prop :=
  B.1.1 < B.1.2 ∧ B.2.1.1 < B.2.1.2 ∧ B.2.2.1 < B.2.2.2

private theorem halfWidths {B : Endpoints} (h : B.1 < B.2) :
    (leftHalf B).1 < (leftHalf B).2 ∧ (rightHalf B).1 < (rightHalf B).2 := by
  dsimp [leftHalf, rightHalf, midpoint]
  exact ⟨by linarith, by linarith⟩

private def splitBox (B : Box) : Box × Box :=
  let (H, A, D) := B
  if radius A ≤ 3/2 * radius H ∧ radius D ≤ 3/2 * radius H then
    ((leftHalf H, A, D), (rightHalf H, A, D))
  else if radius D ≤ radius A then
    ((H, leftHalf A, D), (H, rightHalf A, D))
  else
    ((H, A, leftHalf D), (H, A, rightHalf D))

private def contains (B : Box) (h a d : ℝ) : Prop :=
  InBox B.1 h ∧ InBox B.2.1 a ∧ InBox B.2.2 d

private theorem split_sound {B : Box} {h a d : ℝ}
    (hw : validWidth B) (hx : contains B h a d) :
    (validWidth (splitBox B).1 ∧ contains (splitBox B).1 h a d) ∨
    (validWidth (splitBox B).2 ∧ contains (splitBox B).2 h a d) := by
  obtain ⟨H, A, D⟩ := B
  simp only [splitBox]
  split
  · rcases inHalf hx.1 with hl | hr
    · exact Or.inl ⟨⟨(halfWidths hw.1).1, hw.2⟩, ⟨hl, hx.2⟩⟩
    · exact Or.inr ⟨⟨(halfWidths hw.1).2, hw.2⟩, ⟨hr, hx.2⟩⟩
  split
  · rcases inHalf hx.2.1 with hl | hr
    · exact Or.inl ⟨⟨hw.1, (halfWidths hw.2.1).1, hw.2.2⟩, ⟨hx.1, hl, hx.2.2⟩⟩
    · exact Or.inr ⟨⟨hw.1, (halfWidths hw.2.1).2, hw.2.2⟩, ⟨hx.1, hr, hx.2.2⟩⟩
  · rcases inHalf hx.2.2 with hl | hr
    · exact Or.inl ⟨⟨hw.1, hw.2.1, (halfWidths hw.2.2).1⟩, ⟨hx.1, hx.2.1, hl⟩⟩
    · exact Or.inr ⟨⟨hw.1, hw.2.1, (halfWidths hw.2.2).2⟩, ⟨hx.1, hx.2.1, hr⟩⟩

private def checkCover : ℕ → Box → Bool
  | 0, B => check B
  | n+1, B => check B || (checkCover n (splitBox B).1 && checkCover n (splitBox B).2)

private theorem checkCover_sound {p : ℕ} (hp : 0 < p) {a d : ℝ}
    (hd : 0 < d) (hv : 0 < d+a) (n : ℕ) {B : Box} (hw : validWidth B)
    (hx : contains B (3/(p : ℝ)) a d) (hc : checkCover n B = true) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  induction n generalizing B with
  | zero => exact check_sound hp hd hv hx.1 hx.2.1 hx.2.2 hw hc
  | succ n ih =>
    simp only [checkCover, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hl, hr⟩
    · exact check_sound hp hd hv hx.1 hx.2.1 hx.2.2 hw hc
    · rcases split_sound hw hx with hl' | hr'
      · exact ih hl'.1 hl'.2 hl
      · exact ih hr'.1 hr'.2 hr

private def band (lo hi : ℚ) : Box := ((0,3/11), (0,1/2), (lo,hi))

private theorem band_sound {p : ℕ} (hp : 11 ≤ p) {a d : ℝ}
    (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hd₀ : 0 < d)
    {lo hi : ℚ} (hw : lo < hi) (hd : (lo : ℝ) ≤ d) (hdmax : d ≤ (hi : ℝ))
    {n : ℕ} (hc : checkCover n (band lo hi) = true) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : InBox (0,3/11) (3/(p : ℝ)) := by
    constructor
    · push_cast
      positivity
    · norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have ha' : InBox (0,1/2) a := ⟨by simpa using ha, by simpa using hamax⟩
  exact checkCover_sound hp₀ hd₀ (by linarith) n
    ⟨by norm_num [band], by norm_num [band], hw⟩ ⟨hh, ha', hd, hdmax⟩ hc

/-- The six closed bands for the moderate geometric left strip. -/
def moderateLeftStripCheck (depth : ℕ) : Bool :=
  checkCover depth (band 1 (5/4)) &&
  checkCover depth (band (5/4) (3/2)) &&
  checkCover depth (band (3/2) 2) &&
  checkCover depth (band 2 (5/2)) &&
  checkCover depth (band (5/2) 3) &&
  checkCover depth (band 3 (7/2))

/-- A successful centered enclosure check certifies the exact scalar
throughout the requested real interval. -/
theorem leftStripGeometricScalar_pos_of_check {depth : ℕ}
    (hcheck : moderateLeftStripCheck depth = true) {p : ℕ} (hp : 11 ≤ p)
    {a d : ℝ} (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hd : 1 ≤ d) (hdmax : d ≤ 7/2) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  simp only [moderateLeftStripCheck, Bool.and_eq_true, and_assoc] at hcheck
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hcheck
  have hd₀ : 0 < d := by linarith
  by_cases h₁ : d ≤ 5/4
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using hd)
      (by simpa using h₁) c₁
  by_cases h₂ : d ≤ 3/2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₁)))
      (by simpa using h₂) c₂
  by_cases h₃ : d ≤ 2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₂)))
      (by simpa using h₃) c₃
  by_cases h₄ : d ≤ 5/2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₃)))
      (by simpa using h₄) c₄
  by_cases h₅ : d ≤ 3
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₄)))
      (by simpa using h₅) c₅
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₅)))
      (by simpa using hdmax) c₆

end LocalTaylor

/-- A checked moderate strip gives the strict mixed-derivative sign for the
original kernel at every gap at least one. -/
theorem leftStrip_logKernel_mixed_lt_of_certificate {depth : ℕ}
    (hcheck : LocalTaylor.moderateLeftStripCheck depth = true)
    {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} (hu : 0 < u) (humax : u ≤ 1/2) (hd : 1 ≤ v-u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  leftStrip_logKernel_mixed_lt_of_geometric_interval hp (by norm_num) hu humax hd
    (fun _ _ ↦ LocalTaylor.leftStripGeometricScalar_pos_of_check hcheck hp)

#print axioms LocalTaylor.leftStripGeometricScalar_pos_of_check
#print axioms leftStrip_logKernel_mixed_lt_of_certificate


end

end RefinedBMV.PositiveCenter
