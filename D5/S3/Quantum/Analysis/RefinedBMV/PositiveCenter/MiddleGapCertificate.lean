/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Soundness of the compact right-strip interval certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapHessianRule
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapJet
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapMoments
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapPhysicalJets
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapPolynomial
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripIntervals

/-! # The compact strip of the positive-center kernel -/

namespace RefinedBMV.PositiveCenter.MiddleGapReplay

open SmallCorner (RoundedInterval)
open Set

private abbrev I := RoundedInterval
private abbrev J := QuadraticJet I

private def scalar (q : ℚ) : J := QuadraticJet.const (RoundedInterval.point q)

private def expTerm (k : ℕ) : ℚ := (-1 : ℚ) ^ k / (k.factorial : ℚ)

private def momentTerm (j k : ℕ) : ℚ := expTerm k / ((k + j : ℕ) + 1)

private def polynomialAt (coeff : ℕ → ℚ) (degree : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (degree + 1), coeff k * x ^ k

private def roundedHorner (coeff : ℕ → ℚ) (x : I) : ℕ → ℕ → I
  | 0, j => RoundedInterval.point (coeff j)
  | n + 1, j => RoundedInterval.point (coeff j) + roundedHorner coeff x n (j + 1) * x

private theorem roundedHorner_sound (coeff : ℕ → ℚ) {z : I} {x : ℝ} (hx : z.encloses x)
    (n j : ℕ) : (roundedHorner coeff z n j).encloses
      (∑ k ∈ Finset.range (n + 1), (coeff (j + k) : ℝ) * x ^ k) := by
  induction n generalizing j with
  | zero => simpa [roundedHorner] using RoundedInterval.encloses_point (coeff j)
  | succ n ih =>
    have h := RoundedInterval.encloses_add (RoundedInterval.encloses_point (coeff j))
      (RoundedInterval.encloses_mul (ih (j + 1)) hx)
    change (roundedHorner coeff z (n + 1) j).encloses _ at h
    convert h using 1
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp only [Nat.add_zero, pow_zero, mul_one, add_comm (coeff j : ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show j + (k + 1) = j + 1 + k by omega, pow_succ, mul_assoc]

private theorem roundedHorner_cast (coeff : ℕ → ℚ) (n : ℕ) (x : ℚ) :
    (roundedHorner coeff (RoundedInterval.point x) n 0).encloses
      (polynomialAt coeff n x : ℝ) := by
  simpa only [polynomialAt, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Nat.zero_add] using
    roundedHorner_sound coeff (RoundedInterval.encloses_point x) n 0

private def bracket (coeff : ℕ → ℚ) (degree : ℕ) (x : I) : I :=
  let l := roundedHorner coeff (RoundedInterval.point x.upper) (degree + 1) 0
  let u := roundedHorner coeff (RoundedInterval.point (max 0 x.lower)) degree 0
  ⟨(l.endpoints.1, u.endpoints.2)⟩

private def expBracket (x : I) : I :=
  let b := bracket expTerm 18 (x * RoundedInterval.point (1 / 4))
  let b₂ := b * b
  b₂ * b₂

private structure Box where
  h₀ : ℚ
  h₁ : ℚ
  d₀ : ℚ
  d₁ : ℚ

private def Box.hm (b : Box) : ℚ := (b.h₀ + b.h₁) / 2
private def Box.dm (b : Box) : ℚ := (b.d₀ + b.d₁) / 2

private def Box.center (b : Box) : Box := ⟨b.hm, b.hm, b.dm, b.dm⟩

private def Box.split (b : Box) : Box × Box :=
  if 4 * (b.h₁ - b.h₀) > b.d₁ - b.d₀ then
    (⟨b.h₀, b.hm, b.d₀, b.d₁⟩, ⟨b.hm, b.h₁, b.d₀, b.d₁⟩)
  else
    (⟨b.h₀, b.h₁, b.d₀, b.dm⟩, ⟨b.h₀, b.h₁, b.dm, b.d₁⟩)

private def Box.moment (b : Box) (j : ℕ) : I :=
  let lo := RoundedInterval.point (b.d₀ ^ (j + 1)) * bracket (momentTerm j) 14 (RoundedInterval.point (b.h₁ * b.d₀))
  let hi := RoundedInterval.point (b.d₁ ^ (j + 1)) * bracket (momentTerm j) 14 (RoundedInterval.point (b.h₀ * b.d₁))
  ⟨(lo.endpoints.1, hi.endpoints.2)⟩

private def inputJets (b : Box) : J × J × J × J :=
  let h := RoundedInterval.interval b.h₀ b.h₁
  let d := RoundedInterval.interval b.d₀ b.d₁
  let s := h * d
  let q := expBracket s
  let z := expBracket d
  let one := RoundedInterval.point 1
  let half := RoundedInterval.point (1 / 2)
  let aJ : J := ⟨b.moment 0, 0 - b.moment 1, q, b.moment 2 * half,
    0 - d * q, 0 - h * q * half⟩
  let qJ : J := ⟨q, 0 - d * q, 0 - h * q, d * d * q * half,
    (s - one) * q, h * h * q * half⟩
  let zJ : J := ⟨z, 0, 0 - z, 0, 0, z * half⟩
  let dJ : J := ⟨d, 0, one, 0, 0, 0⟩
  (dJ, aJ, qJ, zJ)

private def evaluate (b : Box) : J × J :=
  let (d, a, q, z) := inputJets b
  middleGapCompactPolynomials scalar d a q z

private def magnitude (x : I) : ℚ := max |x.lower| |x.upper|

private def lower (center wide : J) (rh rd : ℚ) : ℚ :=
  center.value.lower - magnitude center.firstH * rh - magnitude center.firstD * rd +
    min 0 wide.secondH.lower * rh ^ 2 - magnitude wide.mixed * rh * rd +
    min 0 wide.secondD.lower * rd ^ 2

private def Box.check (b : Box) : Bool :=
  let (p, t) := evaluate b
  let (pc, tc) := evaluate b.center
  let rh := (b.h₁ - b.h₀) / 2
  let rd := (b.d₁ - b.d₀) / 2
  decide (1 / 20 < lower pc p rh rd ∧ 1 / 100 < lower tc t rh rd)

private def verify (b : Box) : ℕ → Bool
  | 0 => b.check
  | n + 1 => b.check || (verify b.split.1 n && verify b.split.2 n)

private def rectangle : Box := ⟨0, 3 / 11, 2, 4⟩

private def Encloses (wide : J) (a : QuadraticJet ℝ) : Prop :=
  wide.value.encloses a.value ∧ wide.firstH.encloses a.firstH ∧
    wide.firstD.encloses a.firstD ∧ wide.secondH.encloses a.secondH ∧
    wide.mixed.encloses a.mixed ∧ wide.secondD.encloses a.secondD

private theorem enclosesScalar (q : ℚ) : Encloses (scalar q) (QuadraticJet.const (q : ℝ)) := by
  have h := RoundedInterval.encloses_point q
  have h₀ : (0 : I).encloses 0 := by
    change (RoundedInterval.point 0).encloses (0 : ℝ)
    simpa only [Rat.cast_zero] using RoundedInterval.encloses_point 0
  exact ⟨h, h₀, h₀, h₀, h₀, h₀⟩

private theorem enclosesAdd {wide other : J} {a b : QuadraticJet ℝ}
    (hx : Encloses wide a) (hy : Encloses other b) : Encloses (wide + other) (a + b) := by
  rcases hx with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  rcases hy with ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩
  exact ⟨RoundedInterval.encloses_add h₁ k₁, RoundedInterval.encloses_add h₂ k₂,
    RoundedInterval.encloses_add h₃ k₃, RoundedInterval.encloses_add h₄ k₄,
    RoundedInterval.encloses_add h₅ k₅, RoundedInterval.encloses_add h₆ k₆⟩

private theorem enclosesSub {wide other : J} {a b : QuadraticJet ℝ}
    (hx : Encloses wide a) (hy : Encloses other b) : Encloses (wide - other) (a - b) := by
  rcases hx with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  rcases hy with ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩
  exact ⟨RoundedInterval.encloses_sub h₁ k₁, RoundedInterval.encloses_sub h₂ k₂,
    RoundedInterval.encloses_sub h₃ k₃, RoundedInterval.encloses_sub h₄ k₄,
    RoundedInterval.encloses_sub h₅ k₅, RoundedInterval.encloses_sub h₆ k₆⟩

private theorem enclosesMul {wide other : J} {a b : QuadraticJet ℝ}
    (hx : Encloses wide a) (hy : Encloses other b) : Encloses (wide * other) (a * b) := by
  rcases hx with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  rcases hy with ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩
  exact ⟨RoundedInterval.encloses_mul h₁ k₁,
    RoundedInterval.encloses_add (RoundedInterval.encloses_mul h₁ k₂)
      (RoundedInterval.encloses_mul h₂ k₁),
    RoundedInterval.encloses_add (RoundedInterval.encloses_mul h₁ k₃)
      (RoundedInterval.encloses_mul h₃ k₁),
    RoundedInterval.encloses_add (RoundedInterval.encloses_add (RoundedInterval.encloses_mul h₁ k₄)
      (RoundedInterval.encloses_mul h₂ k₂)) (RoundedInterval.encloses_mul h₄ k₁),
    RoundedInterval.encloses_add (RoundedInterval.encloses_add (RoundedInterval.encloses_add
      (RoundedInterval.encloses_mul h₁ k₅) (RoundedInterval.encloses_mul h₂ k₃))
      (RoundedInterval.encloses_mul h₃ k₂)) (RoundedInterval.encloses_mul h₅ k₁),
    RoundedInterval.encloses_add (RoundedInterval.encloses_add (RoundedInterval.encloses_mul h₁ k₆)
      (RoundedInterval.encloses_mul h₃ k₃)) (RoundedInterval.encloses_mul h₆ k₁)⟩

private structure Related {R S : Type*} (r : R → S → Prop) where
  left : R
  right : S
  sound : r left right

private theorem expression_rel {R S : Type*} [Add R] [Sub R] [Mul R] [Add S] [Sub S] [Mul S]
    {r : R → S → Prop} {c : ℚ → R} {C : ℚ → S}
    (hc : ∀ q, r (c q) (C q))
    (add : ∀ {a b x y}, r a x → r b y → r (a + b) (x + y))
    (sub : ∀ {a b x y}, r a x → r b y → r (a - b) (x - y))
    (mul : ∀ {a b x y}, r a x → r b y → r (a * b) (x * y))
    {d a q z : R} {D A Q Z : S} (hd : r d D) (ha : r a A) (hq : r q Q) (hz : r z Z) :
    let j := middleGapCompactPolynomials c d a q z
    let f := middleGapCompactPolynomials C D A Q Z
    r j.1 f.1 ∧ r j.2 f.2 := by
  letI : Add (Related r) := ⟨fun a b ↦ ⟨a.left+b.left, a.right+b.right, add a.sound b.sound⟩⟩
  letI : Sub (Related r) := ⟨fun a b ↦ ⟨a.left-b.left, a.right-b.right, sub a.sound b.sound⟩⟩
  letI : Mul (Related r) := ⟨fun a b ↦ ⟨a.left*b.left, a.right*b.right, mul a.sound b.sound⟩⟩
  let ef := middleGapCompactPolynomials (R := Related r) (fun k ↦ ⟨c k, C k, hc k⟩)
    ⟨d,D,hd⟩ ⟨a,A,ha⟩ ⟨q,Q,hq⟩ ⟨z,Z,hz⟩
  exact ⟨ef.1.sound, ef.2.sound⟩

private theorem expression_encloses {d a q z : J} {D A Q Z : QuadraticJet ℝ}
    (hd : Encloses d D) (ha : Encloses a A) (hq : Encloses q Q) (hz : Encloses z Z) :
    let s := middleGapCompactPolynomials scalar d a q z
    let S := middleGapCompactPolynomials (fun q ↦ QuadraticJet.const (q : ℝ)) D A Q Z
    Encloses s.1 S.1 ∧ Encloses s.2 S.2 :=
  expression_rel enclosesScalar enclosesAdd enclosesSub enclosesMul hd ha hq hz

private theorem expression_line_at {s x y : ℝ} {d a q z : QuadraticJet ℝ}
    {D A Q Z : ℝ → ℝ}
    (hd : d.IsLineAt D s x y) (ha : a.IsLineAt A s x y)
    (hq : q.IsLineAt Q s x y) (hz : z.IsLineAt Z s x y) :
    let j := middleGapCompactPolynomials (fun q ↦ QuadraticJet.const (q : ℝ)) d a q z
    let f := middleGapCompactPolynomials (fun q _ ↦ (q : ℝ)) D A Q Z
    j.1.IsLineAt f.1 s x y ∧ j.2.IsLineAt f.2 s x y :=
  expression_rel (r := fun j f ↦ QuadraticJet.IsLineAt j f s x y)
    (fun k ↦ QuadraticJet.IsLineAt.const s x y (k : ℝ))
    QuadraticJet.IsLineAt.add QuadraticJet.IsLineAt.sub QuadraticJet.IsLineAt.mul hd ha hq hz

private theorem expPolynomial_cast (n : ℕ) (u : ℚ) :
    (polynomialAt expTerm n u : ℝ) = expNegPartial n (u : ℝ) := by
  simp only [polynomialAt, expNegPartial, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [expTerm, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast]
  rw [show (-(u : ℝ)) ^ i = (-1 : ℝ) ^ i * (u : ℝ) ^ i by rw [← mul_pow, neg_one_mul]]
  ring

private theorem momentPolynomial_cast (n j : ℕ) (u : ℚ) :
    (polynomialAt (momentTerm j) n u : ℝ) = unitDecayMomentPartial n j (u : ℝ) := by
  simp only [polynomialAt, unitDecayMomentPartial, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [momentTerm, expTerm, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, div_eq_mul_inv, mul_inv_rev, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast]
  rw [show (-(u : ℝ)) ^ i = (-1 : ℝ) ^ i * (u : ℝ) ^ i by rw [← mul_pow, neg_one_mul]]
  ring

private theorem bracket_sound {f : ℝ → ℝ} {coeff : ℕ → ℚ} {n : ℕ} {w : I} {x : ℝ}
    (hx : w.encloses x) (hx₀ : 0 ≤ x) (hmono : Antitone f)
    (hl : ∀ u : ℚ, 0 ≤ u → (polynomialAt coeff (n + 1) u : ℝ) ≤ f u)
    (hu : ∀ u : ℚ, 0 ≤ u → f u ≤ (polynomialAt coeff n u : ℝ)) :
    (bracket coeff n w).encloses (f x) := by
  change (w.lower : ℝ) ≤ x ∧ x ≤ (w.upper : ℝ) at hx
  constructor
  · exact (roundedHorner_cast coeff (n + 1) w.upper).1.trans
      ((hl w.upper (by exact_mod_cast hx₀.trans hx.2)).trans (hmono hx.2))
  · have hm : ((max 0 w.lower : ℚ) : ℝ) ≤ x := by
      simpa only [Rat.cast_max, Rat.cast_zero] using max_le hx₀ hx.1
    exact ((hmono hm).trans (hu _ (le_max_left _ _))).trans (roundedHorner_cast coeff n _).2

private theorem expBracket_encloses {w : I} {x : ℝ} {n : ℕ}
    (he : Even n) (hx : w.encloses x) (hx₀ : 0 ≤ x) :
    (bracket expTerm n w).encloses (Real.exp (-x)) := by
  have hNeg : (-1 : ℝ) ^ (n+1) = -1 := by rw [pow_succ, he.neg_one_pow, one_mul]
  have hPos : (-1 : ℝ) ^ (n+1+1) = 1 := by rw [pow_succ, hNeg]; norm_num
  refine bracket_sound (f := fun z ↦ Real.exp (-z)) hx hx₀
    (fun _ _ h ↦ Real.exp_le_exp.mpr (neg_le_neg h)) ?_ ?_
  · intro u hu
    rw [expPolynomial_cast]
    have h := expNegPartial_remainder_signed (n+1) (by exact_mod_cast hu : 0 ≤ (u : ℝ))
    rw [hPos, one_mul, sub_nonneg] at h
    exact h
  · intro u hu
    rw [expPolynomial_cast]
    have h := expNegPartial_remainder_signed n (by exact_mod_cast hu : 0 ≤ (u : ℝ))
    rw [hNeg, neg_one_mul, neg_sub, sub_nonneg] at h
    exact h

private theorem momentBracket_encloses {w : I} {x : ℝ} {n : ℕ} (j : ℕ)
    (he : Even n) (hx : w.encloses x) (hx₀ : 0 ≤ x) :
    (bracket (momentTerm j) n w).encloses (unitDecayMoment j x) := by
  have hNeg : (-1 : ℝ) ^ (n+1) = -1 := by rw [pow_succ, he.neg_one_pow, one_mul]
  have hPos : (-1 : ℝ) ^ (n+1+1) = 1 := by rw [pow_succ, hNeg]; norm_num
  refine bracket_sound hx hx₀ (unitDecayMoment_antitone j) ?_ ?_
  · intro u hu
    rw [momentPolynomial_cast]
    have h := unitDecayMomentPartial_remainder_signed (n+1) j (by exact_mod_cast hu : 0 ≤ (u : ℝ))
    rw [hPos, one_mul, sub_nonneg] at h
    exact h
  · intro u hu
    rw [momentPolynomial_cast]
    have h := unitDecayMomentPartial_remainder_signed n j (by exact_mod_cast hu : 0 ≤ (u : ℝ))
    rw [hNeg, neg_one_mul, neg_sub, sub_nonneg] at h
    exact h

private theorem expBracket_scaled_encloses {w : I} {x : ℝ} (hx : w.encloses x) (h₀ : 0 ≤ x) :
    (expBracket w).encloses (Real.exp (-x)) := by
  have hquarter : (RoundedInterval.point (1 / 4)).encloses (1 / 4) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      RoundedInterval.encloses_point (1 / 4)
  have he := expBracket_encloses (n := 18) (by decide)
    (RoundedInterval.encloses_mul hx hquarter) (by positivity : 0 ≤ x * (1 / 4))
  have hb := RoundedInterval.encloses_mul he he
  have hbb := RoundedInterval.encloses_mul hb hb
  have heq : (Real.exp (-(x * (1 / 4))) * Real.exp (-(x * (1 / 4)))) *
      (Real.exp (-(x * (1 / 4))) * Real.exp (-(x * (1 / 4)))) = Real.exp (-x) := by
    simp_rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbb
  exact hbb

private def Box.contains (b : Box) (h d : ℝ) : Prop :=
  (b.h₀ : ℝ) ≤ h ∧ h ≤ (b.h₁ : ℝ) ∧ (b.d₀ : ℝ) ≤ d ∧ d ≤ (b.d₁ : ℝ)

private theorem momentEndpoint_encloses {j : ℕ} {h d : ℚ} (hh : 0 ≤ h) (hd : 0 ≤ d) :
    (RoundedInterval.point (d ^ (j + 1)) *
      bracket (momentTerm j) 14 (RoundedInterval.point (h * d))).encloses
        (gapDecayMoment j (h : ℝ) (d : ℝ)) := by
  rw [gapDecayMoment_eq_scaled]
  apply RoundedInterval.encloses_mul
  · simpa only [Rat.cast_pow] using RoundedInterval.encloses_point (d ^ (j + 1))
  · have hq : (RoundedInterval.point (h * d)).encloses ((h : ℝ) * (d : ℝ)) := by
      simpa only [Rat.cast_mul] using RoundedInterval.encloses_point (h * d)
    exact momentBracket_encloses j (by decide) hq (by exact_mod_cast mul_nonneg hh hd)

private theorem Box.moment_encloses {b : Box} {j : ℕ} {h d : ℝ} (hB : b.contains h d)
    (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) : (b.moment j).encloses (gapDecayMoment j h d) := by
  rcases hB with ⟨hlo, hhi, dlo, dhi⟩
  have hd₀' : (0 : ℝ) ≤ b.d₀ := by exact_mod_cast hd₀
  have hL := momentEndpoint_encloses (j := j) (h := b.h₁) (d := b.d₀)
    (hh₀.trans (by exact_mod_cast hlo.trans hhi)) hd₀
  have hU := momentEndpoint_encloses (j := j) (h := b.h₀) (d := b.d₁) hh₀
    (hd₀.trans (by exact_mod_cast dlo.trans dhi))
  constructor
  · exact hL.1.trans (((gapDecayMoment_antitone_rate j hd₀') hhi).trans
      (gapDecayMoment_monotone_gap j h hd₀' (hd₀'.trans dlo) dlo))
  · exact ((gapDecayMoment_monotone_gap j h (hd₀'.trans dlo)
      ((hd₀'.trans dlo).trans dhi) dhi).trans
        ((gapDecayMoment_antitone_rate j ((hd₀'.trans dlo).trans dhi)) hlo)).trans hU.2

private noncomputable def realInputJets (h d : ℝ) :
    QuadraticJet ℝ × QuadraticJet ℝ × QuadraticJet ℝ × QuadraticJet ℝ :=
  let q := Real.exp (-(h*d))
  let z := Real.exp (-d)
  (⟨d, 0, 1, 0, 0, 0⟩,
    ⟨gapDecayMoment 0 h d, -gapDecayMoment 1 h d, q,
      gapDecayMoment 2 h d / 2, -d*q, -h*q/2⟩,
    ⟨q, -d*q, -h*q, d*d*q/2, (h*d-1)*q, h*h*q/2⟩,
    ⟨z, 0, -z, 0, 0, z/2⟩)

set_option maxHeartbeats 1000000 in
-- The six projected arithmetic fields share the input endpoints.
private theorem Box.inputJets_enclose {b : Box} {h d : ℝ} (hb : b.contains h d)
    (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) :
    let I := inputJets b
    let R := realInputJets h d
    Encloses I.1 R.1 ∧ Encloses I.2.1 R.2.1 ∧
      Encloses I.2.2.1 R.2.2.1 ∧ Encloses I.2.2.2 R.2.2.2 := by
  let hI := RoundedInterval.interval b.h₀ b.h₁
  let dI := RoundedInterval.interval b.d₀ b.d₁
  let qI := expBracket (hI*dI)
  let zI := expBracket dI
  let q := Real.exp (-(h*d))
  let z := Real.exp (-d)
  have hpos : 0 ≤ h := (by exact_mod_cast hh₀ : (0 : ℝ) ≤ b.h₀).trans hb.1
  have dpos : 0 ≤ d := (by exact_mod_cast hd₀ : (0 : ℝ) ≤ b.d₀).trans hb.2.2.1
  have hh : hI.encloses h := RoundedInterval.encloses_interval hb.1 hb.2.1
  have hd : dI.encloses d := RoundedInterval.encloses_interval hb.2.2.1 hb.2.2.2
  have hq : qI.encloses q := expBracket_scaled_encloses
    (RoundedInterval.encloses_mul hh hd) (mul_nonneg hpos dpos)
  have hz : zI.encloses z := expBracket_scaled_encloses hd dpos
  have hzero : (0 : I).encloses 0 := by
    change (RoundedInterval.point 0).encloses _
    simpa only [Rat.cast_zero] using RoundedInterval.encloses_point 0
  have hone : (RoundedInterval.point 1).encloses 1 := by
    simpa only [Rat.cast_one] using RoundedInterval.encloses_point 1
  have hhalf : (RoundedInterval.point (1/2)).encloses (1/2) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      RoundedInterval.encloses_point (1/2)
  have hM₀ := Box.moment_encloses (j := 0) hb hh₀ hd₀
  have hM₁ := Box.moment_encloses (j := 1) hb hh₀ hd₀
  have hM₂ := Box.moment_encloses (j := 2) hb hh₀ hd₀
  have hneg {I : RoundedInterval} {x : ℝ} (h : I.encloses x) : (0-I).encloses (-x) := by
    simpa only [zero_sub] using RoundedInterval.encloses_sub hzero h
  have hdq := RoundedInterval.encloses_mul hd hq
  have hhq := RoundedInterval.encloses_mul hh hq
  have hdq' : (0 - dI*qI).encloses (-d*q) := by simpa only [neg_mul] using hneg hdq
  have hhq' : (0 - hI*qI).encloses (-h*q) := by simpa only [neg_mul] using hneg hhq
  let half := RoundedInterval.point (1/2)
  refine ⟨⟨hd,hzero,hone,hzero,hzero,hzero⟩,
    ⟨hM₀,hneg hM₁,hq,?_,hdq',?_⟩,
    ⟨hq,hdq',hhq',?_,
      RoundedInterval.encloses_mul (RoundedInterval.encloses_sub
        (RoundedInterval.encloses_mul hh hd) hone) hq,?_⟩,
    ⟨hz,hzero,hneg hz,hzero,hzero,?_⟩⟩
  · change (b.moment 2 * half).encloses (gapDecayMoment 2 h d / 2)
    convert RoundedInterval.encloses_mul hM₂ hhalf using 1 <;> ring
  · change (0 - hI*qI*half).encloses (-h*q/2)
    convert hneg (RoundedInterval.encloses_mul hhq hhalf) using 1 <;> ring
  · change (dI*dI*qI*half).encloses (d*d*q/2)
    convert RoundedInterval.encloses_mul
      (RoundedInterval.encloses_mul (RoundedInterval.encloses_mul hd hd) hq) hhalf using 1 <;> ring
  · change (hI*hI*qI*half).encloses (h*h*q/2)
    convert RoundedInterval.encloses_mul
      (RoundedInterval.encloses_mul (RoundedInterval.encloses_mul hh hh) hq) hhalf using 1 <;> ring
  · change (zI*half).encloses (z/2)
    convert RoundedInterval.encloses_mul hz hhalf using 1 <;> ring

private noncomputable def realEvaluation (h d : ℝ) : QuadraticJet ℝ × QuadraticJet ℝ :=
  let (D, A, Q, Z) := realInputJets h d
  middleGapCompactPolynomials (fun k ↦ QuadraticJet.const (k : ℝ)) D A Q Z

private theorem Box.evaluate_encloses {b : Box} {h d : ℝ} (hb : b.contains h d)
    (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) :
    Encloses (evaluate b).1 (realEvaluation h d).1 ∧
      Encloses (evaluate b).2 (realEvaluation h d).2 := by
  obtain ⟨hd, ha, hq, hz⟩ := b.inputJets_enclose hb hh₀ hd₀
  exact expression_encloses hd ha hq hz

private noncomputable def lineValues (h₀ d₀ x y : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  let H := gapAffine h₀ x
  let D := gapAffine d₀ y
  middleGapCompactPolynomials (fun k _ ↦ (k : ℝ)) D
    (fun s ↦ upperTailGap (H s) (D s))
    (fun s ↦ Real.exp (-(H s * D s))) (fun s ↦ Real.exp (-D s))

private theorem lineValues_jets {h₀ d₀ x y s : ℝ} (hh : 0 < gapAffine h₀ x s) :
    let J := realEvaluation (gapAffine h₀ x s) (gapAffine d₀ y s)
    let F := lineValues h₀ d₀ x y
    J.1.IsLineAt F.1 s x y ∧ J.2.IsLineAt F.2 s x y :=
  expression_line_at (QuadraticJet.affineD d₀ s x y) (gapAline h₀ d₀ s x y hh)
    (gapRhoLine h₀ d₀ s x y) (gapExpLine d₀ s x y)

private theorem abs_le_magnitude {I : RoundedInterval} {x : ℝ} (hx : I.encloses x) :
    |x| ≤ (magnitude I : ℝ) := by
  change (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ) at hx
  unfold magnitude
  rw [Rat.cast_max, Rat.cast_abs, Rat.cast_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := neg_le_neg ((neg_le_abs (I.lower : ℝ)).trans (le_max_left _ |(I.upper : ℝ)|))
    exact (by simpa only [neg_neg] using h : -max |(I.lower : ℝ)| |(I.upper : ℝ)| ≤ I.lower).trans hx.1
  · exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))

private theorem line_lower {F : ℝ → ℝ} {j : ℝ → QuadraticJet ℝ} {center wide : J}
    {x y : ℝ} {rh rd : ℚ} (hx : |x| ≤ (rh : ℝ)) (hy : |y| ≤ (rd : ℝ))
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, (j s).IsLineAt F s x y)
    (hc : Encloses center (j 0)) (hw : ∀ s ∈ Ioo (0 : ℝ) 1, Encloses wide (j s)) :
    (lower center wide rh rd : ℝ) ≤ F 1 := by
  have h0 := hf 0 (by norm_num)
  have hd := (h0.smooth.differentiableAt (by norm_num)).hasDerivAt
  rw [h0.first_eq] at hd
  have hvalue : (center.value.lower : ℝ) ≤ F 0 := by rw [h0.value_eq]; exact hc.1.1
  have h := centeredHessianLowerBound
    (fun s hs ↦ (hf s hs).smooth.contDiffWithinAt) hx hy hvalue hd.hasDerivWithinAt
    (abs_le_magnitude hc.2.1) (abs_le_magnitude hc.2.2.1)
    (lh := wide.secondH.lower) (ld := wide.secondD.lower) (Mhd := magnitude wide.mixed) ?_
  · simpa only [lower, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_min, Rat.cast_zero] using h
  · intro s hs
    have hj := hf s (Ioo_subset_Icc_self hs)
    have he := hj.second_eq
    rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one] at he
    obtain ⟨_,_,_,hH,hM,hD⟩ := hw s hs
    exact ⟨(j s).secondH, (j s).mixed, (j s).secondD, by rw [he]; ring,
      hH.1, abs_le_magnitude hM, hD.1⟩

private theorem Box.checked_polynomials {b : Box} {h d : ℝ} (hb : b.contains h d)
    (hh : 0 < h) (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) (hcheck : b.check = true) :
    let P := middleGapCompactPolynomials (fun r ↦ (r : ℝ)) d (upperTailGap h d)
      (Real.exp (-(h*d))) (Real.exp (-d))
    1/20 < P.1 ∧ 1/100 < P.2 := by
  let hm : ℝ := b.hm
  let dm : ℝ := b.dm
  let x := h - hm
  let y := d - dm
  let H := gapAffine hm x
  let D := gapAffine dm y
  let F := lineValues hm dm x y
  let rh := (b.h₁ - b.h₀) / 2
  let rd := (b.d₁ - b.d₀) / 2
  have hhm : hm = ((b.h₀ : ℝ) + (b.h₁ : ℝ)) / 2 := by simp [hm, Box.hm]
  have hdm : dm = ((b.d₀ : ℝ) + (b.d₁ : ℝ)) / 2 := by simp [dm, Box.dm]
  have hRh : (rh : ℝ) = ((b.h₁ : ℝ) - (b.h₀ : ℝ)) / 2 := by dsimp [rh]; push_cast <;> ring
  have hRd : (rd : ℝ) = ((b.d₁ : ℝ) - (b.d₀ : ℝ)) / 2 := by dsimp [rd]; push_cast <;> ring
  have hh₀' : (0:ℝ) ≤ b.h₀ := by exact_mod_cast hh₀
  have hd₀' : (0:ℝ) ≤ b.d₀ := by exact_mod_cast hd₀
  obtain ⟨hb₁,hb₂,hb₃,hb₄⟩ := hb
  have hcenter : b.contains hm dm := by
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hhm, hdm, hb₁, hb₂, hb₃, hb₄]
  have hcenterPos : 0 < hm := by linarith only [hhm, hh₀', hb₂, hh]
  have hx : |x| ≤ (rh : ℝ) := by
    apply abs_le.mpr
    dsimp only [x]
    constructor <;> linarith only [hRh, hhm, hb₁, hb₂]
  have hy : |y| ≤ (rd : ℝ) := by
    apply abs_le.mpr
    dsimp only [y]
    constructor <;> linarith only [hRd, hdm, hb₃, hb₄]
  have hPath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : b.contains (H s) (D s) ∧ 0 < H s := by
    have hH : H s = (1-s)*hm + s*h := by dsimp [H, gapAffine, x]; ring
    have hD : D s = (1-s)*dm + s*d := by dsimp [D, gapAffine, y]; ring
    have ha : 0 ≤ 1-s := sub_nonneg.mpr hs.2
    have hab : (1-s)+s = 1 := by ring
    have hu := (convex_Icc (b.h₀ : ℝ) (b.h₁ : ℝ)) ⟨hcenter.1,hcenter.2.1⟩ ⟨hb₁,hb₂⟩ ha hs.1 hab
    have hv := (convex_Icc (b.d₀ : ℝ) (b.d₁ : ℝ)) ⟨hcenter.2.2.1,hcenter.2.2.2⟩
      ⟨hb₃,hb₄⟩ ha hs.1 hab
    have hp : H s ∈ Ioi (0 : ℝ) := by
      rw [hH]
      exact (convex_Ioi (0 : ℝ)) hcenterPos hh ha hs.1 hab
    exact ⟨⟨by simpa only [hH, smul_eq_mul] using hu.1,
      by simpa only [hH, smul_eq_mul] using hu.2,
      by simpa only [hD, smul_eq_mul] using hv.1,
      by simpa only [hD, smul_eq_mul] using hv.2⟩, hp⟩
  have hc : b.center.contains (H 0) (D 0) := by
    unfold Box.contains Box.center H D gapAffine
    simp [hm, dm]
  have hcm : 0 ≤ b.center.h₀ := by
    change 0 ≤ b.hm
    exact_mod_cast (show (0 : ℝ) ≤ (b.hm : ℝ) from hh₀'.trans hcenter.1)
  have hcd : 0 ≤ b.center.d₀ := by
    change 0 ≤ b.dm
    exact_mod_cast (show (0 : ℝ) ≤ (b.dm : ℝ) from hd₀'.trans hcenter.2.2.1)
  have hCenter := b.center.evaluate_encloses hc hcm hcd
  have hWide (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :=
    b.evaluate_encloses (hPath s (Ioo_subset_Icc_self hs)).1 hh₀ hd₀
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    lineValues_jets (h₀ := hm) (d₀ := dm) (x := x) (y := y) (s := s) (hPath s hs).2
  have hL := line_lower (F := F.1) (j := fun s ↦ (realEvaluation (H s) (D s)).1) hx hy
    (fun s hs ↦ (hF s hs).1) hCenter.1 (fun s hs ↦ (hWide s hs).1)
  have hR := line_lower (F := F.2) (j := fun s ↦ (realEvaluation (H s) (D s)).2) hx hy
    (fun s hs ↦ (hF s hs).2) hCenter.2 (fun s hs ↦ (hWide s hs).2)
  have h1H : H 1 = h := by dsimp [H, gapAffine, x]; ring
  have h1D : D 1 = d := by dsimp [D, gapAffine, y]; ring
  have hend := expression_rel (r := fun (g : ℝ → ℝ) (v : ℝ) ↦ g 1 = v)
    (c := fun k _ ↦ (k : ℝ)) (C := fun k ↦ (k : ℝ)) (fun _ ↦ rfl)
    (fun h₁ h₂ ↦ congrArg₂ (·+·) h₁ h₂) (fun h₁ h₂ ↦ congrArg₂ (·-·) h₁ h₂)
    (fun h₁ h₂ ↦ congrArg₂ (·*·) h₁ h₂)
    (d := D) (a := fun s ↦ upperTailGap (H s) (D s))
    (q := fun s ↦ Real.exp (-(H s*D s))) (z := fun s ↦ Real.exp (-D s))
    (D := d) (A := upperTailGap h d) (Q := Real.exp (-(h*d))) (Z := Real.exp (-d)) h1D
    (show (fun s ↦ upperTailGap (H s) (D s)) 1 = upperTailGap h d by simp [h1H,h1D])
    (show (fun s ↦ Real.exp (-(H s*D s))) 1 = Real.exp (-(h*d)) by simp [h1H,h1D])
    (show (fun s ↦ Real.exp (-D s)) 1 = Real.exp (-d) by simp [h1D])
  change F.1 1 = _ ∧ F.2 1 = _ at hend
  change decide (1/20 < lower (evaluate b.center).1 (evaluate b).1 rh rd ∧
    1/100 < lower (evaluate b.center).2 (evaluate b).2 rh rd) = true at hcheck
  obtain ⟨hP,hT⟩ := of_decide_eq_true hcheck
  have hP' := (Rat.cast_lt (K := ℝ)).mpr hP
  have hT' := (Rat.cast_lt (K := ℝ)).mpr hT
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    And.intro (hP'.trans_le (hL.trans_eq hend.1)) (hT'.trans_le (hR.trans_eq hend.2))

private theorem Box.split_contains {b : Box} {h d : ℝ} (hb : b.contains h d)
    (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) :
    (b.split.1.contains h d ∧ 0 ≤ b.split.1.h₀ ∧ 0 ≤ b.split.1.d₀) ∨
    (b.split.2.contains h d ∧ 0 ≤ b.split.2.h₀ ∧ 0 ≤ b.split.2.d₀) := by
  have hh₁ := hh₀.trans (by exact_mod_cast hb.1.trans hb.2.1 : b.h₀ ≤ b.h₁)
  have hd₁ := hd₀.trans (by exact_mod_cast hb.2.2.1.trans hb.2.2.2 : b.d₀ ≤ b.d₁)
  have hm₀ : 0 ≤ b.hm := by unfold Box.hm; positivity
  have dm₀ : 0 ≤ b.dm := by unfold Box.dm; positivity
  unfold Box.split
  split
  · rcases le_or_gt h (b.hm : ℝ) with hlo | hhi
    · exact Or.inl ⟨⟨hb.1, hlo, hb.2.2⟩, hh₀, hd₀⟩
    · exact Or.inr ⟨⟨hhi.le, hb.2⟩, hm₀, hd₀⟩
  · rcases le_or_gt d (b.dm : ℝ) with dlo | dhi
    · exact Or.inl ⟨⟨hb.1, hb.2.1, hb.2.2.1, dlo⟩, hh₀, hd₀⟩
    · exact Or.inr ⟨⟨hb.1, hb.2.1, dhi.le, hb.2.2.2⟩, hh₀, dm₀⟩

private theorem verify_sound {h d : ℝ} (hh : 0 < h) {b : Box} {n : ℕ}
    (hb : b.contains h d) (hh₀ : 0 ≤ b.h₀) (hd₀ : 0 ≤ b.d₀) (hv : verify b n = true) :
    let P := middleGapCompactPolynomials (fun r ↦ (r : ℝ)) d (upperTailGap h d)
      (Real.exp (-(h*d))) (Real.exp (-d))
    1/20 < P.1 ∧ 1/100 < P.2 := by
  induction n generalizing b with
  | zero => exact b.checked_polynomials hb hh hh₀ hd₀ hv
  | succ n ih =>
    have hq : b.check = true ∨ (verify b.split.1 n = true ∧ verify b.split.2 n = true) := by
      simpa [verify] using hv
    rcases hq with hq | ⟨hL,hR⟩
    · exact b.checked_polynomials hb hh hh₀ hd₀ hq
    · rcases b.split_contains hb hh₀ hd₀ with ⟨hLc,hLh,hLd⟩ | ⟨hRc,hRh,hRd⟩
      · exact ih hLc hLh hLd hL
      · exact ih hRc hRh hRd hR

private theorem strip_of_verify (hverify : verify rectangle 11 = true)
    {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} (hu : 4 ≤ u) (hd : 2 < v - u) (hdmax : v - u ≤ 4) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v-u
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hh₁ : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hb : rectangle.contains h d := by
    unfold Box.contains rectangle
    push_cast
    exact ⟨hh.le, hh₁, hd.le, hdmax⟩
  have hrel : h * upperTailGap h d = 1 - Real.exp (-(h*d)) := by
    unfold upperTailGap
    field_simp [hh.ne']
  have hpoint := verify_sound hh hb (by decide) (by decide) hverify
  rw [middleGapCompactPolynomials_eq hrel] at hpoint
  obtain ⟨hP,hT⟩ := hpoint
  have ⟨hs,hc⟩ := middleGapFifthOrder_bounds_of_polynomial hh
    ((by norm_num : (0:ℝ) < 2).trans hd) ((by norm_num : (0:ℝ) ≤ 1/20).trans hP.le)
    ((by norm_num : (0:ℝ) < 1/100).trans hT)
  exact logKernel_mixed_of_fifthOrder hp hu hd hs hc

private theorem verify_children {b : Box} {n : ℕ}
    (left : verify b.split.1 n = true) (right : verify b.split.2 n = true) :
    verify b (n + 1) = true := by
  change (b.check || (verify b.split.1 n && verify b.split.2 n)) = true
  rw [left, right, Bool.and_true, Bool.or_true]

end RefinedBMV.PositiveCenter.MiddleGapReplay
