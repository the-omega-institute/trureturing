/- GID: D5/S3/Fourier/HexagonalThetaStability
   generality: G
   mirror-B: D5/B/S3/Fourier/HexagonalThetaStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parametric hexagonal theta stability at every positive temperature. -/

import D5.S3.Fourier.ThetaVerticalPositive
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapMoments
import D5.S3.Entropy.FiniteSpectralEnvelope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Explicit stability of the hexagonal theta minimum -/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- `√(h(h+2))`: amplitude of the orbit deformation at hyperbolic gap `h`. -/
def gapAmplitude (h : ℝ) : ℝ := Real.sqrt (h * (h + 2))

def threePointGap (h a c₁ c₂ c₃ : ℝ) : ℝ :=
  Real.exp (-a * (h + gapAmplitude h * c₁)) +
    Real.exp (-a * (h + gapAmplitude h * c₂)) +
    Real.exp (-a * (h + gapAmplitude h * c₃)) - 3

/-- Admissible orbit coefficients. -/
def OrbitCoeff : Set (ℝ × ℝ × ℝ) :=
  {c | c.1 + c.2.1 + c.2.2 = 0 ∧ c.1 ^ 2 + c.2.1 ^ 2 + c.2.2 ^ 2 = 3 / 2}

def orbitGap (h a : ℝ) : ℝ :=
  ⨅ c : OrbitCoeff, threePointGap h a c.1.1 c.1.2.1 c.1.2.2

def cubicGap (h b : ℝ) : ℝ :=
  -3 * b * h + b ^ 2 / 2 * (3 * h + 9 * h ^ 2 / 2) -
    b ^ 3 / 6 * (9 * h ^ 2 + 15 * h ^ 3 / 2 + 3 / 4 * gapAmplitude h ^ 3)

def escapeGap (h a : ℝ) : ℝ :=
  Real.exp (a * max (gapAmplitude h / 2 - h) 0) - 1 -
    a * max (gapAmplitude h / 2 - h) 0 - 3 * a * h

private def baseCoeff : OrbitCoeff := ⟨(1, -1 / 2, -1 / 2), by norm_num [OrbitCoeff]⟩

private instance : Nonempty OrbitCoeff := ⟨baseCoeff⟩

private lemma threePointGap_lower (h a c d e : ℝ) : -3 ≤ threePointGap h a c d e := by
  unfold threePointGap
  linarith [Real.exp_pos (-a * (h + gapAmplitude h * c)),
    Real.exp_pos (-a * (h + gapAmplitude h * d)),
    Real.exp_pos (-a * (h + gapAmplitude h * e))]

private lemma orbit_bdd (h a : ℝ) :
    BddBelow (Set.range (fun c : OrbitCoeff =>
      threePointGap h a c.1.1 c.1.2.1 c.1.2.2)) :=
  ⟨-3, by rintro _ ⟨c, rfl⟩; exact threePointGap_lower ..⟩

private lemma orbit_lower (h a : ℝ) : -3 ≤ orbitGap h a :=
  le_ciInf fun _ => threePointGap_lower ..

private lemma orbit_le (h a : ℝ) (c : OrbitCoeff) :
    orbitGap h a ≤ threePointGap h a c.1.1 c.1.2.1 c.1.2.2 :=
  ciInf_le (orbit_bdd h a) c

private lemma orbit_zero (h : ℝ) : orbitGap h 0 = 0 := by
  apply le_antisymm
  · convert orbit_le h 0 baseCoeff using 1; norm_num [threePointGap]
  · exact le_ciInf fun c => by norm_num [threePointGap]

open D5.S3.Entropy.FiniteSpectralEnvelope
open D5.S3.Entropy.SpectralEnvelopeParameters

private lemma cubic_exp_lower (v : ℝ) :
    1 + v + v ^ 2 / 2 + v ^ 3 / 6 ≤ Real.exp v := by
  rcases le_total 0 v with hv | hv
  · have he := Real.sum_le_exp_of_nonneg hv 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  · have he := RefinedBMV.PositiveCenter.expNegPartial_remainder_signed
      3 (x := -v) (by linarith)
    norm_num [RefinedBMV.PositiveCenter.expNegPartial, Finset.sum_range_succ] at he
    linarith

private lemma moment_bounds {c d e : ℝ} (hc : c + d + e = 0)
    (hc2 : c ^ 2 + d ^ 2 + e ^ 2 = 3 / 2) : -1 ≤ c ∧ c ≤ 1 := by
  have he : 3 * c ^ 2 + (d - e) ^ 2 = 3 := by
    linear_combination 2 * hc2 + (c - d - e) * hc
  constructor <;> nlinarith [sq_nonneg (d - e)]

private lemma moment_min {c d e : ℝ} (hc : c + d + e = 0)
    (hc2 : c ^ 2 + d ^ 2 + e ^ 2 = 3 / 2) :
    c ≤ -1 / 2 ∨ d ≤ -1 / 2 ∨ e ≤ -1 / 2 := by
  by_contra hn
  push Not at hn
  have hcu : c < 1 := by linarith
  have hdu : d < 1 := by linarith
  have heu : e < 1 := by linarith
  have h1 := mul_pos (by linarith : 0 < c + 1 / 2) (by linarith : 0 < 1 - c)
  have h2 := mul_pos (by linarith : 0 < d + 1 / 2) (by linarith : 0 < 1 - d)
  have h3 := mul_pos (by linarith : 0 < e + 1 / 2) (by linarith : 0 < 1 - e)
  nlinarith

private lemma moment_cube {c d e : ℝ} (hc : c + d + e = 0)
    (hc2 : c ^ 2 + d ^ 2 + e ^ 2 = 3 / 2) :
    |c ^ 3 + d ^ 3 + e ^ 3| ≤ 3 / 4 := by
  have lower (x y z : ℝ) (h1 : x+y+z=0)
      (h2 : x^2+y^2+z^2=3/2) : -3/4 ≤ x^3+y^3+z^3 := by
    let p : Fin 3 → ℝ := ![(2+x)/6, (2+y)/6, (2+z)/6]
    have hp : ∀ i, 0 ≤ p i := by
      intro i
      fin_cases i
      · dsimp [p]; linarith [(moment_bounds h1 h2).1]
      · dsimp [p]
        linarith [(moment_bounds (c := y) (d := z) (e := x) (by linarith) (by linarith)).1]
      · dsimp [p]
        linarith [(moment_bounds (c := z) (d := x) (e := y) (by linarith) (by linarith)).1]
    have hm : ∑ i, p i = 1 := by
      simp [Fin.sum_univ_three, p]
      linarith
    have hq : finitePurity p = 3/8 := by
      simp [finitePurity, Fin.sum_univ_three, p]
      nlinarith [h1,h2]
    have h := finite_budget_envelope p hp hm (q := 3/8) (by norm_num) (by norm_num) hq.le
    have hs : Real.sqrt (1/4 : ℝ) = 1/2 := by norm_num
    have ht : finiteThird p = (39+2*(x^3+y^3+z^3))/1296 := by
      unfold finiteThird
      rw [hm, hq]
      simp [Fin.sum_univ_three, p]
      nlinarith [h1,h2]
    rw [ht] at h
    norm_num [envelope, hs] at h
    linarith
  apply abs_le.mpr
  constructor
  · linarith [lower c d e hc hc2]
  · have h := lower (-c) (-d) (-e) (by linarith) (by nlinarith)
    nlinarith

private lemma three_cubic {h b c d e : ℝ} (hh : 0 ≤ h * (h + 2)) (hb : 0 < b)
    (hc : c + d + e = 0) (hc2 : c ^ 2 + d ^ 2 + e ^ 2 = 3 / 2) :
    cubicGap h b ≤ threePointGap h b c d e := by
  let s := gapAmplitude h
  have hs : s ^ 2 = h * (h + 2) := Real.sq_sqrt hh
  have hcs := (abs_le.mp (moment_cube hc hc2)).2
  have hcub := mul_le_mul_of_nonneg_left hcs (show 0 ≤ s ^ 3 by dsimp [s, gapAmplitude]; positivity)
  have hd1 : (h + s * c) + (h + s * d) + (h + s * e) = 3 * h := by
    linear_combination s * hc
  have hd2 : (h + s * c) ^ 2 + (h + s * d) ^ 2 + (h + s * e) ^ 2 =
      3 * h + 9 * h ^ 2 / 2 := by
    linear_combination 2 * h * s * hc + s ^ 2 * hc2 + 3 / 2 * hs
  have hd3 : (h + s * c) ^ 3 + (h + s * d) ^ 3 + (h + s * e) ^ 3 ≤
      9 * h ^ 2 + 15 * h ^ 3 / 2 + 3 / 4 * s ^ 3 := by
    have heq : (h + s * c) ^ 3 + (h + s * d) ^ 3 + (h + s * e) ^ 3 =
        9 * h ^ 2 + 15 * h ^ 3 / 2 + s ^ 3 * (c ^ 3 + d ^ 3 + e ^ 3) := by
      linear_combination 3 * h ^ 2 * s * hc + 3 * h * s ^ 2 * hc2 +
        9 / 2 * h * hs
    rw [heq]
    nlinarith only [hcub]
  have ht := add_le_add (add_le_add (cubic_exp_lower (-b * (h + s * c)))
    (cubic_exp_lower (-b * (h + s * d)))) (cubic_exp_lower (-b * (h + s * e)))
  have h3 := mul_le_mul_of_nonneg_left hd3 (show 0 ≤ b ^ 3 / 6 by positivity)
  unfold cubicGap threePointGap
  change _ ≤ Real.exp (-b * (h + s * c)) + Real.exp (-b * (h + s * d)) +
    Real.exp (-b * (h + s * e)) - 3
  linear_combination ht + h3 + b * hd1 - b ^ 2 / 2 * hd2

private lemma three_extend {h b a c d e : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    a / b * threePointGap h b c d e ≤ threePointGap h a c d e := by
  have ha : 0 < a := hb.trans_le hba
  have hcoeff : 0 ≤ 1 - b / a := by linarith [(div_le_one ha).mpr hba]
  have hconv (u : ℝ) : Real.exp (-b * (h + gapAmplitude h * u)) ≤
      b / a * Real.exp (-a * (h + gapAmplitude h * u)) + (1 - b / a) := by
    have he := convexOn_exp.2 (Set.mem_univ (-a * (h + gapAmplitude h * u)))
      (Set.mem_univ (0 : ℝ)) (by positivity : 0 ≤ b / a) hcoeff
      (by ring : b / a + (1 - b / a) = 1)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at he
    convert he using 1
    congr 1
    field_simp
  have he := add_le_add (add_le_add (hconv c) (hconv d)) (hconv e)
  have hi : threePointGap h b c d e ≤ b / a * threePointGap h a c d e := by
    unfold threePointGap
    linarith
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ a / b by positivity)
  convert hm using 1
  field_simp

private lemma exp_remainder_mono {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    Real.exp v - 1 - v ≤ Real.exp u - 1 - u := by
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - v))
    (Real.exp_pos v).le
  rw [← Real.exp_add] at he
  have hvexp : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
  have hp := mul_nonneg (sub_nonneg.mpr hvexp) (sub_nonneg.mpr hvu)
  have heq : v + (u - v) = u := by ring
  rw [heq] at he
  nlinarith

private lemma three_escape {h a c d e : ℝ} (ha : 0 ≤ a)
    (hc : c + d + e = 0) (hc2 : c ^ 2 + d ^ 2 + e ^ 2 = 3 / 2) :
    escapeGap h a ≤ threePointGap h a c d e := by
  let s := gapAmplitude h
  let m := max (s / 2 - h) 0
  let f (u : ℝ) := Real.exp (-a * (h + s * u)) - 1 + a * (h + s * u)
  have hf (u : ℝ) : 0 ≤ f u := by
    dsimp [f]
    linarith [Real.add_one_le_exp (-a * (h + s * u))]
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hi (u : ℝ) (hu : u ≤ -1 / 2) :
      Real.exp (a * m) - 1 - a * m ≤ f u := by
    by_cases hm : s / 2 - h ≤ 0
    · have hm0 : m = 0 := max_eq_right hm
      simpa [hm0] using hf u
    · have hm0 : m = s / 2 - h := max_eq_left (le_of_not_ge hm)
      have harg : a * m ≤ -a * (h + s * u) := by
        rw [hm0]
        nlinarith [mul_le_mul_of_nonneg_left hu hs,
          mul_nonneg ha (show 0 ≤ -(h + s * u) - m by rw [hm0]; nlinarith)]
      have he := exp_remainder_mono (show 0 ≤ a * m by dsimp [m]; positivity) harg
      dsimp [f]
      linarith
  have hsum : f c + f d + f e = threePointGap h a c d e + 3 * a * h := by
    dsimp [f, threePointGap, s]
    linear_combination a * gapAmplitude h * hc
  rcases moment_min hc hc2 with hm | hm | hm
  · have := hi c hm
    change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
    linarith [hf d, hf e]
  · have := hi d hm
    change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
    linarith [hf c, hf e]
  · have := hi e hm
    change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
    linarith [hf c, hf d]

theorem orbitGap_lower {h : ℝ} :
    (∀ b a : ℝ, 0 < b → b ≤ a → a / b * cubicGap h b ≤ orbitGap h a) ∧
    (∀ a : ℝ, escapeGap h a ≤ orbitGap h a) := by
  constructor
  · intro b a hb hba
    have ha : 0 < a := hb.trans_le hba
    by_cases hh : 0 ≤ h * (h + 2)
    · apply le_ciInf
      intro c
      exact (mul_le_mul_of_nonneg_left (three_cubic hh hb c.2.1 c.2.2)
        (by positivity : 0 ≤ a / b)).trans (three_extend hb hba)
    have hn : h * (h + 2) < 0 := lt_of_not_ge hh
    have h0 : h < 0 := by nlinarith [sq_nonneg h]
    have hs : gapAmplitude h = 0 := Real.sqrt_eq_zero_of_nonpos hn.le
    have hbase : cubicGap h b ≤ 3 * Real.exp (-b * h) - 3 := by
      have ht := cubic_exp_lower (-b * h)
      have hc : 3 / 4 * (h * (h + 2)) * b ^ 2 * (1 - b * h) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg b)
        · nlinarith
      unfold cubicGap
      rw [hs]
      linear_combination 3 * ht + hc
    apply le_ciInf
    intro c
    have ht : cubicGap h b ≤ threePointGap h b c.1.1 c.1.2.1 c.1.2.2 := by
      simp only [threePointGap, hs, zero_mul, add_zero]
      linarith only [hbase]
    exact (mul_le_mul_of_nonneg_left ht
      (by positivity : 0 ≤ a / b)).trans (three_extend hb hba)
  · intro a
    by_cases ha : 0 ≤ a
    · exact le_ciInf fun c => three_escape ha c.2.1 c.2.2
    have ha0 : a ≤ 0 := le_of_not_ge ha
    apply le_ciInf
    rintro ⟨⟨c, d, e⟩, hc, hc2⟩
    let s := gapAmplitude h
    let m := max (s / 2 - h) 0
    let f (u : ℝ) := Real.exp (-a * (h + s * u)) - 1 + a * (h + s * u)
    have hf (u : ℝ) : 0 ≤ f u := by
      dsimp [f]
      linarith [Real.add_one_le_exp (-a * (h + s * u))]
    have hmono {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 0) :
        Real.exp v - 1 - v ≤ Real.exp u - 1 - u := by
      have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - v))
        (Real.exp_pos v).le
      rw [← Real.exp_add, show v + (u - v) = u by ring] at he
      have hexp : Real.exp v ≤ 1 := Real.exp_le_one_iff.mpr hv
      nlinarith [mul_nonneg (sub_nonneg.mpr hexp) (sub_nonneg.mpr huv)]
    have hi (u : ℝ) (hu : u ≤ -1 / 2) :
        Real.exp (a * m) - 1 - a * m ≤ f u := by
      by_cases hm : s / 2 - h ≤ 0
      · have hm0 : m = 0 := max_eq_right hm
        simpa [hm0] using hf u
      have hm0 : m = s / 2 - h := max_eq_left (le_of_not_ge hm)
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have hd : h + s * u ≤ -m := by rw [hm0]; nlinarith
      have hp := mul_le_mul_of_nonneg_left hd (neg_nonneg.mpr ha0)
      have harg : -a * (h + s * u) ≤ a * m := by nlinarith only [hp]
      have hv : a * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 (le_max_right _ _)
      have ht := hmono harg hv
      dsimp [f]
      linarith
    have hsum : f c + f d + f e = threePointGap h a c d e + 3 * a * h := by
      dsimp [f, threePointGap, s]
      linear_combination a * gapAmplitude h * hc
    rcases moment_min hc hc2 with hm | hm | hm
    · have := hi c hm
      change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
      linarith [hf d, hf e]
    · have := hi d hm
      change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
      linarith [hf c, hf e]
    · have := hi e hm
      change Real.exp (a * m) - 1 - a * m - 3 * a * h ≤ _
      linarith [hf c, hf d]

/-- `hexGap x y = cosh (dist (x+iy) (1/2+i√3/2)) - 1`. -/
def hexGap (x y : ℝ) : ℝ :=
  ((x - 1 / 2) ^ 2 + (y - Real.sqrt 3 / 2) ^ 2) / (Real.sqrt 3 * y)

private lemma hexGap_nonneg {x y : ℝ} (hy : 0 < y) : 0 ≤ hexGap x y := by
  unfold hexGap
  positivity

private lemma hex_norm_scale (v : ℤ × ℤ) :
    Q (1 / 2) (Real.sqrt 3 / 2) v * Real.sqrt 3 =
      2 * ((v.1 : ℝ) ^ 2 + (v.1 : ℝ) * v.2 + (v.2 : ℝ) ^ 2) := by
  have hr : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold Q
  field_simp
  ring_nf
  rw [hr2]
  ring

private lemma hex_norm_lower {v : ℤ × ℤ} (hv : v ≠ 0) :
    2 / Real.sqrt 3 ≤ Q (1 / 2) (Real.sqrt 3 / 2) v := by
  have hn : 0 < (v.1 : ℝ) ^ 2 + (v.1 : ℝ) * v.2 + (v.2 : ℝ) ^ 2 := by
    by_contra hn
    have h0 : (v.1 : ℝ) = 0 ∧ (v.2 : ℝ) = 0 := by
      constructor <;> nlinarith [sq_nonneg ((v.1 : ℝ) + v.2),
        sq_nonneg (v.1 : ℝ), sq_nonneg (v.2 : ℝ)]
    apply hv
    apply Prod.ext
    · exact_mod_cast h0.1
    · exact_mod_cast h0.2
  have hi : (1 : ℤ) ≤ v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 := by
    have : (0 : ℤ) < v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 := by exact_mod_cast hn
    omega
  have hr : 0 < Real.sqrt (3 : ℝ) := by positivity
  apply (div_le_iff₀ hr).mpr
  rw [hex_norm_scale]
  exact_mod_cast (by omega : (2 : ℤ) ≤ 2 * (v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2))

private lemma orbit_moments {x y : ℝ} (hy : 0 < y) (v : ℤ × ℤ) :
    let q := Q (1 / 2) (Real.sqrt 3 / 2) v
    let k := 1 + hexGap x y
    Q x y v + Q x y (hexTurn v) + Q x y (hexTurn (hexTurn v)) = 3 * q * k ∧
    (Q x y v - q * k) ^ 2 + (Q x y (hexTurn v) - q * k) ^ 2 +
      (Q x y (hexTurn (hexTurn v)) - q * k) ^ 2 =
        3 / 2 * q ^ 2 * (hexGap x y) * (hexGap x y + 2) := by
  have hr : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr4 : Real.sqrt (3 : ℝ) ^ 4 = 9 := by
    calc
      _ = (Real.sqrt (3 : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hr2]; norm_num
  have hr6 : Real.sqrt (3 : ℝ) ^ 6 = 27 := by
    calc
      _ = (Real.sqrt (3 : ℝ) ^ 2) ^ 3 := by ring
      _ = _ := by rw [hr2]; norm_num
  have hr8 : Real.sqrt (3 : ℝ) ^ 8 = 81 := by
    calc
      _ = (Real.sqrt (3 : ℝ) ^ 2) ^ 4 := by ring
      _ = _ := by rw [hr2]; norm_num
  dsimp [Q, hexTurn, hexGap]
  push_cast
  constructor <;> field_simp [hy.ne', hr] <;> ring_nf <;>
    simp only [hr2, hr4, hr6, hr8] <;> ring

private lemma orbit_parameters {x y : ℝ} (hy : 0 < y) (v : ℤ × ℤ)
    (hv : v ≠ 0) :
    ∃ c₁ c₂ c₃ : ℝ,
      let s := gapAmplitude (hexGap x y);
      c₁ + c₂ + c₃ = 0 ∧ c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = 3 / 2 ∧
      Q x y v = Q (1 / 2) (Real.sqrt 3 / 2) v * (1 + hexGap x y + s * c₁) ∧
      Q x y (hexTurn v) =
        Q (1 / 2) (Real.sqrt 3 / 2) v * (1 + hexGap x y + s * c₂) ∧
      Q x y (hexTurn (hexTurn v)) =
        Q (1 / 2) (Real.sqrt 3 / 2) v * (1 + hexGap x y + s * c₃) := by
  let h := hexGap x y
  let q := Q (1 / 2) (Real.sqrt 3 / 2) v
  let d₁ := Q x y v - q * (1 + h)
  let d₂ := Q x y (hexTurn v) - q * (1 + h)
  let d₃ := Q x y (hexTurn (hexTurn v)) - q * (1 + h)
  have hq : 0 < q := (by positivity : 0 < 2 / Real.sqrt (3 : ℝ)).trans_le
    (hex_norm_lower hv)
  have hm := orbit_moments (x := x) hy v
  change _ ∧ d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 = 3 / 2 * q ^ 2 * h * (h + 2) at hm
  have hd : d₁ + d₂ + d₃ = 0 := by dsimp [d₁, d₂, d₃]; linarith [hm.1]
  have hh : 0 ≤ h := hexGap_nonneg hy
  let s := gapAmplitude h
  have hs : s ^ 2 = h * (h + 2) := Real.sq_sqrt (by positivity)
  have hd2 : d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 = 3 / 2 * q ^ 2 * s ^ 2 := by
    calc
      _ = 3 / 2 * q ^ 2 * (h * (h + 2)) := by nlinarith [hm.2]
      _ = _ := by rw [← hs]
  by_cases hs0 : s = 0
  · have hz : d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 0 := by
      rw [hs0] at hd2
      constructor
      · nlinarith [sq_nonneg d₂, sq_nonneg d₃]
      constructor <;> nlinarith [sq_nonneg d₁, sq_nonneg d₂, sq_nonneg d₃]
    refine ⟨1, -(1 / 2), -(1 / 2), by norm_num, by norm_num, ?_, ?_, ?_⟩
    · change Q x y v = q * (1 + h + s * 1)
      rw [hs0]
      dsimp [d₁] at hz
      nlinarith [hz.1]
    · change Q x y (hexTurn v) = q * (1 + h + s * -(1 / 2))
      rw [hs0]
      dsimp [d₂] at hz
      nlinarith [hz.2.1]
    · change Q x y (hexTurn (hexTurn v)) = q * (1 + h + s * -(1 / 2))
      rw [hs0]
      dsimp [d₃] at hz
      nlinarith [hz.2.2]
  · refine ⟨d₁ / (q * s), d₂ / (q * s), d₃ / (q * s), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← add_div, ← add_div, hd, zero_div]
    · apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
      field_simp [hq.ne', hs0]
      nlinarith [hd2]
    all_goals
      dsimp [d₁, d₂, d₃]
      change _ = q * _
      field_simp [hq.ne', hs0]
      ring


private lemma orbit_upper {h a : ℝ} (ha : 0 ≤ a) :
    orbitGap h a ≤ 3 * Real.exp (a * (gapAmplitude h - h)) := by
  have he (c : ℝ) (hc : -1 ≤ c) :
      Real.exp (-a * (h + gapAmplitude h * c)) ≤
        Real.exp (a * (gapAmplitude h - h)) := by
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ gapAmplitude h := Real.sqrt_nonneg _
    nlinarith [mul_nonneg ha (mul_nonneg hs (by linarith : 0 ≤ c + 1))]
  have hb := orbit_le h a baseCoeff
  dsimp [baseCoeff, threePointGap] at hb
  linarith [he 1 (by norm_num), he (-1 / 2) (by norm_num)]

private lemma orbit_summable {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Summable (fun v : ℤ × ℤ =>
      orbitGap h (Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) *
        Real.exp (-Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v)) := by
  let s := gapAmplitude h
  have hs : s ^ 2 = h * (h + 2) := Real.sq_sqrt (by positivity)
  have hdec : 0 < 1 + h - s := by
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    nlinarith
  have hy0 : 0 < Real.sqrt (3 : ℝ) / 2 := by positivity
  have hb := ((summable t (1 / 2) ht hy0).mul_left (3 : ℝ)).add
    ((summable (t * (1 + h - s)) (1 / 2) (mul_pos ht hdec) hy0).mul_left 3)
  apply hb.of_norm_bounded
  intro v
  let a := Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v
  have ha : 0 ≤ a := by dsimp [a, Q]; positivity
  have habs : |orbitGap h a| ≤ 3 + 3 * Real.exp (a * (s - h)) := by
    apply abs_le.mpr
    constructor
    · linarith [orbit_lower h a, Real.exp_pos (a * (s - h))]
    · linarith [orbit_upper (h := h) ha]
  have hm := mul_le_mul_of_nonneg_right habs (Real.exp_pos (-a)).le
  have he : Real.exp (a * (s - h)) * Real.exp (-a) =
      Real.exp (-Real.pi * (t * (1 + h - s)) *
        Q (1 / 2) (Real.sqrt 3 / 2) v) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  simp only [neg_mul]
  change ‖orbitGap h a * Real.exp (-a)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (3 + 3 * Real.exp (a * (s - h))) * Real.exp (-a) := hm
    _ = _ := by rw [add_mul, mul_assoc, he]; simp only [a, neg_mul]

theorem hexagonal_theta_stability {t x y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Summable (fun v : ℤ × ℤ =>
      orbitGap (hexGap x y) (Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) *
        Real.exp (-Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v)) ∧
    1 / 3 * ∑' v : ℤ × ℤ,
      orbitGap (hexGap x y) (Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) *
        Real.exp (-Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) ≤
      F t x y - F t (1 / 2) (Real.sqrt 3 / 2) := by
  have hy0 : 0 < Real.sqrt 3 / 2 := by positivity
  let a (v : ℤ × ℤ) := Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v
  let w (v : ℤ × ℤ) := orbitGap (hexGap x y) (a v) * Real.exp (-(a v))
  let d (v : ℤ × ℤ) := Real.exp (-Real.pi * t * Q x y v) - Real.exp (-(a v))
  have hw : Summable w := by
    simpa [w, a] using orbit_summable ht (hexGap_nonneg (x := x) hy)
  refine ⟨by simpa [w, a] using hw, ?_⟩
  have hd : Summable d :=
    (summable t x ht hy).sub (by simpa [a] using summable t (1 / 2) ht hy0)
  have hd1 := hexTurn.summable_iff.mpr hd
  have hd2 := hexTurn.summable_iff.mpr hd1
  have hp (v : ℤ × ℤ) : w v ≤ d v + d (hexTurn v) + d (hexTurn (hexTurn v)) := by
    by_cases hv : v = (0, 0)
    · subst v
      norm_num [a, w, d, Q, hexTurn, orbit_zero]
    obtain ⟨c₁, c₂, c₃, hc, hc2, hq1, hq2, hq3⟩ := orbit_parameters hy v hv
    have hg := orbit_le (hexGap x y) (a v) ⟨(c₁, c₂, c₃), hc, hc2⟩
    have he (u c : ℝ) (hu : u = Q (1 / 2) (Real.sqrt 3 / 2) v *
        (1 + hexGap x y + gapAmplitude (hexGap x y) * c)) :
        Real.exp (-Real.pi * t * u) = Real.exp (-(a v)) *
          Real.exp (-(a v) * (hexGap x y + gapAmplitude (hexGap x y) * c)) := by
      rw [← Real.exp_add, hu]
      congr 1
      dsimp [a]
      ring
    have hg' := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-(a v))).le
    dsimp [w, d]
    rw [he _ _ hq1, he _ _ hq2, he _ _ hq3]
    simp only [a, hex_q_turn, threePointGap] at *
    nlinarith only [hg']
  have hsum := hw.tsum_le_tsum hp ((hd.add hd1).add hd2)
  have hsum_exp : (∑' i, (d i + d (hexTurn i) + d (hexTurn (hexTurn i)))) =
      (∑' i, d i) + (∑' i, d (hexTurn i)) + (∑' i, d (hexTurn (hexTurn i))) := by
    calc
      _ = (∑' i, (d i + d (hexTurn i))) +
          (∑' i, d (hexTurn (hexTurn i))) := by
        simpa only [Function.comp_apply, add_assoc] using (hd.add hd1).tsum_add hd2
      _ = _ := by
        rw [show (∑' i, (d i + d (hexTurn i))) = (∑' i, d i) +
          (∑' i, d (hexTurn i)) from by
            simpa only [Function.comp_apply] using hd.tsum_add hd1]
  rw [hsum_exp] at hsum
  have he1 : (∑' v, d (hexTurn v)) = ∑' v, d v := hexTurn.tsum_eq d
  have he2 : (∑' v, d (hexTurn (hexTurn v))) = ∑' v, d v := by
    rw [hexTurn.tsum_eq (fun v => d (hexTurn v)), he1]
  have hdsum : (∑' v, d v) = F t x y - F t (1 / 2) (Real.sqrt 3 / 2) := by
    simpa [d, a, F] using (summable t x ht hy).tsum_sub (summable t (1 / 2) ht hy0)
  rw [he1, he2, hdsum] at hsum
  have hfinal : 1 / 3 * (∑' v, w v) ≤
      F t x y - F t (1 / 2) (Real.sqrt 3 / 2) := by linarith
  simpa only [w, a, neg_mul] using hfinal

end
end D5.S3.Fourier.PlanarTheta
