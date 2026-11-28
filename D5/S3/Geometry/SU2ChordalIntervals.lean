/- GID: D5/S3/Geometry/SU2ChordalIntervals
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-caratheodory-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Alternating series bounds for the cosine, sine and arctangent supply the rational endpoint estimates in the spherical cap inequalities. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

Alternating series bounds for the cosine, sine and arctangent supply the
rational endpoint estimates in the spherical cap inequalities.
-/

open Filter Finset
open scoped Topology

noncomputable section

namespace Omega.Geometry.SU2ChordalIntervals

open Real

private def trigTerm (x : ℝ) (s i : ℕ) : ℝ := x ^ (2 * i + s) / (2 * i + s).factorial

private def trigSum (x : ℝ) (s n : ℕ) : ℝ :=
  ∑ i ∈ range n, (-1 : ℝ) ^ i * trigTerm x s i

private theorem trigTerm_antitone {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π) (s : ℕ) :
    Antitone (fun i => trigTerm x s (i + 1)) := by
  apply antitone_nat_of_succ_le
  intro i
  let k := 2 * (i + 1) + s
  have h₁ : (3 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk : 2 ≤ k := by dsimp [k]; omega
    exact_mod_cast (show 3 ≤ k + 1 by omega)
  have h₂ : (4 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have hsq : x ^ 2 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) := by
    have hb : x ≤ 10 / 3 := by linarith [pi_lt_d2]
    have hs := pow_le_pow_left₀ hx hb 2
    have hm := mul_le_mul h₂ h₁ (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 0 ≤ (k : ℝ) + 2)
    nlinarith only [hs, hm]
  have he : 2 * (i + 1 + 1) + s = k + 2 := by dsimp [k]; omega
  change x ^ (2 * (i + 1 + 1) + s) / (↑(2 * (i + 1 + 1) + s).factorial : ℝ) ≤
    x ^ k / (k.factorial : ℝ)
  rw [he, pow_add, show (k + 2).factorial = (k + 2) * ((k + 1) * k.factorial) by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ k]]
  push_cast
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hden : 0 < ((k : ℝ) + 2) * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by positivity
  apply (div_le_div_iff₀ hden hf).mpr
  have hmul := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (pow_nonneg hx k) hf.le)
  nlinarith only [hmul]

private theorem alternating_tail_bounds {a : ℕ → ℝ} {l : ℝ}
    (ha : Antitone fun i => a (i + 1))
    (ht : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * a i) atTop (𝓝 l))
    (k : ℕ) :
    (∑ i ∈ range (2 * k + 2), (-1 : ℝ) ^ i * a i) ≤ l ∧
      l ≤ (∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i) := by
  have hid (n : ℕ) :
      (∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * a i) =
        a 0 - ∑ i ∈ range n, (-1 : ℝ) ^ i * a (i + 1) := by
    rw [Finset.sum_range_succ']
    simp only [pow_succ, pow_zero, one_mul]
    have hsum : (∑ x ∈ range n, (-1 : ℝ) ^ x * -1 * a (x + 1)) =
        -(∑ i ∈ range n, (-1 : ℝ) ^ i * a (i + 1)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]
    ring
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * a i) atTop (𝓝 l) at ht'
  simp only [hid] at ht'
  have htail : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * a (i + 1))
      atTop (𝓝 (a 0 - l)) := by
    simpa only [sub_sub_cancel] using (tendsto_const_nhds (x := a 0)).sub ht'
  have hlo := ha.alternating_series_le_tendsto htail k
  have hup := ha.tendsto_le_alternating_series htail k
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, hid, hid]
  constructor <;> linarith only [hlo, hup]

/-- The alternating cosine partial sums bound cosine throughout `[0, π]`. -/
theorem cos_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π) (k : ℕ) :
    trigSum x 0 (2 * k + 2) ≤ cos x ∧ cos x ≤ trigSum x 0 (2 * k + 1) := by
  apply alternating_tail_bounds (trigTerm_antitone hx hx' 0)
  simpa only [trigTerm, Nat.add_zero, mul_div_assoc] using (hasSum_cos x).tendsto_sum_nat

/-- The alternating sine partial sums bound sine throughout `[0, π]`. -/
theorem sin_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π) (k : ℕ) :
    trigSum x 1 (2 * k + 2) ≤ sin x ∧ sin x ≤ trigSum x 1 (2 * k + 1) := by
  apply alternating_tail_bounds (trigTerm_antitone hx hx' 1)
  simpa only [trigTerm, mul_div_assoc] using (hasSum_sin x).tendsto_sum_nat

private def atanTerm (x : ℝ) (i : ℕ) : ℝ := x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

private theorem atan_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (k : ℕ) :
    (∑ i ∈ range (2 * k + 2), (-1 : ℝ) ^ i * atanTerm x i) ≤ arctan x ∧
      arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * atanTerm x i := by
  apply alternating_tail_bounds
  · apply antitone_nat_of_succ_le
    intro i
    unfold atanTerm
    push_cast
    apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
    exact pow_le_pow_of_le_one hx hx'.le (by omega)
  · simpa only [atanTerm, mul_div_assoc, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
      using (hasSum_arctan (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx')).tendsto_sum_nat

/-- Rational bounds for pi from the alternating arctangent series and Machin's identity. -/
theorem machin_pi_bounds : (3141592653 : ℝ) / 10 ^ 9 < π ∧ π < 3141592654 / 10 ^ 9 := by
  have h₁ := atan_bounds (x := 1 / 5) (by norm_num) (by norm_num) 5
  have h₂ := atan_bounds (x := 1 / 5) (by norm_num) (by norm_num) 6
  have h₃ := atan_bounds (x := 1 / 239) (by norm_num) (by norm_num) 1
  have hm := four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [← one_div, ← one_div] at hm
  norm_num [atanTerm, Finset.sum_range_succ] at h₁ h₂ h₃
  constructor <;> linarith only [hm, h₁.1, h₂.2, h₃.1, h₃.2]


private theorem quadratic_pos {a b c : ℝ} (ha : 0 < a) (hdisc : 0 < 4 * a * c - b ^ 2)
    (x : ℝ) : 0 < a * x ^ 2 + b * x + c := by
  have h : 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
    nlinarith only [hdisc, sq_nonneg (2 * a * x + b)]
  exact pos_of_mul_pos_right h (by positivity)

private def rho : ℝ := 7 / 8

private def quarticShift (z G : ℝ) (i : Fin 5) : ℝ :=
  let n := 1 + rho ^ 2
  let p₀ := rho ^ 2 * z
  let p₁ := 2 * rho * z * (G - n)
  let p₂ := G ^ 2 - G * n * (1 + z) + z * (n ^ 2 + 2 * rho ^ 2)
  let p₃ := 2 * rho * (G - n * z)
  let p₄ := p₀
  ![p₀ + (2 / 5) * p₁ + (2 / 5) ^ 2 * p₂ + (2 / 5) ^ 3 * p₃ + (2 / 5) ^ 4 * p₄,
    p₁ + (4 / 5) * p₂ + (12 / 25) * p₃ + (32 / 125) * p₄,
    p₂ + (6 / 5) * p₃ + (24 / 25) * p₄,
    p₃ + (8 / 5) * p₄,
    p₄] i

/-- Strict positivity conditions for the shifted quartic. All its coefficients
and both discriminants are rational at rational arguments. -/
def QuarticCertificate (s G : ℝ) : Prop :=
  let z := s ^ 2
  let q := quarticShift z G
  let m := q 2 + q 3 * (s - 2 / 5)
  0 < q 3 ∧ 0 < q 4 ∧ 0 < m ∧ 0 < 4 * m * q 0 - (q 1) ^ 2 ∧
    0 < 16 * rho ^ 2 * z - (2 * G - (1 + rho ^ 2) * (1 + z)) ^ 2

/-- A shifted quartic certificate excludes the scalar asymmetric overlap bound. -/
theorem quartic_obstruction {s G α : ℝ} (hcert : QuarticCertificate s G) (hα : s ≤ α) :
    let z := s ^ 2
    let n := 1 + (7 / 8 : ℝ) ^ 2
    let J := 2 * (7 / 8) * α ^ 2 + (2 * G - n * (1 + z)) * α + 2 * (7 / 8) * z
    √((1 - z) * (α ^ 2 * (n - 2 * (7 / 8) * α) ^ 2 -
      z * (2 * (7 / 8) - n * α) ^ 2)) < J := by
  let z := s ^ 2
  let n := 1 + rho ^ 2
  let J := 2 * rho * α ^ 2 + (2 * G - n * (1 + z)) * α + 2 * rho * z
  let D := (1 - z) * (α ^ 2 * (n - 2 * rho * α) ^ 2 - z * (2 * rho - n * α) ^ 2)
  change √D < J
  rcases hcert with ⟨h₃, h₄, hm, hdisc, hJdisc⟩
  have hJ : 0 < J := quadratic_pos (by norm_num [rho] : 0 < 2 * rho)
    (by linarith only [hJdisc]) α
  let q := quarticShift z G
  let y := α - 2 / 5
  let m := q 2 + q 3 * (s - 2 / 5)
  have hp : 0 < m * y ^ 2 + q 1 * y + q 0 := quadratic_pos hm hdisc y
  have h₃' : 0 ≤ q 3 * (α - s) * y ^ 2 :=
    mul_nonneg (mul_nonneg h₃.le (sub_nonneg.mpr hα)) (sq_nonneg _)
  have h₄' : 0 ≤ q 4 * y ^ 4 := mul_nonneg h₄.le (by positivity)
  have he : J ^ 2 - D = 4 * (m * y ^ 2 + q 1 * y + q 0 + q 3 * (α - s) * y ^ 2 +
      q 4 * y ^ 4) := by
    dsimp [J, D, m, y, q, n, quarticShift]
    ring
  exact (sqrt_lt' hJ).mpr (by linarith only [he, hp, h₃', h₄'])

private theorem grid_cover {n : ℕ} (hn : 0 < n) (edge : Fin (n + 1) → ℝ) {δ : ℝ}
    (hlo : edge 0 ≤ δ) (hhi : δ ≤ edge (Fin.last n)) :
    ∃ i : Fin n, edge i.castSucc ≤ δ ∧ δ ≤ edge i.succ := by
  classical
  let upper (i : ℕ) := ∃ hi : i < n, δ ≤ edge (Fin.succ (⟨i, hi⟩ : Fin n))
  have hlast : n - 1 < n := by omega
  have hsome : ∃ i, upper i := ⟨n - 1, hlast, by
    have he : Fin.succ (⟨n - 1, hlast⟩ : Fin n) = Fin.last n := by
      apply Fin.ext
      simp
      omega
    rwa [he]⟩
  obtain ⟨hi, hi'⟩ := Nat.find_spec hsome
  refine ⟨⟨Nat.find hsome, hi⟩, ?_, hi'⟩
  by_cases hzero : Nat.find hsome = 0
  · have he : (⟨Nat.find hsome, hi⟩ : Fin n).castSucc = 0 := Fin.ext hzero
    rwa [he]
  · by_contra! hbad
    have hlt : Nat.find hsome - 1 < n := by omega
    apply Nat.find_min hsome (show Nat.find hsome - 1 < Nat.find hsome by omega)
    refine ⟨hlt, ?_⟩
    have he : Fin.succ (⟨Nat.find hsome - 1, hlt⟩ : Fin n) =
        Fin.castSucc (⟨Nat.find hsome, hi⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    exact he.symm ▸ hbad.le


private structure HolonomyCell where
  cosine : ℝ
  parameter : ℝ
  cap : ℝ
  angleCosine : ℝ
  angleSine : ℝ
  capSine : ℝ
  overlap : ℝ
  gapSquare : ℝ

private def holonomyGrid : Fin 23 → ℝ := ![4/5, 5737196327/6944000000, 2959596327/3472000000, 2404076327/2777600000, 6101188981/6944000000, 24586752251/27776000000, 1769196327/1984000000, 49719493483/55552000000, 4990148981/5555200000, 99984975947/111104000000, 1615596327/1792000000, 1604127527/1777664000, 14335566943/15872000000, 401577870731/444416000000, 200879933529/222208000000, 803701730443/888832000000, 80388372677/88883200000, 1607949449867/1777664000000, 114866531871/126976000000, 51881078791/57344000000, 3216808881369/3555328000000, 183822850259/203161600000, 1570796327/1736000000]

private def holonomyCell : Fin 22 → HolonomyCell := ![
  ⟨169417073/250000000, 216660299/1000000000, 436069541/1000000000, -467241429/500000000, 5562627/15625000, 224978243/250000000, -43561589/500000000, 568366827/1000000000⟩,
  ⟨329082199/500000000, 111362911/500000000, 78401499/200000000, -962967851/1000000000, 269616239/1000000000, 114995253/125000000, -64726957/500000000, 119022877/200000000⟩,
  ⟨81030259/125000000, 112868963/500000000, 369040233/1000000000, -983484331/1000000000, 180993289/1000000000, 929413421/1000000000, -97363847/500000000, 670153119/1000000000⟩,
  ⟨79776053/125000000, 228736183/1000000000, 345422309/1000000000, -198139741/200000000, 68036891/500000000, 18768947/20000000, -107255677/500000000, 682120487/1000000000⟩,
  ⟨633150393/1000000000, 2302301/10000000, 333362713/1000000000, -995862523/1000000000, 22718157/250000000, 471399327/500000000, -246308841/1000000000, 180060459/250000000⟩,
  ⟨628065179/1000000000, 46344107/200000000, 321132301/1000000000, -498835983/500000000, 68195653/1000000000, 947034343/1000000000, -63950267/250000000, 725718469/1000000000⟩,
  ⟨625512447/1000000000, 232464443/1000000000, 39369019/125000000, -199793019/200000000, 9096677/200000000, 949107551/1000000000, -135728791/500000000, 372417149/500000000⟩,
  ⟨622953001/1000000000, 116603739/500000000, 77182051/250000000, -499708911/500000000, 34117689/1000000000, 475575151/500000000, -276097419/1000000000, 186856593/250000000⟩,
  ⟨621670769/1000000000, 58394667/250000000, 38199961/125000000, -24993531/25000000, 22747579/1000000000, 952160087/1000000000, -141930637/500000000, 75698593/100000000⟩,
  ⟨620386869/1000000000, 233949639/1000000000, 302460083/1000000000, -249963611/250000000, 1066333/62500000, 953162053/1000000000, -286153847/1000000000, 758242979/1000000000⟩,
  ⟨309872147/500000000, 117067521/500000000, 300886111/1000000000, -249983827/250000000, 454981/40000000, 953660081/1000000000, -58003843/200000000, 381510827/500000000⟩,
  ⟨77387663/125000000, 234320391/1000000000, 299309343/1000000000, -99996361/100000000, 4265487/500000000, 954156129/1000000000, -29115857/100000000, 76364013/100000000⟩,
  ⟨618779653/1000000000, 46882609/200000000, 29851991/100000000, -499991913/500000000, 1137471/200000000, 59650213/62500000, -5861741/20000000, 766028991/1000000000⟩,
  ⟨309228949/500000000, 46901137/200000000, 14886489/50000000, -499995451/500000000, 2132763/500000000, 954650187/1000000000, -146827493/500000000, 766335683/1000000000⟩,
  ⟨309148491/500000000, 29319/125000, 297334451/1000000000, -249998989/250000000, 2843689/1000000000, 954773389/1000000000, -294618169/1000000000, 767529973/1000000000⟩,
  ⟨15453401/25000000, 234598311/1000000000, 37117369/125000000, -39999909/40000000, 66649/31250000, 190979293/200000000, -294901703/1000000000, 767682683/1000000000⟩,
  ⟨618055559/1000000000, 117310733/500000000, 29674113/100000000, -999998989/1000000000, 710923/500000000, 954957959/1000000000, -147691513/500000000, 96034973/125000000⟩,
  ⟨19311721/31250000, 234644619/1000000000, 148271637/500000000, -999999431/1000000000, 213277/200000000, 955019417/1000000000, -147762343/500000000, 384177991/500000000⟩,
  ⟨308947289/500000000, 58666943/250000000, 148172683/500000000, -999999747/1000000000, 710923/1000000000, 955080847/1000000000, -147833151/500000000, 96054013/125000000⟩,
  ⟨617854329/1000000000, 58669837/250000000, 148123199/500000000, -15624999/15625000, 177731/500000000, 19102231/20000000, -295906873/1000000000, 384365309/500000000⟩,
  ⟨154458551/250000000, 14667821/62500000, 296196909/1000000000, -62499999/62500000, 177731/1000000000, 477563449/500000000, -74006787/250000000, 768879879/1000000000⟩,
  ⟨308907039/500000000, 58672731/250000000, 296147417/1000000000, -249999999/250000000, 17773/200000000, 191028449/200000000, -296062537/1000000000, 96112361/125000000⟩]

private def sharpCoefficient : ℝ := 434 / 125

private def ValidHolonomyCell (l u : ℝ) (b : HolonomyCell) : Prop :=
  0 < u ∧ u < 1 ∧ (3141592654 : ℝ) / 2 / 10 ^ 9 < sharpCoefficient * l ∧
    sharpCoefficient * l < 3141592653 / 10 ^ 9 ∧
    9 / 16 < b.cosine ∧ b.cosine ≤ trigSum u 0 14 ∧
    0 < b.parameter ∧ b.parameter ≤ 1 / 4 ∧ 0 ≤ 4 * b.parameter ^ 2 + 4 * b.parameter - 1 ∧
    1 - b.cosine ≤ 6 * b.parameter ^ 2 + 4 * b.parameter ^ 3 ∧
    0 < 1 - 3 * b.parameter - 3 * b.parameter ^ 2 ∧
    1 / 4 < b.cap ∧ b.cap < 1 ∧
    b.cap ^ 2 * (1 - 2 * b.parameter - 2 * b.parameter ^ 2) ≤
      (1 + 2 * b.parameter) ^ 2 * (1 - 3 * b.parameter - 3 * b.parameter ^ 2) ^ 2 ∧
    trigSum (sharpCoefficient * l) 0 13 ≤ b.angleCosine ∧ b.angleCosine < 0 ∧
    trigSum (sharpCoefficient * l) 1 13 ≤ b.angleSine ∧ 0 ≤ b.angleSine ∧
    0 ≤ b.capSine ∧ 1 - b.cap ^ 2 ≤ b.capSine ^ 2 ∧
    b.angleCosine * b.cap + b.angleSine * b.capSine ≤ b.overlap ∧
    b.overlap < 0 ∧ b.cosine - b.overlap > 1 / 2 ∧
    0 < b.gapSquare ∧ b.gapSquare ≤ (b.cosine - rho * b.overlap) ^ 2 ∧
    QuarticCertificate b.cap b.gapSquare

set_option maxHeartbeats 4000000 in
private theorem holonomyGrid_valid (i : Fin 22) :
    ValidHolonomyCell (holonomyGrid i.castSucc) (holonomyGrid i.succ) (holonomyCell i) := by
  fin_cases i <;>
    norm_num [ValidHolonomyCell, holonomyGrid, holonomyCell, sharpCoefficient, trigSum,
      trigTerm, Finset.sum_range_succ, Nat.factorial_succ, QuarticCertificate, quarticShift, rho]

/-- The twenty-two rational cells cover the range where the asymmetric
holonomy estimate applies. -/
theorem exists_holonomy_cell {δ : ℝ} (hlo : 4 / 5 ≤ δ) (hhi : (434 / 125) * δ ≤ π) :
    ∃ l u, ∃ b : HolonomyCell, l ≤ δ ∧ δ ≤ u ∧ ValidHolonomyCell l u b := by
  have hu : δ ≤ holonomyGrid (Fin.last 22) := by
    have h := machin_pi_bounds.2
    have he : holonomyGrid (Fin.last 22) = (1570796327 : ℝ) / 1736000000 := by
      rfl
    rw [he]
    linarith only [h, hhi]
  obtain ⟨i, hi, hi'⟩ := grid_cover (by decide) holonomyGrid (by exact hlo) hu
  exact ⟨_, _, holonomyCell i, hi, hi', holonomyGrid_valid i⟩


private structure CapCell where
  cosine : ℝ
  angleCosine : ℝ
  sine : ℝ
  lowerCap : ℝ
  upperCapSine : ℝ

private def capGrid (i : Fin 16) : ℝ := 1 / 2 + (i.val : ℝ) / 50

private def capCell : Fin 15 → CapCell := ![
  ⟨867819179/1000000000, 35368601/500000000, 248440069/500000000, 158702891/200000000, 304275701/500000000⟩,
  ⟨857708681/1000000000, 5398059/500000000, 64266999/125000000, 31074009/40000000, 31484271/50000000⟩,
  ⟨847255111/1000000000, -49183821/1000000000, 265593099/500000000, 6075587/8000000, 162641893/250000000⟩,
  ⟨836462649/1000000000, -851459/7812500, 548023937/1000000000, 148257161/200000000, 167797377/250000000⟩,
  ⟨412667807/500000000, -168397447/1000000000, 282321237/500000000, 722335319/1000000000, 10805359/15625000⟩,
  ⟨101734807/125000000, -113601047/500000000, 581035161/1000000000, 351282369/500000000, 142323967/200000000⟩,
  ⟨802095757/1000000000, -285189059/1000000000, 298597721/500000000, 681935777/1000000000, 91426507/125000000⟩,
  ⟨789992231/1000000000, -342149651/1000000000, 153279213/250000000, 132080519/200000000, 750911721/1000000000⟩,
  ⟨388786359/500000000, -397878873/1000000000, 25151721/40000000, 318954933/500000000, 770111033/1000000000⟩,
  ⟨764842187/1000000000, -226088081/500000000, 80527211/125000000, 614390231/1000000000, 789002309/1000000000⟩,
  ⟨751805729/1000000000, -63105763/125000000, 20605771/31250000, 589760783/1000000000, 201894499/250000000⟩,
  ⟨369234279/500000000, -277849573/500000000, 84285989/125000000, 281959091/500000000, 825830663/1000000000⟩,
  ⟨72483601/100000000, -604552271/1000000000, 344460723/500000000, 1048304/1953125, 52734563/62500000⟩,
  ⟨355456769/500000000, -32561483/50000000, 35163971/50000000, 101606513/200000000, 430668931/500000000⟩,
  ⟨696706709/1000000000, -347781663/500000000, 717356091/1000000000, 477598531/1000000000, 439289097/500000000⟩]

def capSquare (c : ℝ) : ℝ := (3 * c ^ 2 - 1) / 2

private def ValidCapCell (l u : ℝ) (b : CapCell) : Prop :=
  0 ≤ l ∧ u ≤ 4 / 5 ∧
    0 ≤ b.cosine ∧ b.cosine ≤ trigSum u 0 14 ∧
    trigSum (3 * l) 0 13 ≤ b.angleCosine ∧
    0 ≤ b.sine ∧ trigSum u 1 13 ≤ b.sine ∧
    0 ≤ b.lowerCap ∧ b.lowerCap ^ 2 ≤ capSquare b.cosine ∧
    0 ≤ b.upperCapSine ∧ 1 - capSquare b.cosine ≤ b.upperCapSine ^ 2 ∧
    (if b.angleCosine ≤ 0 then b.lowerCap * b.angleCosine else b.angleCosine) <
      b.lowerCap * b.cosine - b.upperCapSine * b.sine

set_option maxHeartbeats 3000000 in
private theorem capGrid_valid (i : Fin 15) :
    ValidCapCell (capGrid i.castSucc) (capGrid i.succ) (capCell i) := by
  fin_cases i <;>
    norm_num [ValidCapCell, capGrid, capCell, capSquare, trigSum, trigTerm,
      Finset.sum_range_succ, Nat.factorial_succ]

/-- In the middle defect range, a cap-center projection at angle at least
`3δ` violates the fifteen-cell cosine bound. -/
theorem cap_center_cosine_lt {δ a : ℝ} (hlo : 1 / 2 ≤ δ) (hhi : δ ≤ 4 / 5)
    (ha : √(capSquare (cos δ)) ≤ a) (ha' : a ≤ 1) :
    a * cos (3 * δ) < √(capSquare (cos δ)) * cos δ -
      √(1 - capSquare (cos δ)) * sin δ := by
  obtain ⟨i, hl, hu⟩ := grid_cover (n := 15) (by decide) capGrid (by norm_num [capGrid]; exact hlo)
    (by norm_num [capGrid, Fin.last]; exact hhi)
  let b := capCell i
  have hvalid := capGrid_valid i
  change ValidCapCell (capGrid i.castSucc) (capGrid i.succ) b at hvalid
  rcases hvalid with ⟨hl₀, hu₁, hc₀, hc, hC, hS₀, hS, hA₀, hA, hB₀, hB, hb⟩
  have huπ : capGrid i.succ ≤ π / 2 := by linarith [pi_gt_three]
  have hc' : b.cosine ≤ cos δ :=
    hc.trans ((cos_bounds (hl₀.trans (hl.trans hu)) (by linarith [pi_pos]) 6).1.trans
      (cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) hu))
  have hs' : sin δ ≤ b.sine :=
    (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) huπ hu).trans
      ((sin_bounds (hl₀.trans (hl.trans hu)) (by linarith [pi_pos]) 6).2.trans hS)
  have ht' : cos (3 * δ) ≤ b.angleCosine :=
    (cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three]) (by linarith)).trans
      ((cos_bounds (by linarith : 0 ≤ 3 * capGrid i.castSucc)
        (by linarith [pi_gt_three] : 3 * capGrid i.castSucc ≤ π) 6).2.trans hC)
  have hw : capSquare b.cosine ≤ capSquare (cos δ) := by
    unfold capSquare
    nlinarith only [pow_le_pow_left₀ hc₀ hc' 2]
  have hA' : b.lowerCap ≤ √(capSquare (cos δ)) := le_sqrt_of_sq_le (hA.trans hw)
  have hB' : √(1 - capSquare (cos δ)) ≤ b.upperCapSine :=
    sqrt_le_iff.mpr ⟨hB₀, (sub_le_sub_left hw 1).trans hB⟩
  have hS' : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
  have hleft : a * cos (3 * δ) ≤
      (if b.angleCosine ≤ 0 then b.lowerCap * b.angleCosine else b.angleCosine) := by
    apply (mul_le_mul_of_nonneg_left ht' ((sqrt_nonneg _).trans ha)).trans
    split_ifs with h
    · exact mul_le_mul_of_nonpos_right (hA'.trans ha) h
    · simpa using mul_le_mul_of_nonneg_right ha' (le_of_not_ge h)
  have hright : b.lowerCap * b.cosine - b.upperCapSine * b.sine ≤
      √(capSquare (cos δ)) * cos δ - √(1 - capSquare (cos δ)) * sin δ :=
    sub_le_sub (mul_le_mul hA' hc' hc₀ (sqrt_nonneg _))
      (mul_le_mul hB' hs' hS' hB₀)
  exact hleft.trans_lt (hb.trans_le hright)


/-- The four-point Jung radius is at most `27δ/20` throughout the first range. -/
theorem jung_radius_first_range {δ : ℝ} (hδ : 0 ≤ δ) (hmax : δ ≤ 4 / 5) :
    arccos (√(capSquare (cos δ))) ≤ 27 / 20 * δ := by
  let x := (27 / 20 : ℝ) * δ
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxπ : x ≤ π / 2 := by dsimp [x]; linarith [pi_gt_three]
  have hδπ : δ ≤ π := by linarith [pi_gt_three]
  have hlow := (sin_bounds hx (by linarith [pi_pos, hxπ]) 1).1
  have hhigh := (sin_bounds hδ hδπ 1).2
  norm_num [trigSum, trigTerm, Finset.sum_range_succ, Nat.factorial_succ] at hlow hhigh
  have hsinδ : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi hδ hδπ
  have hh : √(3 / 2 : ℝ) ≤ 49 / 40 :=
    sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := mul_le_mul_of_nonneg_right hh hsinδ
  let y := δ ^ 2
  have hy : y ≤ 16 / 25 := pow_le_pow_left₀ hδ hmax 2 |>.trans_eq (by norm_num)
  have hy₀ : 0 ≤ y := sq_nonneg _
  have hy₂ : y ^ 2 ≤ (16 / 25 : ℝ) ^ 2 := pow_le_pow_left₀ hy₀ hy 2
  have hy₃ : y ^ 3 ≤ (16 / 25 : ℝ) ^ 3 := pow_le_pow_left₀ hy₀ hy 3
  have hid :
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 -
        (49 / 40) * (δ - δ ^ 3 / 6 + δ ^ 5 / 120) =
      δ * ((27 / 20 - 49 / 40) - (((27 / 20) ^ 3 - 49 / 40) / 6) * y +
        (((27 / 20) ^ 5 - 49 / 40) / 120) * y ^ 2 - (27 / 20) ^ 7 / 5040 * y ^ 3) := by
    dsimp [x, y]
    ring
  have hpoly : 0 ≤ (27 / 20 - 49 / 40) - (((27 / 20) ^ 3 - 49 / 40) / 6) * y +
        (((27 / 20) ^ 5 - 49 / 40) / 120) * y ^ 2 - (27 / 20) ^ 7 / 5040 * y ^ 3 := by
    have hsec := mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ (((27 / 20 : ℝ) ^ 3 - 49 / 40) / 6) -
          (((27 / 20 : ℝ) ^ 5 - 49 / 40) / 120) * (16 / 25 + y) by
        norm_num
        linarith only [hy])
    nlinarith only [hsec, hy₃]
  have hnet : √(3 / 2 : ℝ) * sin δ ≤ sin x := by
    have hdiff := mul_nonneg hδ hpoly
    rw [← hid] at hdiff
    linarith only [hlow, hhigh, hdiff, h]
  have hsq := pow_le_pow_left₀ (mul_nonneg (sqrt_nonneg _) hsinδ) hnet 2
  rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)] at hsq
  have hc : cos x ≤ √(capSquare (cos δ)) := by
    apply le_sqrt_of_sq_le
    unfold capSquare
    nlinarith only [hsq, sin_sq_add_cos_sq δ, sin_sq_add_cos_sq x]
  have ha := arccos_le_arccos hc
  rwa [arccos_cos hx (by linarith [pi_pos])] at ha


/-- The rational cells bound the holonomy cap radius and the largest possible
real part of a candidate whose cap center is at the forbidden angle. -/
theorem exists_range_two_bounds {δ : ℝ} (hlo : 4 / 5 ≤ δ) (hhi : (434 / 125) * δ ≤ π) :
    ∃ t s k G : ℝ, 0 ≤ t ∧ t ≤ 1 / 4 ∧ 0 ≤ 4 * t ^ 2 + 4 * t - 1 ∧
      9 / 16 < cos δ ∧ 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ cos δ ∧
      1 / 4 < s ∧ s < 1 ∧
      s ≤ (1 + 2 * t) * (1 - 3 * t - 3 * t ^ 2) / √(1 - 2 * t - 2 * t ^ 2) ∧
      2 * arccos s ≤ (434 / 125) * δ ∧
      0 ≤ (434 / 125) * δ - arccos s ∧ cos ((434 / 125) * δ - arccos s) ≤ k ∧
      k < 0 ∧ 1 / 2 < cos δ - k ∧ 0 < G ∧ G ≤ (cos δ - (7 / 8) * k) ^ 2 ∧
      QuarticCertificate s G := by
  obtain ⟨l, u, b, hl, hu, hb⟩ := exists_holonomy_cell hlo hhi
  rcases hb with ⟨hu₀, hu₁, hl₁, hl₂, hc, hc', ht₀, ht₁, ht₂, ht₃, ht₄, hs₀, hs₁, hs₂,
    hC₁, hC₂, hS₁, hS₂, hT₀, hT₁, hk₀, hk₁, hk₂, hG₀, hG₁, hcert⟩
  let K := sharpCoefficient
  have hk : K * δ ≤ π := hhi
  have hl₀ : 0 ≤ K * l := by linarith only [hl₁]
  have hlπ : K * l ≤ π := by linarith only [hl₂, machin_pi_bounds.1]
  have hmid : π / 2 ≤ K * l := by linarith only [hl₁, machin_pi_bounds.2]
  have hcδ : b.cosine ≤ cos δ :=
    hc'.trans ((cos_bounds hu₀.le (by linarith [pi_gt_three]) 6).1.trans
      (cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three]) hu))
  have htSq := pow_le_pow_left₀ ht₀.le ht₁ 2
  have hd : 0 < 1 - 2 * b.parameter - 2 * b.parameter ^ 2 := by linarith
  have hcap : b.cap ≤ (1 + 2 * b.parameter) * (1 - 3 * b.parameter - 3 * b.parameter ^ 2) /
      √(1 - 2 * b.parameter - 2 * b.parameter ^ 2) := by
    rw [le_div_iff₀ (sqrt_pos.mpr hd)]
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [mul_pow, sq_sqrt hd.le, mul_pow]
    exact hs₂
  let R := arccos b.cap
  have hR₀ : 0 ≤ R := arccos_nonneg _
  have hR : R ≤ π / 2 := arccos_le_pi_div_two.mpr (by linarith)
  have hR' : R ≤ 4 / 3 := by
    have hC := (cos_bounds (x := 4 / 3) (by norm_num) (by linarith [pi_gt_three]) 1).2
    norm_num [trigSum, trigTerm, sum_range_succ, Nat.factorial_succ] at hC
    have h := arccos_le_arccos (show cos (4 / 3) ≤ b.cap by linarith only [hC, hs₀])
    rw [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at h
    exact h
  have hk0 : K * l ≤ K * δ := mul_le_mul_of_nonneg_left hl (by norm_num [K, sharpCoefficient])
  have hkt : cos (K * δ - R) ≤ b.overlap := by
    have hcos : cos (K * l) ≤ b.angleCosine := (cos_bounds hl₀ hlπ 6).2.trans hC₁
    have hsin : sin (K * l) ≤ b.angleSine := (sin_bounds hl₀ hlπ 6).2.trans hS₁
    have hsin₀ : 0 ≤ sin (K * l) := sin_nonneg_of_nonneg_of_le_pi hl₀ hlπ
    have hcosR : cos R = b.cap := cos_arccos (by linarith) hs₁.le
    have hsR : sin R = √(1 - b.cap ^ 2) := sin_arccos _
    have hT : sin R ≤ b.capSine := by rw [hsR]; exact sqrt_le_iff.mpr ⟨hT₀, hT₁⟩
    have hsinR : 0 ≤ sin R := sin_nonneg_of_nonneg_of_le_pi hR₀ (by linarith [pi_pos])
    calc
      _ ≤ cos (K * l - R) := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
      _ = cos (K * l) * b.cap + sin (K * l) * sin R := by rw [cos_sub, hcosR]
      _ ≤ b.angleCosine * b.cap + b.angleSine * b.capSine :=
        add_le_add (mul_le_mul_of_nonneg_right hcos (by linarith)) (mul_le_mul hsin hT hsinR hS₂)
      _ ≤ _ := hk₀
  refine ⟨b.parameter, b.cap, b.overlap, b.gapSquare, ht₀.le, ht₁, ht₂, hc.trans_le hcδ, ?_,
    hs₀, hs₁, hcap, ?_, ?_, hkt, hk₁, ?_, hG₀, ?_, hcert⟩
  · linarith only [ht₃, hcδ]
  · change 2 * R ≤ K * δ
    unfold K sharpCoefficient
    linarith only [hR', hlo]
  · change 0 ≤ K * δ - R
    linarith only [hR, hmid, hk0]
  · linarith only [hcδ, hk₂]
  · apply hG₁.trans
    exact pow_le_pow_left₀
      (show 0 ≤ b.cosine - rho * b.overlap by
        have h := mul_nonpos_of_nonneg_of_nonpos (by norm_num [rho] : 0 ≤ rho) hk₁.le
        linarith only [h, hc])
      (show b.cosine - rho * b.overlap ≤ cos δ - (7 / 8) * b.overlap from
        sub_le_sub_right hcδ _) 2

end Omega.Geometry.SU2ChordalIntervals
