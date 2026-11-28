/- GID: D5/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuNearRankTwoSpectralPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional near-rank-two transfer from the strict tracial baseline to unequal temperatures. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The pointwise cell, energy, logarithmic, and entropy estimates give the explicit
9 ε root-raising loss and 26 log r temperature loss. Under the stated strict tracial baseline
hypothesis hbase, the rankTwoMargin definition and these losses transfer the margin to the
unequal-temperature near-rank-two spectrum.
-/

import D5.S3.Quantum.Semigroups.WuCubicThermalBasis
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases

/-! Same-frame perturbation of Wu's cubic deficit, arXiv:2610.33686v1,
Remark 3.15, (3.54)–(3.55). The spectral data use the directed CAR jump
weights and the product Gibbs spectrum in occupation order `00,01,10,11`.
In a unitary frame `U`, the two jump arrays are the squared moduli of
the entries of `Uᴴ J U`, and the reference weights are `|U(o,i)|²`. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuNearRankTwoSpectralPerturbation

open WuCubicOperatorBridge (Occupation)
open WuCubicThermalBasis (a b a_add_b)
open WuRepeatedMiddleCubic (alpha)
open private gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

/-- The target of the lowering jump provides the first root. -/
def cell (t x y : ℝ) : ℝ := gamma t * (t * x - y) ^ 2 * (t * x + y)

def energy (t : ℝ) (w : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, cell t (v i) (v j) * w i j

def mass (v : Fin 4 → ℝ) : ℝ := ∑ i, v i ^ 3

/-- The Gibbs occupations of a mode with cubic-root ratio `t`. -/
def occupationWeight (t : ℝ) (k : Fin 2) : ℝ := if k = 0 then a t else b t

def gibbsEigenvalue (R r : ℝ) (o : Occupation) : ℝ :=
  occupationWeight r o.1 * occupationWeight R o.2

/-- `p i o` is the squared modulus of the occupation component `o` of
spectral vector `i` in the fixed complex frame. -/
def gibbsLogField (R r : ℝ) (p : Fin 4 → Occupation → ℝ) (i : Fin 4) : ℝ :=
  ∑ o, p i o * Real.log (gibbsEigenvalue R r o)

def entropy (L v : Fin 4 → ℝ) : ℝ :=
  (∑ i, (v i ^ 3 * Real.log (v i ^ 3) - v i ^ 3 * L i)) -
    mass v * Real.log (mass v)

/-- The cold energy always uses `R`. Only the spectator energy and the
product Gibbs logarithm depend on `r`. -/
def deficit (R r : ℝ) (cold spectator : Fin 4 → Fin 4 → ℝ)
    (p : Fin 4 → Occupation → ℝ) (v : Fin 4 → ℝ) : ℝ :=
  energy R cold v + energy r spectator v - alpha R * entropy (gibbsLogField R r p) v

def rankTwoMargin (R : ℝ) : ℝ :=
  if R ≤ 4 then 1 / 200 else if R ≤ 5 then 199 / 80000 else 1 / R ^ 3

private theorem gamma_eq (t : ℝ) : gamma t = (9 / 4) * a t := by
  rw [gamma, a, div_mul_div_comm, mul_one]

theorem cell_eq_normalized (t x y : ℝ) :
    cell t x y = (9 / 4) * (b t * x ^ 3 + a t * y ^ 3 -
      (a t * t ^ 2) * (x ^ 2 * y) - (a t * t) * (x * y ^ 2)) := by
  rw [cell, gamma_eq, b]
  ring

private theorem cube_le_cube {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx hxy _

/-- The pointwise loss when roots formerly equal to zero are raised to at
most `ε`, with both roots bounded by one. -/
theorem cell_two_root_loss {t ε x₀ y₀ x y : ℝ} (ht : 1 ≤ t) (hε : 0 ≤ ε)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hx₀ : x₀ = x ∨ x₀ = 0 ∧ x ≤ ε) (hy₀ : y₀ = y ∨ y₀ = 0 ∧ y ≤ ε) :
    cell t x₀ y₀ - cell t x y ≤ (9 / 4) * ε := by
  by_cases h : x₀ = x ∧ y₀ = y
  · rw [h.1, h.2, sub_self]
    positivity
  have hx₀' : 0 ≤ x₀ ∧ x₀ ≤ x := by
    rcases hx₀ with hEq | ⟨hEq, _⟩
    · exact ⟨by simpa only [hEq] using hx.1, hEq.le⟩
    · exact ⟨hEq.ge, hEq.trans_le hx.1⟩
  have hy₀' : 0 ≤ y₀ ∧ y₀ ≤ y := by
    rcases hy₀ with hEq | ⟨hEq, _⟩
    · exact ⟨by simpa only [hEq] using hy.1, hEq.le⟩
    · exact ⟨hEq.ge, hEq.trans_le hy.1⟩
  have hsmall : x ≤ ε ∨ y ≤ ε := by
    rcases hx₀ with hEq | ⟨_, hxe⟩
    · exact Or.inr (hy₀.resolve_left (fun hEq' => h ⟨hEq, hEq'⟩)).2
    · exact Or.inl hxe
  have hxy : x * y ≤ ε := by
    rcases hsmall with hxe | hye
    · exact (mul_le_of_le_one_right hx.1 hy.2).trans hxe
    · exact (mul_le_of_le_one_left hy.1 hx.2).trans hye
  have hx2 : x ^ 2 ≤ x := by nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hy2 : y ^ 2 ≤ y := by nlinarith only [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  have hm₁ := (mul_le_mul_of_nonneg_right hx2 hy.1).trans hxy
  have hm₂ := (mul_le_mul_of_nonneg_left hy2 hx.1).trans hxy
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hpoly : (t * x₀ - y₀) ^ 2 * (t * x₀ + y₀) -
      (t * x - y) ^ 2 * (t * x + y) ≤ (t ^ 2 + t) * ε := by
    nlinarith only [mul_le_mul_of_nonneg_left (cube_le_cube hx₀'.1 hx₀'.2)
        (pow_nonneg ht₀ 3), cube_le_cube hy₀'.1 hy₀'.2,
      mul_le_mul_of_nonneg_left hm₁ (sq_nonneg t), mul_le_mul_of_nonneg_left hm₂ ht₀,
      mul_nonneg (sq_nonneg t) (mul_nonneg (sq_nonneg x₀) hy₀'.1),
      mul_nonneg ht₀ (mul_nonneg hx₀'.1 (sq_nonneg y₀))]
  have ht' : t ^ 2 + t ≤ 1 + t ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg (t - 1)) (show 0 ≤ t + 1 by positivity)]
  have hden : 0 < 1 + t ^ 3 := by positivity
  have hγ : 0 ≤ gamma t := by rw [gamma]; positivity
  calc
    _ = gamma t * ((t * x₀ - y₀) ^ 2 * (t * x₀ + y₀) -
        (t * x - y) ^ 2 * (t * x + y)) := by unfold cell; ring
    _ ≤ gamma t * ((1 + t ^ 3) * ε) :=
      mul_le_mul_of_nonneg_left (hpoly.trans (mul_le_mul_of_nonneg_right ht' hε)) hγ
    _ = _ := by rw [gamma]; field_simp [hden.ne'] <;> ring

theorem energy_two_root_loss {t ε : ℝ} (ht : 1 ≤ t) (hε : 0 ≤ ε)
    {w : Fin 4 → Fin 4 → ℝ} (hw : ∀ i j, 0 ≤ w i j) (hs : ∑ i, ∑ j, w i j = 2)
    {v₀ v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1)
    (hraise : ∀ i, v₀ i = v i ∨ v₀ i = 0 ∧ v i ≤ ε) :
    energy t w v₀ - energy t w v ≤ (9 / 2) * ε := by
  calc
    _ = ∑ i, ∑ j, (cell t (v₀ i) (v₀ j) - cell t (v i) (v j)) * w i j := by
      simp only [energy, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, ((9 / 4) * ε) * w i j := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_right
        (cell_two_root_loss ht hε (hv i) (hv j) (hraise i) (hraise j)) (hw i j)
    _ = _ := by simp only [← Finset.mul_sum, hs]; ring

/-- The exact logarithmic sign when adding a mass below the least Gibbs
eigenvalue. The zero case follows from the `x log x` convention. -/
theorem added_mass_sign {s d L : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hsd : s ≤ d)
    (hL : Real.log d ≤ L) :
    s * Real.log s - s * L ≤ s * Real.log (s / d) ∧ s * Real.log (s / d) ≤ 0 := by
  rcases hs.eq_or_lt with hzero | hs'
  · simp [← hzero]
  constructor
  · rw [Real.log_div hs'.ne' hd.ne', mul_sub]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hL hs) _
  · exact mul_nonpos_of_nonneg_of_nonpos hs
      (Real.log_nonpos (div_nonneg hs hd.le) ((div_le_iff₀ hd).2 (by simpa using hsd)))

theorem entropy_le_of_raising_small_roots {ε d : ℝ} (hd : 0 < d)
    (hsmall : ε ^ 3 ≤ d) {L v₀ v : Fin 4 → ℝ} (hL : ∀ i, Real.log d ≤ L i)
    (hv : ∀ i, 0 ≤ v i) (hmass : 1 ≤ mass v₀)
    (hraise : ∀ i, v₀ i = v i ∨ v₀ i = 0 ∧ v i ≤ ε) :
    entropy L v ≤ entropy L v₀ := by
  have hmass' : mass v₀ ≤ mass v := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases hraise i with hEq | ⟨hEq, _⟩
    · rw [hEq]
    · rw [hEq, zero_pow (by decide : (3 : ℕ) ≠ 0)]
      exact pow_nonneg (hv i) _
  have hnorm : mass v₀ * Real.log (mass v₀) ≤ mass v * Real.log (mass v) :=
    mul_le_mul hmass' (Real.log_le_log (by linarith) hmass')
      (Real.log_nonneg hmass) (by linarith)
  unfold entropy
  refine sub_le_sub (Finset.sum_le_sum fun i _ => ?_) hnorm
  rcases hraise i with hEq | ⟨hEq, hsmall'⟩
  · rw [hEq]
  · have hs := added_mass_sign (pow_nonneg (hv i) 3) hd
      ((cube_le_cube (hv i) hsmall').trans hsmall) (hL i)
    simpa [hEq] using hs.1.trans hs.2

private theorem occupationWeight_bounds {t : ℝ} (ht : 1 ≤ t) (k : Fin 2) :
    0 < a t ∧ a t ≤ occupationWeight t k ∧ occupationWeight t k ≤ b t := by
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have ha : 0 < a t := by unfold a; positivity
  have hab : a t ≤ b t := by
    have hpow : 1 ≤ t ^ 3 := by simpa using cube_le_cube zero_le_one ht
    simpa [b] using mul_le_mul_of_nonneg_right hpow ha.le
  by_cases hk : k = 0
  · exact ⟨ha, by simp [occupationWeight, hk], by simpa [occupationWeight, hk] using hab⟩
  · exact ⟨ha, by simpa [occupationWeight, hk] using hab, by simp [occupationWeight, hk]⟩

theorem gibbsEigenvalue_bounds {R r : ℝ} (hR : 1 ≤ R) (hr : 1 ≤ r) (o : Occupation) :
    a r * a R ≤ gibbsEigenvalue R r o ∧ gibbsEigenvalue R r o ≤ b r * b R := by
  obtain ⟨hr₀, hr₁, hr₂⟩ := occupationWeight_bounds hr o.1
  obtain ⟨hR₀, hR₁, hR₂⟩ := occupationWeight_bounds hR o.2
  exact ⟨mul_le_mul hr₁ hR₁ hR₀.le (hr₀.le.trans hr₁),
    mul_le_mul hr₂ hR₂ (hR₀.le.trans hR₁) (hr₀.le.trans (hr₁.trans hr₂))⟩

theorem gibbsLogField_bounds {R r : ℝ} (hR : 1 ≤ R) (hr : 1 ≤ r)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    (i : Fin 4) :
    Real.log (a r * a R) ≤ gibbsLogField R r p i ∧
      gibbsLogField R r p i ≤ Real.log (b r * b R) := by
  have hlow : 0 < a r * a R :=
    mul_pos (occupationWeight_bounds hr 0).1 (occupationWeight_bounds hR 0).1
  constructor
  · calc
      _ = ∑ o, p i o * Real.log (a r * a R) := by rw [← Finset.sum_mul, hp₁ i, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left
        (Real.log_le_log hlow (gibbsEigenvalue_bounds hR hr o).1) (hp i o)
  · calc
      _ ≤ ∑ o, p i o * Real.log (b r * b R) := Finset.sum_le_sum fun o _ =>
        mul_le_mul_of_nonneg_left (Real.log_le_log (hlow.trans_le (gibbsEigenvalue_bounds hR hr o).1)
          (gibbsEigenvalue_bounds hR hr o).2) (hp i o)
      _ = _ := by rw [← Finset.sum_mul, hp₁ i, one_mul]

private theorem tracial_min_eq (R : ℝ) : a 1 * a R = 1 / (2 * (1 + R ^ 3)) := by
  rw [show a 1 = 1 / 2 by norm_num [a], a, div_mul_div_comm, one_mul]

private theorem alpha_bounds {R : ℝ} (hR : 1 < R) : 0 ≤ alpha R ∧ alpha R ≤ 3 / 4 := by
  have hR₀ : 0 < R := zero_lt_one.trans hR
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hden : 0 < 4 * (R ^ 2 + R + 1) * Real.log R := by positivity
  rw [alpha, if_neg hR.ne']
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (by nlinarith only [sq_nonneg (R - 1), hR])) hden.le
  · have hl := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos hR₀) hR₀.le
    rw [sub_mul, one_mul, inv_mul_cancel₀ hR₀.ne'] at hl
    have hbound : R ^ 2 - 1 ≤ (R ^ 2 + R + 1) * Real.log R := calc
      _ = (R - 1) * (R + 1) := by ring
      _ ≤ (Real.log R * R) * (R + 1) := mul_le_mul_of_nonneg_right hl (by positivity)
      _ = (R * (R + 1)) * Real.log R := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hlog.le
    exact (div_le_iff₀ hden).2 (by nlinarith only [hbound])

/-- At the tracial spectator, raising the two small roots costs at most
`9 ε` in the deficit. The same estimate applies to any set of replaced zeros. -/
theorem deficit_two_root_loss {R ε : ℝ} (hR : 1 < R) (hε : 0 ≤ ε)
    (hsmall : ε ^ 3 ≤ 1 / (2 * (1 + R ^ 3)))
    {cold spectator : Fin 4 → Fin 4 → ℝ}
    (hc : ∀ i j, 0 ≤ cold i j) (hcs : ∑ i, ∑ j, cold i j = 2)
    (hs : ∀ i j, 0 ≤ spectator i j) (hss : ∑ i, ∑ j, spectator i j = 2)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    {v₀ v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1) (hmass : 1 ≤ mass v₀)
    (hraise : ∀ i, v₀ i = v i ∨ v₀ i = 0 ∧ v i ≤ ε) :
    deficit R 1 cold spectator p v₀ - deficit R 1 cold spectator p v ≤ 9 * ε := by
  have hR₀ : 0 < R := zero_lt_one.trans hR
  have hL (i : Fin 4) : Real.log (1 / (2 * (1 + R ^ 3))) ≤ gibbsLogField R 1 p i := by
    rw [← tracial_min_eq]
    exact (gibbsLogField_bounds hR.le le_rfl hp hp₁ i).1
  have he := entropy_le_of_raising_small_roots (by positivity) hsmall hL
    (fun i => (hv i).1) hmass hraise
  have he' := mul_le_mul_of_nonneg_left he (alpha_bounds hR).1
  unfold deficit
  linarith only [he', energy_two_root_loss hR.le hε hc hcs hv hraise,
    energy_two_root_loss le_rfl hε hs hss hv hraise]

private theorem exp_cube (q : ℝ) : Real.exp (3 * q) = Real.exp q ^ 3 := by
  simpa only [Nat.cast_ofNat] using Real.exp_nat_mul q 3

private theorem hasDerivAt_normalized_coefficient (k : ℕ) (q : ℝ) :
    HasDerivAt (fun s : ℝ => a (Real.exp s) * Real.exp s ^ k)
      (((k : ℝ) - 3 * b (Real.exp q)) * (a (Real.exp q) * Real.exp q ^ k)) q := by
  have hExp (n : ℕ) : HasDerivAt (fun s : ℝ => Real.exp ((n : ℝ) * s))
      ((n : ℝ) * Real.exp ((n : ℝ) * q)) q := by
    rw [mul_comm (n : ℝ) (Real.exp ((n : ℝ) * q))]
    exact (hasDerivAt_const_mul (x := q) (n : ℝ)).exp
  have hden : 0 < 1 + Real.exp (3 * q) := by positivity
  have hBot : HasDerivAt (fun s : ℝ => 1 + Real.exp (3 * s)) (3 * Real.exp (3 * q)) q := by
    simpa only [Nat.cast_ofNat] using (hExp 3).const_add (1 : ℝ)
  have hfun : (fun s : ℝ => a (Real.exp s) * Real.exp s ^ k) =
      (fun s : ℝ => Real.exp ((k : ℝ) * s) / (1 + Real.exp (3 * s))) := by
    funext s
    rw [Real.exp_nat_mul, exp_cube, a, div_mul_eq_mul_div, one_mul]
  have hSlope : ((k : ℝ) - 3 * b (Real.exp q)) * (a (Real.exp q) * Real.exp q ^ k) =
      (((k : ℝ) * Real.exp ((k : ℝ) * q)) * (1 + Real.exp (3 * q)) -
        Real.exp ((k : ℝ) * q) * (3 * Real.exp (3 * q))) / (1 + Real.exp (3 * q)) ^ 2 := by
    simp only [Real.exp_nat_mul q k, exp_cube, b, a]
    have hne : 1 + Real.exp q ^ 3 ≠ 0 := by positivity
    field_simp [hne] <;> ring
  rw [hfun, hSlope]
  exact (hExp k).fun_div hBot hden.ne'

private def logCellSlope (q x y : ℝ) : ℝ :=
  let t := Real.exp q
  (9 / 4) * (3 * a t * b t * (x ^ 3 - y ^ 3) -
    ((2 - 3 * b t) * (a t * t ^ 2)) * (x ^ 2 * y) -
    ((1 - 3 * b t) * (a t * t)) * (x * y ^ 2))

private theorem hasDerivAt_cell_log (q x y : ℝ) :
    HasDerivAt (fun s : ℝ => cell (Real.exp s) x y) (logCellSlope q x y) q := by
  have hab := a_add_b (Real.exp_pos q).le
  have hb : HasDerivAt (fun s : ℝ => b (Real.exp s))
      (3 * a (Real.exp q) * b (Real.exp q)) q := by
    have hEq (s : ℝ) : a (Real.exp s) * Real.exp s ^ 3 = b (Real.exp s) := by rw [b, mul_comm]
    have hSlope : (3 - 3 * b (Real.exp q)) * b (Real.exp q) =
        3 * a (Real.exp q) * b (Real.exp q) := by
      rw [show 3 - 3 * b (Real.exp q) = 3 * a (Real.exp q) by linarith only [hab]]
    simpa only [hEq, Nat.cast_ofNat, hSlope] using hasDerivAt_normalized_coefficient 3 q
  have ha : HasDerivAt (fun s : ℝ => a (Real.exp s))
      (-(3 * a (Real.exp q) * b (Real.exp q))) q := by
    have hSlope : (0 - 3 * b (Real.exp q)) * a (Real.exp q) =
        -(3 * a (Real.exp q) * b (Real.exp q)) := by ring
    simpa only [pow_zero, mul_one, Nat.cast_zero, hSlope] using
      hasDerivAt_normalized_coefficient 0 q
  have h₁ := hasDerivAt_normalized_coefficient 1 q
  have h₂ := hasDerivAt_normalized_coefficient 2 q
  have h := ((((hb.mul_const (x ^ 3)).add (ha.mul_const (y ^ 3))).sub
    (h₂.mul_const (x ^ 2 * y))).sub (h₁.mul_const (x * y ^ 2))).const_mul (9 / 4 : ℝ)
  have hfun : (fun s : ℝ => cell (Real.exp s) x y) =
      (fun s : ℝ => (9 / 4) * (b (Real.exp s) * x ^ 3 + a (Real.exp s) * y ^ 3 -
        (a (Real.exp s) * Real.exp s ^ 2) * (x ^ 2 * y) -
        (a (Real.exp s) * Real.exp s ^ 1) * (x * y ^ 2))) := by
    funext s
    rw [pow_one, cell_eq_normalized]
  rw [hfun]
  convert h using 1 <;> simp only [logCellSlope, pow_one, Nat.cast_one, Nat.cast_ofNat] <;> ring

private theorem abs_logCellSlope_le {q x y : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |logCellSlope q x y| ≤ (9 / 4) * (15 / 4) := by
  let t := Real.exp q
  have ht : 1 ≤ t := Real.one_le_exp hq
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  obtain ⟨ha, hab, _⟩ := occupationWeight_bounds ht 1
  have hab' : a t ≤ b t := by simpa [occupationWeight] using hab
  have hsum := a_add_b ht₀
  have hb₁ : 1 / 2 ≤ b t := by linarith only [hab', hsum]
  have hb₂ : b t ≤ 1 := by linarith only [ha, hsum]
  have hb₀ : 0 ≤ b t := by linarith only [hb₁]
  have hpure : 3 * a t * b t ≤ 3 / 4 := by
    nlinarith only [sq_nonneg (a t - b t), congrArg (fun z : ℝ => z ^ 2) hsum]
  have hpure₀ : 0 ≤ 3 * a t * b t := mul_nonneg (mul_nonneg (by norm_num) ha.le) hb₀
  have hx₃ : x ^ 3 ≤ 1 := by simpa using cube_le_cube hx.1 hx.2
  have hy₃ : y ^ 3 ≤ 1 := by simpa using cube_le_cube hy.1 hy.2
  have hdiff : |x ^ 3 - y ^ 3| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hx₃, hy₃, pow_nonneg hx.1 3, pow_nonneg hy.1 3]
  have hA : |3 * a t * b t * (x ^ 3 - y ^ 3)| ≤ 3 / 4 := by
    rw [abs_mul, abs_of_nonneg hpure₀]
    exact (mul_le_of_le_one_right hpure₀ hdiff).trans hpure
  have hcoeff (k : ℕ) (hk : k ≤ 3) : a t * t ^ k ∈ Set.Icc 0 1 := by
    refine ⟨mul_nonneg ha.le (pow_nonneg ht₀ k), ?_⟩
    calc
      a t * t ^ k ≤ a t * t ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) ha.le
      _ = b t := by rw [b, mul_comm]
      _ ≤ 1 := hb₂
  have hx₂ : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 2
  have hy₂ : y ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hy.1 hy.2 2
  have hxy₁ : x ^ 2 * y ∈ Set.Icc 0 1 :=
    ⟨mul_nonneg (sq_nonneg x) hy.1, (mul_le_of_le_one_right (sq_nonneg x) hy.2).trans hx₂⟩
  have hxy₂ : x * y ^ 2 ∈ Set.Icc 0 1 :=
    ⟨mul_nonneg hx.1 (sq_nonneg y), (mul_le_of_le_one_left (sq_nonneg y) hx.2).trans hy₂⟩
  have hmixed {c u v C : ℝ} (hc : |c| ≤ C) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
      |c * u * v| ≤ C := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu.1, abs_of_nonneg hv.1]
    exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg c) hu.1) hv.2).trans
      ((mul_le_of_le_one_right (abs_nonneg c) hu.2).trans hc)
  have hB := hmixed (c := 2 - 3 * b t) (C := 1)
    (abs_le.mpr ⟨by linarith only [hb₂], by linarith only [hb₁]⟩)
    (hcoeff 2 (by decide)) hxy₁
  have hC := hmixed (c := 1 - 3 * b t) (C := 2)
    (abs_le.mpr ⟨by linarith only [hb₂], by linarith only [hb₁]⟩)
    (hcoeff 1 (by decide)) hxy₂
  simp only [pow_one] at hC
  change |(9 / 4) * (3 * a t * b t * (x ^ 3 - y ^ 3) -
    ((2 - 3 * b t) * (a t * t ^ 2)) * (x ^ 2 * y) -
    ((1 - 3 * b t) * (a t * t)) * (x * y ^ 2))| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have htriangle (u v : ℝ) : |u - v| ≤ |u| + |v| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le u 0 v
  refine (htriangle _ _).trans ?_
  linarith only [hA, hB, hC, htriangle (3 * a t * b t * (x ^ 3 - y ^ 3))
    (((2 - 3 * b t) * (a t * t ^ 2)) * (x ^ 2 * y))]

theorem cell_temperature_change {r x y : ℝ} (hr : 1 ≤ r)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |cell r x y - cell 1 x y| ≤ ((9 / 4) * (15 / 4)) * Real.log r := by
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := Real.log r) (f := fun q => cell (Real.exp q) x y)
    (f' := fun q => logCellSlope q x y)
    (C := (9 / 4) * (15 / 4))
    (fun q _ => (hasDerivAt_cell_log q x y).hasDerivWithinAt)
    (fun q hq => by simpa only [Real.norm_eq_abs] using abs_logCellSlope_le hq.1 hx hy)
    (Real.log r) (Set.right_mem_Icc.2 hlog)
  simpa only [Real.norm_eq_abs, Real.exp_log (zero_lt_one.trans_le hr), Real.exp_zero, sub_zero]
    using h

private theorem abs_sum_le_of_abs_le {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : ∀ i, |f i| ≤ g i) : |∑ i, f i| ≤ ∑ i, g i :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

theorem energy_temperature_change {r : ℝ} (hr : 1 ≤ r)
    {w : Fin 4 → Fin 4 → ℝ} (hw : ∀ i j, 0 ≤ w i j) (hs : ∑ i, ∑ j, w i j = 2)
    {v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1) :
    |energy r w v - energy 1 w v| ≤ (135 / 8) * Real.log r := by
  let C : ℝ := ((9 / 4) * (15 / 4)) * Real.log r
  calc
    _ = |∑ i, ∑ j, (cell r (v i) (v j) - cell 1 (v i) (v j)) * w i j| := by
      simp only [energy, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, C * w i j := by
      refine abs_sum_le_of_abs_le fun i => abs_sum_le_of_abs_le fun j => ?_
      rw [abs_mul, abs_of_nonneg (hw i j)]
      exact mul_le_mul_of_nonneg_right (cell_temperature_change hr (hv i) (hv j)) (hw i j)
    _ = _ := by simp only [← Finset.mul_sum, hs, C]; ring

theorem occupation_log_temperature_change {r : ℝ} (hr : 1 ≤ r) (k : Fin 2) :
    |Real.log (occupationWeight r k) - Real.log (occupationWeight 1 k)| ≤ 3 * Real.log r := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hp : 1 ≤ r ^ 3 := by simpa using cube_le_cube zero_le_one hr
  have hden : 0 < 1 + r ^ 3 := by positivity
  have hlow : Real.log 2 ≤ Real.log (1 + r ^ 3) :=
    Real.log_le_log (by norm_num) (by linarith only [hp])
  have hhigh : Real.log (1 + r ^ 3) ≤ Real.log 2 + 3 * Real.log r := calc
    _ ≤ Real.log (2 * r ^ 3) := Real.log_le_log hden (by linarith only [hp])
    _ = _ := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hr₀.ne'), Real.log_pow] <;> norm_num
  have ha (t : ℝ) : Real.log (a t) = -Real.log (1 + t ^ 3) := by
    rw [a, one_div, Real.log_inv]
  have hb {t : ℝ} (ht : 1 ≤ t) : Real.log (b t) = 3 * Real.log t - Real.log (1 + t ^ 3) := by
    rw [b, Real.log_mul (pow_ne_zero _ (zero_lt_one.trans_le ht).ne')
      (occupationWeight_bounds ht 0).1.ne', Real.log_pow, ha] <;> norm_num [sub_eq_add_neg]
  have hq := Real.log_nonneg hr
  rw [abs_le]
  by_cases hk : k = 0
  · simp only [occupationWeight, if_pos hk, ha, one_pow, one_add_one_eq_two]
    constructor <;> linarith only [hlow, hhigh, hq]
  · simp only [occupationWeight, if_neg hk, hb hr, hb (le_rfl : (1 : ℝ) ≤ 1),
      Real.log_one, one_pow, one_add_one_eq_two, mul_zero, zero_sub]
    constructor <;> linarith only [hlow, hhigh, hq]

theorem gibbsLogField_temperature_change {R r : ℝ} (hR : 1 ≤ R) (hr : 1 ≤ r)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    (i : Fin 4) : |gibbsLogField R r p i - gibbsLogField R 1 p i| ≤ 3 * Real.log r := by
  have hentry {t : ℝ} (ht : 1 ≤ t) (k : Fin 2) : 0 < occupationWeight t k :=
    (occupationWeight_bounds ht k).1.trans_le (occupationWeight_bounds ht k).2.1
  have hlog {t : ℝ} (ht : 1 ≤ t) (o : Occupation) :
      Real.log (gibbsEigenvalue R t o) =
        Real.log (occupationWeight t o.1) + Real.log (occupationWeight R o.2) :=
    Real.log_mul (hentry ht o.1).ne' (hentry hR o.2).ne'
  calc
    _ = |∑ o, p i o * (Real.log (occupationWeight r o.1) - Real.log (occupationWeight 1 o.1))| := by
      simp only [gibbsLogField, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro o _
      rw [hlog hr, hlog le_rfl]
      ring
    _ ≤ ∑ o, p i o * (3 * Real.log r) := by
      refine abs_sum_le_of_abs_le fun o => ?_
      rw [abs_mul, abs_of_nonneg (hp i o)]
      exact mul_le_mul_of_nonneg_left (occupation_log_temperature_change hr o.1) (hp i o)
    _ = _ := by rw [← Finset.sum_mul, hp₁ i, one_mul]

theorem entropy_temperature_change {R r : ℝ} (hR : 1 ≤ R) (hr : 1 ≤ r)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    {v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1) :
    |entropy (gibbsLogField R r p) v - entropy (gibbsLogField R 1 p) v| ≤ 12 * Real.log r := by
  have hmass : mass v ≤ 4 := calc
    _ ≤ ∑ _ : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
      simpa using cube_le_cube (hv i).1 (hv i).2
    _ = _ := by simp
  calc
    _ = |∑ i, v i ^ 3 * (gibbsLogField R 1 p i - gibbsLogField R r p i)| := by
      unfold entropy
      rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, v i ^ 3 * (3 * Real.log r) := by
      refine abs_sum_le_of_abs_le fun i => ?_
      rw [abs_mul, abs_of_nonneg (pow_nonneg (hv i).1 3), abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (gibbsLogField_temperature_change hR hr hp hp₁ i)
        (pow_nonneg (hv i).1 3)
    _ = mass v * (3 * Real.log r) := by rw [mass, Finset.sum_mul]
    _ ≤ 4 * (3 * Real.log r) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg (by norm_num) (Real.log_nonneg hr))
    _ = _ := by ring

/-- Temperature variation at fixed spectral roots and fixed frame. -/
theorem deficit_temperature_change {R r : ℝ} (hR : 1 < R) (hr : 1 ≤ r)
    {cold spectator : Fin 4 → Fin 4 → ℝ}
    (hs : ∀ i j, 0 ≤ spectator i j) (hss : ∑ i, ∑ j, spectator i j = 2)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    {v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1) :
    |deficit R r cold spectator p v - deficit R 1 cold spectator p v| ≤ 26 * Real.log r := by
  have he := energy_temperature_change hr hs hss hv
  have hS := entropy_temperature_change hR.le hr hp hp₁ hv
  obtain ⟨ha₀, ha₁⟩ := alpha_bounds hR
  have hlog := Real.log_nonneg hr
  calc
    _ = |(energy r spectator v - energy 1 spectator v) -
        alpha R * (entropy (gibbsLogField R r p) v - entropy (gibbsLogField R 1 p) v)| := by
      unfold deficit
      congr 1
      ring
    _ ≤ |energy r spectator v - energy 1 spectator v| +
        |alpha R * (entropy (gibbsLogField R r p) v - entropy (gibbsLogField R 1 p) v)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (energy r spectator v - energy 1 spectator v) 0
          (alpha R * (entropy (gibbsLogField R r p) v - entropy (gibbsLogField R 1 p) v))
    _ ≤ 26 * Real.log r := by
      rw [abs_mul, abs_of_nonneg ha₀]
      have hRef := mul_le_mul ha₁ hS (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [he, hRef, hlog]

theorem near_rank_two_deficit_lower {R r ε : ℝ} (hR : 1 < R) (hr : 1 ≤ r) (hε : 0 ≤ ε)
    (hsmall : ε ^ 3 ≤ 1 / (2 * (1 + R ^ 3)))
    {cold spectator : Fin 4 → Fin 4 → ℝ}
    (hc : ∀ i j, 0 ≤ cold i j) (hcs : ∑ i, ∑ j, cold i j = 2)
    (hs : ∀ i j, 0 ≤ spectator i j) (hss : ∑ i, ∑ j, spectator i j = 2)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    {v₀ v : Fin 4 → ℝ} (hv : ∀ i, v i ∈ Set.Icc 0 1) (hmass : 1 ≤ mass v₀)
    (hraise : ∀ i, v₀ i = v i ∨ v₀ i = 0 ∧ v i ≤ ε) :
    deficit R 1 cold spectator p v₀ - 9 * ε - 26 * Real.log r ≤
      deficit R r cold spectator p v := by
  have hroots := deficit_two_root_loss hR hε hsmall hc hcs hs hss hp hp₁ hv hmass hraise
  have htemp := (abs_le.mp (deficit_temperature_change (cold := cold) hR hr hs hss hp hp₁ hv)).1
  linarith only [hroots, htemp]

private theorem rankTwoMargin_pos {R : ℝ} (hR : 1 < R) : 0 < rankTwoMargin R := by
  have hR₀ : 0 < R := zero_lt_one.trans hR
  unfold rankTwoMargin
  split
  · norm_num
  · split
    · norm_num
    · positivity

/-- The normalized near-rank-two unequal-temperature theorem. `hbase` is
the strict tracial rank-two estimate in the same frame, with its mass factor. -/
theorem near_rank_two_unequal_temperature {R r ε u v m : ℝ}
    (hR : 1 < R) (hr : r ∈ Set.Icc 1 R) (hu : 0 ≤ u) (huv : u ≤ v) (hvm : v ≤ m) (hm : m ≤ 1)
    (hve : v ≤ ε)
    (hε : ε ≤ min (rankTwoMargin R / 36) ((2 * (1 + R ^ 3)) ^ (-(1 / 3) : ℝ)))
    (hlog : Real.log r ≤ rankTwoMargin R / 104)
    {cold spectator : Fin 4 → Fin 4 → ℝ}
    (hc : ∀ i j, 0 ≤ cold i j) (hcs : ∑ i, ∑ j, cold i j = 2)
    (hs : ∀ i j, 0 ≤ spectator i j) (hss : ∑ i, ∑ j, spectator i j = 2)
    {p : Fin 4 → Occupation → ℝ} (hp : ∀ i o, 0 ≤ p i o) (hp₁ : ∀ i, ∑ o, p i o = 1)
    (hbase : rankTwoMargin R * mass ![0, 0, m, 1] < deficit R 1 cold spectator p ![0, 0, m, 1]) :
    rankTwoMargin R / 2 < deficit R r cold spectator p ![u, v, m, 1] := by
  have hv₀ : 0 ≤ v := hu.trans huv
  have hm₀ : 0 ≤ m := hv₀.trans hvm
  have hε₀ : 0 ≤ ε := hv₀.trans hve
  have hδ : ε ≤ rankTwoMargin R / 36 := (le_min_iff.mp hε).1
  have hR₀ : 0 < R := zero_lt_one.trans hR
  have hden : 0 < 2 * (1 + R ^ 3) := by positivity
  have hcut : ((2 * (1 + R ^ 3)) ^ (-(1 / 3) : ℝ)) ^ 3 = 1 / (2 * (1 + R ^ 3)) := by
    rw [← Real.rpow_mul_natCast hden.le,
      show (-(1 / 3) : ℝ) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, one_div]
  have hsmall : ε ^ 3 ≤ 1 / (2 * (1 + R ^ 3)) :=
    (cube_le_cube hε₀ (le_min_iff.mp hε).2).trans_eq hcut
  have hroots : ∀ i : Fin 4, (![u, v, m, 1] : Fin 4 → ℝ) i ∈ Set.Icc 0 1 := by
    intro i
    fin_cases i
    · exact ⟨hu, huv.trans (hvm.trans hm)⟩
    · exact ⟨hv₀, hvm.trans hm⟩
    · exact ⟨hm₀, hm⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have hmass : 1 ≤ mass ![0, 0, m, 1] := by
    norm_num [mass, Fin.sum_univ_four] <;> linarith only [pow_nonneg hm₀ 3]
  have hraise : ∀ i : Fin 4, (![0, 0, m, 1] : Fin 4 → ℝ) i = ![u, v, m, 1] i ∨
      ![0, 0, m, 1] i = 0 ∧ ![u, v, m, 1] i ≤ ε := by
    intro i
    fin_cases i
    · exact Or.inr ⟨rfl, huv.trans hve⟩
    · exact Or.inr ⟨rfl, hve⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hpert := near_rank_two_deficit_lower hR hr.1 hε₀ hsmall hc hcs hs hss hp hp₁ hroots hmass hraise
  have hbase' : rankTwoMargin R < deficit R 1 cold spectator p ![0, 0, m, 1] := by
    exact (le_mul_of_one_le_right (rankTwoMargin_pos hR).le hmass).trans_lt hbase
  linarith only [hpert, hbase', hδ, hlog]

private theorem cell_scale (t h x y : ℝ) : cell t (h * x) (h * y) = h ^ 3 * cell t x y := by
  unfold cell
  ring

private theorem energy_scale (t h : ℝ) (w : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    energy t w (fun i => h * v i) = h ^ 3 * energy t w v := by
  simp only [energy, cell_scale, mul_assoc, ← Finset.mul_sum]

private theorem mul_log_mul (c z : ℝ) (hc : c ≠ 0) :
    (c * z) * Real.log (c * z) = c * (z * Real.log z) + (c * Real.log c) * z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [Real.log_mul hc hz]
  ring

private theorem entropy_scale {h : ℝ} (hh : 0 < h) (L v : Fin 4 → ℝ) :
    entropy L (fun i => h * v i) = h ^ 3 * entropy L v := by
  have hh₃ : h ^ 3 ≠ 0 := pow_ne_zero _ hh.ne'
  have hmass : mass (fun i => h * v i) = h ^ 3 * mass v := by
    simp only [mass, mul_pow, Finset.mul_sum]
  have hterm (i : Fin 4) :
      (h * v i) ^ 3 * Real.log ((h * v i) ^ 3) - (h * v i) ^ 3 * L i =
        h ^ 3 * (v i ^ 3 * Real.log (v i ^ 3) - v i ^ 3 * L i) +
          (h ^ 3 * Real.log (h ^ 3)) * v i ^ 3 := by
    rw [mul_pow, mul_log_mul _ _ hh₃]
    ring
  have hsum : (∑ i, ((h * v i) ^ 3 * Real.log ((h * v i) ^ 3) - (h * v i) ^ 3 * L i)) =
      h ^ 3 * (∑ i, (v i ^ 3 * Real.log (v i ^ 3) - v i ^ 3 * L i)) +
        (h ^ 3 * Real.log (h ^ 3)) * mass v := by
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, mass]
  unfold entropy
  rw [hsum, hmass, mul_log_mul _ _ hh₃]
  ring

/-- Restores any positive largest root from the normalized theorem. -/
theorem deficit_scale {h : ℝ} (hh : 0 < h) (R r : ℝ) (cold spectator : Fin 4 → Fin 4 → ℝ)
    (p : Fin 4 → Occupation → ℝ) (v : Fin 4 → ℝ) :
    deficit R r cold spectator p (fun i => h * v i) = h ^ 3 * deficit R r cold spectator p v := by
  simp only [deficit, energy_scale, entropy_scale hh]
  ring

end D5.S3.Quantum.Semigroups.WuNearRankTwoSpectralPerturbation
