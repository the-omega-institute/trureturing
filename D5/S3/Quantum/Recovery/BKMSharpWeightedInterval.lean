/- GID: D5/S3/Quantum/Recovery/BKMSharpWeightedInterval
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMSharpWeightedInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp weighted interval estimates for the qutrit BKM step profiles. -/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
The weighted step-profile estimate for qutrit BKM resolvent rows. The first interval of the scalar
mesh has level zero. In the band estimate the first two jumps are prescribed.
The mixed term is kept with its band-wide coefficient for summation over rows.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace D5.S3.Quantum.Recovery.BKMSharpWeightedInterval

/-- The mass of `dx / x²` between positive endpoints. -/
def intervalWeight (a b : ℝ) : ℝ := a⁻¹ - b⁻¹

/-- The squared length divided by the interval weight when `0 < a < b`.
This expression also extends to a collapsed interval or to `a = 0`. -/
def intervalCoefficient (a b : ℝ) : ℝ := a * b * (b - a)

theorem intervalWeight_eq_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    intervalWeight a b = ∫ x in a..b, (x ^ 2)⁻¹ := by
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1
  have h := integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
    (Or.inr ⟨by decide, hzero⟩)
  have hpow (x : ℝ) : x ^ (-2 : ℤ) = (x ^ (2 : ℕ))⁻¹ := zpow_negSucc x 1
  simp only [hpow, show (-2 : ℤ) + 1 = -1 by decide, zpow_neg_one] at h
  rw [intervalWeight, h]
  norm_num
  ring

private theorem intervalWeight_eq_length_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    intervalWeight a b = (b - a) / (a * b) := by
  unfold intervalWeight
  field_simp [ha.ne', hb.ne']

private theorem intervalWeight_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ intervalWeight a b := by
  rw [intervalWeight_eq_length_div ha (ha.trans_le hab)]
  exact div_nonneg (sub_nonneg.mpr hab) (mul_nonneg ha.le (ha.trans_le hab).le)

private theorem intervalCoefficient_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ intervalCoefficient a b :=
  mul_nonneg (mul_nonneg ha (ha.trans hab)) (sub_nonneg.mpr hab)

private theorem intervalCoefficient_mono_right {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    intervalCoefficient a b ≤ intervalCoefficient a c := by
  unfold intervalCoefficient
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hbc ha) (sub_le_sub_right hbc a)
    (sub_nonneg.mpr hab) (mul_nonneg ha (ha.trans (hab.trans hbc)))

private theorem intervalCoefficient_mul_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    intervalCoefficient a b * intervalWeight a b = (b - a) ^ 2 := by
  rw [intervalWeight_eq_length_div ha hb, intervalCoefficient]
  field_simp [ha.ne', hb.ne']

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stepIntegral (a b : ℝ) (u : E) : E := (b - a) • u

def stepEnergy (a b : ℝ) (u : E) : ℝ := intervalWeight a b * ‖u‖ ^ 2

theorem step_integrals [CompleteSpace E] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (u : E) :
    stepIntegral a b u = (∫ _ in a..b, u) ∧
    stepEnergy a b u = ∫ x in a..b, (x ^ 2)⁻¹ * ‖u‖ ^ 2 := by
  constructor
  · rw [stepIntegral, intervalIntegral.integral_const]
  · rw [stepEnergy, intervalIntegral.integral_mul_const, intervalWeight_eq_integral ha hab]

private theorem norm_real_smul_sq (r : ℝ) (u : E) :
    ‖r • u‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

omit [NormedSpace ℝ E] in
private theorem stepEnergy_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (u : E) :
    0 ≤ stepEnergy a b u :=
  mul_nonneg (intervalWeight_nonneg ha hab) (sq_nonneg _)

private theorem step_norm_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : E) :
    ‖stepIntegral a b u‖ ^ 2 = intervalCoefficient a b * stepEnergy a b u := by
  rw [stepIntegral, norm_real_smul_sq, stepEnergy, ← mul_assoc,
    intervalCoefficient_mul_weight ha hb]

end Step

/-- The sum of interval coefficients for the mesh `0, x, x+y, x+y+z`. -/
def meshCoefficient (x y z : ℝ) : ℝ :=
  intervalCoefficient x (x + y) + intervalCoefficient (x + y) (x + y + z)

theorem meshCoefficient_eq_cubes (x y z : ℝ) :
    meshCoefficient x y z = ((x + y + z) ^ 3 - x ^ 3 - y ^ 3 - z ^ 3) / 3 := by
  unfold meshCoefficient intervalCoefficient
  ring

/-- The deficit from equal spacing, in nonnegative terms for nonnegative lengths. -/
theorem three_interval_mesh_deficit (x y z : ℝ) :
    let m := (x + y + z) / 3
    (8 / 27 : ℝ) * (x + y + z) ^ 3 - meshCoefficient x y z =
      ((x - m) ^ 2 * (x + 2 * m) +
       (y - m) ^ 2 * (y + 2 * m) +
       (z - m) ^ 2 * (z + 2 * m)) / 3 := by
  dsimp only
  rw [meshCoefficient_eq_cubes]
  ring

theorem three_interval_mesh_sharp {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hL : 0 < x + y + z) :
    meshCoefficient x y z ≤ (8 / 27 : ℝ) * (x + y + z) ^ 3 ∧
    (meshCoefficient x y z = (8 / 27 : ℝ) * (x + y + z) ^ 3 ↔ x = y ∧ y = z) := by
  let m := (x + y + z) / 3
  have hm : 0 < m := div_pos hL (by norm_num)
  have hx' : 0 < x + 2 * m := by linarith
  have hy' : 0 < y + 2 * m := by linarith
  have hz' : 0 < z + 2 * m := by linarith
  have hX := mul_nonneg (sq_nonneg (x - m)) hx'.le
  have hY := mul_nonneg (sq_nonneg (y - m)) hy'.le
  have hZ := mul_nonneg (sq_nonneg (z - m)) hz'.le
  have hgap := three_interval_mesh_deficit x y z
  change _ = ((x - m) ^ 2 * (x + 2 * m) + (y - m) ^ 2 * (y + 2 * m) +
    (z - m) ^ 2 * (z + 2 * m)) / 3 at hgap
  refine ⟨by linarith only [hgap, hX, hY, hZ], ?_⟩
  constructor
  · intro heq
    have hzero {a : ℝ} (ha : 0 < a + 2 * m) (h : (a - m) ^ 2 * (a + 2 * m) = 0) :
        a = m := by
      have hsq := (mul_eq_zero.mp h).resolve_right ha.ne'
      have hdiff : a - m = 0 := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq
      exact sub_eq_zero.mp hdiff
    have ex := hzero hx' (by linarith only [hgap, heq, hX, hY, hZ])
    have ey := hzero hy' (by linarith only [hgap, heq, hX, hY, hZ])
    have ez := hzero hz' (by linarith only [hgap, heq, hX, hY, hZ])
    exact ⟨ex.trans ey.symm, ey.trans ez.symm⟩
  · rintro ⟨rfl, rfl⟩
    rw [meshCoefficient_eq_cubes]
    ring

section Mesh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def meshIntegral (x y z : ℝ) (u w : E) : E :=
  stepIntegral x (x + y) u + stepIntegral (x + y) (x + y + z) w

def meshEnergy (x y z : ℝ) (u w : E) : ℝ :=
  stepEnergy x (x + y) u + stepEnergy (x + y) (x + y + z) w

/-- Exact Cauchy–Schwarz deficit for the two active levels of the mesh. -/
theorem three_interval_energy_deficit {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (u w : E) :
    let p := x * (x + y)
    let q := (x + y) * (x + y + z)
    meshCoefficient x y z * meshEnergy x y z u w - ‖meshIntegral x y z u w‖ ^ 2 =
      (y * z / (p * q)) * ‖q • u - p • w‖ ^ 2 := by
  let p := x * (x + y)
  let q := (x + y) * (x + y + z)
  have hxy : 0 < x + y := add_pos hx hy
  have hxyz : 0 < x + y + z := add_pos hxy hz
  have hp : 0 < p := mul_pos hx hxy
  have hq : 0 < q := mul_pos hxy hxyz
  have hlen₁ : x + y - x = y := by ring
  have hlen₂ : x + y + z - (x + y) = z := by ring
  change _ = (y * z / (p * q)) * ‖q • u - p • w‖ ^ 2
  unfold meshCoefficient meshEnergy meshIntegral intervalCoefficient stepEnergy stepIntegral
  rw [intervalWeight_eq_length_div hx hxy, intervalWeight_eq_length_div hxy hxyz, hlen₁, hlen₂]
  change (p * y + q * z) * (y / p * ‖u‖ ^ 2 + z / q * ‖w‖ ^ 2) -
    ‖y • u + z • w‖ ^ 2 = (y * z / (p * q)) * ‖q • u - p • w‖ ^ 2
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_real_smul_sq, real_inner_smul_left, real_inner_smul_right]
  field_simp [hp.ne', hq.ne']
  ring

/-- The normalized bound and its equality case for a profile of positive energy. -/
theorem three_interval_normalized {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (htotal : x + y + z = 1) (u w : E) :
    ‖meshIntegral x y z u w‖ ^ 2 ≤ (8 / 27 : ℝ) * meshEnergy x y z u w ∧
    (0 < meshEnergy x y z u w →
      (‖meshIntegral x y z u w‖ ^ 2 = (8 / 27 : ℝ) * meshEnergy x y z u w ↔
        x = 1 / 3 ∧ y = 1 / 3 ∧ z = 1 / 3 ∧
        ((x + y) * (x + y + z)) • u = (x * (x + y)) • w)) := by
  have hmesh := three_interval_mesh_sharp hx.le hy.le hz.le (add_pos (add_pos hx hy) hz)
  rw [htotal, one_pow, mul_one] at hmesh
  have hE : 0 ≤ meshEnergy x y z u w :=
    add_nonneg (stepEnergy_nonneg hx (by linarith) u)
      (stepEnergy_nonneg (add_pos hx hy) (by linarith) w)
  have hgap := three_interval_energy_deficit hx hy hz u w
  dsimp only at hgap
  have hfactor : 0 < y * z / (x * (x + y) * ((x + y) * (x + y + z))) := by positivity
  have hfixed : ‖meshIntegral x y z u w‖ ^ 2 ≤ meshCoefficient x y z * meshEnergy x y z u w := by
    apply sub_nonneg.mp
    rw [hgap]
    exact mul_nonneg hfactor.le (sq_nonneg _)
  have hbound := mul_le_mul_of_nonneg_right hmesh.1 hE
  refine ⟨hfixed.trans hbound, fun hpos => ⟨?_, ?_⟩⟩
  · intro heq
    have hmax : meshCoefficient x y z = (8 / 27 : ℝ) := by
      refine le_antisymm hmesh.1 (le_of_mul_le_mul_right ?_ hpos)
      rw [← heq]
      exact hfixed
    obtain ⟨hxy, hyz⟩ := hmesh.2.mp hmax
    have hlevel : ((x + y) * (x + y + z)) • u - (x * (x + y)) • w = 0 := by
      have hproduct : (y * z / (x * (x + y) * ((x + y) * (x + y + z)))) *
          ‖((x + y) * (x + y + z)) • u - (x * (x + y)) • w‖ ^ 2 = 0 := by
        rw [← hgap, hmax, heq, sub_self]
      have hsq := (mul_eq_zero.mp hproduct).resolve_left hfactor.ne'
      exact norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq)
    exact ⟨by linarith, by linarith, by linarith, sub_eq_zero.mp hlevel⟩
  · rintro ⟨ex, ey, ez, hlevel⟩
    have hmax := hmesh.2.mpr ⟨ex.trans ey.symm, ey.trans ez.symm⟩
    rw [hmax, hlevel, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero] at hgap
    exact (sub_eq_zero.mp hgap).symm

end Mesh

def headCoefficient (s t c : ℝ) : ℝ :=
  max (intervalCoefficient s c) (intervalCoefficient t c)

def tailCoefficient (c d T : ℝ) : ℝ :=
  intervalCoefficient c (min d T) + intervalCoefficient d (max d T)

def bandCoefficient (s t c T : ℝ) : ℝ :=
  headCoefficient s t c + tailCoefficient c (s + t) T

/-- The second tail uses a collapsed interval when `1-v < d`. -/
theorem band_tail_identity (d v : ℝ) :
    tailCoefficient (d - v) d (1 - v) =
      if d ≤ 1 - v then d * (1 - d) * (1 - 2 * v)
      else (d - v) * (1 - v) * (1 - d) := by
  by_cases h : d ≤ 1 - v
  · rw [ite_eq_left h, tailCoefficient, min_eq_left h, max_eq_right h]
    unfold intervalCoefficient
    ring
  · have h' : 1 - v ≤ d := le_of_lt (lt_of_not_ge h)
    rw [ite_eq_right h, tailCoefficient, min_eq_right h', max_eq_left h']
    unfold intervalCoefficient
    ring

/-- Uniform band coefficient, retaining the mesh deficit and the cutoff allowance. -/
theorem band_coefficient_bound {s t v η : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hd : s + t ≤ 1)
    (hv : 0 ≤ v) (hη : 0 ≤ η) (hc : t < s + t - v - η) :
    bandCoefficient s t (s + t - v - η) (1 - v) ≤
      meshCoefficient s t (1 - (s + t)) + η := by
  let d := s + t
  let c₀ := d - v
  let c := c₀ - η
  let T := 1 - v
  let U := min d T
  change t < c at hc
  change d ≤ 1 at hd
  have ht := hs.trans_le hst
  have hc₀ : c ≤ c₀ := sub_le_self _ hη
  have hc₀d : c₀ ≤ d := sub_le_self _ hv
  have hc₀T : c₀ ≤ T := sub_le_sub_right hd _
  have hc₀U : c₀ ≤ U := le_min hc₀d hc₀T
  have hU : 0 ≤ U := ht.le.trans (hc.le.trans (hc₀.trans hc₀U))
  have hU1 : U ≤ 1 := (min_le_left d T).trans hd
  have hhead : headCoefficient s t c ≤ s * t * d := by
    apply max_le
    · calc
        intervalCoefficient s c ≤ intervalCoefficient s d :=
          intervalCoefficient_mono_right hs.le (hst.trans hc.le) (hc₀.trans hc₀d)
        _ = s * t * d := by dsimp [intervalCoefficient, d]; ring
    · calc
        intervalCoefficient t c ≤ intervalCoefficient t d :=
          intervalCoefficient_mono_right ht.le hc.le (hc₀.trans hc₀d)
        _ = s * t * d := by dsimp [intervalCoefficient, d]; ring
  have hshift : tailCoefficient c d T ≤ tailCoefficient c₀ d T + η := by
    have hdiff : tailCoefficient c d T - tailCoefficient c₀ d T =
        (η * U) * (c + c₀ - U) := by
      change (intervalCoefficient c U + intervalCoefficient d (max d T)) -
        (intervalCoefficient c₀ U + intervalCoefficient d (max d T)) =
          (η * U) * (c + c₀ - U)
      unfold intervalCoefficient
      dsimp only [c]
      ring
    have hfactor : c + c₀ - U ≤ 1 := by linarith only [hc₀, hc₀U, hU1]
    have hle : (η * U) * (c + c₀ - U) ≤ η :=
      calc
        _ ≤ (η * U) * 1 := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hη hU)
        _ ≤ η := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hU1 hη
    linarith only [hdiff, hle]
  have hd₀ : 0 ≤ d := ht.le.trans (hc.le.trans (hc₀.trans hc₀d))
  have htail : tailCoefficient c₀ d T ≤ d * (1 - d) := by
    change tailCoefficient (d - v) d (1 - v) ≤ d * (1 - d)
    rw [band_tail_identity]
    split_ifs with h
    · simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left (show 1 - 2 * v ≤ 1 by linarith)
          (mul_nonneg hd₀ (sub_nonneg.mpr hd)))
    · have hT : 0 ≤ T := ht.le.trans (hc.le.trans (hc₀.trans hc₀T))
      have hT1 : T ≤ 1 := sub_le_self _ hv
      have hprod : c₀ * T ≤ d := by
        simpa only [mul_one] using mul_le_mul hc₀d hT1 hT hd₀
      exact mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hd)
  have hmesh : meshCoefficient s t (1 - d) = s * t * d + d * (1 - d) := by
    dsimp [meshCoefficient, intervalCoefficient, d]
    ring
  change headCoefficient s t c + tailCoefficient c d T ≤ meshCoefficient s t (1 - d) + η
  linarith only [hhead, hshift, htail, hmesh]

/-- The real-inner-product multiplier inside the corrected energy. Multiplying
by the band coefficient gives the mixed coefficient in the row inequality. -/
def jumpCorrection (s t c : ℝ) : ℝ :=
  2 * ((c - s) * (c - t) / headCoefficient s t c - intervalWeight t c)

theorem jumpCorrection_eq_gap {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (htc : t < c)
    (hcd : c ≤ s + t) :
    jumpCorrection s t c = 2 * (c - t) * (t - s) / (s * t * c) ∧
      (0 < jumpCorrection s t c ↔ s < t) := by
  have ht := hs.trans_le hst
  have hc := ht.trans htc
  have hsc : 0 < c - s := sub_pos.mpr (hst.trans_lt htc)
  have hmax : intervalCoefficient t c ≤ intervalCoefficient s c := by
    have hprod := mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hst)) (sub_nonneg.mpr hcd)
    unfold intervalCoefficient
    nlinarith only [hprod]
  have hformula : jumpCorrection s t c = 2 * (c - t) * (t - s) / (s * t * c) := by
    rw [jumpCorrection, headCoefficient, max_eq_left hmax, intervalWeight_eq_length_div ht hc]
    unfold intervalCoefficient
    field_simp [hs.ne', ht.ne', hc.ne', hsc.ne']
  refine ⟨hformula, ?_⟩
  rw [hformula]
  constructor
  · intro h
    by_contra! h'
    have heq : t = s := le_antisymm h' hst
    simp [heq] at h
  · intro h
    exact div_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr htc)) (sub_pos.mpr h))
      (mul_pos (mul_pos hs ht) hc)

section Band

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def headIntegral (s t c : ℝ) (a b : E) : E :=
  stepIntegral s t a + stepIntegral t c (a + b)

def headEnergy (s t c : ℝ) (a b : E) : ℝ :=
  stepEnergy s t a + stepEnergy t c (a + b)

def rowIntegral (s t c r : ℝ) (a b u w : E) : E :=
  headIntegral s t c a b + stepIntegral c (min (s + t) r) u +
    stepIntegral (s + t) (max (s + t) r) w

def rowEnergy (s t c r : ℝ) (a b u w : E) : ℝ :=
  headEnergy s t c a b + stepEnergy c (min (s + t) r) u +
    stepEnergy (s + t) (max (s + t) r) w

private theorem headCoefficient_pos {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (htc : t < c) :
    0 < headCoefficient s t c := by
  have hsc : s < c := hst.trans_lt htc
  have h : 0 < intervalCoefficient s c :=
    mul_pos (mul_pos hs (hs.trans hsc)) (sub_pos.mpr hsc)
  exact h.trans_le (le_max_left _ _)

private theorem head_bound {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (htc : t < c) (a b : E) :
    ‖headIntegral s t c a b‖ ^ 2 ≤
      headCoefficient s t c * (headEnergy s t c a b + jumpCorrection s t c * ⟪a, b⟫_ℝ) := by
  let D := headCoefficient s t c
  have ht := hs.trans_le hst
  have hc := ht.trans htc
  have hD : 0 < D := headCoefficient_pos hs hst htc
  have hdiag₁ : (c - s) ^ 2 * ‖a‖ ^ 2 ≤ D * intervalWeight s c * ‖a‖ ^ 2 := by
    rw [← intervalCoefficient_mul_weight hs hc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (intervalWeight_nonneg hs (hst.trans htc.le)))
      (sq_nonneg _)
  have hdiag₂ : (c - t) ^ 2 * ‖b‖ ^ 2 ≤ D * intervalWeight t c * ‖b‖ ^ 2 := by
    rw [← intervalCoefficient_mul_weight ht hc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (intervalWeight_nonneg ht htc.le))
      (sq_nonneg _)
  have hE : headEnergy s t c a b =
      intervalWeight s c * ‖a‖ ^ 2 + intervalWeight t c * ‖b‖ ^ 2 +
        2 * intervalWeight t c * ⟪a, b⟫_ℝ := by
    have htel : intervalWeight s t + intervalWeight t c = intervalWeight s c := by
      unfold intervalWeight
      ring
    simp only [headEnergy, stepEnergy, norm_add_sq_real]
    rw [← htel]
    ring
  have hmix : D * jumpCorrection s t c =
      2 * ((c - s) * (c - t) - D * intervalWeight t c) := by
    change D * (2 * ((c - s) * (c - t) / D - intervalWeight t c)) = _
    rw [mul_left_comm D 2, mul_sub, mul_div_cancel₀ _ hD.ne']
  have hI : headIntegral s t c a b = (c - s) • a + (c - t) • b := by
    unfold headIntegral stepIntegral
    rw [smul_add, ← add_assoc, ← add_smul, show t - s + (c - t) = c - s by ring]
  change ‖headIntegral s t c a b‖ ^ 2 ≤
    D * (headEnergy s t c a b + jumpCorrection s t c * ⟪a, b⟫_ℝ)
  rw [hI, norm_add_sq_real, hE]
  simp only [norm_real_smul_sq, real_inner_smul_left, real_inner_smul_right]
  rw [mul_add, ← mul_assoc D, hmix]
  have hdiag := add_le_add_right (add_le_add hdiag₁ hdiag₂)
    (2 * (c - s) * (c - t) * ⟪a, b⟫_ℝ)
  convert hdiag using 1 <;> ring

omit [InnerProductSpace ℝ E] in
private theorem norm_add_three_sq_le (u₀ u₁ u₂ : E) (D E' : Fin 3 → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hE : ∀ i, 0 ≤ E' i)
    (h : ∀ i, ‖(![u₀, u₁, u₂] : Fin 3 → E) i‖ ^ 2 ≤ D i * E' i) :
    ‖u₀ + u₁ + u₂‖ ^ 2 ≤ (D 0 + D 1 + D 2) * (E' 0 + E' 1 + E' 2) := by
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin 3))
    (fun i _ => hD i) (fun i _ => hE i) (fun i _ => h i)
  have htriangle : ‖u₀ + u₁ + u₂‖ ≤ ‖u₀‖ + ‖u₁‖ + ‖u₂‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  calc
    _ ≤ (‖u₀‖ + ‖u₁‖ + ‖u₂‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
    _ ≤ _ := by simpa [Fin.sum_univ_three, add_assoc] using hCS

/-- The row estimate with a fixed signed mixed term and a variable cutoff `r`. -/
theorem band_row_bound {s t c T r : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (htc : t < c) (hcd : c ≤ s + t) (hcr : c ≤ r) (hrT : r ≤ T) (a b u w : E) :
    ‖rowIntegral s t c r a b u w‖ ^ 2 ≤ bandCoefficient s t c T *
      (rowEnergy s t c r a b u w + jumpCorrection s t c * ⟪a, b⟫_ℝ) := by
  let d := s + t
  let D₀ := headCoefficient s t c
  let D₁ := intervalCoefficient c (min d T)
  let D₂ := intervalCoefficient d (max d T)
  let E₀ := headEnergy s t c a b + jumpCorrection s t c * ⟪a, b⟫_ℝ
  let E₁ := stepEnergy c (min d r) u
  let E₂ := stepEnergy d (max d r) w
  have hc : 0 < c := ((hs.trans_le hst).trans htc)
  have hd : 0 < d := hc.trans_le hcd
  have h₁ : c ≤ min d r := le_min hcd hcr
  have h₂ : d ≤ max d r := le_max_left _ _
  have hd₀ : 0 < D₀ := headCoefficient_pos hs hst htc
  have hd₁ : 0 ≤ D₁ := intervalCoefficient_nonneg hc.le (le_min hcd (hcr.trans hrT))
  have hd₂ : 0 ≤ D₂ := intervalCoefficient_nonneg hd.le (le_max_left _ _)
  have he₁ : 0 ≤ E₁ := stepEnergy_nonneg hc h₁ u
  have he₂ : 0 ≤ E₂ := stepEnergy_nonneg hd h₂ w
  have hb₀ : ‖headIntegral s t c a b‖ ^ 2 ≤ D₀ * E₀ := head_bound hs hst htc a b
  have he₀ : 0 ≤ E₀ := by
    by_contra! hn
    exact (not_lt_of_ge ((sq_nonneg _).trans hb₀)) (mul_neg_of_pos_of_neg hd₀ hn)
  have hb₁ : ‖stepIntegral c (min d r) u‖ ^ 2 ≤ D₁ * E₁ := by
    rw [step_norm_sq hc (hc.trans_le h₁)]
    exact mul_le_mul_of_nonneg_right (intervalCoefficient_mono_right hc.le h₁
      (min_le_min le_rfl hrT)) he₁
  have hb₂ : ‖stepIntegral d (max d r) w‖ ^ 2 ≤ D₂ * E₂ := by
    rw [step_norm_sq hd (hd.trans_le h₂)]
    exact mul_le_mul_of_nonneg_right (intervalCoefficient_mono_right hd.le h₂
      (max_le_max le_rfl hrT)) he₂
  have h := norm_add_three_sq_le (headIntegral s t c a b) (stepIntegral c (min d r) u)
    (stepIntegral d (max d r) w) ![D₀, D₁, D₂] ![E₀, E₁, E₂]
    (by
      intro i
      fin_cases i
      · exact hd₀.le
      · exact hd₁
      · exact hd₂)
    (by
      intro i
      fin_cases i
      · exact he₀
      · exact he₁
      · exact he₂)
    (by
      intro i
      fin_cases i
      · exact hb₀
      · exact hb₁
      · exact hb₂)
  have henergy : E₀ + E₁ + E₂ = rowEnergy s t c r a b u w + jumpCorrection s t c * ⟪a, b⟫_ℝ := by
    dsimp only [E₀, E₁, E₂, rowEnergy, d]
    ring
  change ‖rowIntegral s t c r a b u w‖ ^ 2 ≤
    (D₀ + D₁ + D₂) * (E₀ + E₁ + E₂) at h
  rw [henergy, add_assoc D₀ D₁ D₂] at h
  exact h

/-- Summation over a spectral band. Orthogonality of the jump vectors cancels
the last sum. For complex Hilbert spaces use the real inner product induced by
`InnerProductSpace.complexToReal`, so the last sum is the real part of the
complex inner product of the jump families. -/
theorem band_row_sum_sharp {ι : Type*} (rows : Finset ι) {s t v η : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hd : s + t ≤ 1) (hv : 0 ≤ v) (hη : 0 ≤ η)
    (hc : t < s + t - v - η) (r : ι → ℝ) (a b u w : ι → E)
    (hcut : ∀ i ∈ rows, s + t - v - η ≤ r i ∧ r i ≤ 1 - v) :
    let c := s + t - v - η
    let T := 1 - v
    (∑ i ∈ rows, ‖rowIntegral s t c (r i) (a i) (b i) (u i) (w i)‖ ^ 2) ≤
      (8 / 27 + η) * (∑ i ∈ rows, rowEnergy s t c (r i) (a i) (b i) (u i) (w i)) +
      (bandCoefficient s t c T * jumpCorrection s t c) * ∑ i ∈ rows, ⟪a i, b i⟫_ℝ := by
  let c := s + t - v - η
  let T := 1 - v
  let C := bandCoefficient s t c T
  let k := jumpCorrection s t c
  let e (i : ι) := rowEnergy s t c (r i) (a i) (b i) (u i) (w i)
  let q (i : ι) := ⟪a i, b i⟫_ℝ
  let I (i : ι) := rowIntegral s t c (r i) (a i) (b i) (u i) (w i)
  change (∑ i ∈ rows, ‖I i‖ ^ 2) ≤
    (8 / 27 + η) * (∑ i ∈ rows, e i) + (C * k) * ∑ i ∈ rows, q i
  have ht := hs.trans_le hst
  have hcpos : 0 < c := ht.trans hc
  have hcd : c ≤ s + t := by dsimp [c]; linarith
  have hdpos : 0 < s + t := add_pos hs ht
  have he : 0 ≤ ∑ i ∈ rows, e i := by
    refine Finset.sum_nonneg fun i hi => ?_
    dsimp only [e, rowEnergy, headEnergy]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (stepEnergy_nonneg hs hst (a i))
          (stepEnergy_nonneg ht hc.le (a i + b i)))
        (stepEnergy_nonneg hcpos (le_min hcd (hcut i hi).1) (u i)))
      (stepEnergy_nonneg hdpos (le_max_left _ _) (w i))
  have hmax := (three_interval_mesh_sharp hs.le ht.le (sub_nonneg.mpr hd)
    (show 0 < s + t + (1 - (s + t)) by linarith)).1
  rw [show s + t + (1 - (s + t)) = (1 : ℝ) by ring, one_pow, mul_one] at hmax
  have hC : C ≤ 8 / 27 + η :=
    (band_coefficient_bound hs hst hd hv hη hc).trans (add_le_add_left hmax η)
  calc
    _ ≤ ∑ i ∈ rows, C * (e i + k * q i) := Finset.sum_le_sum fun i hi =>
      band_row_bound hs hst hc hcd (hcut i hi).1 (hcut i hi).2 (a i) (b i) (u i) (w i)
    _ = C * (∑ i ∈ rows, e i) + (C * k) * ∑ i ∈ rows, q i := by
      simp only [mul_add, mul_assoc, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hC he) _

/-- The zero-width band attains the constant at equal thirds. The last level
is three times the sum of the prescribed jumps. -/
theorem band_equal_thirds_attains (a b : E) (hne : a + b ≠ 0) :
    let s : ℝ := 1 / 3
    let d := s + s
    let T := d + s
    let w : E := (3 : ℝ) • (a + b)
    0 < rowEnergy s s d T a b 0 w ∧
      ‖rowIntegral s s d T a b 0 w‖ ^ 2 = (8 / 27 : ℝ) * rowEnergy s s d T a b 0 w := by
  let s : ℝ := 1 / 3
  let d := s + s
  let T := d + s
  let w : E := (3 : ℝ) • (a + b)
  change 0 < rowEnergy s s d T a b 0 w ∧
    ‖rowIntegral s s d T a b 0 w‖ ^ 2 = (8 / 27 : ℝ) * rowEnergy s s d T a b 0 w
  have hs : 0 < s := by norm_num [s]
  have ht : s + s + s = 1 := by norm_num [s]
  have hdT : d ≤ T := le_add_of_nonneg_right hs.le
  have he : rowEnergy s s d T a b 0 w = meshEnergy s s s (a + b) w := by
    change headEnergy s s d a b + stepEnergy d (min d T) (0 : E) +
      stepEnergy d (max d T) w = _
    rw [min_eq_left hdT, max_eq_right hdT]
    simp [headEnergy, meshEnergy, stepEnergy, intervalWeight, d, T]
  have hI : rowIntegral s s d T a b 0 w = meshIntegral s s s (a + b) w := by
    change headIntegral s s d a b + stepIntegral d (min d T) (0 : E) +
      stepIntegral d (max d T) w = _
    rw [min_eq_left hdT, max_eq_right hdT]
    simp [headIntegral, meshIntegral, stepIntegral, d, T]
  have hweight : 0 < intervalWeight s d := by norm_num [intervalWeight, d, s]
  have hpos : 0 < meshEnergy s s s (a + b) w := by
    change 0 < intervalWeight s d * ‖a + b‖ ^ 2 + stepEnergy d T w
    exact add_pos_of_pos_of_nonneg
      (mul_pos hweight (pow_pos (norm_pos_iff.mpr hne) _))
      (stepEnergy_nonneg (add_pos hs hs) hdT w)
  rw [he, hI]
  refine ⟨hpos, ((three_interval_normalized hs hs hs ht (a + b) w).2 hpos).mpr
    ⟨rfl, rfl, rfl, ?_⟩⟩
  dsimp only [w]
  rw [show (s + s) * (s + s + s) = s * (s + s) * 3 by norm_num [s], mul_smul]

end Band

end D5.S3.Quantum.Recovery.BKMSharpWeightedInterval
