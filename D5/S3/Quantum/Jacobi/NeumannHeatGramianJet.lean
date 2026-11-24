/- GID: D5/S3/Quantum/Jacobi/NeumannHeatGramianJet
   generality: G
   mirror-B: D5/B/S3/Quantum/Jacobi/NeumannHeatGramianJet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Quantum.Jacobi.EndpointMomentTruncation]
   utility: none
   digest: A common prefix delays the first zero-net heat Gramian difference. -/

module

public import D5.S3.Quantum.Jacobi.EndpointMomentTruncation
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Zero-net heat Gramian coefficients on a positive Neumann path -/

@[expose] public section
namespace D5.S3.Quantum.Jacobi.NeumannHeatGramianJet

open Finset PowerSeries EndpointMomentTruncation
noncomputable section

/-- The formal time average, obtained by integrating from zero and removing the factor of time. -/
def timeAverage (H : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.mk fun r => coeff r H / (r + 1 : ℝ)

/-- The integral of the squared heat response minus time times the squared mean. -/
def gramian (H : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  X * (timeAverage (H * H) - timeAverage H * timeAverage H)

private theorem timeAverage_add (H G : ℝ⟦X⟧) :
    timeAverage (H + G) = timeAverage H + timeAverage G := by
  ext r
  simp [timeAverage, add_div]

private theorem timeAverage_const (c : ℝ) : timeAverage (C c) = C c := by
  ext r
  cases r <;> simp [timeAverage, coeff_C]

private theorem timeAverage_const_mul (c : ℝ) (H : ℝ⟦X⟧) :
    timeAverage (C c * H) = C c * timeAverage H := by
  ext r
  simp [timeAverage, coeff_C_mul, mul_div_assoc]

private theorem gramian_add_const (H : ℝ⟦X⟧) (c : ℝ) : gramian (H + C c) = gramian H := by
  have h : (H + C c) * (H + C c) = H * H + (C c * H + C c * H) + C (c * c) := by
    rw [map_mul]
    ring
  rw [gramian, gramian, h]
  simp only [timeAverage_add, timeAverage_const, timeAverage_const_mul, map_mul]
  ring

private theorem derivative_average (H : ℝ⟦X⟧) :
    X * PowerSeries.derivative (timeAverage H) = H - timeAverage H := by
  ext r
  cases r with
  | zero => simp [timeAverage, coeff_zero_X_mul]
  | succ r =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [timeAverage, coeff_mk, map_sub, Nat.cast_succ]
    field_simp
    ring

private theorem derivative_gramian (H : ℝ⟦X⟧) :
    PowerSeries.derivative (gramian H) = (timeAverage H - H) * (timeAverage H - H) := by
  have h := derivative_average H
  have hsq := derivative_average (H * H)
  simp only [gramian, Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul,
    map_sub]
  linear_combination hsq - 2 * timeAverage H * h

private theorem coeff_gramian_succ (H : ℝ⟦X⟧) (r : ℕ) :
    coeff (r + 1) (gramian H) =
      coeff r ((timeAverage H - H) * (timeAverage H - H)) / (r + 1 : ℝ) := by
  apply (eq_div_iff (by positivity)).2
  rw [← coeff_derivative, derivative_gramian]

private theorem coeff_centered (H : ℝ⟦X⟧) (r : ℕ) :
    coeff r (timeAverage H - H) = - (r : ℝ) * coeff r H / (r + 1 : ℝ) := by
  simp only [timeAverage, map_sub, coeff_mk]
  field_simp
  ring

private theorem coeff_mul_range (F G : ℝ⟦X⟧) (d : ℕ) :
    coeff d (F * G) = ∑ i ∈ range (d + 1), coeff i F * coeff (d - i) G := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij => coeff ij.1 F * coeff ij.2 G) d

/-- Centering eliminates order zero. At the first changed positive coefficient of order
at least two, only the cross term with the shared linear coefficient contributes. -/
private theorem first_difference (H G : ℝ⟦X⟧) {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ i, 0 < i → i < r → coeff i H = coeff i G) :
    (∀ d < r + 2, coeff d (gramian H - gramian G) = 0) ∧
    coeff (r + 2) (gramian H - gramian G) =
      (coeff 1 H * (r : ℝ) * (coeff r H - coeff r G)) /
        ((r + 1 : ℝ) * (r + 2 : ℝ)) := by
  let F := timeAverage H - H
  let J := timeAverage G - G
  have hlow (i : ℕ) (hi : i < r) : coeff i (F - J) = 0 := by
    change coeff i ((timeAverage H - H) - (timeAverage G - G)) = 0
    rw [map_sub, coeff_centered, coeff_centered]
    by_cases hz : i = 0
    · subst i
      simp
    · rw [h i (by omega) hi, sub_self]
  have hzero : coeff 0 (F + J) = 0 := by
    change coeff 0 ((timeAverage H - H) + (timeAverage G - G)) = 0
    rw [map_add, coeff_centered, coeff_centered]
    simp
  have hproduct : F * F - J * J = (F - J) * (F + J) := by ring
  have hstep (d : ℕ) : coeff (d + 1) (gramian H - gramian G) =
      coeff d ((F - J) * (F + J)) / (d + 1 : ℝ) := by
    rw [map_sub, coeff_gramian_succ, coeff_gramian_succ]
    change coeff d (F * F) / _ - coeff d (J * J) / _ = _
    rw [← sub_div, ← map_sub, hproduct]
  constructor
  · intro d hd
    cases d with
    | zero => simp [gramian]
    | succ d =>
      rw [hstep, coeff_mul_range, sum_eq_zero, zero_div]
      intro i hi
      have hi' := mem_range.mp hi
      by_cases hl : i < r
      · rw [hlow i hl, zero_mul]
      · rw [show d - i = 0 by omega, hzero, mul_zero]
  · rw [show r + 2 = (r + 1) + 1 by omega, hstep, coeff_mul_range,
      sum_eq_single r]
    · rw [show r + 1 - r = 1 by omega]
      rw [map_sub, map_add]
      change (coeff r (timeAverage H - H) - coeff r (timeAverage G - G)) *
        (coeff 1 (timeAverage H - H) + coeff 1 (timeAverage G - G)) / _ = _
      simp only [coeff_centered, Nat.cast_add, Nat.cast_one]
      rw [← h 1 (by omega) (by omega)]
      field_simp
      ring
    · intro i hi hne
      have hi' := mem_range.mp hi
      by_cases hl : i < r
      · rw [hlow i hl, zero_mul]
      · rw [show r + 1 - i = 0 by omega, hzero, mul_zero]
    · simp

/-- A finite path arranged from the measured endpoint, with strictly positive cell lengths. -/
structure Path (n : ℕ) where
  length : Fin n → ℝ
  positive : ∀ i, 0 < length i

/-- The zero extension of the ordered edge lengths. Edges are indexed from zero. -/
def Path.edge {n : ℕ} (p : Path n) (i : ℕ) : ℝ :=
  if h : i < n then p.length ⟨i, h⟩ else 0

/-- Lumped mass at a vertex. Each incident edge contributes half its length. -/
def Path.mass {n : ℕ} (p : Path n) (i : ℕ) : ℝ :=
  ((if i = 0 then 0 else p.edge (i - 1)) + p.edge i) / 2

/-- Diagonal of the symmetric mass-normalized Neumann stiffness. -/
def Path.diagonal {n : ℕ} (p : Path n) (i : ℕ) : ℝ :=
  ((if i = 0 then 0 else (p.edge (i - 1))⁻¹) + (p.edge i)⁻¹) / p.mass i

/-- The signed coupling across edge `i` in the symmetric mass-normalized stiffness. -/
def Path.bond {n : ℕ} (p : Path n) (i : ℕ) : ℝ :=
  -(p.edge i)⁻¹ / Real.sqrt (p.mass i * p.mass (i + 1))

/-- Endpoint moment with the physical port normalization `1 / m₀`. The finite
stiffness acts by the three-term Jacobi recurrence with zero couplings past the right end. -/
def Path.moment {n : ℕ} (p : Path n) (r : ℕ) : ℝ :=
  amplitude p.diagonal p.bond (some (n + 1)) r 0 / p.mass 0

/-- Formal impulse response of the collocated heat port, with an additive constant offset. -/
def Path.heat {n : ℕ} (p : Path n) (c : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk (fun r => (-1 : ℝ) ^ r * p.moment r / (r.factorial : ℝ)) + C c

private theorem finite_amplitude {n : ℕ} (p : Path n) (r i : ℕ) :
    amplitude p.diagonal p.bond (some (n + 1)) r i =
      amplitude p.diagonal p.bond none r i := by
  induction r generalizing i with
  | zero =>
    by_cases hi : i < n + 1
    · simp [amplitude, Option.elim, hi]
    · simp [amplitude, Option.elim, hi, show i ≠ 0 by omega]
  | succ r ih =>
    by_cases hi : i < n + 1
    · simp only [amplitude, Option.elim, hi, decide_true, ite_true, ih]
    · have hprev : p.edge (i - 1) = 0 := by
        simp [Path.edge, show ¬(i - 1 < n) by omega]
      have hedge : p.edge i = 0 := by simp [Path.edge, show ¬i < n by omega]
      simp [amplitude, Option.elim, hi, Path.bond, Path.diagonal, hprev, hedge]

private theorem edge_pos {n i : ℕ} (p : Path n) (hi : i < n) : 0 < p.edge i := by
  simpa [Path.edge, hi] using p.positive ⟨i, hi⟩

private theorem mass_pos {n i : ℕ} (p : Path n) (hi : i < n) : 0 < p.mass i := by
  have he := edge_pos p hi
  unfold Path.mass
  split
  · positivity
  · have hp := edge_pos p (show i - 1 < n by omega)
    positivity

private theorem bond_sq {n i : ℕ} (p : Path n) (hi : i + 1 < n) :
    p.bond i ^ 2 = ((p.edge i) ^ 2 * p.mass i)⁻¹ * (p.mass (i + 1))⁻¹ := by
  have hm := mul_pos (mass_pos p (show i < n by omega)) (mass_pos p hi)
  rw [Path.bond, div_pow, neg_sq, Real.sq_sqrt hm.le, inv_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem mass_eq {n i k : ℕ} {p q : Path n}
    (h : ∀ j < k, p.edge j = q.edge j) (hi : i < k) : p.mass i = q.mass i := by
  simp only [Path.mass, h i hi]
  split <;> simp_all only [h (i - 1) (show i - 1 < k by omega)]

private theorem trunc_eq {n k : ℕ} {p q : Path n} (h : ∀ j < k, p.edge j = q.edge j)
    (r i : ℕ) :
    amplitude p.diagonal p.bond (some k) r i =
      amplitude q.diagonal q.bond (some k) r i := by
  have hd (j : ℕ) (hj : j < k) : p.diagonal j = q.diagonal j := by
    simp [Path.diagonal, mass_eq h hj, h j hj, h (j - 1) (show j - 1 < k by omega)]
  have hb (j : ℕ) (hj : j + 1 < k) : p.bond j = q.bond j := by
    rw [Path.bond, Path.bond, h j (by omega), mass_eq h (by omega), mass_eq h hj]
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    by_cases hi : i < k
    · simp only [amplitude, Option.elim, hi, decide_true, ite_true]
      rw [ih, ih, ih, hd i hi]
      congr 1
      · by_cases hz : i = 0
        · simp [hz]
        · rw [hb (i - 1) (by omega)]
      · by_cases hn : i + 1 < k
        · rw [hb i hn]
        · cases r <;> simp [amplitude, Option.elim, hn]
    · simp [amplitude, Option.elim, hi]

private theorem moments_of_prefix {n k : ℕ} {p q : Path n} (hk : 0 < k)
    (h : ∀ i < k, p.edge i = q.edge i) :
    (∀ r < 2 * k, p.moment r = q.moment r) ∧
    p.moment (2 * k) - q.moment (2 * k) =
      ((∏ i ∈ range k, p.bond i ^ 2) - (∏ i ∈ range k, q.bond i ^ 2)) / p.mass 0 := by
  have hp := first_omitted_moment p.diagonal p.bond k
  have hq := first_omitted_moment q.diagonal q.bond k
  have hm := mass_eq h (show 0 < k from hk)
  constructor
  · intro r hr
    rw [Path.moment, Path.moment, finite_amplitude, finite_amplitude,
      hp.1 r hr, hq.1 r hr, trunc_eq h, hm]
  · rw [Path.moment, Path.moment, finite_amplitude, finite_amplitude, ← hm, ← sub_div]
    congr 1
    rw [← hp.2, ← hq.2, trunc_eq h]
    ring

private theorem moment_gap {n k : ℕ} {p q : Path n} (hk : 0 < k) (hn : k < n)
    (h : ∀ i < k, p.edge i = q.edge i) (hne : p.edge k ≠ q.edge k) :
    p.moment (2 * k) - q.moment (2 * k) ≠ 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [(moments_of_prefix hk h).2, prod_range_succ, prod_range_succ, bond_sq p hn, bond_sq q hn]
  have hb : (∏ i ∈ range j, q.bond i ^ 2) = ∏ i ∈ range j, p.bond i ^ 2 := by
    apply prod_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [Path.bond, Path.bond, h i (by omega), mass_eq h (by omega), mass_eq h (by omega)]
  rw [hb, ← h j (by omega), ← mass_eq h (show j < j + 1 by omega)]
  have hpos : 0 < ∏ i ∈ range j, p.bond i ^ 2 := by
    apply prod_pos
    intro i hi
    have hi' := mem_range.mp hi
    rw [bond_sq p (by omega)]
    have he := edge_pos p (show i < n by omega)
    have hm := mass_pos p (show i < n by omega)
    have hm' := mass_pos p (show i + 1 < n by omega)
    positivity
  have heg : p.mass (j + 1) ≠ q.mass (j + 1) := by
    intro hm
    apply hne
    simp [Path.mass, h j (show j < j + 1 by omega)] at hm
    linarith [hm]
  have hleft : 0 < ((p.edge j) ^ 2 * p.mass j)⁻¹ := by
    exact inv_pos.mpr (mul_pos (sq_pos_of_pos (edge_pos p (by omega))) (mass_pos p (by omega)))
  apply div_ne_zero _ (mass_pos p (by omega)).ne'
  rw [← mul_sub, ← mul_sub]
  exact mul_ne_zero hpos.ne' (mul_ne_zero hleft.ne'
    (sub_ne_zero.mpr (fun e => heg (inv_injective e))))

private theorem heat_coeff {n r : ℕ} (p : Path n) (c : ℝ) (hr : 0 < r) :
    coeff r (p.heat c) = (-1 : ℝ) ^ r * p.moment r / (r.factorial : ℝ) := by
  simp [Path.heat, coeff_C_of_ne_zero hr.ne']

private theorem moment_one_pos {n : ℕ} (p : Path n) (hn : 0 < n) : 0 < p.moment 1 := by
  have hm := mass_pos p hn
  have he := edge_pos p hn
  rw [Path.moment, finite_amplitude]
  norm_num [amplitude, Option.elim, Path.diagonal]
  positivity

/-- When the first unequal edge follows a positive prefix of length `k`, the centered
Gramian series first differ at degree `2k + 2`. Their gap is a nonzero multiple of the
first unequal physical moment. The two heat offsets are arbitrary. -/
theorem first_reveal {n : ℕ} (p q : Path n) (k : ℕ) (c e : ℝ)
    (hk : 0 < k) (hn : k < n) (h : ∀ i < k, p.edge i = q.edge i)
    (hne : p.edge k ≠ q.edge k) :
    (∀ d < 2 * k + 2, coeff d (gramian (p.heat c) - gramian (q.heat e)) = 0) ∧
    coeff (2 * k + 2) (gramian (p.heat c) - gramian (q.heat e)) =
      -(p.moment 1) * (2 * k : ℕ) * (p.moment (2 * k) - q.moment (2 * k)) /
        (((2 * k + 2 : ℕ).factorial : ℝ)) ∧
    coeff (2 * k + 2) (gramian (p.heat c) - gramian (q.heat e)) ≠ 0 := by
  have hoffset (a : Path n) (t : ℝ) : gramian (a.heat t) = gramian (a.heat 0) := by
    simp only [Path.heat, gramian_add_const]
  rw [hoffset p c, hoffset q e]
  have hprefix := (moments_of_prefix hk h).1
  obtain ⟨hbelow, hexact⟩ := first_difference (p.heat 0) (q.heat 0) (show 2 ≤ 2 * k by omega)
    (fun i hi hir => by rw [heat_coeff p 0 hi, heat_coeff q 0 hi, hprefix i hir])
  have heven : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [heat_coeff p 0 (by decide), heat_coeff p 0 (by omega), heat_coeff q 0 (by omega),
    heven] at hexact
  have hfactorial : (((2 * k + 2 : ℕ).factorial : ℝ)) =
      ((2 * k : ℕ) + 2 : ℝ) * (((2 * k : ℕ) + 1 : ℝ) * ((2 * k : ℕ).factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hg : coeff (2 * k + 2) (gramian (p.heat 0) - gramian (q.heat 0)) =
      -(p.moment 1) * (2 * k : ℕ) * (p.moment (2 * k) - q.moment (2 * k)) /
        (((2 * k + 2 : ℕ).factorial : ℝ)) := by
    rw [hexact, hfactorial]
    norm_num
    rw [← sub_div]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨hbelow, hg, ?_⟩
  rw [hg]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (moment_one_pos p (by omega)).ne') (by positivity))
      (moment_gap hk hn h hne)) (by positivity)

end
end D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
