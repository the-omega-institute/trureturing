/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockLattice
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-universal-algebra)
   anchors: []
   digest: Unimodular Fibonacci lattices identify every nonzero Beatty return with an oriented golden phase window. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice

noncomputable section

/-- Positive golden rotation angle; the existing contracting eigenvalue is its negative. -/
abbrev alpha : ℝ := -Real.goldenConj

def previous (L : ℕ) : ℤ := Nat.fib (L + 1)
def boundary (L : ℕ) : ℤ := Nat.fib (L + 2)
def leading (L : ℕ) : ℤ := Nat.fib (L + 3)
def orientation (L : ℕ) : ℤ := (-1) ^ L

/-- Signed window width. Its sign alternates with resolution, not with physical time. -/
def signedWidth (L : ℕ) : ℝ := Real.goldenConj ^ (L + 2)
def width (L : ℕ) : ℝ := alpha ^ (L + 2)

def entry (L : ℕ) (m : ℤ) : ℤ :=
  leading L * m + boundary L * ⌊(m : ℝ) * alpha⌋

def phaseCoordinate (L : ℕ) (e h : ℤ) : ℝ :=
  ((e : ℝ) * alpha - h) / signedWidth L

/-- An open oriented arc, expressed without choosing a discontinuous representative of the circle. -/
def Hits (L : ℕ) (e : ℤ) : Prop :=
  ∃ h : ℤ, 0 < phaseCoordinate L e h ∧ phaseCoordinate L e h < 1

lemma alpha_pos : 0 < alpha := neg_pos.mpr Real.goldenConj_neg
lemma alpha_lt_one : alpha < 1 := by
  dsimp [alpha]
  linarith [Real.neg_one_lt_goldenConj]
lemma alpha_sq_add : alpha ^ 2 + alpha = 1 := by
  dsimp [alpha]
  nlinarith [Real.goldenConj_sq]
lemma alpha_irrational : Irrational alpha := Real.goldenConj_irrational.neg
lemma signedWidth_ne_zero (L : ℕ) : signedWidth L ≠ 0 :=
  pow_ne_zero _ Real.goldenConj_ne_zero
lemma width_pos (L : ℕ) : 0 < width L := pow_pos alpha_pos _

lemma leading_eq (L : ℕ) : leading L = previous L + boundary L := by
  simp only [leading, previous, boundary]
  exact_mod_cast (Nat.fib_add_two (n := L + 1))
lemma boundary_succ (L : ℕ) : boundary (L + 1) = leading L := by
  simp [boundary, leading, Nat.add_assoc]
lemma previous_succ (L : ℕ) : previous (L + 1) = boundary L := by
  simp [previous, boundary, Nat.add_assoc]
lemma leading_succ (L : ℕ) : leading (L + 1) = boundary L + leading L := by
  rw [leading_eq, previous_succ, boundary_succ]
lemma orientation_sq (L : ℕ) : orientation L * orientation L = 1 := by
  simp only [orientation, ← mul_pow]
  norm_num

/-- Cassini in the exact coordinates used by the return lattice. -/
theorem lattice_determinant (L : ℕ) :
    leading L * previous L - boundary L ^ 2 = orientation L := by
  induction L with
  | zero => norm_num [leading, previous, boundary, orientation]
  | succ L ih =>
      change leading (L + 1) * previous (L + 1) - boundary (L + 1) ^ 2 =
        orientation (L + 1)
      rw [leading_succ, previous_succ, boundary_succ]
      have hs : orientation (L + 1) = -orientation L := by
        simp [orientation, pow_succ]
      rw [hs, leading_eq L]
      rw [leading_eq L] at ih
      nlinarith

/-- A signed contracting mode: successive resolutions reverse and shrink. -/
theorem signedWidth_succ (L : ℕ) :
    signedWidth (L + 1) = -alpha * signedWidth L := by
  simp only [signedWidth, alpha, neg_neg]
  rw [show L + 1 + 2 = (L + 2) + 1 by omega, pow_succ]
  ring

lemma signedWidth_two (L : ℕ) :
    signedWidth (L + 2) = alpha ^ 2 * signedWidth L := by
  rw [show L + 2 = (L + 1) + 1 by omega, signedWidth_succ, signedWidth_succ]
  ring

lemma signedWidth_abs (L : ℕ) : |signedWidth L| = width L := by
  simp only [signedWidth, width, abs_pow, abs_of_neg Real.goldenConj_neg, alpha]

lemma boundary_error (L : ℕ) :
    (boundary L : ℝ) * alpha - previous L = -signedWidth L := by
  have h := Real.goldenConj_mul_fib_succ_add_fib (L + 1)
  simp only [Nat.add_assoc] at h
  dsimp [boundary, previous, signedWidth, alpha]
  push_cast
  nlinarith

lemma leading_error (L : ℕ) :
    (leading L : ℝ) * alpha - boundary L = alpha * signedWidth L := by
  have h := boundary_error (L + 1)
  rw [boundary_succ, previous_succ, signedWidth_succ] at h
  nlinarith

/-- Both coordinates are transformed: the omitted integer coordinate is essential. -/
theorem lattice_phase_identity (L : ℕ) (m k : ℤ) :
    (((leading L * m + boundary L * k : ℤ) : ℝ) * alpha -
      ((boundary L * m + previous L * k : ℤ) : ℝ)) =
      signedWidth L * ((m : ℝ) * alpha - k) := by
  push_cast
  calc
    _ = ((leading L : ℝ) * alpha - boundary L) * m +
        ((boundary L : ℝ) * alpha - previous L) * k := by ring
    _ = _ := by rw [leading_error, boundary_error]; ring

lemma lattice_phase_coordinate (L : ℕ) (m k : ℤ) :
    phaseCoordinate L (leading L * m + boundary L * k)
      (boundary L * m + previous L * k) = (m : ℝ) * alpha - k := by
  unfold phaseCoordinate
  rw [lattice_phase_identity]
  apply (div_eq_iff (signedWidth_ne_zero L)).2
  ring

/-- Explicit integral inverse; no real inverse is assumed to preserve lattice points. -/
theorem lattice_inverse (L : ℕ) (e h : ℤ) :
    let m := orientation L * (previous L * e - boundary L * h)
    let k := orientation L * (leading L * h - boundary L * e)
    leading L * m + boundary L * k = e ∧
      boundary L * m + previous L * k = h := by
  dsimp only
  constructor
  · calc
      _ = (orientation L * (leading L * previous L - boundary L ^ 2)) * e := by ring
      _ = e := by rw [lattice_determinant, orientation_sq, one_mul]
  · calc
      _ = (orientation L * (leading L * previous L - boundary L ^ 2)) * h := by ring
      _ = h := by rw [lattice_determinant, orientation_sq, one_mul]

lemma fractional_bounds (m : ℤ) (hm : m ≠ 0) :
    0 < (m : ℝ) * alpha - (⌊(m : ℝ) * alpha⌋ : ℤ) ∧
      (m : ℝ) * alpha - (⌊(m : ℝ) * alpha⌋ : ℤ) < 1 := by
  have hlo := Int.floor_le ((m : ℝ) * alpha)
  have hhi := Int.lt_floor_add_one ((m : ℝ) * alpha)
  have hne := (alpha_irrational.intCast_mul hm).ne_int ⌊(m : ℝ) * alpha⌋
  constructor <;> linarith

/-- Exact return/phase equivalence on the full integer lattice. Natural events use e > 0. -/
theorem hits_iff_entry (L : ℕ) (e : ℤ) :
    Hits L e ↔ ∃ m : ℤ, m ≠ 0 ∧ e = entry L m := by
  constructor
  · rintro ⟨h, hlo, hhi⟩
    let m := orientation L * (previous L * e - boundary L * h)
    let k := orientation L * (leading L * h - boundary L * e)
    have hinv := lattice_inverse L e h
    change leading L * m + boundary L * k = e ∧
      boundary L * m + previous L * k = h at hinv
    have hc : phaseCoordinate L e h = (m : ℝ) * alpha - k := by
      rw [← hinv.1, ← hinv.2]
      exact lattice_phase_coordinate L m k
    rw [hc] at hlo hhi
    have hk : ⌊(m : ℝ) * alpha⌋ = k :=
      Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    have hm : m ≠ 0 := by
      intro hz
      have hltR : (k : ℝ) < 0 := by simpa [hz] using hlo
      have hgtR : (-1 : ℝ) < k := by
        simp only [hz, Int.cast_zero, zero_mul, zero_sub] at hhi
        linarith
      have hlt : k < 0 := by exact_mod_cast hltR
      have hgt : -1 < k := by exact_mod_cast hgtR
      omega
    refine ⟨m, hm, ?_⟩
    unfold entry
    rw [hk]
    exact hinv.1.symm
  · rintro ⟨m, hm, rfl⟩
    refine ⟨boundary L * m + previous L * ⌊(m : ℝ) * alpha⌋, ?_⟩
    change 0 < phaseCoordinate L (leading L * m + boundary L * ⌊(m : ℝ) * alpha⌋)
        (boundary L * m + previous L * ⌊(m : ℝ) * alpha⌋) ∧ _
    rw [lattice_phase_coordinate]
    exact fractional_bounds m hm

/-- A later same-parity scale gives a genuine subset of the earlier phase-event set. -/
theorem hits_two_steps (L : ℕ) (e : ℤ) : Hits (L + 2) e → Hits L e := by
  rintro ⟨h, hlo, hhi⟩
  refine ⟨h, ?_⟩
  have hc : phaseCoordinate L e h = alpha ^ 2 * phaseCoordinate (L + 2) e h := by
    unfold phaseCoordinate
    rw [signedWidth_two]
    field_simp [signedWidth_ne_zero L, ne_of_gt alpha_pos] <;> ring
  rw [hc]
  have ha2 : 0 < alpha ^ 2 := sq_pos_of_pos alpha_pos
  have ha2lt : alpha ^ 2 < 1 := by nlinarith [alpha_sq_add, alpha_pos]
  constructor
  · exact mul_pos ha2 hlo
  · have hm : alpha ^ 2 * phaseCoordinate (L + 2) e h < alpha ^ 2 := by
      simpa using mul_lt_mul_of_pos_left hhi ha2
    exact hm.trans ha2lt

/-- Every (L+1)-event has an L-event exactly F_(L+2) integer steps earlier. -/
theorem hits_preceding_boundary (L : ℕ) (e : ℤ) :
    Hits (L + 1) e → Hits L (e - boundary L) := by
  rintro ⟨h, hlo, hhi⟩
  refine ⟨h - previous L, ?_⟩
  have hc : phaseCoordinate L (e - boundary L) (h - previous L) =
      1 - alpha * phaseCoordinate (L + 1) e h := by
    have hb := boundary_error L
    have hnum : ((e - boundary L : ℤ) : ℝ) * alpha - (h - previous L : ℤ) =
        (e : ℝ) * alpha - h + signedWidth L := by
      push_cast
      linarith
    unfold phaseCoordinate
    rw [hnum, signedWidth_succ]
    field_simp [signedWidth_ne_zero L, ne_of_gt alpha_pos] <;> ring
  rw [hc]
  have hv0 : 0 < alpha * phaseCoordinate (L + 1) e h := mul_pos alpha_pos hlo
  have hv1 : alpha * phaseCoordinate (L + 1) e h < 1 := by
    have hh : alpha * phaseCoordinate (L + 1) e h < alpha := by
      simpa using mul_lt_mul_of_pos_left hhi alpha_pos
    exact hh.trans alpha_lt_one
  constructor <;> linarith

/-- No fixed finite clock, including 60 or 64 positions, is an exact period of this rotation. -/
theorem no_nonzero_clock_period (p : ℤ) (hp : p ≠ 0) :
    ¬ ∃ q : ℤ, (p : ℝ) * alpha = q := by
  rintro ⟨q, hq⟩
  exact (alpha_irrational.intCast_mul hp).ne_int q hq

/-- The cross-layer signed separation inherits the same contracting reflection. -/
def relativeSeparation (L r : ℕ) : ℝ := signedWidth L - signedWidth (L + r)

theorem relativeSeparation_succ (L r : ℕ) :
    relativeSeparation (L + 1) r = -alpha * relativeSeparation L r := by
  unfold relativeSeparation
  rw [signedWidth_succ,
    show L + 1 + r = (L + r) + 1 by omega, signedWidth_succ]
  ring

theorem relativeSeparation_ne_zero (L r : ℕ) (hr : 0 < r) :
    relativeSeparation L r ≠ 0 := by
  intro hz
  have heq : signedWidth L = signedWidth (L + r) := sub_eq_zero.mp hz
  have habs := congrArg abs heq
  rw [signedWidth_abs, signedWidth_abs] at habs
  have hp : alpha ^ r < 1 := pow_lt_one₀ (le_of_lt alpha_pos) alpha_lt_one (by omega)
  have hpow : width (L + r) = width L * alpha ^ r := by
    unfold width
    rw [show L + r + 2 = (L + 2) + r by omega, pow_add]
  rw [hpow] at habs
  have hlt : width L * alpha ^ r < width L := by
    simpa using mul_lt_mul_of_pos_left hp (width_pos L)
  linarith

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice
