import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/- Source candidate only. No elaboration or kernel acceptance is asserted. -/
set_option autoImplicit false
namespace D5.S0.Certificates.BoxCover.QuadraticCorner

/-- A recursive polynomial, quadratic in its first variable with constant
square coefficient. Every total-degree-two polynomial has this representation. -/
inductive Poly : Nat → Type where
  | scalar (c : ℚ) : Poly 0
  | step {n : Nat} (c l : Poly n) (d : ℚ) : Poly (n+1)
  deriving DecidableEq

def constant : (n : Nat) → ℚ → Poly n
  | 0, c => .scalar c
  | n+1, c => .step (constant n c) (constant n 0) 0

def add : {n : Nat} → Poly n → Poly n → Poly n
  | 0, .scalar a, .scalar b => .scalar (a+b)
  | _+1, .step a b d, .step c e f => .step (add a c) (add b e) (d+f)

def scale : {n : Nat} → ℚ → Poly n → Poly n
  | 0, t, .scalar a => .scalar (t*a)
  | _+1, t, .step a b d => .step (scale t a) (scale t b) (t*d)

noncomputable def value : {n : Nat} → Poly n → (Fin n → ℝ) → ℝ
  | 0, .scalar c, _ => c
  | _+1, .step c l d, x =>
      value c (Fin.tail x) + x 0 * value l (Fin.tail x) + (d : ℝ)*(x 0)^2

@[simp] theorem value_constant (n : Nat) (c : ℚ) (x : Fin n → ℝ) :
    value (constant n c) x = c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [constant, value, ih]

@[simp] theorem value_add {n : Nat} (p q : Poly n) (x : Fin n → ℝ) :
    value (add p q) x = value p x + value q x := by
  induction p with
  | scalar c => cases q; simp [add, value]
  | step c l d ihc ihl =>
      cases q
      simp only [add, value, ihc, ihl, Rat.cast_add]
      ring

@[simp] theorem value_scale {n : Nat} (t : ℚ) (p : Poly n) (x : Fin n → ℝ) :
    value (scale t p) x = (t : ℝ)*value p x := by
  induction p with
  | scalar c => simp [scale, value]
  | step c l d ihc ihl =>
      simp only [scale, value, ihc, ihl, Rat.cast_mul]
      ring

def at_coord {n : Nat} (c l : Poly n) (d t : ℚ) : Poly n :=
  add (add c (scale t l)) (constant n (d*t^2))

@[simp] theorem value_at {n : Nat} (c l : Poly n) (d t : ℚ) (x : Fin n → ℝ) :
    value (at_coord c l d t) x = value c x + (t : ℝ)*value l x + (d : ℝ)*(t : ℝ)^2 := by
  simp [at_coord]

/-- The exact one-variable diagonal correction; closed endpoints and zero
width are included. This is the only nonlinear enclosure argument. -/
theorem quadratic_lower (c l d lo hi x L : ℝ)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (h0 : L ≤ c+l*lo+d*lo^2) (h1 : L ≤ c+l*hi+d*hi^2) :
    L - max d 0*(hi-lo)^2/4 ≤ c+l*x+d*x^2 := by
  have hw : 0 ≤ hi-lo := by linarith
  have hz : (x-lo)*(x-hi) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx0) (sub_nonpos.mpr hx1)
  have hz' : -(hi-lo)^2/4 ≤ (x-lo)*(x-hi) := by
    nlinarith [sq_nonneg (x-(lo+hi)/2)]
  have hc : -(max d 0)*(hi-lo)^2/4 ≤ d*((x-lo)*(x-hi)) := by
    by_cases hd : 0 ≤ d
    · rw [max_eq_left hd]
      nlinarith [mul_le_mul_of_nonneg_left hz' hd]
    · rw [max_eq_right (le_of_not_ge hd)]
      simpa using mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hd) hz
  by_cases he : lo = hi
  · have hxe : x = lo := by linarith
    subst hi; subst x
    simpa using h0
  · have hw' : 0 < hi-lo := sub_pos.mpr (lt_of_le_of_ne (hx0.trans hx1) he)
    have hweighted := add_le_add
      (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hx1))
      (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hx0))
    have hinterp : L ≤ c+l*x+d*x^2-d*((x-lo)*(x-hi)) := by
      apply (mul_le_mul_iff_left₀ hw').mp
      nlinarith only [hweighted]
    linarith

theorem quadratic_upper (c l d lo hi x U : ℝ)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (h0 : c+l*lo+d*lo^2 ≤ U) (h1 : c+l*hi+d*hi^2 ≤ U) :
    c+l*x+d*x^2 ≤ U + max (-d) 0*(hi-lo)^2/4 := by
  have h := quadratic_lower (-c) (-l) (-d) lo hi x (-U) hx0 hx1
    (by linarith) (by linarith)
  linarith

abbrev Box (n : Nat) := Fin n → ℚ × ℚ

def lower : {n : Nat} → Poly n → Box n → ℚ
  | 0, .scalar c, _ => c
  | _+1, .step c l d, b =>
      min (lower (at_coord c l d (b 0).1) (Fin.tail b))
          (lower (at_coord c l d (b 0).2) (Fin.tail b)) -
        max d 0*((b 0).2-(b 0).1)^2/4

def upper : {n : Nat} → Poly n → Box n → ℚ
  | 0, .scalar c, _ => c
  | _+1, .step c l d, b =>
      max (upper (at_coord c l d (b 0).1) (Fin.tail b))
          (upper (at_coord c l d (b 0).2) (Fin.tail b)) +
        max (-d) 0*((b 0).2-(b 0).1)^2/4

def Inside {n : Nat} (b : Box n) (x : Fin n → ℝ) : Prop :=
  ∀ i, ((b i).1 : ℝ) ≤ x i ∧ x i ≤ ((b i).2 : ℝ)

/-- Kernel-oriented enclosure for every real point, with no positivity premise
on the polynomial and no external evaluator in the hypotheses. -/
theorem encloses {n : Nat} (p : Poly n) (b : Box n) (x : Fin n → ℝ)
    (hx : Inside b x) : (lower p b : ℝ) ≤ value p x ∧ value p x ≤ (upper p b : ℝ) := by
  induction n with
  | zero => cases p; exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
      cases p with
      | step c l d =>
          have ht : Inside (Fin.tail b) (Fin.tail x) := fun i => hx i.succ
          have h0 := ih (at_coord c l d (b 0).1) (Fin.tail b) (Fin.tail x) ht
          have h1 := ih (at_coord c l d (b 0).2) (Fin.tail b) (Fin.tail x) ht
          simp only [value_at, mul_comm] at h0 h1
          constructor
          · have h := quadratic_lower (value c (Fin.tail x)) (value l (Fin.tail x))
              (d : ℝ) ((b 0).1 : ℝ) ((b 0).2 : ℝ) (x 0)
              (min (lower (at_coord c l d (b 0).1) (Fin.tail b) : ℝ)
                (lower (at_coord c l d (b 0).2) (Fin.tail b) : ℝ))
              (hx 0).1 (hx 0).2
              ((min_le_left _ _).trans (by nlinarith only [h0.1]))
              ((min_le_right _ _).trans (by nlinarith only [h1.1]))
            simpa [lower, value, Rat.cast_min, Rat.cast_max, mul_comm] using h
          · have h := quadratic_upper (value c (Fin.tail x)) (value l (Fin.tail x))
              (d : ℝ) ((b 0).1 : ℝ) ((b 0).2 : ℝ) (x 0)
              (max (upper (at_coord c l d (b 0).1) (Fin.tail b) : ℝ)
                (upper (at_coord c l d (b 0).2) (Fin.tail b) : ℝ))
              (hx 0).1 (hx 0).2
              (le_trans (by nlinarith only [h0.2]) (le_max_left _ _))
              (le_trans (by nlinarith only [h1.2]) (le_max_right _ _))
            simpa [upper, value, Rat.cast_min, Rat.cast_max, mul_comm] using h

end D5.S0.Certificates.BoxCover.QuadraticCorner
