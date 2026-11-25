/- GID: D5/S3/Arith/Divisors/ErdosNicolas/PairChecker
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00.chunk_checked
   digest: Integer rounding certificates for complete reciprocal gap sums. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Basic

/-! All pairs are generated internally from the complete divisor list. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Upward integer rounding; denominators used by the checker are positive. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Ordered-pair integer sum, retaining exactly the increasing orientation. -/
def pairNat (c : ℕ → ℕ) (ds : List ℕ) : ℕ :=
  (ds.map fun x => (ds.map fun y => if x < y then c (y - x) else 0).sum).sum

/-- Rational version of the same exhaustive traversal. -/
def pairRat (ds : List ℕ) : ℚ :=
  (ds.map fun x => (ds.map fun y =>
    if x < y then ((y - x : ℕ) : ℚ)⁻¹ else 0).sum).sum

/-- Rounded upper sum; there is no caller-supplied pair list. -/
def pairUpper (Q : ℕ) (ds : List ℕ) : ℕ := pairNat (ceilDiv Q) ds

/-- Rounded lower sum for the exceptional lower inequality. -/
def pairLower (Q : ℕ) (ds : List ℕ) : ℕ := pairNat (Q / ·) ds

private theorem ceilDiv_mul_ge (a b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  have hmod := Nat.mod_lt (a + b - 1) hb
  have hdiv := Nat.mod_add_div (a + b - 1) b
  unfold ceilDiv
  rw [Nat.mul_comm b] at hdiv
  omega

private theorem floor_reciprocal_le (Q g : ℕ) (hg : 0 < g) :
    (Q / g : ℕ) ≤ (Q : ℚ) * (g : ℚ)⁻¹ := by
  have h := Nat.div_mul_le_self Q g
  have h' : ((Q / g : ℕ) : ℚ) * g ≤ Q := by exact_mod_cast h
  exact (le_div_iff₀ (by exact_mod_cast hg)).mpr h'

theorem reciprocal_le_ceil (Q g : ℕ) :
    (Q : ℚ) * (g : ℚ)⁻¹ ≤ ceilDiv Q g := by
  by_cases hg : g = 0
  · simp [hg, ceilDiv]
  have hg : 0 < g := Nat.pos_of_ne_zero hg
  have h' : (Q : ℚ) ≤ (ceilDiv Q g : ℚ) * g := by
    exact_mod_cast ceilDiv_mul_ge Q g hg
  exact (div_le_iff₀ (by exact_mod_cast hg)).mpr h'

private theorem sum_cast (xs : List ℕ) :
    ((xs.sum : ℕ) : ℚ) = (xs.map (Nat.cast : ℕ → ℚ)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem sum_scale (xs : List ℚ) (Q : ℚ) :
    Q * xs.sum = (xs.map (Q * ·)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [mul_add, ih]

private theorem sum_compare (xs : List ℕ) (f g : ℕ → ℚ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private theorem sum_list_finset (xs : List ℕ) (hx : xs.Nodup) (f : ℕ → ℚ) :
    (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := List.nodup_cons.mp hx
    simp [List.toFinset_cons, h.1, ih h.2]

theorem pairRat_eq_pairSum (ds : List ℕ) (hd : ds.Nodup) :
    pairRat ds = pairSum ds.toFinset := by
  unfold pairRat pairSum
  rw [sum_list_finset ds hd]
  exact Finset.sum_congr rfl fun x _ => sum_list_finset ds hd _

private theorem pair_rounding_bounds (Q : ℕ) (ds : List ℕ) :
    (pairLower Q ds : ℚ) ≤ Q * pairRat ds ∧
      (Q : ℚ) * pairRat ds ≤ pairUpper Q ds := by
  have point (x y : ℕ) :
      ((if x < y then Q / (y - x) else 0 : ℕ) : ℚ) ≤
        (Q : ℚ) * (if x < y then ((y - x : ℕ) : ℚ)⁻¹ else 0) ∧
      (Q : ℚ) * (if x < y then ((y - x : ℕ) : ℚ)⁻¹ else 0) ≤
        ((if x < y then ceilDiv Q (y - x) else 0 : ℕ) : ℚ) := by
    split_ifs with h
    · exact ⟨floor_reciprocal_le Q _ (Nat.sub_pos_of_lt h),
        reciprocal_le_ceil Q _⟩
    · simp
  unfold pairLower pairUpper pairNat pairRat
  simp only [sum_cast, List.map_map, Function.comp_def, sum_scale]
  constructor
  · apply sum_compare
    intro x _
    exact sum_compare ds _ _ fun y _ => (point x y).1
  · apply sum_compare
    intro x _
    exact sum_compare ds _ _ fun y _ => (point x y).2

/-- Upper comparison using an independently certified complete divisor table. -/
theorem hHat_lt_of_pairUpper {n Q t : ℕ} {ds : List ℕ}
    (hQ : 0 < Q) (hd : ds.Nodup) (he : ds.toFinset = n.divisors)
    (ht : n.divisors.card = t) (h : pairUpper Q ds < Q * t) : hHat n < (n.divisors.card : ℚ) := by
  have hb := (pair_rounding_bounds Q ds).2
  rw [pairRat_eq_pairSum ds hd, he] at hb
  have hh : (pairUpper Q ds : ℚ) < (Q : ℚ) * t := by exact_mod_cast h
  rw [ht]
  change hHat n < (t : ℚ)
  have hq : (0 : ℚ) < Q := by exact_mod_cast hQ
  change (Q : ℚ) * hHat n ≤ _ at hb
  nlinarith

/-- The two rounded strict comparisons certify both exceptional inequalities. -/
theorem exceptional_of_pairBounds {n Q t : ℕ} {ds : List ℕ}
    (hQ : 0 < Q) (hd : ds.Nodup) (he : ds.toFinset = n.divisors)
    (ht : n.divisors.card = t) (hlo : Q * t < pairLower Q ds)
    (hhi : 7 * pairUpper Q ds < 8 * Q * t) :
    (n.divisors.card : ℚ) < hHat n ∧ 7 * hHat n < 8 * (n.divisors.card : ℚ) := by
  obtain ⟨hl, hu⟩ := pair_rounding_bounds Q ds
  rw [pairRat_eq_pairSum ds hd, he] at hl hu
  change (pairLower Q ds : ℚ) ≤ (Q : ℚ) * hHat n at hl
  change (Q : ℚ) * hHat n ≤ (pairUpper Q ds : ℚ) at hu
  have hlo' : (Q : ℚ) * t < pairLower Q ds := by exact_mod_cast hlo
  have hhi' : (7 : ℚ) * pairUpper Q ds < 8 * Q * t := by exact_mod_cast hhi
  have hq : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [ht]
  constructor <;> nlinarith

#print axioms pair_rounding_bounds
#print axioms hHat_lt_of_pairUpper
#print axioms exceptional_of_pairBounds

end D5.S3.Arith.ErdosNicolas
