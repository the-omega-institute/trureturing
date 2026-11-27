/- GID: D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit nested-arch cylinder Pfaffian is regular on the closed integer range and reduces by a unit pair at its boundary. -/

import D5.S0.Certificates.Combinatorics.ForcedLastPairPfaffian
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators
open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation (pfaffian)
open D5.S0.Certificates.Combinatorics.NormalizedPfaffian (embed last0 last1 pfaffian_forced_last_pair)

namespace RomikRational

/-- The common denominator of the paired factors and the (5.1) summand. -/
private def denominator (x : ℚ) (a : ℕ) : ℚ := 4 * x ^ 2 - (a : ℚ) ^ 2

/-- The paired product in (4.12) and (5.1). -/
private def paired (x : ℚ) (c : ℕ) : ℚ :=
  ∏ a ∈ Finset.Ico 1 c, (x ^ 2 - (a : ℚ) ^ 2) / denominator x a

/-- The Catalan constant, in the standard binomial representation. -/
private def catalan (n : ℕ) : ℚ := (Nat.choose (2 * n) n : ℚ) / (n + 1 : ℕ)

/-- The continuation of the signed (p(N-1,N-c,0)) in (4.12). -/
private def p (x : ℚ) (c : ℕ) : ℚ :=
  ((-1 : ℚ) ^ c * (3 * (c : ℚ) - 1) * catalan (c - 1) / 2) * paired x c

/-- Equation (5.2). -/
private def X0 (a j : ℚ) : ℚ :=
  3 * a ^ 3 * (3 * j - 1) + 3 * a ^ 2 * (3 * j ^ 2 - 8 * j + 3) +
    a * (-17 * j ^ 2 + 19 * j - 6) - 2 * j * (2 * j - 1) * (j - 1)

/-- Equation (5.3). -/
private def X1 (a j : ℚ) : ℚ :=
  -12 * a ^ 3 - 6 * a ^ 2 * (4 * j - 3) -
    2 * a * (12 * j ^ 2 - 10 * j - 1) - 2 * (3 * j + 2) * (2 * j - 1) * (j - 1)

/-- Products over signed integer endpoints, including zero and the empty product. -/
private def integerProduct (lo hi : ℤ) : ℚ :=
  ∏ t ∈ Finset.Icc lo hi, (t : ℚ)

private def summand (x : ℚ) (a b j : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (j + 1) * catalan (a - 1) *
      ((j : ℚ) * X0 a j + x ^ 2 * X1 a j) * j *
      (2 * a - b - 2).factorial * (a + j - 2).factorial * (2 * j).factorial /
    (4 * (j + 1).factorial * (2 * a - j - 2).factorial * j.factorial *
      (2 * (j : ℚ) - 1))) *
    (1 / denominator x j) *
    integerProduct ((a : ℤ) - 2 * b + 2) ((a : ℤ) - 2 * j - 1) * paired x j

/-- All of the bracket in (5.1). -/
private def bracket (x : ℚ) (a b : ℕ) : ℚ :=
  ((a : ℚ) + 1) * integerProduct ((a : ℤ) - 2 * b + 2) (2 * (a : ℤ) - b - 2) +
    ∑ j ∈ Finset.Ico 1 b, summand x a b j

/-- Equation (5.1), for `1 ≤ b < a`. -/
private def Hlower (x : ℚ) (a b : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (a - 1) * (3 * (a : ℚ) - 1) * (3 * (b : ℚ) - 1) *
    ((a : ℚ) - b) / (2 * (a + b).factorial)) * paired x a * bracket x a b

/-- Proposition 5.1, with skew extension and zero diagonal. -/
private def H (x : ℚ) (a b : ℕ) : ℚ :=
  if b < a then Hlower x a b else if a < b then -Hlower x b a else 0

/-- The paper's binomial convention for an integer lower index. -/
private def binomial (n : ℕ) (i : ℤ) : ℚ :=
  if i < 0 then 0 else (Nat.choose n i.toNat : ℚ)

private def whiteIndices (r : ℕ) : Finset ℕ := Finset.Icc (r + 2) (2 * r + 2)
private def blackIndices (r : ℕ) : Finset ℕ := Finset.Icc 1 (2 * r + 2)

private def whiteWeight (r c : ℕ) : ℚ := binomial (c - 1) (2 * (r : ℤ) - c + 2)

private def blackWeight (r c : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (2 * r + 3 - c), binomial c (2 * (r : ℤ) - c - m + 2)

private def edgeDelta (r s : ℕ) : ℚ := if r = s then 1 else 0

/-- Equation (4.8). -/
private def f11 (x : ℚ) (r s : ℕ) : ℚ :=
  ∑ a ∈ whiteIndices r, ∑ b ∈ whiteIndices s, H x a b * whiteWeight r a * whiteWeight s b

/-- Equation (4.9). -/
private def f00 (x : ℚ) (r s : ℕ) : ℚ :=
  (∑ a ∈ blackIndices r, ∑ b ∈ blackIndices s, H x a b * blackWeight r a * blackWeight s b) +
    (∑ a ∈ blackIndices r, p x a * blackWeight r a) -
    (∑ b ∈ blackIndices s, p x b * blackWeight s b) -
    (Int.sign ((s : ℤ) - r) : ℚ)

/-- Equation (4.10). -/
private def f10 (x : ℚ) (r s : ℕ) : ℚ :=
  (∑ a ∈ whiteIndices r, ∑ b ∈ blackIndices s, H x a b * whiteWeight r a * blackWeight s b) +
    (∑ a ∈ whiteIndices r, p x a * whiteWeight r a) + edgeDelta r s

/-- Equation (4.11). -/
private def f01 (x : ℚ) (r s : ℕ) : ℚ := -f10 x s r

private theorem denominator_pos (k a : ℕ) (ha : a < 2 * k) :
    0 < denominator (k : ℚ) a := by
  have hl : (a : ℚ) < 2 * (k : ℚ) := by exact_mod_cast ha
  have ha0 : 0 ≤ (a : ℚ) := by exact_mod_cast (Nat.zero_le a)
  have hk0 : 0 < (k : ℚ) := by linarith
  have hm := mul_pos (sub_pos.mpr hl) (show 0 < 2 * (k : ℚ) + a by linarith)
  unfold denominator
  linarith only [show (2 * (k : ℚ) - a) * (2 * (k : ℚ) + a) =
    4 * (k : ℚ) ^ 2 - (a : ℚ) ^ 2 by ring, hm]

private theorem paired_zero (k c : ℕ) (hk : 1 ≤ k) (hkc : k < c) :
    paired (k : ℚ) c = 0 := by
  unfold paired
  exact Finset.prod_eq_zero (i := k) (Finset.mem_Ico.mpr ⟨hk, hkc⟩)
    (by rw [sub_self, zero_div])

private theorem p_zero (k c : ℕ) (hk : 1 ≤ k) (hkc : k < c) : p (k : ℚ) c = 0 := by
  simp [p, paired_zero k c hk hkc]

private theorem H_skew (x : ℚ) (a b : ℕ) : H x a b = -H x b a := by
  rcases lt_trichotomy a b with h | h | h
  · simp [H, h, not_lt_of_ge h.le]
  · subst b
    simp [H]
  · simp [H, h, not_lt_of_ge h.le]

private theorem H_zero (k a b : ℕ) (hk : 1 ≤ k) (h : k < a ∨ k < b) :
    H (k : ℚ) a b = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hkb : k < b := by omega
    simp [H, hab, not_lt_of_ge hab.le, Hlower, paired_zero k b hk hkb]
  · subst b
    simp [H]
  · have hka : k < a := by omega
    simp [H, hab, Hlower, paired_zero k a hk hka]

private theorem whiteIndices_bounds {k r c : ℕ} (hr : r < k) (hc : c ∈ whiteIndices r) :
    r + 2 ≤ c ∧ 1 ≤ c ∧ c ≤ 2 * k := by
  have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hc
  omega

private theorem blackIndices_bounds {k r c : ℕ} (hr : r < k) (hc : c ∈ blackIndices r) :
    1 ≤ c ∧ c ≤ 2 * k := by
  have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hc
  omega

private theorem f11_last_white (k s : ℕ) (hk : 1 ≤ k) :
    f11 (k : ℚ) (k - 1) s = 0 := by
  unfold f11
  apply Finset.sum_eq_zero
  intro a ha
  have hlo := (whiteIndices_bounds (k := k) (by omega) ha).1
  apply Finset.sum_eq_zero
  intro b _hb
  rw [H_zero k a b hk (Or.inl (by omega)), zero_mul, zero_mul]

private theorem f10_last_white (k s : ℕ) (hk : 1 ≤ k) :
    f10 (k : ℚ) (k - 1) s = if k - 1 = s then 1 else 0 := by
  unfold f10
  have hH : (∑ a ∈ whiteIndices (k - 1), ∑ b ∈ blackIndices s,
      H (k : ℚ) a b * whiteWeight (k - 1) a * blackWeight s b) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hlo := (whiteIndices_bounds (k := k) (by omega) ha).1
    apply Finset.sum_eq_zero
    intro b _hb
    rw [H_zero k a b hk (Or.inl (by omega)), zero_mul, zero_mul]
  have hp : (∑ a ∈ whiteIndices (k - 1), p (k : ℚ) a * whiteWeight (k - 1) a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hlo := (whiteIndices_bounds (k := k) (by omega) ha).1
    rw [p_zero k a hk (by omega), zero_mul]
  simp [hH, hp, edgeDelta]

/-- The entries of Lemma 4.3 in the order of Corollary 4.2:
(w₀, b₀, …, wₘ₋₁, bₘ₋₁). -/
def cylinderMatrix (m : ℕ) (x : ℚ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ :=
  fun i j =>
    if i.val % 2 = 0 then
      if j.val % 2 = 0 then f11 x (i.val / 2) (j.val / 2)
      else f10 x (i.val / 2) (j.val / 2)
    else
      if j.val % 2 = 0 then f01 x (i.val / 2) (j.val / 2)
      else f00 x (i.val / 2) (j.val / 2)

private theorem f11_skew (x : ℚ) (r s : ℕ) : f11 x r s = -f11 x s r := by
  unfold f11
  simp_rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [H_skew x a b]
  ring

private theorem cylinderMatrix_prefix (n : ℕ) (x : ℚ) :
    (cylinderMatrix (n + 1) x).submatrix embed embed = cylinderMatrix n x := rfl

private theorem cylinderMatrix_penultimate_zero (n : ℕ) (i : Fin (2 * n)) :
    cylinderMatrix (n + 1) (↑(n + 1) : ℚ) (embed i) (last0 n) = 0 := by
  have hi : i.val / 2 < n := by omega
  have hwhite := f11_last_white (n + 1) (i.val / 2) (by omega)
  have hblack := f10_last_white (n + 1) (i.val / 2) (by omega)
  have hne : n ≠ i.val / 2 := Nat.ne_of_gt hi
  change f11 (↑(n + 1) : ℚ) n (i.val / 2) = 0 at hwhite
  change f10 (↑(n + 1) : ℚ) n (i.val / 2) = (if n = i.val / 2 then 1 else 0) at hblack
  change (if i.val % 2 = 0 then
    if (2 * n) % 2 = 0 then f11 (↑(n + 1) : ℚ) (i.val / 2) (2 * n / 2)
    else f10 (↑(n + 1) : ℚ) (i.val / 2) (2 * n / 2)
    else if (2 * n) % 2 = 0 then f01 (↑(n + 1) : ℚ) (i.val / 2) (2 * n / 2)
    else f00 (↑(n + 1) : ℚ) (i.val / 2) (2 * n / 2)) = 0
  have hmod : (2 * n) % 2 = 0 := by omega
  have hdiv : 2 * n / 2 = n := by omega
  simp only [hmod, hdiv, ite_true]
  split
  · rw [f11_skew _ (i.val / 2) n, hwhite, neg_zero]
  · rw [f01, hblack, ite_eq_right hne, neg_zero]

private theorem cylinderMatrix_last_edge (n : ℕ) :
    cylinderMatrix (n + 1) (↑(n + 1) : ℚ) (last0 n) (last1 n) = 1 := by
  have hedge := f10_last_white (n + 1) n (by omega)
  change f10 (↑(n + 1) : ℚ) n n = (if n = n then 1 else 0) at hedge
  have h0 : (last0 n).val % 2 = 0 := by change (2 * n) % 2 = 0; omega
  have h1 : (last1 n).val % 2 ≠ 0 := by change (2 * n + 1) % 2 ≠ 0; omega
  have hd0 : (last0 n).val / 2 = n := by change (2 * n) / 2 = n; omega
  have hd1 : (last1 n).val / 2 = n := by change (2 * n + 1) / 2 = n; omega
  simpa only [cylinderMatrix, h0, h1, hd0, hd1, ite_true, ite_false] using hedge

/-- At the integer boundary the last white and black endpoints contribute a unit pair. -/
theorem cylinder_pfaffian_boundary (n : ℕ) :
    pfaffian (cylinderMatrix (n + 1) (↑(n + 1) : ℚ)) =
      pfaffian (cylinderMatrix n (↑(n + 1) : ℚ)) := by
  rw [pfaffian_forced_last_pair _ (cylinderMatrix_penultimate_zero n),
    cylinderMatrix_last_edge n, mul_one, cylinderMatrix_prefix]

noncomputable section

private theorem map_pfaffian {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :
    f (pfaffian A) = pfaffian (fun i j => f (A i j)) := by
  simp only [pfaffian, map_sum, map_mul, map_prod, map_intCast]

private theorem eval_ne_zero_of_dvd (k : ℚ) {p q : Polynomial ℚ} (h : p ∣ q)
    (hq : q.eval₂ (RingHom.id ℚ) k ≠ 0) : p.eval₂ (RingHom.id ℚ) k ≠ 0 := by
  obtain ⟨r, rfl⟩ := h
  intro hp
  apply hq
  rw [Polynomial.eval₂_mul, hp, zero_mul]

/-- Rational functions regular at the evaluation point, using the reduced denominator. -/
def regularAt (k : ℚ) : Subring (RatFunc ℚ) where
  carrier := {r | r.denom.eval₂ (RingHom.id ℚ) k ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy :=
    eval_ne_zero_of_dvd k (RatFunc.denom_add_dvd x y)
      (by rw [Polynomial.eval₂_mul]; exact mul_ne_zero hx hy)
  mul_mem' {x y} hx hy :=
    eval_ne_zero_of_dvd k (RatFunc.denom_mul_dvd x y)
      (by rw [Polynomial.eval₂_mul]; exact mul_ne_zero hx hy)
  neg_mem' {x} hx := by
    apply eval_ne_zero_of_dvd k _ hx
    apply (RatFunc.denom_dvd x.denom_ne_zero).mpr
    refine ⟨-x.num, ?_⟩
    rw [map_neg, neg_div, RatFunc.num_div_denom]

/-- The canonical RatFunc evaluation on the subring where it is a ring homomorphism. -/
private def evaluate (k : ℚ) : regularAt k →+* ℚ where
  toFun r := RatFunc.eval (RingHom.id ℚ) k r.1
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' x y := RatFunc.eval_add (RingHom.id ℚ) k x.property y.property
  map_mul' x y := RatFunc.eval_mul (RingHom.id ℚ) k x.property y.property

private def polynomialAt (k : ℚ) : Polynomial ℚ →+* regularAt k :=
  (algebraMap (Polynomial ℚ) (RatFunc ℚ)).codRestrict
    (regularAt k) (fun p => by change (RatFunc.denom _).eval₂ _ _ ≠ 0; simp)

@[simp] private theorem evaluate_polynomialAt (k : ℚ) (p : Polynomial ℚ) :
    evaluate k (polynomialAt k p) = p.eval₂ (RingHom.id ℚ) k :=
  by
    change RatFunc.eval (RingHom.id ℚ) k (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) = _
    simp [RatFunc.eval]

/-- A polynomial quotient at a point where its displayed denominator is nonzero. -/
private def quotientAt (k : ℚ) (p q : Polynomial ℚ)
    (hq : q.eval₂ (RingHom.id ℚ) k ≠ 0) : regularAt k :=
  ⟨algebraMap (Polynomial ℚ) (RatFunc ℚ) p / algebraMap (Polynomial ℚ) (RatFunc ℚ) q,
    eval_ne_zero_of_dvd k (RatFunc.denom_div_dvd p q) hq⟩

@[simp] private theorem evaluate_quotientAt (k : ℚ) (p q : Polynomial ℚ)
    (hq : q.eval₂ (RingHom.id ℚ) k ≠ 0) :
    evaluate k (quotientAt k p q hq) =
      p.eval₂ (RingHom.id ℚ) k / q.eval₂ (RingHom.id ℚ) k := by
  let r := quotientAt k p q hq
  have hq' : q ≠ 0 := by
    intro h
    exact hq (by simp [h])
  have hcross : (r : RatFunc ℚ).num * q = p * (r : RatFunc ℚ).denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hq').mpr rfl
  change (r : RatFunc ℚ).num.eval₂ (RingHom.id ℚ) k /
    (r : RatFunc ℚ).denom.eval₂ (RingHom.id ℚ) k = _
  apply (div_eq_div_iff r.property hq).mpr
  simpa only [Polynomial.eval₂_mul] using congrArg (Polynomial.eval₂ (RingHom.id ℚ) k) hcross

/-- The Pfaffian of a matrix regular at k is regular, and its canonical
evaluation is the Pfaffian of the coefficientwise evaluated matrix. -/
private theorem eval_pfaffian {n : ℕ} (k : ℚ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) (RatFunc ℚ))
    (hA : ∀ i j, A i j ∈ regularAt k) :
    pfaffian A ∈ regularAt k ∧ RatFunc.eval (RingHom.id ℚ) k (pfaffian A) =
      pfaffian (fun i j => RatFunc.eval (RingHom.id ℚ) k (A i j)) := by
  let B : Matrix (Fin (2 * n)) (Fin (2 * n)) (regularAt k) := fun i j => ⟨A i j, hA i j⟩
  have hB : ((pfaffian B : regularAt k) : RatFunc ℚ) = pfaffian A := map_pfaffian (regularAt k).subtype B
  rw [← hB]
  exact ⟨(pfaffian B).property, map_pfaffian (evaluate k) B⟩

private def normDenom (t : ℕ) : Polynomial ℚ := 4 * Polynomial.X ^ 2 - Polynomial.C (t : ℚ) ^ 2

private theorem normDenom_regular (k t : ℕ) (ht : t < 2 * k) :
    (normDenom t).eval₂ (RingHom.id ℚ) (k : ℚ) ≠ 0 := by
  simpa [normDenom, denominator, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub] using (denominator_pos k t ht).ne'

private def variableRatioAt (k t : ℕ) (ht : t < 2 * k) : regularAt (k : ℚ) :=
  quotientAt k (Polynomial.X ^ 2 - Polynomial.C (t : ℚ) ^ 2)
    (normDenom t) (normDenom_regular k t ht)

private theorem evaluate_variableRatioAt (k t : ℕ) (ht : t < 2 * k) :
    evaluate (k : ℚ) (variableRatioAt k t ht) =
      ((k : ℚ) ^ 2 - (t : ℚ) ^ 2) / (4 * (k : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
  simp [variableRatioAt, normDenom, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub]

private def prefixProduct (x : RatFunc ℚ) (c : ℕ) : RatFunc ℚ :=
  ∏ t ∈ Finset.Ico 1 c, (x ^ 2 - RatFunc.C (t : ℚ) ^ 2) / (4 * x ^ 2 - RatFunc.C (t : ℚ) ^ 2)

private theorem eval_prefixProduct (k c : ℕ) (hc : c ≤ 2 * k) :
    let r := prefixProduct RatFunc.X c
    r ∈ regularAt (k : ℚ) ∧ RatFunc.eval (RingHom.id ℚ) (k : ℚ) r =
      ∏ t ∈ Finset.Ico 1 c,
        ((k : ℚ) ^ 2 - (t : ℚ) ^ 2) / (4 * (k : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
  classical
  let P : regularAt (k : ℚ) :=
    ∏ t ∈ (Finset.Ico 1 c).attach, variableRatioAt k t
      (lt_of_lt_of_le (Finset.mem_Ico.mp t.property).2 hc)
  have hP : (P : RatFunc ℚ) = prefixProduct RatFunc.X c := by
    change (regularAt (k : ℚ)).subtype P = _
    unfold P prefixProduct
    simp only [map_prod]
    calc
      _ = ∏ t ∈ (Finset.Ico 1 c).attach,
          (RatFunc.X ^ 2 - RatFunc.C (t.val : ℚ) ^ 2) /
            (4 * RatFunc.X ^ 2 - RatFunc.C (t.val : ℚ) ^ 2) := by
        apply Finset.prod_congr rfl
        intro t _
        change algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (Polynomial.X ^ 2 - Polynomial.C (t.val : ℚ) ^ 2) /
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (normDenom t.val) = _
        simp [normDenom, map_ofNat]
      _ = _ := Finset.prod_attach (Finset.Ico 1 c) (fun t : ℕ =>
        (RatFunc.X ^ 2 - RatFunc.C (t : ℚ) ^ 2) /
          (4 * RatFunc.X ^ 2 - RatFunc.C (t : ℚ) ^ 2))
  change prefixProduct RatFunc.X c ∈ regularAt (k : ℚ) ∧ _
  rw [← hP]
  refine ⟨P.property, ?_⟩
  change evaluate (k : ℚ) P = _
  unfold P
  simp only [map_prod, evaluate_variableRatioAt]
  exact Finset.prod_attach (Finset.Ico 1 c) (fun t : ℕ =>
    ((k : ℚ) ^ 2 - (t : ℚ) ^ 2) / (4 * (k : ℚ) ^ 2 - (t : ℚ) ^ 2))

/-- The only variable-dependent denominators in Romik's formulas occur in
paired products and in the reciprocal in (5.1). -/
private inductive Formula where
  | scalar (q : ℚ)
  | square
  | paired (c : ℕ)
  | reciprocal (j : ℕ)
  | add (a b : Formula)
  | mul (a b : Formula)
  | sub (a b : Formula)
  | neg (a : Formula)
  | sum (indices : Finset ℕ) (term : ℕ → Formula)

private def Formula.interpret {R : Type*} [CommRing R]
    (C : ℚ → R) (sq : R) (P D : ℕ → R) : Formula → R
  | .scalar q => C q
  | .square => sq
  | .paired c => P c
  | .reciprocal j => D j
  | .add a b => interpret C sq P D a + interpret C sq P D b
  | .mul a b => interpret C sq P D a * interpret C sq P D b
  | .sub a b => interpret C sq P D a - interpret C sq P D b
  | .neg a => -interpret C sq P D a
  | .sum s f => ∑ j ∈ s, interpret C sq P D (f j)

private def Formula.safe (k : ℕ) : Formula → Prop
  | .scalar _ | .square => True
  | .paired c => c ≤ 2 * k
  | .reciprocal j => j < 2 * k
  | .add a b | .mul a b | .sub a b => safe k a ∧ safe k b
  | .neg a => safe k a
  | .sum s f => ∀ j ∈ s, safe k (f j)

private theorem Formula.map_interpret {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) {k : ℕ} {C : ℚ → R} {C' : ℚ → S} {sq : R} {sq' : S}
    {P D : ℕ → R} {P' D' : ℕ → S}
    (hC : ∀ q, g (C q) = C' q) (hsq : g sq = sq')
    (hP : ∀ c, c ≤ 2 * k → g (P c) = P' c)
    (hD : ∀ j, j < 2 * k → g (D j) = D' j)
    (f : Formula) (hf : f.safe k) :
    g (f.interpret C sq P D) = f.interpret C' sq' P' D' := by
  induction f with
  | scalar q => exact hC q
  | square => exact hsq
  | paired c => exact hP c hf
  | reciprocal j => exact hD j hf
  | add a b ha hb =>
      simp only [Formula.interpret, map_add, ha hf.1, hb hf.2]
  | mul a b ha hb =>
      simp only [Formula.interpret, map_mul, ha hf.1, hb hf.2]
  | sub a b ha hb =>
      simp only [Formula.interpret, map_sub, ha hf.1, hb hf.2]
  | neg a ha => simp only [Formula.interpret, map_neg, ha hf]
  | sum s f ih =>
      simp only [Formula.interpret, map_sum]
      exact Finset.sum_congr rfl (fun j hj => ih j (hf j hj))

private def variableInverse (j : ℕ) : RatFunc ℚ :=
  1 / (4 * RatFunc.X ^ 2 - RatFunc.C (j : ℚ) ^ 2)

private def localPaired (k c : ℕ) : regularAt (k : ℚ) :=
  if h : c ≤ 2 * k then ⟨prefixProduct RatFunc.X c, (eval_prefixProduct k c h).1⟩ else 0

private def localInverse (k j : ℕ) : regularAt (k : ℚ) :=
  if h : j < 2 * k then quotientAt k 1 (normDenom j) (normDenom_regular k j h) else 0

private theorem Formula.specialize (k : ℕ) (f : Formula) (hf : f.safe k) :
    let r := f.interpret RatFunc.C (RatFunc.X ^ 2) (prefixProduct RatFunc.X) variableInverse
    r ∈ regularAt (k : ℚ) ∧ RatFunc.eval (RingHom.id ℚ) (k : ℚ) r =
      f.interpret id ((k : ℚ) ^ 2) (RomikRational.paired k)
        (fun j => 1 / denominator k j) := by
  let C (q : ℚ) := polynomialAt (k : ℚ) (Polynomial.C q)
  let sq := polynomialAt (k : ℚ) (Polynomial.X ^ 2)
  let v := f.interpret C sq (localPaired k) (localInverse k)
  have hr : (regularAt (k : ℚ)).subtype v =
      f.interpret RatFunc.C (RatFunc.X ^ 2) (prefixProduct RatFunc.X) variableInverse := by
    apply f.map_interpret (k := k) (regularAt (k : ℚ)).subtype _ _ _ _ hf
    · intro q
      exact RatFunc.algebraMap_C q
    · change algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 2) = _
      simp
    · intro c hc
      simp [localPaired, hc]
    · intro j hj
      rw [localInverse, dite_eq_left hj]
      change algebraMap (Polynomial ℚ) (RatFunc ℚ) 1 /
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (normDenom j) = _
      simp [normDenom, variableInverse, map_ofNat]
  have he : evaluate (k : ℚ) v =
      f.interpret id ((k : ℚ) ^ 2) (RomikRational.paired k)
        (fun j => 1 / denominator k j) := by
    apply f.map_interpret (k := k) (evaluate (k : ℚ)) _ _ _ _ hf
    · intro q
      simp [C]
    · simp [sq]
    · intro c hc
      rw [localPaired, dite_eq_left hc]
      exact (eval_prefixProduct k c hc).2
    · intro j hj
      rw [localInverse, dite_eq_left hj]
      simp [normDenom, denominator, Polynomial.eval₂_pow,
        Polynomial.eval₂_mul, Polynomial.eval₂_sub]
  rw [← hr]
  exact ⟨v.property, he⟩

private def pFormula (c : ℕ) : Formula :=
  .mul (.scalar (((-1 : ℚ) ^ c * (3 * (c : ℚ) - 1) * catalan (c - 1) / 2))) (.paired c)

private def summandFormula (a b j : ℕ) : Formula :=
  let coefficient := (-1 : ℚ) ^ (j + 1) * catalan (a - 1)
  let linear := .add (.scalar ((j : ℚ) * X0 a j)) (.mul .square (.scalar (X1 a j)))
  let numerator := Formula.mul (.mul (.mul (.mul (.mul (.scalar coefficient) linear)
    (.scalar (j : ℚ))) (.scalar (2 * a - b - 2).factorial))
    (.scalar (a + j - 2).factorial)) (.scalar (2 * j).factorial)
  let divisor := 4 * ((j + 1).factorial : ℚ) * (2 * a - j - 2).factorial *
    j.factorial * (2 * (j : ℚ) - 1)
  let intProduct := integerProduct ((a : ℤ) - 2 * b + 2) ((a : ℤ) - 2 * j - 1)
  .mul (.mul (.mul (.mul numerator (.scalar divisor⁻¹)) (.reciprocal j))
    (.scalar intProduct)) (.paired j)

private def lowerFormula (a b : ℕ) : Formula :=
  .mul (.mul (.scalar ((-1 : ℚ) ^ (a - 1) * (3 * (a : ℚ) - 1) *
    (3 * (b : ℚ) - 1) * ((a : ℚ) - b) / (2 * (a + b).factorial))) (.paired a))
    (.add (.scalar (((a : ℚ) + 1) *
      integerProduct ((a : ℤ) - 2 * b + 2) (2 * (a : ℤ) - b - 2)))
      (.sum (Finset.Ico 1 b) (summandFormula a b)))

private def hFormula (a b : ℕ) : Formula :=
  if b < a then lowerFormula a b else if a < b then .neg (lowerFormula b a) else .scalar 0

private def weightedH (is js : Finset ℕ) (w z : ℕ → ℚ) : Formula :=
  .sum is (fun a => .sum js (fun b =>
    .mul (.mul (hFormula a b) (.scalar (w a))) (.scalar (z b))))

private def weightedP (is : Finset ℕ) (w : ℕ → ℚ) : Formula :=
  .sum is (fun a => .mul (pFormula a) (.scalar (w a)))

private def f11Formula (r s : ℕ) : Formula :=
  weightedH (whiteIndices r) (whiteIndices s) (whiteWeight r) (whiteWeight s)

private def f00Formula (r s : ℕ) : Formula :=
  .sub (.sub (.add (weightedH (blackIndices r) (blackIndices s) (blackWeight r) (blackWeight s))
    (weightedP (blackIndices r) (blackWeight r))) (weightedP (blackIndices s) (blackWeight s)))
    (.scalar (Int.sign ((s : ℤ) - r) : ℚ))

private def f10Formula (r s : ℕ) : Formula :=
  .add (.add (weightedH (whiteIndices r) (blackIndices s) (whiteWeight r) (blackWeight s))
    (weightedP (whiteIndices r) (whiteWeight r))) (.scalar (edgeDelta r s))

private def entry {m : ℕ} (i j : Fin (2 * m)) : Formula :=
  if i.val % 2 = 0 then
    if j.val % 2 = 0 then f11Formula (i.val / 2) (j.val / 2)
    else f10Formula (i.val / 2) (j.val / 2)
  else
    if j.val % 2 = 0 then .neg (f10Formula (j.val / 2) (i.val / 2))
    else f00Formula (i.val / 2) (j.val / 2)

private theorem lower_safe {k a b : ℕ} (ha : a ≤ 2 * k) (hb : b < a) :
    (lowerFormula a b).safe k := by
  simp only [lowerFormula, summandFormula, Formula.safe, true_and, and_true]
  exact ⟨ha, fun j hj => by
    have := (Finset.mem_Ico.mp hj).2
    exact ⟨by omega, by omega⟩⟩

private theorem h_safe {k a b : ℕ} (ha : a ≤ 2 * k) (hb : b ≤ 2 * k) :
    (hFormula a b).safe k := by
  unfold hFormula
  split
  · exact lower_safe ha ‹b < a›
  · split
    · exact lower_safe hb ‹a < b›
    · trivial

private theorem weightedH_safe {k : ℕ} {is js : Finset ℕ} {w z : ℕ → ℚ}
    (hi : ∀ a ∈ is, a ≤ 2 * k) (hj : ∀ b ∈ js, b ≤ 2 * k) :
    (weightedH is js w z).safe k := by
  simp only [weightedH, Formula.safe, and_true]
  exact fun a ha b hb => h_safe (hi a ha) (hj b hb)

private theorem weightedP_safe {k : ℕ} {is : Finset ℕ} {w : ℕ → ℚ}
    (hi : ∀ a ∈ is, a ≤ 2 * k) : (weightedP is w).safe k := by
  simpa only [weightedP, pFormula, Formula.safe, true_and, and_true] using hi

private theorem entry_safe {m k : ℕ} (hm : m ≤ k) (i j : Fin (2 * m)) :
    (entry i j).safe k := by
  have rib : i.val / 2 < k := by have := i.isLt; omega
  have rjb : j.val / 2 < k := by have := j.isLt; omega
  have wi : ∀ a ∈ whiteIndices (i.val / 2), a ≤ 2 * k :=
    fun _ ha => (whiteIndices_bounds rib ha).2.2
  have wj : ∀ a ∈ whiteIndices (j.val / 2), a ≤ 2 * k :=
    fun _ ha => (whiteIndices_bounds rjb ha).2.2
  have bi : ∀ a ∈ blackIndices (i.val / 2), a ≤ 2 * k :=
    fun _ ha => (blackIndices_bounds rib ha).2
  have bj : ∀ a ∈ blackIndices (j.val / 2), a ≤ 2 * k :=
    fun _ ha => (blackIndices_bounds rjb ha).2
  unfold entry
  split <;> split
  · exact weightedH_safe wi wj
  · exact ⟨⟨weightedH_safe wi bj, weightedP_safe wi⟩, trivial⟩
  · exact ⟨⟨weightedH_safe wj bi, weightedP_safe wj⟩, trivial⟩
  · exact ⟨⟨⟨weightedH_safe bi bj, weightedP_safe bi⟩, weightedP_safe bj⟩, trivial⟩

private def atPoint (x : ℚ) (f : Formula) : ℚ :=
  f.interpret id (x ^ 2) (paired x) (fun j => 1 / denominator x j)

private theorem atPoint_lower (x : ℚ) (a b : ℕ) :
    atPoint x (lowerFormula a b) = Hlower x a b := by
  simp only [atPoint, lowerFormula, summandFormula, Formula.interpret, id_eq,
    Hlower, bracket, summand, div_eq_mul_inv]

private theorem atPoint_h (x : ℚ) (a b : ℕ) : atPoint x (hFormula a b) = H x a b := by
  unfold hFormula H
  split
  · exact atPoint_lower x a b
  · split
    · change -atPoint x (lowerFormula b a) = -Hlower x b a
      rw [atPoint_lower]
    · rfl

private theorem interpret_h_atPoint (x : ℚ) (a b : ℕ) :
    (hFormula a b).interpret id (x ^ 2) (paired x) (fun j => 1 / denominator x j) =
      H x a b := atPoint_h x a b

private theorem atPoint_entry (x : ℚ) {m : ℕ} (i j : Fin (2 * m)) :
    atPoint x (entry i j) = cylinderMatrix m x i j := by
  unfold entry cylinderMatrix
  split <;> split <;>
    simp only [atPoint, f11Formula, f00Formula, f10Formula, weightedH, weightedP,
      pFormula, Formula.interpret, id_eq, f11, f00, f10, f01, p, interpret_h_atPoint]

/-- The cylinder matrix over ℚ(X), with entries from (4.8)–(4.12) and (5.1)–(5.3). -/
private def rationalCylinderMatrix (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) (RatFunc ℚ) :=
  fun i j => (entry i j).interpret RatFunc.C (RatFunc.X ^ 2)
    (prefixProduct RatFunc.X) variableInverse

/-- The explicit Pfaffian as a rational function. -/
def rationalCylinder (m : ℕ) : RatFunc ℚ := pfaffian (rationalCylinderMatrix m)

/-- The explicit Pfaffian is regular at every integer k ≥ m. Its canonical
evaluation is the Pfaffian of the published formulas evaluated at k. -/
theorem evaluate_rationalCylinder (m k : ℕ) (hm : m ≤ k) :
    rationalCylinder m ∈ regularAt (k : ℚ) ∧
      RatFunc.eval (RingHom.id ℚ) (k : ℚ) (rationalCylinder m) =
        pfaffian (cylinderMatrix m (k : ℚ)) := by
  have he (i j : Fin (2 * m)) :=
    (entry i j).specialize k (entry_safe hm i j)
  have h := eval_pfaffian (k : ℚ) (rationalCylinderMatrix m) (fun i j => (he i j).1)
  refine ⟨h.1, h.2.trans (congrArg pfaffian ?_)⟩
  funext i j
  exact (he i j).2.trans (atPoint_entry (k : ℚ) i j)

end
end RomikRational
