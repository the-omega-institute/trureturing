/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scalar positivity certificates for the three-dimensional refined BMV bounds. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreePackedCheck
import D5.S3.Quantum.Analysis.RefinedBMVDimThreeSize
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Ordered scalar certificates for the dimension-three refined BMV bounds -/

namespace RefinedBMV.DimThree

open Certificate

open scoped BigOperators

variable {R : Type*} [CommRing R]

private def Certificate.Term.eval (s t u : R) (a : Term) : R :=
  (a.coefficient : R) * s ^ a.exponents.1 * t ^ a.exponents.2.1 * u ^ a.exponents.2.2

private theorem Certificate.Term.eval_mul (s t u : R) (a b : Term) :
    (a.mul b).eval s t u = a.eval s t u * b.eval s t u := by
  simp only [Term.eval, Term.mul, Int.cast_mul, pow_add]
  ring

private theorem Certificate.Term.eval_neg (s t u : R) (a : Term) :
    a.neg.eval s t u = -a.eval s t u := by
  simp [Term.eval, Term.neg]

private def evalTerms (s t u : R) (xs : List Term) : R :=
  (xs.map (Term.eval s t u)).sum

private def Certificate.Sparse.eval (s t u : R) (p : Sparse) : R :=
  evalTerms s t u p.terms

private theorem evalTerms_merge (s t u : R) (xs ys : List Term) :
    evalTerms s t u (mergeTerms xs ys) = evalTerms s t u xs + evalTerms s t u ys := by
  induction xs generalizing ys with
  | nil => simp [mergeTerms, evalTerms]
  | cons x xs ih =>
    change evalTerms s t u (mergeInsert x xs (mergeTerms xs) ys) =
      evalTerms s t u (x :: xs) + evalTerms s t u ys
    induction ys with
    | nil => simp [mergeInsert, evalTerms]
    | cons y ys jh =>
      rw [mergeInsert]
      split
      · rename_i h
        change _ + evalTerms s t u (mergeTerms xs ys) = _
        rw [ih]
        simp only [evalTerms, List.map_cons, List.sum_cons, Term.eval, Int.cast_add, ← h]
        ring
      · split
        · change _ + evalTerms s t u (mergeTerms xs (y :: ys)) = _
          rw [ih]
          simp only [evalTerms, List.map_cons, List.sum_cons]
          ring
        · change y.eval s t u + evalTerms s t u (mergeInsert x xs (mergeTerms xs) ys) = _
          rw [jh]
          simp only [evalTerms, List.map_cons, List.sum_cons]
          ring

private theorem evalTerms_map_mul (s t u : R) (x : Term) (ys : List Term) :
    evalTerms s t u (ys.map (Term.mul x)) = x.eval s t u * evalTerms s t u ys := by
  induction ys with
  | nil => simp [evalTerms]
  | cons y ys ih =>
    simp only [evalTerms, List.map_cons, List.sum_cons] at *
    rw [Term.eval_mul, ih, mul_add]

private theorem eval_mergePairs (s t u : R) (ps : List (List Term)) :
    ((mergePairs ps).map (evalTerms s t u)).sum = (ps.map (evalTerms s t u)).sum := by
  match ps with
  | [] => rfl
  | [_] => rfl
  | xs :: ys :: rest =>
    simp only [mergePairs, List.map_cons, List.sum_cons, eval_mergePairs s t u rest,
      evalTerms_merge, add_assoc]
termination_by structural ps

private theorem eval_mergeProducts (s t u : R) (k : ℕ) (ps : List (List Term)) :
    evalTerms s t u (mergeProducts k ps) = (ps.map (evalTerms s t u)).sum := by
  induction k generalizing ps with
  | zero =>
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      change evalTerms s t u (mergeTerms p (mergeProducts 0 ps)) =
        evalTerms s t u p + (ps.map (evalTerms s t u)).sum
      rw [evalTerms_merge, ih]
  | succ k ih =>
    rcases ps with _ | ⟨p, _ | ⟨q, ps⟩⟩
    · rfl
    · simp [mergeProducts]
    · rw [mergeProducts, ih, eval_mergePairs]

private theorem eval_multiply (s t u : R) (xs ys : List Term) :
    evalTerms s t u (multiply xs ys) = evalTerms s t u xs * evalTerms s t u ys := by
  rw [multiply, eval_mergeProducts, List.map_map]
  simp only [Function.comp_def, evalTerms_map_mul]
  induction xs with
  | nil => simp [evalTerms]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at *
    change x.eval s t u * evalTerms s t u ys +
      (List.map (fun x => x.eval s t u * evalTerms s t u ys) xs).sum =
        (x.eval s t u + evalTerms s t u xs) * evalTerms s t u ys
    rw [ih, add_mul]

private theorem evalTerms_neg (s t u : R) (xs : List Term) :
    evalTerms s t u (xs.map Term.neg) = -evalTerms s t u xs := by
  induction xs with
  | nil => simp [evalTerms]
  | cons x xs ih =>
    simp only [evalTerms, List.map_cons, List.sum_cons] at *
    rw [Term.eval_neg, ih, neg_add]

private theorem eval_zero (s t u : R) : (0 : Sparse).eval s t u = 0 := rfl

private theorem eval_cast (s t u : R) (n : ℕ) : (n : Sparse).eval s t u = n := by
  change evalTerms s t u (Sparse.constant n).terms = _
  simp [evalTerms, Sparse.constant, Term.eval]

private theorem eval_add (s t u : R) (p q : Sparse) :
    (p + q).eval s t u = p.eval s t u + q.eval s t u :=
  evalTerms_merge s t u p.terms q.terms

private theorem eval_sub (s t u : R) (p q : Sparse) :
    (p - q).eval s t u = p.eval s t u - q.eval s t u := by
  change evalTerms s t u (mergeTerms p.terms (q.terms.map Term.neg)) =
    evalTerms s t u p.terms - evalTerms s t u q.terms
  rw [evalTerms_merge, evalTerms_neg, sub_eq_add_neg]

private theorem eval_mul (s t u : R) (p q : Sparse) :
    (p * q).eval s t u = p.eval s t u * q.eval s t u :=
  eval_multiply s t u p.terms q.terms

private theorem eval_pow (s t u : R) (p : Sparse) (n : ℕ) :
    (p ^ n).eval s t u = p.eval s t u ^ n := by
  induction n with
  | zero =>
    change (Sparse.constant 1).eval s t u = _
    rw [pow_zero]
    have h := eval_cast s t u 1
    change (Sparse.constant 1).eval s t u = (↑(1 : ℕ) : R) at h
    simpa only [Nat.cast_one] using h
  | succ n ih =>
    change ((p ^ n) * p).eval s t u = _
    rw [eval_mul, ih, pow_succ]

private theorem eval_sum (s t u : R) (ps : List Sparse) :
    ps.sum.eval s t u = (ps.map (Sparse.eval s t u)).sum := by
  induction ps with
  | nil => exact eval_zero s t u
  | cons p ps ih => simp only [List.sum_cons, eval_add, ih, List.map_cons]

private theorem eval_defect (s t u : R) (p : ℕ) (a b c : Sparse) :
    (defect p a b c).eval s t u = defect p (a.eval s t u) (b.eval s t u) (c.eval s t u) := by
  simp [defect, eval_sub, eval_mul, eval_pow, eval_cast, eval_sum, List.map_map, Function.comp_def]

private theorem eval_criterion (s t u : R) (p : ℕ) (a b c : Sparse) :
    (criterion p a b c).eval s t u = criterion p (a.eval s t u) (b.eval s t u) (c.eval s t u) := by
  simp only [criterion, eval_defect, eval_pow, eval_add, eval_sub, eval_mul, eval_cast]

private theorem eval_orderedPolynomial (p : ℕ) (s t u : R) :
    (orderedPolynomial p).eval s t u = criterion p s (s + t) (s + t + u) := by
  simp only [orderedPolynomial, eval_criterion, eval_add]
  simp [Sparse.eval, evalTerms, Term.eval]

private def key (d : ℕ) (m : Term) : ℕ :=
  m.exponents.2.1 + (d + 1) * m.exponents.2.2

private def column (d j : ℕ) (xs : List Term) : ℤ :=
  (xs.map fun m => if key d m = j then m.coefficient else 0).sum

private theorem column_abs_bound (d j : ℕ) (xs : List Term) :
    (column d j xs).natAbs ≤ (xs.map fun m => m.coefficient.natAbs).sum := by
  induction xs with
  | nil => simp [column]
  | cons x xs ih =>
    by_cases h : key d x = j
    · simp only [column, List.map_cons, List.sum_cons, ite_eq_left h]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
    · simp only [column, List.map_cons, List.sum_cons, ite_eq_right h, zero_add]
      exact ih.trans (Nat.le_add_left _ _)

private theorem key_lt {d : ℕ} {m : Term}
    (hm : m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d) :
    key d m < d * (d + 1) + 1 := by
  unfold key
  have hu : m.exponents.2.2 ≤ d := by omega
  have htu : m.exponents.2.1 ≤ d - m.exponents.2.2 := by omega
  have hh : m.exponents.2.1 + (d + 1) * m.exponents.2.2 ≤
      d - m.exponents.2.2 + (d + 1) * m.exponents.2.2 :=
    Nat.add_le_add_right htu _
  have he : d - m.exponents.2.2 + (d + 1) * m.exponents.2.2 =
      d * (m.exponents.2.2 + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  rw [he] at hh
  exact Nat.lt_succ_of_le (hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hu _)))

private theorem key_div {d : ℕ} {m : Term}
    (hm : m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d) :
    key d m / (d + 1) = m.exponents.2.2 := by
  unfold key
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]

private theorem key_mod {d : ℕ} {m : Term}
    (hm : m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d) :
    key d m % (d + 1) = m.exponents.2.1 := by
  unfold key
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem sum_columns {R : Type*} [CommRing R] (d L : ℕ) (xs : List Term)
    (v : ℕ → R) (hkey : ∀ m ∈ xs, key d m < L) :
    ∑ j ∈ Finset.range L, (column d j xs : R) * v j =
      (xs.map fun m => (m.coefficient : R) * v (key d m)).sum := by
  induction xs with
  | nil => simp [column]
  | cons m xs ih =>
    have hhead := hkey m (by simp)
    have htail : ∀ x ∈ xs, key d x < L := fun x hx => hkey x (by simp [hx])
    simp only [column, List.map_cons, List.sum_cons, Int.cast_add, add_mul,
      Finset.sum_add_distrib, Int.cast_ite, Int.cast_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_range.mpr hhead, ite_true]
    exact congrArg (fun x => (m.coefficient : R) * v (key d m) + x)
      (by simpa only [column] using ih htail)

private theorem packSigned_range (b : ℤ) (f : ℕ → ℤ) (n : ℕ) :
    PackedCheck.packSigned b ((List.range n).map f) =
      ∑ j ∈ Finset.range n, f j * b ^ j := by
  induction n generalizing f with
  | zero => simp [PackedCheck.packSigned]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, PackedCheck.packSigned, ih,
      Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one]
    rw [add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.comp_def, pow_succ]
    ring

private theorem packed_repunit (n b h : ℕ) (hb : 0 < b) :
    PackedCheck.packDigits b (List.replicate n h) * (b - 1) = h * (b ^ n - 1) := by
  induction n with
  | zero => simp [PackedCheck.packDigits]
  | succ n ih =>
    rw [List.replicate_succ, PackedCheck.packDigits, add_mul, mul_assoc, ih, pow_succ']
    calc
      _ = h * ((b - 1) + b * (b ^ n - 1)) := by ring
      _ = _ := by
        rw [Nat.mul_sub, mul_one]
        have hh : b ≤ b * b ^ n := Nat.le_mul_of_pos_right _ (Nat.pow_pos hb)
        congr 1
        omega

private theorem mask_eq_repunit (w d : ℕ) :
    PackedCheck.centeredMask w d = PackedCheck.packDigits (2 ^ (w + 1))
      (List.replicate (d * (d + 1) + 1) (2 ^ w)) := by
  unfold PackedCheck.centeredMask
  have hb : 0 < 2 ^ (w + 1) - 1 := by
    rw [Nat.pow_succ]
    have h := Nat.pow_pos (by decide : 0 < 2) (n := w)
    omega
  rw [← packed_repunit _ _ _ (by positivity), Nat.mul_div_cancel _ hb]

private theorem column_digit_nonneg
    {d w : ℕ} {xs : List Term} {encoded : ℤ}
    (hnorm : (xs.map fun m => m.coefficient.natAbs).sum < 2 ^ w)
    (hpacked : PackedCheck.packSigned ↑(2 ^ (w + 1) : ℕ)
      ((List.range (d * (d + 1) + 1)).map (fun j => column d j xs)) = encoded)
    (hcheck : (encoded + ↑(PackedCheck.centeredMask w d)).toNat &&&
      PackedCheck.centeredMask w d = PackedCheck.centeredMask w d) :
    ∀ j < d * (d + 1) + 1, 0 ≤ column d j xs := by
  let cs := (List.range (d * (d + 1) + 1)).map (fun j => column d j xs)
  change PackedCheck.packSigned _ cs = encoded at hpacked
  have hbound : ∀ c ∈ cs, -((2 ^ w : ℕ) : ℤ) ≤ c ∧ c < ((2 ^ w : ℕ) : ℤ) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    have hle := (column_abs_bound d j xs).trans_lt hnorm
    have h1 : column d j xs ≤ ↑(column d j xs).natAbs := Int.le_natAbs
    have h2 : -(column d j xs) ≤ ↑(column d j xs).natAbs := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(column d j xs)))
    omega
  have hlen : cs.length = d * (d + 1) + 1 := by simp [cs]
  have hshift := PackedCheck.packDigits_shift (2 ^ (w + 1)) (2 ^ w) cs (fun c hc => (hbound c hc).1)
  have hmask := mask_eq_repunit w d
  have htest : PackedCheck.packDigits (2 ^ (w + 1))
        (cs.map fun c => (c + ↑(2 ^ w : ℕ)).toNat) &&&
      PackedCheck.packDigits (2 ^ (w + 1)) (List.replicate cs.length (2 ^ w)) =
        PackedCheck.packDigits (2 ^ (w + 1)) (List.replicate cs.length (2 ^ w)) := by
    let n := PackedCheck.packDigits (2 ^ (w + 1)) (cs.map fun c => (c + ↑(2 ^ w : ℕ)).toNat)
    have hn : (n : ℤ) = encoded + ↑(PackedCheck.centeredMask w d) := by
      rw [show (n : ℤ) = _ by exact hshift, hpacked, hlen, ← hmask]
    rw [hlen, ← hmask]
    change n &&& PackedCheck.centeredMask w d = _
    calc
      _ = (n : ℤ).toNat &&& PackedCheck.centeredMask w d := rfl
      _ = _ := by rw [hn]; exact hcheck
  intro j hj
  exact PackedCheck.digit_signs_of_mask w cs hbound htest _ (List.mem_map.mpr
    ⟨j, List.mem_range.mpr hj, rfl⟩)

private theorem encode_columns (d : ℕ) (b : ℤ) (xs : List Term)
    (hdegree : ∀ m ∈ xs, m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d) :
    PackedCheck.packSigned b
      ((List.range (d * (d + 1) + 1)).map (fun j => column d j xs)) =
        evalTerms (1 : ℤ) b (b ^ (d + 1)) xs := by
  rw [packSigned_range]
  have h := sum_columns (R := ℤ) d (d * (d + 1) + 1) xs
    (fun j => b ^ j) (fun m hm => key_lt (hdegree m hm))
  change ∑ j ∈ Finset.range (d * (d + 1) + 1), column d j xs * b ^ j =
    (xs.map fun m => m.coefficient * b ^ key d m).sum at h
  rw [h]
  unfold evalTerms
  congr 1
  apply List.map_congr_left
  intro m hm
  unfold key Term.eval
  simp only [Int.cast_id, id_def, one_pow, mul_one, pow_add, pow_mul, mul_assoc]

private theorem real_eval_nonneg {d : ℕ} {xs : List Term} {s t u : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hdegree : ∀ m ∈ xs, m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d)
    (hnn : ∀ j < d * (d + 1) + 1, 0 ≤ column d j xs) :
    0 ≤ evalTerms s t u xs := by
  let v := fun j : ℕ =>
    s ^ (d - j % (d + 1) - j / (d + 1)) * t ^ (j % (d + 1)) * u ^ (j / (d + 1))
  have he : evalTerms s t u xs =
      ∑ j ∈ Finset.range (d * (d + 1) + 1), (column d j xs : ℝ) * v j := by
    rw [sum_columns d _ _ _ (fun m hm => key_lt (hdegree m hm))]
    unfold evalTerms
    congr 1
    apply List.map_congr_left
    intro m hm
    have hd := hdegree m hm
    simp only [v, key_div hd, key_mod hd, Term.eval, show
      d - m.exponents.2.1 - m.exponents.2.2 = m.exponents.1 by omega]
    ring
  rw [he]
  refine Finset.sum_nonneg fun j hj => mul_nonneg
    (Int.cast_nonneg (hnn _ (Finset.mem_range.mp hj))) ?_
  dsimp [v]
  positivity

/-- The coefficient bounds and the packed sign comparison imply ordered scalar positivity. -/
theorem criterion_nonneg_ordered (p : ℕ) (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ criterion p a b c := by
  let w := digitBits p
  let d := 12 * p
  let base : ℕ := 2 ^ (w + 1)
  let xs := (orderedPolynomial p).terms
  have hd : ∀ m ∈ xs, m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d :=
    ordered_degree p
  have hn : (xs.map fun m => m.coefficient.natAbs).sum < 2 ^ w := ordered_norm_lt p hp
  have hpacked := encode_columns d (base : ℤ) xs hd
  change _ = (orderedPolynomial p).eval (1 : ℤ) base ((base : ℤ) ^ (d + 1)) at hpacked
  rw [eval_orderedPolynomial] at hpacked
  have hc : PackedCheck.maskCheck p w = true := by
    rcases hp with rfl | rfl | rfl
    · exact PackedCheck.mask_check_five
    · exact PackedCheck.mask_check_six
    · exact PackedCheck.mask_check_seven
  have hmask :
      (PackedCheck.centeredCriterion p w).toNat &&& PackedCheck.centeredMask w d =
        PackedCheck.centeredMask w d :=
    beq_iff_eq.mp (show (((PackedCheck.centeredCriterion p w).toNat &&&
      PackedCheck.centeredMask w d) == PackedCheck.centeredMask w d) = true from hc)
  have hn' := column_digit_nonneg hn hpacked (by
    simpa only [PackedCheck.centeredCriterion, Int.natCast_pow, base, d] using hmask)
  have h := real_eval_nonneg ha (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc) hd hn'
  change 0 ≤ (orderedPolynomial p).eval a (b - a) (c - b) at h
  simpa only [eval_orderedPolynomial, show a + (b - a) = b by ring,
    show b + (c - b) = c by ring] using h

#print axioms criterion_nonneg_ordered

end RefinedBMV.DimThree
