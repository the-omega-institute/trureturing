/- GID: D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive standard brackets are homogeneous integral word polynomials. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization

open private lex_append_of_lex_of_length_eq from
  D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

variable {A : Type*} [LinearOrder A]

/-- Integral noncommutative polynomials whose monomials are finite words. -/
abbrev WordPolynomial (A : Type*) := MonoidAlgebra ℤ (FreeMonoid A)

/-- The basis monomial represented by a word. -/
noncomputable def wordMonomial (w : List A) : WordPolynomial A :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

/-- Every monomial occurring in `p` has word length `n`. -/
def Homogeneous (p : WordPolynomial A) (n : ℕ) : Prop :=
  ∀ m ∈ p.coeff.support, FreeMonoid.length m = n

private theorem homogeneous_sub {p q : WordPolynomial A} {n : ℕ}
    (hp : Homogeneous p n) (hq : Homogeneous q n) : Homogeneous (p - q) n := by
  intro m hm
  by_contra hnot
  have hp0 : p.coeff m = 0 := by
    by_contra hpne
    exact hnot (hp m (Finsupp.mem_support_iff.mpr hpne))
  have hq0 : q.coeff m = 0 := by
    by_contra hqne
    exact hnot (hq m (Finsupp.mem_support_iff.mpr hqne))
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, hp0, hq0, sub_zero] at hm
  exact hm rfl

private theorem homogeneous_mul {p q : WordPolynomial A} {m n : ℕ}
    (hp : Homogeneous p m) (hq : Homogeneous q n) : Homogeneous (p * q) (m + n) := by
  classical
  intro x hx
  have hx' := MonoidAlgebra.support_coeff_mul_subset p q hx
  rcases Finset.mem_mul.mp hx' with ⟨u, hu, v, hv, huv⟩
  rw [← huv, FreeMonoid.length_mul, hp u hu, hq v hv]

private theorem coeff_mul_append {p q : WordPolynomial A} {u v : List A}
    (hp : Homogeneous p u.length) (hq : Homogeneous q v.length) :
    (p * q).coeff (FreeMonoid.ofList (u ++ v)) =
      p.coeff (FreeMonoid.ofList u) * q.coeff (FreeMonoid.ofList v) := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  calc
    _ = q.coeff.sum (fun y ry ↦
          if FreeMonoid.ofList u * y = FreeMonoid.ofList (u ++ v)
          then p.coeff (FreeMonoid.ofList u) * ry else 0) := by
      apply Finsupp.sum_eq_single (FreeMonoid.ofList u)
      · intro x hx hxu
        rw [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro y hy
        split_ifs with heq
        · exfalso
          apply hxu
          apply List.append_inj_left heq
          exact hp x (Finsupp.mem_support_iff.mpr hx)
        · rfl
      · intro hu0
        simp
    _ = _ := by
      rw [Finsupp.sum_eq_single (FreeMonoid.ofList v)]
      · simp
      · intro y hy hyv
        split_ifs with heq
        · exfalso
          apply hyv
          apply List.append_inj_right heq
          simpa using hq y (Finsupp.mem_support_iff.mpr hy)
        · rfl
      · intro hv0
        simp

/-- A polynomial has leading word `w` when `w` has coefficient one and every
word in its support is lexicographically no smaller than `w`. -/
def HasLeadingWord (p : WordPolynomial A) (w : List A) : Prop :=
  Homogeneous p w.length ∧
    p.coeff (FreeMonoid.ofList w) = 1 ∧
    ∀ x ∈ p.coeff.support, w ≤ FreeMonoid.toList x

private theorem append_le_append_of_le_of_le {u v x y : List A}
    (hu : u ≤ x) (hv : v ≤ y) (hlen : u.length = x.length) :
    u ++ v ≤ x ++ y := by
  rcases hu.eq_or_lt with rfl | hux
  · rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact (show u ++ v < u ++ y by
        change List.Lex (· < ·) (u ++ v) (u ++ y)
        change List.Lex (· < ·) v y at hv
        exact List.Lex.append_left (· < ·) hv _).le
  · exact (lex_append_of_lex_of_length_eq hux hlen v y).le

/-- The commutator in the integral word algebra. -/
noncomputable def commutator (p q : WordPolynomial A) : WordPolynomial A := p * q - q * p

private theorem hasLeadingWord_mul {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) :
    HasLeadingWord (p * q) (u ++ v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa [List.length_append] using homogeneous_mul hp.1 hq.1
  · rw [coeff_mul_append hp.1 hq.1, hp.2.1, hq.2.1, one_mul]
  · intro z hz
    have hz' := MonoidAlgebra.support_coeff_mul_subset p q hz
    rcases Finset.mem_mul.mp hz' with ⟨x, hx, y, hy, hxy⟩
    rw [← hxy]
    exact append_le_append_of_le_of_le
      (hp.2.2 x hx) (hq.2.2 y hy) (hp.1 x hx).symm

private theorem reverse_product_coeff_zero {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) (hrot : u ++ v < v ++ u) :
    (q * p).coeff (FreeMonoid.ofList (u ++ v)) = 0 := by
  classical
  rw [← Finsupp.notMem_support_iff]
  intro hz
  have hz' := MonoidAlgebra.support_coeff_mul_subset q p hz
  rcases Finset.mem_mul.mp hz' with ⟨x, hx, y, hy, hxy⟩
  have hle : v ++ u ≤ FreeMonoid.toList (x * y) :=
    append_le_append_of_le_of_le
      (hq.2.2 x hx) (hp.2.2 y hy) (hq.1 x hx).symm
  have heq : FreeMonoid.toList (x * y) = u ++ v := by
    exact congrArg FreeMonoid.toList hxy
  exact (not_lt_of_ge (heq ▸ hle)) hrot

private theorem hasLeadingWord_commutator {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) (hrot : u ++ v < v ++ u) :
    HasLeadingWord (commutator p q) (u ++ v) := by
  classical
  have hpq := hasLeadingWord_mul hp hq
  have hqp := hasLeadingWord_mul hq hp
  refine ⟨?_, ?_, ?_⟩
  · rw [commutator, List.length_append]
    apply homogeneous_sub (homogeneous_mul hp.1 hq.1)
    simpa [Nat.add_comm] using homogeneous_mul hq.1 hp.1
  · rw [commutator, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      hpq.2.1, reverse_product_coeff_zero hp hq hrot, sub_zero]
  · intro z hz
    rw [commutator, Finsupp.mem_support_iff, MonoidAlgebra.coeff_sub,
      Finsupp.sub_apply] at hz
    by_cases hpqz : z ∈ (p * q).coeff.support
    · exact hpq.2.2 z hpqz
    · have hpq0 := Finsupp.notMem_support_iff.mp hpqz
      have hqpz : z ∈ (q * p).coeff.support := by
        rw [Finsupp.mem_support_iff]
        intro hzero
        exact hz (by rw [hpq0, hzero, sub_zero])
      exact (hrot.le.trans (hqp.2.2 z hqpz))

/-- Recursive standard bracketing, using the longest proper Lyndon suffix at every
word of length at least two.  The value at the empty word is zero. -/
noncomputable def standardBracket : (w : List A) → WordPolynomial A
  | [] => 0
  | [a] => wordMonomial [a]
  | a :: b :: tail =>
      let w := a :: b :: tail
      let hw : 2 ≤ w.length := by simp [w]
      commutator
        (standardBracket (standardLeft w hw))
        (standardBracket (standardRight w hw))
termination_by w => w.length
decreasing_by
  all_goals
    simp only [standardLeft, standardRight, standardCut,
      List.length_take, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut (a :: b :: tail) (by simp))
    omega

theorem standardBracket_homogeneous (w : List A) :
    Homogeneous (standardBracket w) w.length := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil =>
          intro m hm
          simp [standardBracket] at hm
      | cons a tail =>
          cases tail with
          | nil =>
              rw [standardBracket]
              intro m hm
              simp only [wordMonomial, MonoidAlgebra.coeff_single,
                Finsupp.support_single_ne_zero _ one_ne_zero,
                Finset.mem_singleton] at hm
              subst m
              rfl
          | cons b tail =>
              let w := a :: b :: tail
              let hw : 2 ≤ w.length := by simp [w]
              rw [standardBracket]
              have hleft : (standardLeft w hw).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w hw)
                change 0 < standardCut w hw ∧
                  standardCut w hw < w.length ∧ _ at hc
                omega
              have hright : (standardRight w hw).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w hw)
                change 0 < standardCut w hw ∧
                  standardCut w hw < w.length ∧ _ at hc
                omega
              have hfactor := congrArg List.length (show
                standardLeft w hw ++ standardRight w hw = w by
                  simpa [standardLeft, standardRight] using
                    List.take_append_drop (standardCut w hw) w)
              rw [List.length_append] at hfactor
              rw [← hfactor]
              rw [commutator]
              apply homogeneous_sub
                (homogeneous_mul (ih _ hleft _ rfl) (ih _ hright _ rfl))
              simpa [Nat.add_comm] using
                homogeneous_mul (ih _ hright _ rfl) (ih _ hleft _ rfl)


end D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
