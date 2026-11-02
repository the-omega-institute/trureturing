/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/PhysicalArithmetic
   generality: I
   mirror-B: none(waiver:private-implementation-for-later-endpoint)
   mirror-E: none(waiver:private-implementation-for-later-endpoint)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Exact natural exponents for the low-X physical reservations. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

private def physicalDomain (a b c d : ℕ) : Prop :=
  2 ≤ c ∧ 2*c+1 ≤ a ∧ a ≤ d ∧ d+1 ≤ b

private abbrev eOn (a b : ℕ) : Prop := 2*a-2 < b
private abbrev rOn (b c d : ℕ) : Prop := 2*c ≤ b-d
private abbrev collide (a b c d : ℕ) : Prop := eOn a b ∧ d+2*c+1 = 2*a

-- Parentheses are essential: b+1-2*a includes the exponent-zero e=1 case.
private def eExponent (a b : ℕ) : ℕ := b+1-2*a
private def rExponent (a b c d : ℕ) : ℕ :=
  b-d-2*c + if collide a b c d then 1 else 0
private def eWeight (a b : ℕ) : ℚ := if eOn a b then 2^(eExponent a b) else 0
private def rWeight (a b c d : ℕ) : ℚ :=
  if rOn b c d then 2^(rExponent a b c d) else 0

private theorem reservation_bounds (a b c d : ℕ) (h : physicalDomain a b c d) :
    (eOn a b → eExponent a b < b-a) ∧
    (rOn b c d → rExponent a b c d < b-a) ∧
    (eOn a b → rOn b c d → eExponent a b ≠ rExponent a b c d) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  refine ⟨?_,?_,?_⟩
  · dsimp [eOn,eExponent]; omega
  · intro hr
    dsimp [rOn] at hr
    dsimp [rExponent]
    split_ifs <;> omega
  · intro he hr
    dsimp [eOn] at he
    dsimp [rOn] at hr
    dsimp [eExponent,rExponent,collide,eOn]
    split_ifs <;> omega

private theorem reservation_choices (a b c d : ℕ) (h : physicalDomain a b c d) :
    eWeight a b = (if b ≤ 2*a-2 then 0 else (2:ℚ)^(b+1-2*a)) ∧
    rWeight a b c d = (if b-d ≤ 2*c-1 then 0 else
      if eOn a b ∧ d+2*c+1=2*a then 2*(2:ℚ)^(b-d-2*c)
      else (2:ℚ)^(b-d-2*c)) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  constructor
  · by_cases he : eOn a b
    · have hn : ¬ b ≤ 2*a-2 := by dsimp [eOn] at he; omega
      simp [eWeight,eExponent,he,hn]
    · have hn : b ≤ 2*a-2 := by dsimp [eOn] at he; omega
      simp [eWeight,he,hn]
  · by_cases hr : rOn b c d
    · have hn : ¬ b-d ≤ 2*c-1 := by dsimp [rOn] at hr; omega
      by_cases hx : collide a b c d
      · simp only [rWeight,ite_eq_left hr,ite_eq_right hn,rExponent,ite_eq_left hx,
          pow_succ]
        ring
      · simp only [rWeight,ite_eq_left hr,ite_eq_right hn,rExponent,ite_eq_right hx,
          Nat.add_zero]
    · have hn : b-d ≤ 2*c-1 := by dsimp [rOn] at hr; omega
      simp [rWeight,hr,hn]

-- A field identity only; used below for the five exact dyadic quotients.
private theorem dyadic_quotient (n j : ℕ) (hj : j ≤ n) :
    (2:ℚ)^n / 2^j = 2^(n-j) := by
  apply (div_eq_iff (by positivity : (2:ℚ)^j ≠ 0)).2
  rw [← pow_add,Nat.sub_add_cancel hj]

private theorem physical_coordinates (a b c d : ℕ) (h : physicalDomain a b c d) :
    (2:ℚ)^(d-a)*2^a = 2^d ∧
    2*(2:ℚ)^(b-a-1) = 2^(b-a) ∧
    (2:ℚ)^a*2^(b-a-1) = 2^(b-1) ∧
    (2:ℚ)^a/(2*((2:ℚ)^c)^2) = 2^(a-2*c-1) ∧
    (2:ℚ)^a/4 = 2^(a-2) ∧
    (2:ℚ)^c/4 = 2^(c-2) ∧
    ((2:ℚ)^(d-a)*2^a)/(2*(2:ℚ)^c) = 2^(d-c-1) ∧
    ((2:ℚ)^(d-a)*2^a)/2 = 2^(d-1) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  have hw : (2:ℚ)^(d-a)*2^a = 2^d := by rw [← pow_add]; congr 1; omega
  have hL : 2*(2:ℚ)^(b-a-1) = 2^(b-a) := by
    rw [← pow_succ']; congr 1; omega
  have hy : (2:ℚ)^a*2^(b-a-1) = 2^(b-1) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨hw,hL,hy,?_,?_,?_,?_,?_⟩
  · have hden : 2*((2:ℚ)^c)^2 = 2^(2*c+1) := by
      rw [← pow_mul,show c*2=2*c by omega,pow_succ]; ring
    rw [hden,dyadic_quotient a (2*c+1) ha]
    congr 1
  · simpa only [show (2:ℚ)^2=4 by norm_num] using dyadic_quotient a 2 (by omega)
  · simpa only [show (2:ℚ)^2=4 by norm_num] using dyadic_quotient c 2 hc
  · rw [hw,← pow_succ',dyadic_quotient d (c+1) (by omega)]
    congr 1
  · rw [hw]
    simpa using dyadic_quotient d 1 (by omega)

private theorem physical_regimes (a b c d : ℕ) (h : physicalDomain a b c d) :
    (2:ℚ)^(d-a)*2^(b-d-1) = 2^(b-a-1) ∧
    (eOn a b → (2:ℚ)^(b-a-1) = (2:ℚ)^a*eWeight a b/4) ∧
    (rOn b c d → (2:ℚ)^(b-a-1) =
      (2:ℚ)^(d-a)*((2:ℚ)^c)^2*2^(b-d-2*c)/2) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  refine ⟨?_,?_,?_⟩
  · rw [← pow_add]; congr 1; omega
  · intro he
    have he' : 2*a-2 < b := he
    rw [eWeight,if_pos he,eExponent,← pow_add,show (4:ℚ)=2^2 by norm_num]
    have ht : 2 ≤ a+(b+1-2*a) := by omega
    rw [dyadic_quotient _ _ ht]
    congr 1; omega
  · intro hr
    have hr' : 2*c ≤ b-d := hr
    have hp : (2:ℚ)^(d-a)*((2:ℚ)^c)^2*2^(b-d-2*c) =
        2*(2:ℚ)^(b-a-1) := by
      rw [← pow_mul,← pow_add,← pow_add,← pow_succ']
      congr 1; omega
    rw [hp]; ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
