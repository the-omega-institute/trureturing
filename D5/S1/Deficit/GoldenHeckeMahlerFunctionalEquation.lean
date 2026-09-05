/- GID: D5/S1/Deficit/GoldenHeckeMahlerFunctionalEquation
   generality: I
   mirror-B: D5/B/S1/Deficit/GoldenHeckeMahlerFunctionalEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Hecke-Mahler series obeys its exact two-branch monomial substitution law. -/

import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf

namespace D5.S1.Deficit.GoldenHeckeMahlerFunctionalEquation

open D5.S0.Conventions
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf

/-- A pair records the exponents of `P` and `Q` in a bivariate monomial. -/
abbrev Degree := Nat × Nat

/-- The exponent pair of the term `P ^ S(v) * Q ^ v`. -/
def heckeMahlerDegree (v : Nat) : Degree :=
  (goldenSubstStart v, v)

/-- The exponent pair after the substitution `(P, Q) -> (P Q, P)`. -/
def pqPBranchDegree (v : Nat) : Degree :=
  (goldenSubstStart v + v, goldenSubstStart v)

/-- The exponent pair after the substitution `(P, Q) -> (P^2 Q, P Q)` and
multiplication by `P^2 Q`. -/
def pSquaredQBranchDegree (v : Nat) : Degree :=
  (2 + 2 * goldenSubstStart v + v, 1 + goldenSubstStart v + v)

private theorem goldenSubstStart_iterate (v : Nat) :
    goldenSubstStart (goldenSubstStart v) = goldenSubstStart v + v := by
  calc
    goldenSubstStart (goldenSubstStart v) =
        displacementDecode (goldenSubstStart v) :=
      golden_subst_start_eq_displacement_decode _
    _ = (((wdigits v).map fun k => k + 1).map fun k => Nat.fib (k + 1)).sum := by
      rw [displacementDecode, golden_subst_start_wdigits]
    _ = ((wdigits v).map fun k => Nat.fib (k + 2)).sum := by
      simp only [List.map_map, Function.comp_apply]
      congr 1
    _ = ((wdigits v).map fun k => Nat.fib k + Nat.fib (k + 1)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro k _
      exact Nat.fib_add_two
    _ = ((wdigits v).map Nat.fib).sum +
        ((wdigits v).map fun k => Nat.fib (k + 1)).sum := by
      rw [List.sum_map_add]
    _ = v + displacementDecode v := by
      rw [decode_wdigits]
      rfl
    _ = goldenSubstStart v + v := by
      rw [golden_subst_start_eq_displacement_decode]
      omega

private theorem goldenSubstStart_complement (v : Nat) :
    goldenSubstStart (1 + goldenSubstStart v + v) =
      2 + 2 * goldenSubstStart v + v := by
  have hstart : 1 + goldenSubstStart v + v =
      goldenSubstStart (goldenSubstStart v) + 1 := by
    rw [goldenSubstStart_iterate]
    omega
  rw [hstart, goldenSubstStart_step_true (goldenWord_goldenSubstStart _),
    goldenSubstStart_iterate, goldenSubstStart_iterate]
  omega

/-- The two exponent substitutions are indexed by the image of `S` and its complement. -/
private def branchIndex : Nat ⊕ Nat → Nat
  | .inl v => goldenSubstStart v
  | .inr v => 1 + goldenSubstStart v + v

private theorem branchIndex_left_word (v : Nat) :
    goldenWord (branchIndex (.inl v)) = true :=
  goldenWord_goldenSubstStart v

private theorem branchIndex_right_word (v : Nat) :
    goldenWord (branchIndex (.inr v)) = false := by
  change goldenWord (1 + goldenSubstStart v + v) = false
  have hindex : 1 + goldenSubstStart v + v =
      goldenSubstStart (goldenSubstStart v) + 1 := by
    rw [goldenSubstStart_iterate]
    omega
  rw [hindex, goldenWord_goldenSubstStart_succ,
    goldenWord_goldenSubstStart]
  rfl

private theorem complementIndex_strictMono :
    StrictMono fun v : Nat => 1 + goldenSubstStart v + v := by
  intro a b hab
  have hstart := goldenSubstStart_strictMono hab
  change 1 + goldenSubstStart a + a < 1 + goldenSubstStart b + b
  omega

private theorem branchIndex_bijective : Function.Bijective branchIndex := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [branchIndex] at hab
            exact congrArg Sum.inl (goldenSubstStart_strictMono.injective hab)
        | inr b =>
            have hword := congrArg goldenWord hab
            rw [branchIndex_left_word, branchIndex_right_word] at hword
            contradiction
    | inr a =>
        cases b with
        | inl b =>
            have hword := congrArg goldenWord hab
            rw [branchIndex_right_word, branchIndex_left_word] at hword
            contradiction
        | inr b =>
            simp only [branchIndex] at hab
            exact congrArg Sum.inr (complementIndex_strictMono.injective hab)
  · intro v
    by_cases hv : goldenWord v = true
    · obtain ⟨k, hk⟩ := exists_goldenSubstStart_of_true hv
      exact ⟨.inl k, by simpa [branchIndex] using hk⟩
    · have hvfalse : goldenWord v = false := by simpa using hv
      have hvpos : 0 < v := by
        by_contra h
        have hvzero : v = 0 := Nat.eq_zero_of_not_pos h
        rw [hvzero, goldenWord_zero] at hvfalse
        contradiction
      have hprev : goldenWord (v - 1) = true := by
        by_contra h
        have hprevFalse : goldenWord (v - 1) = false := by simpa using h
        have hnext := golden_no_two_false hprevFalse
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hvpos.ne')] at hnext
        rw [hvfalse] at hnext
        contradiction
      obtain ⟨k, hk⟩ := exists_goldenSubstStart_of_true hprev
      have hkword : goldenWord k = true := by
        cases hword : goldenWord k with
        | false =>
            have hnext := goldenWord_goldenSubstStart_succ k
            have hindex : goldenSubstStart k + 1 = v := by omega
            rw [hindex, hvfalse, hword] at hnext
            contradiction
        | true => rfl
      obtain ⟨n, hn⟩ := exists_goldenSubstStart_of_true hkword
      refine ⟨.inr n, ?_⟩
      calc
        branchIndex (.inr n) = 1 + goldenSubstStart n + n := rfl
        _ = goldenSubstStart (goldenSubstStart n) + 1 := by
          rw [goldenSubstStart_iterate]
          omega
        _ = goldenSubstStart k + 1 := by rw [hn]
        _ = v := by omega

private noncomputable def branchIndexEquiv : Nat ⊕ Nat ≃ Nat :=
  Equiv.ofBijective branchIndex branchIndex_bijective

private theorem degree_at_left_branch (v : Nat) :
    heckeMahlerDegree (branchIndexEquiv (.inl v)) = pqPBranchDegree v := by
  change heckeMahlerDegree (goldenSubstStart v) = pqPBranchDegree v
  simp [heckeMahlerDegree, pqPBranchDegree, goldenSubstStart_iterate]

private theorem degree_at_right_branch (v : Nat) :
    heckeMahlerDegree (branchIndexEquiv (.inr v)) = pSquaredQBranchDegree v := by
  change heckeMahlerDegree (1 + goldenSubstStart v + v) = pSquaredQBranchDegree v
  simp [heckeMahlerDegree, pSquaredQBranchDegree, goldenSubstStart_complement]

/-- Coefficients of `F(P,Q) = sum_v P ^ S(v) * Q ^ v`. -/
def heckeMahlerSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {v : Nat // heckeMahlerDegree v = degree}

/-- Coefficients of `F(P Q, P)`. -/
def pqPBranchSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {v : Nat // pqPBranchDegree v = degree}

/-- Coefficients of `P^2 Q * F(P^2 Q, P Q)`. -/
def pSquaredQBranchSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {v : Nat // pSquaredQBranchDegree v = degree}

private def branchPredicate (degree : Degree) : Nat ⊕ Nat → Prop
  | .inl v => pqPBranchDegree v = degree
  | .inr v => pSquaredQBranchDegree v = degree

private noncomputable def coefficientSplit (degree : Degree) :
    {v : Nat // heckeMahlerDegree v = degree} ≃
      {v : Nat // pqPBranchDegree v = degree} ⊕
        {v : Nat // pSquaredQBranchDegree v = degree} :=
  ((branchIndexEquiv.subtypeEquiv
      (p := branchPredicate degree)
      (q := fun v => heckeMahlerDegree v = degree) fun branch => by
        cases branch with
        | inl v => simpa [branchPredicate, degree_at_left_branch]
        | inr v => simpa [branchPredicate, degree_at_right_branch]).symm).trans
    (Equiv.subtypeSum (p := branchPredicate degree))

/-- **Golden Hecke-Mahler functional equation, coefficientwise.** The formal bivariate series
`F(P,Q) = sum_v P ^ S(v) * Q ^ v` satisfies
`F(P,Q) = F(P Q,P) + P^2 Q * F(P^2 Q,P Q)`.

The equality is stated coefficientwise, so it needs no analytic convergence assumptions. The
left branch is indexed by `S(v)` and the right branch by the complementary indices
`1 + S(v) + v`; together they form a bijection with all natural indices. -/
theorem golden_hecke_mahler_functional_equation :
    heckeMahlerSeries =
      fun degree => pqPBranchSeries degree + pSquaredQBranchSeries degree := by
  funext degree
  change Cardinal.mk {v : Nat // heckeMahlerDegree v = degree} =
    Cardinal.mk {v : Nat // pqPBranchDegree v = degree} +
      Cardinal.mk {v : Nat // pSquaredQBranchDegree v = degree}
  simpa only [Cardinal.mk_sum, Cardinal.lift_id] using
    Cardinal.mk_congr (coefficientSplit degree)

#print axioms golden_hecke_mahler_functional_equation

end D5.S1.Deficit.GoldenHeckeMahlerFunctionalEquation
