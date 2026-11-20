import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection

/-! The signed fiber equations for a balanced cubic nine-cube support omitting prefix 11. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9SignedProjection (signedRow)

local notation "flip" => BalancedCriticalSpectrum.flip

/-- The two prefix bits, in coordinate order. -/
def prefixBits (a b : Bool) : Q 2 := Fin.cases a (fun _ => b)

/-- Restrict a signed function on Q9 to the seven coordinates following a fixed prefix. -/
def fiber (z : Q 9 → ℤ) (a b : Bool) (y : Q 7) : ℤ := z (Fin.append (prefixBits a b) y)

private theorem prefix_lt_suffix (i : Fin 2) (j : Fin 7) : i.castAdd 7 < j.natAdd 2 := by
  change i.val < 2 + j.val
  exact lt_of_lt_of_le i.isLt (Nat.le_add_right 2 j.val)

private theorem flip_append_prefix (x : Q 2) (y : Q 7) (i : Fin 2) :
    flip (Fin.append x y) (i.castAdd 7) = Fin.append (flip x i) y := by
  funext k
  refine Fin.addCases (m := 2) (n := 7) ?_ ?_ k
  · intro j
    simp only [BalancedCriticalSpectrum.flip, Function.update_apply, Fin.castAdd_inj,
      Fin.append_left]
  · intro j
    simp [BalancedCriticalSpectrum.flip, (prefix_lt_suffix i j).ne.symm]

private theorem flip_append_suffix (x : Q 2) (y : Q 7) (i : Fin 7) :
    flip (Fin.append x y) (i.natAdd 2) = Fin.append x (flip y i) := by
  funext k
  refine Fin.addCases (m := 2) (n := 7) ?_ ?_ k
  · intro j
    simp [BalancedCriticalSpectrum.flip, (prefix_lt_suffix j i).ne]
  · intro j
    simp only [BalancedCriticalSpectrum.flip, Function.update_apply, Fin.natAdd_inj,
      Fin.append_right]

private theorem suffix_not_lt_prefix (i : Fin 2) (j : Fin 7) : ¬ j.natAdd 2 < i.castAdd 7 :=
  not_lt_of_ge (prefix_lt_suffix i j).le

private theorem castAdd_lt_castAdd (i j : Fin 2) : i.castAdd 7 < j.castAdd 7 ↔ i < j := Iff.rfl

private theorem sign_append_prefix (x : Q 2) (y : Q 7) (i : Fin 2) :
    truePrefixSign (Fin.append x y) (i.castAdd 7) = truePrefixSign x i := by
  simp only [truePrefixSign]
  rw [Finset.card_filter, Fin.sum_univ_add (a := 2) (b := 7)]
  simp only [Finset.card_filter, Fin.append_left, castAdd_lt_castAdd,
    suffix_not_lt_prefix, false_and, ite_false, Finset.sum_const_zero, add_zero]

private theorem sign_append_suffix (x : Q 2) (y : Q 7) (j : Fin 7) :
    truePrefixSign (Fin.append x y) (j.natAdd 2) =
      (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin 2 => x i = true)).card * truePrefixSign y j := by
  simp only [truePrefixSign]
  rw [Finset.card_filter, Fin.sum_univ_add (a := 2) (b := 7)]
  simp only [Finset.card_filter, Fin.append_left, Fin.append_right, prefix_lt_suffix,
    true_and, Fin.natAdd_lt_natAdd_iff, pow_add]

private theorem signed_row_append (z : Q 9 → ℤ) (x : Q 2) (y : Q 7) :
    signedRow z (Fin.append x y) =
      signedRow (fun v => z (Fin.append v y)) x +
        (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin 2 => x i = true)).card *
          signedRow (fun v => z (Fin.append x v)) y := by
  unfold signedRow
  rw [Fin.sum_univ_add (a := 2) (b := 7)]
  simp only [sign_append_prefix, sign_append_suffix, flip_append_prefix, flip_append_suffix,
    Finset.mul_sum, mul_assoc]

private theorem prefix_row_eleven (g : Q 2 → ℤ) :
    signedRow g (prefixBits true true) = g (prefixBits false true) - g (prefixBits true false) := by
  have h0 : flip (prefixBits true true) 0 = prefixBits false true := by decide +kernel
  have h1 : flip (prefixBits true true) 1 = prefixBits true false := by decide +kernel
  have hs0 : truePrefixSign (prefixBits true true) 0 = 1 := by decide +kernel
  have hs1 : truePrefixSign (prefixBits true true) 1 = -1 := by decide +kernel
  simp [signedRow, Fin.sum_univ_two, h0, h1, hs0, hs1, sub_eq_add_neg]

private theorem prefix_row_zero (g : Q 2 → ℤ) :
    signedRow g (prefixBits false false) =
      g (prefixBits true false) + g (prefixBits false true) := by
  have h0 : flip (prefixBits false false) 0 = prefixBits true false := by decide +kernel
  have h1 : flip (prefixBits false false) 1 = prefixBits false true := by decide +kernel
  have hs0 : truePrefixSign (prefixBits false false) 0 = 1 := by decide +kernel
  have hs1 : truePrefixSign (prefixBits false false) 1 = 1 := by decide +kernel
  simp [signedRow, Fin.sum_univ_two, h0, h1, hs0, hs1]

open Classical in
/-- When prefix 11 is absent, the integral switching function has equal 10 and 01 fibers.
The signed row of the 00 fiber determines their common value. -/
theorem q9_missing_pair_signed_fibers {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hmissing : ∀ y : Q 7, Fin.append (prefixBits true true) y ∉ C) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ y, fiber z true false y = fiber z false true y) ∧
      ∀ y, 2 * fiber z true false y =
        3 * fiber z false false y - signedRow (fiber z false false) y := by
  obtain ⟨z, hunit, hzero, _, hz⟩ := q9_integral_true_prefix_switching hreg hb
  have h11 (y : Q 7) : fiber z true true y = 0 := hzero _ (hmissing y)
  have hequal (y : Q 7) : fiber z true false y = fiber z false true y := by
    have h := (signed_row_append z (prefixBits true true) y).symm.trans
      (hz (Fin.append (prefixBits true true) y))
    rw [prefix_row_eleven] at h
    change fiber z false true y - fiber z true false y +
      (-1 : ℤ) ^ _ * signedRow (fiber z true true) y = 3 * fiber z true true y at h
    have hrow : signedRow (fiber z true true) y = 0 := by simp [signedRow, h11]
    simp only [hrow, h11, mul_zero, add_zero] at h
    omega
  refine ⟨z, hunit, hzero, hz, hequal, ?_⟩
  intro y
  have h := (signed_row_append z (prefixBits false false) y).symm.trans
    (hz (Fin.append (prefixBits false false) y))
  rw [prefix_row_zero] at h
  change fiber z true false y + fiber z false true y +
    (-1 : ℤ) ^ _ * signedRow (fiber z false false) y = 3 * fiber z false false y at h
  have hsign :
      (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin 2 => prefixBits false false i = true)).card =
        1 := by decide +kernel
  rw [hsign, one_mul, ← hequal y] at h
  omega

open Classical in
/-- The number of selected suffix neighbors at a point of the 00 fiber is odd
exactly when the point is selected. -/
theorem q9_missing_pair_zero_fiber_parity {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hmissing : ∀ y : Q 7, Fin.append (prefixBits true true) y ∉ C)
    (y : Q 7) :
    (Finset.univ.filter (fun i : Fin 7 =>
      Fin.append (prefixBits false false) (flip y i) ∈ C)).card % 2 =
        if Fin.append (prefixBits false false) y ∈ C then 1 else 0 := by
  obtain ⟨z, hunit, hzero, _, _, hrow⟩ := q9_missing_pair_signed_fibers hreg hb hmissing
  let occupied (v : Q 7) : ℕ := if Fin.append (prefixBits false false) v ∈ C then 1 else 0
  have hneg : (-1 : ZMod 2) = 1 := by decide +kernel
  have htwo : (2 : ZMod 2) = 0 := by decide +kernel
  have hthree : (3 : ZMod 2) = 1 := by decide +kernel
  have hcast (v : Q 7) : (fiber z false false v : ZMod 2) = (occupied v : ZMod 2) := by
    by_cases hv : Fin.append (prefixBits false false) v ∈ C
    · rcases hunit _ hv with hp | hm
      · simp [fiber, occupied, hv, hp]
      · simp [fiber, occupied, hv, hm, hneg]
    · simp [fiber, occupied, hv, hzero _ hv]
  have hdiff : (occupied y : ZMod 2) - ∑ i : Fin 7, (occupied (flip y i) : ZMod 2) = 0 := by
    have h := congrArg (fun t : ℤ => (t : ZMod 2)) (hrow y)
    simpa only [signedRow, Int.cast_sum, Int.cast_mul, Int.cast_sub, truePrefixSign, Int.cast_pow,
      Int.cast_neg, Int.cast_one, hneg, one_pow, one_mul, Int.cast_ofNat, hthree, htwo,
      zero_mul, hcast] using h.symm
  have hcard :
      ((Finset.univ.filter (fun i : Fin 7 =>
        Fin.append (prefixBits false false) (flip y i) ∈ C)).card : ZMod 2) =
          (occupied y : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    exact (sub_eq_zero.mp hdiff).symm
  have hmod := congrArg (ZMod.val : ZMod 2 → ℕ) hcard
  rw [ZMod.val_natCast, ZMod.val_natCast] at hmod
  change _ = occupied y
  rw [hmod]
  by_cases hy : Fin.append (prefixBits false false) y ∈ C <;> simp [occupied, hy]

#print axioms q9_missing_pair_signed_fibers
#print axioms q9_missing_pair_zero_fiber_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers
