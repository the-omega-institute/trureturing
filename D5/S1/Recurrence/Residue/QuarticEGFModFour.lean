/- GID: D5/S1/Recurrence/Residue/QuarticEGFModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/QuarticEGFModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The fourth compositional iterate yields the unbounded A396804 congruence modulo four. -/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint

namespace D5.S1.Recurrence.Residue.QuarticEGFModFour

noncomputable def F : PowerSeries ℚ := X * exp ℚ

private theorem eCoeff_F (n : ℕ) : eCoeff F n = n := by
  cases n <;> simp [F]

private theorem coeff_F (n : ℕ) : coeff n F = (n : ℚ) / n.factorial := by
  apply (eq_div_iff (by exact_mod_cast n.factorial_ne_zero)).mpr
  simpa only [eCoeff, mul_comm] using eCoeff_F n

private theorem coeff_F_pow (n k : ℕ) : coeff n (F ^ k) =
    if k ≤ n then (k : ℚ) ^ (n - k) / (n - k).factorial else 0 := by
  rw [F, mul_pow, exp_pow_eq_rescale_exp, coeff_X_pow_mul']
  split_ifs <;> simp [coeff_exp, div_eq_mul_inv]

/-- The exact binomial sum for the square of X exp(X), before reducing modulo two. -/
theorem square_coeff (n : ℕ) :
    eCoeff (F.subst F) n =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * k * (k : ℚ) ^ (n - k) := by
  rw [eCoeff, coeff_subst' (.of_constantCoeff_zero (show constantCoeff F = 0 by simp [F]))]
  have hs : (Function.support (fun k => coeff k F • coeff n (F ^ k))) ⊆
      (range (n + 1) : Set ℕ) := by
    intro k hk
    by_contra h
    have hkn : ¬k ≤ n := by simpa using h
    exact hk (by simp [coeff_F_pow, hkn])
  rw [finsum_eq_sum_of_support_subset _ hs, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range_succ_iff.mp hk
  rw [coeff_F, coeff_F_pow, if_pos hkn, smul_eq_mul]
  have hc : (n.choose k : ℚ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [← hc]
  field_simp

private def linear (n : ℕ) : ℤ := n

private def square : ℕ → ℤ := composition linear linear

private theorem square_formula (n : ℕ) :
    square n = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * k * (k : ℤ) ^ (n - k) := by
  have h := square_coeff n
  rw [eCoeff_composition _ _ (by simp [F]),
    show eCoeff F = (fun n : ℕ => (n : ℚ)) from funext eCoeff_F] at h
  have hm := composition_map (Int.castRingHom ℚ) linear linear n
  have he : (square n : ℚ) = composition (fun n : ℕ => (n : ℚ)) (fun n : ℕ => (n : ℚ)) n := by
    simpa [square, linear] using hm
  rw [← he] at h
  exact_mod_cast h

private theorem square_even (n : ℕ) (hn : 2 ≤ n) : (square n : ZMod 2) = 0 := by
  rw [square_formula]
  push_cast
  have hp (k : ℕ) : (k : ZMod 2) * (k : ZMod 2) ^ (n - k) = k := by
    have hz : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases hz k with hk | hk <;> rw [hk] <;> simp
  have he : (∑ k ∈ range (n + 1), (k : ZMod 2) * n.choose k) =
      (n : ZMod 2) * 2 ^ (n - 1) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ZMod 2)) (Nat.sum_range_mul_choose n)
  calc
    (∑ k ∈ range (n + 1), (n.choose k : ZMod 2) * k * (k : ZMod 2) ^ (n - k)) =
        ∑ k ∈ range (n + 1), (k : ZMod 2) * n.choose k := by
      apply sum_congr rfl
      intro k _
      rw [mul_assoc, hp, mul_comm]
    _ = 0 := by
      rw [he, show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : n - 1 ≠ 0), mul_zero]

private theorem square_mod_two (n : ℕ) : (square n : ZMod 2) = identity n := by
  rcases n with _ | _ | n
  · simp [square, composition, linear, identity]
  · norm_num [square, composition, linear, identity]
  · simpa [identity] using square_even (n + 2) (by omega)

private noncomputable def intSeries (f : ℕ → ℤ) : PowerSeries ℚ :=
  encode (fun n => f n)

private theorem intSeries_injective : Function.Injective intSeries := by
  intro f g h
  funext n
  have he := congrArg (fun s => eCoeff s n) h
  simpa [intSeries] using he

private theorem intSeries_composition (f g : ℕ → ℤ) (hg : g 0 = 0) :
    intSeries (composition f g) = (intSeries f).subst (intSeries g) := by
  have he : (fun n => ((composition f g n : ℤ) : ℚ)) =
      composition (fun n => (f n : ℚ)) (fun n => (g n : ℚ)) := by
    funext n
    exact composition_map (Int.castRingHom ℚ) f g n
  simpa only [intSeries, he] using encode_composition
    (fun n => (f n : ℚ)) (fun n => (g n : ℚ)) (by simp [hg])

private theorem composition_assoc (f g h : ℕ → ℤ) (hg : g 0 = 0) (hh : h 0 = 0) :
    composition (composition f g) h = composition f (composition g h) := by
  apply intSeries_injective
  rw [intSeries_composition _ _ hh, intSeries_composition _ _ hg,
    intSeries_composition _ _ (by simpa [composition] using hg),
    intSeries_composition _ _ hh]
  exact subst_comp_subst_apply
    (.of_constantCoeff_zero (show constantCoeff (intSeries g) = 0 by simp [intSeries, hg]))
    (.of_constantCoeff_zero (show constantCoeff (intSeries h) = 0 by simp [intSeries, hh])) _

private theorem composition_identity_right (f : ℕ → ℤ) : composition f identity = f := by
  apply intSeries_injective
  rw [intSeries_composition _ _ (by simp [identity])]
  have he : intSeries identity = X := by
    apply eCoeff_ext
    simp [intSeries, identity]
  rw [he, X_subst]

private theorem composition_identity_left (f : ℕ → ℤ) (hf : f 0 = 0) :
    composition identity f = f := by
  apply intSeries_injective
  rw [intSeries_composition _ _ hf]
  have he : intSeries identity = X := by
    apply eCoeff_ext
    simp [intSeries, identity]
  rw [he, subst_X (.of_constantCoeff_zero
    (show constantCoeff (intSeries f) = 0 by simp [intSeries, hf]))]

private theorem composition_linear_outer (f h g : ℕ → ℤ) (c : ℤ) (n : ℕ) :
    composition (fun j => f j + c * h j) g n =
      composition f g n + c * composition h g n := by
  induction n using Nat.strong_induction_on generalizing f h with
  | h n ih =>
    cases n with
    | zero => simp [composition]
    | succ n =>
      simp only [composition]
      simp_rw [ih _ (Fin.isLt _)]
      simp only [mul_add, add_mul, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      ring

private theorem fourth_square : iterate linear 4 = composition square square := by
  change composition linear (composition linear (composition linear
    (composition linear identity))) = composition square square
  rw [composition_identity_right]
  exact (composition_assoc linear linear (composition linear linear) rfl
    (by simp [composition, linear])).symm

/-- The characteristic-zero calculation and integral lifting prove the fourth-iterate escape. -/
theorem linear_fourth_mod_four (n : ℕ) : ((iterate linear 4 n : ℤ) : ZMod 4) = identity n := by
  have hd (j : ℕ) : (2 : ℤ) ∣ square j - identity j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simp only [Int.cast_sub]
    rw [square_mod_two]
    simp [identity]
  let h (j : ℕ) : ℤ := (square j - identity j) / 2
  have hs : square = (fun j => identity j + 2 * h j) := by
    funext j
    have he := Int.ediv_mul_cancel (hd j)
    dsimp [h]
    omega
  have hc (j : ℕ) : ((composition h square j : ℤ) : ZMod 2) = (h j : ZMod 2) := by
    have hi : (fun j => (square j : ZMod 2)) =
        (fun j => ((identity j : ℤ) : ZMod 2)) := by
      funext j
      simpa [identity] using square_mod_two j
    change (Int.castRingHom (ZMod 2)) (composition h square j) = _
    rw [composition_map]
    change composition (fun j => (h j : ZMod 2)) (fun j => (square j : ZMod 2)) j = _
    rw [hi]
    have hm := composition_map (Int.castRingHom (ZMod 2)) h identity j
    rw [composition_identity_right] at hm
    exact hm.symm
  have hd' : (2 : ℤ) ∣ composition h square n - h n := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simp only [Int.cast_sub, hc, sub_self]
  obtain ⟨k, hk⟩ := hd'
  have hl := composition_linear_outer identity h square 2 n
  rw [← hs, composition_identity_left square (by simp [square, composition, linear])] at hl
  have he : composition square square n = identity n + 4 * (h n + k) := by
    have hsn := congrFun hs n
    omega
  rw [fourth_square, he]
  push_cast
  rw [show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]
  simp [identity]

private theorem linear_mod_four_fixed :
    step (fun n : ℕ => (n : ZMod 4)) = (fun n : ℕ => (n : ZMod 4)) := by
  have hi : iterate (fun n : ℕ => (n : ZMod 4)) 4 = identity := by
    funext n
    have hm := iterate_map (Int.castRingHom (ZMod 4)) linear 4 n
    simpa [linear, linear_fourth_mod_four] using hm.symm
  have hc (n : ℕ) : composition (fun _ => (1 : ZMod 4)) identity n = 1 := by
    have h := congrFun (composition_identity_right (fun _ => 1)) n
    have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
    change (Int.castRingHom (ZMod 4)) (composition (fun _ => 1) identity n) = _ at hm
    rw [composition_map] at hm
    change composition (fun _ => (1 : ZMod 4)) (fun j => if j = 1 then 1 else 0) n = 1
    simpa [identity] using hm
  funext n
  cases n with
  | zero => simp [step]
  | succ n => simp [step, hi, hc]

private theorem approximation_mod_four (d n : ℕ) :
    (approximation d n : ZMod 4) = n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    change (Nat.castRingHom (ZMod 4)) (step (approximation d) n) = _
    rw [step_map]
    change step (fun j => (approximation d j : ZMod 4)) n = _
    rw [show (fun j => (approximation d j : ZMod 4)) = (fun j : ℕ => (j : ZMod 4))
      from funext ih, linear_mod_four_fixed]

/-- OEIS A396804's modulo-four conjecture, for the independently constructed natural sequence. -/
theorem mod_four (n : ℕ) (hn : 1 ≤ n) : Nat.ModEq 4 (a n) n := by
  cases n with
  | zero => omega
  | succ n =>
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    exact approximation_mod_four (n + 2) (n + 1)

/-- All positive-degree nonlinear EGF coefficients of the fourth iterate are multiples of four. -/
theorem fourth_coeff_divisible (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, eCoeff (iterateComp A 4) n = 4 * k := by
  have he : eCoeff (iterateComp A 4) n = ((iterate a 4 n : ℕ) : ℚ) := by
    rw [eCoeff_iterate A_equation.1]
    change iterate (eCoeff (encode _)) 4 n = _
    rw [show eCoeff (encode (fun j => (a j : ℚ))) = (fun j => (a j : ℚ)) from
      funext (eCoeff_encode _)]
    exact (iterate_map (Nat.castRingHom ℚ) a 4 n).symm
  have hz : ((iterate a 4 n : ℕ) : ZMod 4) = 0 := by
    change (Nat.castRingHom (ZMod 4)) (iterate a 4 n) = _
    rw [iterate_map]
    change iterate (fun j => (a j : ZMod 4)) 4 n = _
    rw [show (fun j => (a j : ZMod 4)) = (fun j : ℕ => (j : ZMod 4)) from
      funext (fun j => approximation_mod_four (j + 1) j)]
    have hm := iterate_map (Int.castRingHom (ZMod 4)) linear 4 n
    have hl := linear_fourth_mod_four n
    have hm' : ((iterate linear 4 n : ℤ) : ZMod 4) =
        iterate (fun j : ℕ => (j : ZMod 4)) 4 n := by simpa [linear] using hm
    rw [hm'] at hl
    simpa [identity, show n ≠ 1 by omega] using hl
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff (iterate a 4 n) 4).mp hz
  exact ⟨k, by rw [he, hk]; push_cast; rfl⟩

-- Nonempty sanity checks for both sides of the congruence, not bounded substitutes for it.
private theorem composition_one {R : Type*} [CommSemiring R] (f g : ℕ → R) :
    composition f g 1 = f 1 * g 1 := by
  rw [composition, Fin.sum_univ_one]
  simp [composition]

private theorem composition_two {R : Type*} [CommSemiring R] (f g : ℕ → R) :
    composition f g 2 = f 1 * g 2 + f 2 * g 1 * g 1 := by
  rw [composition, Fin.sum_univ_two]
  simp [composition_one, composition]

private theorem initial_values : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 27 := by
  have h1 : a 1 = 1 := by
    conv_lhs => rw [a_fixed]
    norm_num [step, composition]
  have h2 : a 2 = 2 := by
    conv_lhs => rw [a_fixed]
    norm_num [step, iterate, composition_one, identity, h1]
  have h3 : a 3 = 27 := by
    conv_lhs => rw [a_fixed]
    norm_num [step, iterate, composition_two, composition_one, identity, h1, h2]
  exact ⟨a_zero, h1, h2, h3⟩

example : eCoeff A 3 = 27 ∧ (a 3 % 4 = 3) ∧ ((3 : ℕ) % 4 = 3) := by
  rw [show eCoeff A 3 = (a 3 : ℚ) from (integral_coefficients 3).symm,
    initial_values.2.2.2]
  norm_num

example : eCoeff (iterateComp A 4) 2 = 8 ∧ (8 : ℕ) % 4 = 0 := by
  rw [eCoeff_iterate A_equation.1]
  have he (n : ℕ) : eCoeff A n = (a n : ℚ) := (integral_coefficients n).symm
  norm_num [iterate, composition_two, composition_one, identity, he,
    initial_values.2.1, initial_values.2.2.1]

#print axioms mod_four
#print axioms fourth_coeff_divisible
#print axioms unique_solution
#print axioms integral_coefficients

end D5.S1.Recurrence.Residue.QuarticEGFModFour
