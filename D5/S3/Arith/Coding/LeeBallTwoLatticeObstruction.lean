/- GID: D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/Coding/LeeBallTwoLatticeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The radius-two Lee ball has no injective index-25 lattice quotient in Z cubed. -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/- Library-search audit trail (2026-09-05):
   * Current-tree name and conclusion-shape searches found no Lee-ball,
     Golomb--Welch, index-25 quotient, or matching moment declaration.
   * Pinned Mathlib supplies finite sums, cyclic-group classification tools,
     ZMod module structure, and finite-dimensional cardinality, but no Lee
     metric or perfect Lee-code obstruction.
   * The proof independently verifies the three-dimensional lattice case;
     it makes no assertion about non-lattice tilings or other radii.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Coding.LeeBallTwoLatticeObstruction

private abbrev Point := ℤ × ℤ × ℤ
private abbrev R25 := ZMod 25
private abbrev F5 := ZMod 5

/-- The complete radius-two Lee ball in `ℤ × ℤ × ℤ`. -/
def leeBallTwo : Finset (ℤ × ℤ × ℤ) :=
  {(-2, 0, 0),
   (-1, -1, 0), (-1, 0, -1), (-1, 0, 0), (-1, 0, 1), (-1, 1, 0),
   (0, -2, 0), (0, -1, -1), (0, -1, 0), (0, -1, 1),
   (0, 0, -2), (0, 0, -1), (0, 0, 0), (0, 0, 1), (0, 0, 2),
   (0, 1, -1), (0, 1, 0), (0, 1, 1), (0, 2, 0),
   (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 1, 0),
   (2, 0, 0)}

/-- Membership in the enumerated ball is exactly the radius-two Lee inequality. -/
theorem mem_leeBallTwo_iff (x : ℤ × ℤ × ℤ) :
    x ∈ leeBallTwo ↔ |x.1| + |x.2.1| + |x.2.2| ≤ 2 := by
  rcases x with ⟨x0, ⟨x1, x2⟩⟩
  change (x0, x1, x2) ∈ leeBallTwo ↔ |x0| + |x1| + |x2| ≤ 2
  constructor
  · intro h
    simp only [leeBallTwo, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with
      (h | h | h | h | h | h | h | h | h | h | h | h | h |
       h | h | h | h | h | h | h | h | h | h | h | h)
    all_goals
      rcases Prod.ext_iff.mp h with ⟨h0, h12⟩
      rcases Prod.ext_iff.mp h12 with ⟨h1, h2⟩
      simp at h0 h1 h2
      subst x0
      subst x1
      subst x2
      norm_num
  · intro h
    have h0 : |x0| ≤ 2 := by
      have h1 : 0 ≤ |x1| := abs_nonneg x1
      have h2 : 0 ≤ |x2| := abs_nonneg x2
      omega
    have h1 : |x1| ≤ 2 := by
      have h0' : 0 ≤ |x0| := abs_nonneg x0
      have h2 : 0 ≤ |x2| := abs_nonneg x2
      omega
    have h2 : |x2| ≤ 2 := by
      have h0' : 0 ≤ |x0| := abs_nonneg x0
      have h1' : 0 ≤ |x1| := abs_nonneg x1
      omega
    rcases abs_le.mp h0 with ⟨hx0l, hx0u⟩
    rcases abs_le.mp h1 with ⟨hx1l, hx1u⟩
    rcases abs_le.mp h2 with ⟨hx2l, hx2u⟩
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2
    all_goals norm_num at h
    all_goals decide

/-- The radius-two Lee ball in dimension three has twenty-five points. -/
theorem leeBallTwo_card : leeBallTwo.card = 25 := by
  exact Classical.choice (show Nonempty (leeBallTwo.card = 25) from ⟨by decide⟩)

private def pointCoordinates (x : Point) : Fin 3 → ℤ :=
  ![x.1, x.2.1, x.2.2]

private def scalarProduct25 (a : Fin 3 → R25) (x : Point) : R25 :=
  ∑ i, a i * (pointCoordinates x i : R25)

private def powerSum25 (a : Fin 3 → R25) (j : ℕ) : R25 :=
  ∑ i, a i ^ j

/-- The second moment of every `ZMod 25` linear readout of the Lee ball. -/
theorem leeBallTwo_second_moment (a : Fin 3 → ZMod 25) :
    (∑ x ∈ leeBallTwo,
      (∑ i, a i * (![x.1, x.2.1, x.2.2] i : ZMod 25)) ^ 2) =
        18 * ∑ i, a i ^ 2 := by
  simp [leeBallTwo, Fin.sum_univ_succ]
  ring

/-- The fourth moment of every `ZMod 25` linear readout of the Lee ball. -/
theorem leeBallTwo_fourth_moment (a : Fin 3 → ZMod 25) :
    (∑ x ∈ leeBallTwo,
      (∑ i, a i * (![x.1, x.2.1, x.2.2] i : ZMod 25)) ^ 4) =
        30 * (∑ i, a i ^ 4) + 12 * (∑ i, a i ^ 2) ^ 2 := by
  simp [leeBallTwo, Fin.sum_univ_succ]
  ring

private theorem all_residues_second_moment25 : (∑ y : R25, y ^ 2) = 0 := by
  decide

private theorem all_residues_fourth_moment25 : (∑ y : R25, y ^ 4) = 20 := by
  decide

private def reduceFive : R25 →+* F5 :=
  ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5)

private theorem five_mul_eq_twenty_reduces_to_four (z : R25) (h : 5 * z = 20) :
    reduceFive z = 4 := by
  have hval := congrArg ZMod.val h
  rw [ZMod.val_mul, ZMod.val_ofNat, ZMod.val_ofNat] at hval
  norm_num at hval
  rw [reduceFive, ZMod.castHom_apply, ZMod.cast_eq_val]
  apply ZMod.val_injective 5
  rw [ZMod.val_natCast, ZMod.val_ofNat]
  norm_num
  have hz := z.val_lt
  omega

private theorem three_fourth_powers_ne_four (b : Fin 3 → F5) :
    (∑ i, b i ^ 4) ≠ 4 := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfourth (z : F5) : z ^ 4 = if z ≠ 0 then 1 else 0 := by
    simpa using ZMod.pow_card_sub_one z
  simp only [Fin.sum_univ_succ, hfourth]
  by_cases h0 : b 0 = 0 <;>
    by_cases h1 : b 1 = 0 <;>
      by_cases h2 : b 2 = 0 <;> simp_all <;> decide

private theorem image_eq_univ_of_injOn25 (a : Fin 3 → R25)
    (hinj : Set.InjOn (scalarProduct25 a) leeBallTwo) :
    leeBallTwo.image (scalarProduct25 a) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_iff.mpr hinj, leeBallTwo_card]
  norm_num [R25, ZMod.card]

private theorem scalarProduct25_not_injective (a : Fin 3 → R25) :
    ¬ Set.InjOn (scalarProduct25 a) leeBallTwo := by
  intro hinj
  have himage := image_eq_univ_of_injOn25 a hinj
  have hsum2 :
      (∑ x ∈ leeBallTwo, scalarProduct25 a x ^ 2) = ∑ y : R25, y ^ 2 := by
    calc
      _ = ∑ y ∈ leeBallTwo.image (scalarProduct25 a), y ^ 2 :=
        (Finset.sum_image hinj).symm
      _ = _ := by simp [himage]
  have hsum4 :
      (∑ x ∈ leeBallTwo, scalarProduct25 a x ^ 4) = ∑ y : R25, y ^ 4 := by
    calc
      _ = ∑ y ∈ leeBallTwo.image (scalarProduct25 a), y ^ 4 :=
        (Finset.sum_image hinj).symm
      _ = _ := by simp [himage]
  have hs2 : 18 * powerSum25 a 2 = 0 := by
    calc
      _ = ∑ x ∈ leeBallTwo, scalarProduct25 a x ^ 2 := by
        simpa [scalarProduct25, pointCoordinates, powerSum25] using
          (leeBallTwo_second_moment a).symm
      _ = ∑ y : R25, y ^ 2 := hsum2
      _ = 0 := all_residues_second_moment25
  have hpowerSum2 : powerSum25 a 2 = 0 := by
    calc
      powerSum25 a 2 = (126 : R25) * powerSum25 a 2 := by
        rw [show (126 : R25) = 1 by decide]
        simp
      _ = 7 * (18 * powerSum25 a 2) := by ring
      _ = 0 := by rw [hs2]; simp
  have hs4 : 30 * powerSum25 a 4 + 12 * powerSum25 a 2 ^ 2 = 20 := by
    calc
      _ = ∑ x ∈ leeBallTwo, scalarProduct25 a x ^ 4 := by
        simpa [scalarProduct25, pointCoordinates, powerSum25] using
          (leeBallTwo_fourth_moment a).symm
      _ = ∑ y : R25, y ^ 4 := hsum4
      _ = 20 := all_residues_fourth_moment25
  have hfive : 5 * powerSum25 a 4 = 20 := by
    calc
      _ = 30 * powerSum25 a 4 + 12 * powerSum25 a 2 ^ 2 := by
        rw [hpowerSum2]
        rw [show (30 : R25) = 5 by decide]
        simp
      _ = 20 := hs4
  have hreduced : reduceFive (powerSum25 a 4) = 4 :=
    five_mul_eq_twenty_reduces_to_four _ hfive
  have hthree : (∑ i, (reduceFive (a i)) ^ 4) = 4 := by
    simpa [powerSum25] using hreduced
  exact three_fourth_powers_ne_four (fun i ↦ reduceFive (a i)) hthree

/-- No `ZMod 25` coefficient vector gives an injective readout on the Lee ball. -/
theorem zmod25_readout_not_injective :
    ∀ a : Fin 3 → ZMod 25,
      ¬ Set.InjOn
        (fun x : ℤ × ℤ × ℤ ↦
          ∑ i, a i * (![x.1, x.2.1, x.2.2] i : ZMod 25))
        leeBallTwo := by
  intro a
  change ¬ Set.InjOn (scalarProduct25 a) leeBallTwo
  exact scalarProduct25_not_injective a

private def basis0 : Point := (1, 0, 0)
private def basis1 : Point := (0, 1, 0)
private def basis2 : Point := (0, 0, 1)

private def coefficients25 (f : Point →+ R25) : Fin 3 → R25 :=
  ![f basis0, f basis1, f basis2]

private theorem additiveHom_eq_scalarProduct25 (f : Point →+ R25) (x : Point) :
    f x = scalarProduct25 (coefficients25 f) x := by
  have hx : x = x.1 • basis0 + x.2.1 • basis1 + x.2.2 • basis2 := by
    ext <;> simp [basis0, basis1, basis2]
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  simp [scalarProduct25, pointCoordinates, coefficients25, basis0, basis1, basis2,
    Fin.sum_univ_succ]
  ring

private theorem no_cyclic_quotient_injective
    (L : AddSubgroup Point) (e : (Point ⧸ L) ≃+ R25) :
    ¬ Set.InjOn (fun x : Point ↦ e (QuotientAddGroup.mk x)) leeBallTwo := by
  let f : Point →+ R25 := e.toAddMonoidHom.comp (QuotientAddGroup.mk' L)
  have hfun : (fun x : Point ↦ e (QuotientAddGroup.mk x)) =
      scalarProduct25 (coefficients25 f) := by
    funext x
    exact additiveHom_eq_scalarProduct25 f x
  rw [hfun]
  exact scalarProduct25_not_injective (coefficients25 f)

private def scalarProductFive (a : Fin 3 → F5) (x : Point) : F5 :=
  ∑ i, a i * (pointCoordinates x i : F5)

private def powerSumFive (a : Fin 3 → F5) (j : ℕ) : F5 :=
  ∑ i, a i ^ j

private def linearCombinationFive
    (a b : Fin 3 → F5) (lambda mu : F5) : Fin 3 → F5 :=
  fun i ↦ lambda * a i + mu * b i

private def pairReadoutFive (a b : Fin 3 → F5) (x : Point) : F5 × F5 :=
  (scalarProductFive a x, scalarProductFive b x)

private theorem second_moment_five (a : Fin 3 → F5) :
    (∑ x ∈ leeBallTwo, scalarProductFive a x ^ 2) = 18 * powerSumFive a 2 := by
  simp [leeBallTwo, scalarProductFive, pointCoordinates, powerSumFive, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 100000 in
private theorem nonzero_linear_functional_fiber_card_five :
    ∀ lambda mu : F5,
      (lambda, mu) ≠ (0, 0) →
        ∀ y : F5,
          (Finset.univ.filter
            (fun p : F5 × F5 ↦ lambda * p.1 + mu * p.2 = y)).card = 5 := by
  decide

private theorem all_pair_linear_second_moment_five :
    ∀ lambda mu : F5,
      (∑ p : F5 × F5, (lambda * p.1 + mu * p.2) ^ 2) = 0 := by
  intro lambda mu
  by_cases hzero : (lambda, mu) = (0, 0)
  · have hlambda : lambda = 0 := congrArg Prod.fst hzero
    have hmu : mu = 0 := congrArg Prod.snd hzero
    simp [hlambda, hmu]
  · let linear : F5 × F5 → F5 := fun p ↦ lambda * p.1 + mu * p.2
    have hfiber := nonzero_linear_functional_fiber_card_five lambda mu hzero
    calc
      (∑ p : F5 × F5, (lambda * p.1 + mu * p.2) ^ 2) =
          ∑ p : F5 × F5, linear p ^ 2 := by rfl
      _ = ∑ y : F5,
          ∑ p ∈ Finset.univ with linear p = y, linear p ^ 2 :=
        (Finset.sum_fiberwise Finset.univ linear (fun p ↦ linear p ^ 2)).symm
      _ = ∑ y : F5,
          ∑ p ∈ Finset.univ with linear p = y, y ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = 0 := by
        have hfive : (5 : F5) = 0 := by decide
        simp [linear, hfiber, hfive]

private theorem scalarProductFive_linearCombination
    (a b : Fin 3 → F5) (lambda mu : F5) (x : Point) :
    scalarProductFive (linearCombinationFive a b lambda mu) x =
      lambda * (pairReadoutFive a b x).1 + mu * (pairReadoutFive a b x).2 := by
  simp [scalarProductFive, linearCombinationFive, pairReadoutFive, Fin.sum_univ_succ]
  ring

private theorem pairReadoutFive_image_eq_univ
    (a b : Fin 3 → F5) (hinj : Set.InjOn (pairReadoutFive a b) leeBallTwo) :
    leeBallTwo.image (pairReadoutFive a b) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_iff.mpr hinj, leeBallTwo_card]
  norm_num [F5, ZMod.card]

set_option maxHeartbeats 800000 in
private theorem readout_linear_second_moment_five
    (a b : Fin 3 → F5) (lambda mu : F5)
    (hinj : Set.InjOn (pairReadoutFive a b) leeBallTwo) :
    (∑ x ∈ leeBallTwo,
      scalarProductFive (linearCombinationFive a b lambda mu) x ^ 2) = 0 := by
  have himage := pairReadoutFive_image_eq_univ a b hinj
  have hsum_image :
      (∑ p ∈ leeBallTwo.image (pairReadoutFive a b),
        (lambda * p.1 + mu * p.2) ^ 2) =
        ∑ x ∈ leeBallTwo,
          (lambda * (pairReadoutFive a b x).1 +
            mu * (pairReadoutFive a b x).2) ^ 2 :=
    Finset.sum_image hinj
  calc
    (∑ x ∈ leeBallTwo,
        scalarProductFive (linearCombinationFive a b lambda mu) x ^ 2) =
        ∑ x ∈ leeBallTwo,
          (lambda * (pairReadoutFive a b x).1 +
            mu * (pairReadoutFive a b x).2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [scalarProductFive_linearCombination]
    _ = ∑ p ∈ leeBallTwo.image (pairReadoutFive a b),
          (lambda * p.1 + mu * p.2) ^ 2 := hsum_image.symm
    _ = ∑ p : F5 × F5, (lambda * p.1 + mu * p.2) ^ 2 := by
      rw [himage]
    _ = 0 := all_pair_linear_second_moment_five lambda mu

private theorem readout_span_isotropic_five
    (a b : Fin 3 → F5) (hinj : Set.InjOn (pairReadoutFive a b) leeBallTwo) :
    ∀ lambda mu : F5,
      powerSumFive (linearCombinationFive a b lambda mu) 2 = 0 := by
  intro lambda mu
  have hmoment := readout_linear_second_moment_five a b lambda mu hinj
  have hscaled :
      18 * powerSumFive (linearCombinationFive a b lambda mu) 2 = 0 := by
    calc
      _ = ∑ x ∈ leeBallTwo,
          scalarProductFive (linearCombinationFive a b lambda mu) x ^ 2 :=
        (second_moment_five _).symm
      _ = 0 := hmoment
  have hunit : (2 : F5) * 18 = 1 := by decide
  calc
    powerSumFive (linearCombinationFive a b lambda mu) 2 =
        1 * powerSumFive (linearCombinationFive a b lambda mu) 2 := by simp
    _ = (2 * 18) * powerSumFive (linearCombinationFive a b lambda mu) 2 := by
      rw [hunit]
    _ = 2 * (18 * powerSumFive (linearCombinationFive a b lambda mu) 2) := by ring
    _ = 0 := by rw [hscaled]; simp

set_option maxRecDepth 100000 in
private theorem isotropic_pair_dependent_five :
    ∀ a b : Fin 3 → F5,
      powerSumFive a 2 = 0 →
      powerSumFive b 2 = 0 →
      powerSumFive (linearCombinationFive a b 1 1) 2 = 0 →
      ∃ lambda mu : F5,
        (lambda, mu) ≠ (0, 0) ∧
          ∀ i, lambda * a i + mu * b i = 0 := by
  decide

private theorem pairReadoutFive_has_no_nontrivial_relation
    (a b : Fin 3 → F5) (hinj : Set.InjOn (pairReadoutFive a b) leeBallTwo) :
    ¬ ∃ lambda mu : F5,
        (lambda, mu) ≠ (0, 0) ∧
          ∀ i, lambda * a i + mu * b i = 0 := by
  intro hrelation
  rcases hrelation with ⟨lambda, mu, hnonzero, hcoeff⟩
  have himage := pairReadoutFive_image_eq_univ a b hinj
  have hpreimage (p : F5 × F5) :
      ∃ x ∈ leeBallTwo, pairReadoutFive a b x = p := by
    have hp : p ∈ leeBallTwo.image (pairReadoutFive a b) := by
      rw [himage]
      simp
    exact Finset.mem_image.mp hp
  have hfunctional_zero (x : Point) :
      lambda * (pairReadoutFive a b x).1 +
        mu * (pairReadoutFive a b x).2 = 0 := by
    rw [← scalarProductFive_linearCombination]
    simp [scalarProductFive, linearCombinationFive, hcoeff]
  by_cases hlambda : lambda = 0
  · have hmu : mu ≠ 0 := by
      intro hmu
      apply hnonzero
      simp [hlambda, hmu]
    obtain ⟨x, hx, hreadout⟩ := hpreimage (0, 1)
    have hzero := hfunctional_zero x
    rw [hreadout] at hzero
    simp [hlambda] at hzero
    exact hmu hzero
  · obtain ⟨x, hx, hreadout⟩ := hpreimage (1, 0)
    have hzero := hfunctional_zero x
    rw [hreadout] at hzero
    simp at hzero
    exact hlambda hzero

private theorem pairReadoutFive_not_injective (a b : Fin 3 → F5) :
    ¬ Set.InjOn (pairReadoutFive a b) leeBallTwo := by
  intro hinj
  have hisotropic := readout_span_isotropic_five a b hinj
  have hcombA : linearCombinationFive a b 1 0 = a := by
    funext i
    simp [linearCombinationFive]
  have hcombB : linearCombinationFive a b 0 1 = b := by
    funext i
    simp [linearCombinationFive]
  have ha : powerSumFive a 2 = 0 := by
    simpa [hcombA] using hisotropic 1 0
  have hb : powerSumFive b 2 = 0 := by
    simpa [hcombB] using hisotropic 0 1
  have hab : powerSumFive (linearCombinationFive a b 1 1) 2 = 0 :=
    hisotropic 1 1
  have hdependent := isotropic_pair_dependent_five a b ha hb hab
  exact pairReadoutFive_has_no_nontrivial_relation a b hinj hdependent

/-- No pair of `ZMod 5` coefficient vectors gives an injective paired readout. -/
theorem zmod5_pair_readout_not_injective :
    ∀ a b : Fin 3 → ZMod 5,
      ¬ Set.InjOn
        (fun x : ℤ × ℤ × ℤ ↦
          (∑ i, a i * (![x.1, x.2.1, x.2.2] i : ZMod 5),
           ∑ i, b i * (![x.1, x.2.1, x.2.2] i : ZMod 5)))
        leeBallTwo := by
  intro a b
  have hfun :
      (fun x : Point ↦
        (∑ i, a i * (![x.1, x.2.1, x.2.2] i : F5),
         ∑ i, b i * (![x.1, x.2.1, x.2.2] i : F5))) =
        pairReadoutFive a b := by
    funext x
    simp [pairReadoutFive, scalarProductFive, pointCoordinates]
  rw [hfun]
  exact pairReadoutFive_not_injective a b

private def coefficientsFive (f : Point →+ F5) : Fin 3 → F5 :=
  ![f basis0, f basis1, f basis2]

private theorem additiveHom_eq_scalarProductFive (f : Point →+ F5) (x : Point) :
    f x = scalarProductFive (coefficientsFive f) x := by
  have hx : x = x.1 • basis0 + x.2.1 • basis1 + x.2.2 • basis2 := by
    ext <;> simp [basis0, basis1, basis2]
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
  simp [scalarProductFive, pointCoordinates, coefficientsFive,
    basis0, basis1, basis2, Fin.sum_univ_succ]
  ring

private theorem no_elementary_quotient_injective
    (L : AddSubgroup Point) (e : (Point ⧸ L) ≃+ F5 × F5) :
    ¬ Set.InjOn (fun x : Point ↦ e (QuotientAddGroup.mk x)) leeBallTwo := by
  let f : Point →+ F5 × F5 :=
    e.toAddMonoidHom.comp (QuotientAddGroup.mk' L)
  let f0 : Point →+ F5 := (AddMonoidHom.fst F5 F5).comp f
  let f1 : Point →+ F5 := (AddMonoidHom.snd F5 F5).comp f
  have hfun : (fun x : Point ↦ e (QuotientAddGroup.mk x)) =
      pairReadoutFive (coefficientsFive f0) (coefficientsFive f1) := by
    funext x
    change f x = pairReadoutFive (coefficientsFive f0) (coefficientsFive f1) x
    apply Prod.ext
    · change f0 x = scalarProductFive (coefficientsFive f0) x
      exact additiveHom_eq_scalarProductFive f0 x
    · change f1 x = scalarProductFive (coefficientsFive f1) x
      exact additiveHom_eq_scalarProductFive f1 x
  rw [hfun]
  exact pairReadoutFive_not_injective (coefficientsFive f0) (coefficientsFive f1)

/-- Every additive commutative group of order twenty-five is cyclic or elementary. -/
theorem addCommGroup_card_twenty_five_classification
    (G : Type*) [AddCommGroup G] (hcard : Nat.card G = 25) :
    Nonempty (G ≃+ ZMod 25) ∨ Nonempty (G ≃+ ZMod 5 × ZMod 5) := by
  letI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  by_cases hcyclic : IsAddCyclic G
  · letI : IsAddCyclic G := hcyclic
    left
    exact ⟨addEquivOfAddCyclicCardEq (G := G) (G' := ZMod 25) (by simpa using hcard)⟩
  · right
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hcardpow : Nat.card G = 5 ^ 2 := by norm_num [hcard]
    have hexponent : AddMonoid.exponent G = 5 :=
      (not_isAddCyclic_iff_exponent_eq_prime (by norm_num) hcardpow).mp hcyclic
    have hfive : ∀ x : G, 5 • x = 0 :=
      AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp (by simp [hexponent])
    letI : Module F5 G := AddCommGroup.zmodModule hfive
    have hpow : 5 ^ Module.finrank F5 G = 5 ^ 2 := by
      calc
        5 ^ Module.finrank F5 G = Nat.card G := by
          simpa using (Module.natCard_eq_pow_finrank (K := F5) (V := G)).symm
        _ = 5 ^ 2 := hcardpow
    have hfinrank : Module.finrank F5 G = 2 :=
      Nat.pow_right_injective (by norm_num) hpow
    let elin : G ≃ₗ[F5] (Fin 2 → F5) :=
      LinearEquiv.ofFinrankEq G (Fin 2 → F5) (by simpa [hfinrank])
    exact ⟨(elin.trans (LinearEquiv.finTwoArrow F5 F5)).toAddEquiv⟩

private theorem no_classified_index_twenty_five_lattice_injective
    (L : AddSubgroup Point)
    (hclassification :
      Nonempty ((Point ⧸ L) ≃+ ZMod 25) ∨
        Nonempty ((Point ⧸ L) ≃+ ZMod 5 × ZMod 5)) :
    ¬ Set.InjOn (QuotientAddGroup.mk : Point → Point ⧸ L) leeBallTwo := by
  intro hinj
  cases hclassification with
  | inl he =>
      rcases he with ⟨e⟩
      apply no_cyclic_quotient_injective L e
      intro x hx y hy hxy
      apply hinj hx hy
      exact e.injective hxy
  | inr he =>
      rcases he with ⟨e⟩
      apply no_elementary_quotient_injective L e
      intro x hx y hy hxy
      apply hinj hx hy
      exact e.injective hxy

/-- The quotient map of every index-twenty-five lattice in `ℤ³` identifies two
points of the radius-two Lee ball. -/
theorem leeBallTwo_lattice_obstruction
    (L : AddSubgroup (ℤ × ℤ × ℤ))
    (hcard : Nat.card ((ℤ × ℤ × ℤ) ⧸ L) = 25) :
    ¬ Set.InjOn
      (QuotientAddGroup.mk : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) ⧸ L)
      leeBallTwo := by
  exact no_classified_index_twenty_five_lattice_injective L
    (addCommGroup_card_twenty_five_classification ((ℤ × ℤ × ℤ) ⧸ L) hcard)

#print axioms mem_leeBallTwo_iff
#print axioms leeBallTwo_card
#print axioms leeBallTwo_second_moment
#print axioms leeBallTwo_fourth_moment
#print axioms zmod25_readout_not_injective
#print axioms zmod5_pair_readout_not_injective
#print axioms addCommGroup_card_twenty_five_classification
#print axioms leeBallTwo_lattice_obstruction

end D5.S3.Arith.Coding.LeeBallTwoLatticeObstruction
