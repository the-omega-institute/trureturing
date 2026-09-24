/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartFixedSupportBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartFixedSupportBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-support sums of source-root contribution norms. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
noncomputable section
namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartFixedSupportBound
open scoped BigOperators
open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity
open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound
open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound

open private sylvester_pos sylvester_sub_one_eq_prod two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private sylvester_quotient_sum_for_root_bound from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound

open private sourceLocalRootContributionPolynomial from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient
private abbrev q (i : ℕ) : ℕ := sylvester (i + 1)

private abbrev period (n : ℕ) : ℕ := sylvester (n + 1) - 1

private def roots (m : ℕ) : Finset ℂ := Polynomial.nthRootsFinset m (1 : ℂ)

private def rootCoordinates (n : ℕ) :
    {z // z ∈ roots (period n)} → (i : Fin n) → {u // u ∈ roots (q i)} :=
  fun z i => ⟨z.1 ^ (period n / q i), by
    have hM : 0 < period n := Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
    have hq : 0 < q i := sylvester_pos _
    have hqM : q i ∣ period n := by
      rw [show period n = ∏ j : Fin n, q j by
        calc
          period n = ∏ j ∈ Finset.range (n + 1), sylvester j :=
            sylvester_sub_one_eq_prod (n + 1) (by omega)
          _ = ∏ j ∈ Finset.range n, sylvester (j + 1) := by
            rw [Finset.prod_range_succ']
            simp [sylvester]
          _ = ∏ j : Fin n, q j := by
            symm
            exact Fin.prod_univ_eq_prod_range (fun j => sylvester (j + 1)) n]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    rw [roots, Polynomial.mem_nthRootsFinset hq]
    rw [← pow_mul, Nat.div_mul_cancel hqM]
    exact (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp z.2⟩

private lemma rootCoordinates_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (rootCoordinates n) := by
  intro z w hzw
  have hM : 0 < period n := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hzM : z.1 ^ period n = 1 :=
    (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp z.2
  have hwM : w.1 ^ period n = 1 :=
    (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp w.2
  have hpowSum (x : ℂ) :
      x ^ (∑ i : Fin n, period n / q i) =
        ∏ i : Fin n, x ^ (period n / q i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
  have hquotientSum : ∑ i : Fin n, period n / q i = period n - 1 := by
    have hallRange : ∏ i ∈ Finset.range n, sylvester (i + 1) = period n := by
      change (∏ i ∈ Finset.range n, sylvester (i + 1)) = sylvester (n + 1) - 1
      rw [sylvester_sub_one_eq_prod (n + 1) (by omega), Finset.prod_range_succ']
      simp [sylvester]
    change (∑ i : Fin n, period n / sylvester (i.1 + 1)) = period n - 1
    calc
      ∑ i : Fin n, period n / sylvester (i.1 + 1) =
          ∑ i ∈ Finset.range n, period n / sylvester (i + 1) :=
        Fin.sum_univ_eq_sum_range
          (fun i : ℕ => period n / sylvester (i + 1)) n
      _ = ∑ i ∈ Finset.range n,
          (∏ j ∈ Finset.range n, sylvester (j + 1)) / sylvester (i + 1) := by
        rw [hallRange]
      _ = (∏ j ∈ Finset.range n, sylvester (j + 1)) - 1 :=
        sylvester_quotient_sum_for_root_bound n hn
      _ = period n - 1 := by rw [hallRange]
  have hprev : z.1 ^ (period n - 1) = w.1 ^ (period n - 1) := by
    rw [← hquotientSum, hpowSum, hpowSum]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg Subtype.val (congrFun hzw i)
  have hsplit : period n = (period n - 1) + 1 := by omega
  have hz0 : z.1 ^ (period n - 1) ≠ 0 := pow_ne_zero _
    (Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero z.2)
  have hzfact : z.1 ^ (period n - 1) * z.1 = 1 := by
    calc
      z.1 ^ (period n - 1) * z.1 = z.1 ^ ((period n - 1) + 1) := by
        rw [pow_add, pow_one]
      _ = z.1 ^ period n := congrArg (fun k : ℕ => z.1 ^ k) hsplit.symm
      _ = 1 := hzM
  have hwfact : w.1 ^ (period n - 1) * w.1 = 1 := by
    calc
      w.1 ^ (period n - 1) * w.1 = w.1 ^ ((period n - 1) + 1) := by
        rw [pow_add, pow_one]
      _ = w.1 ^ period n := congrArg (fun k : ℕ => w.1 ^ k) hsplit.symm
      _ = 1 := hwM
  apply Subtype.ext
  apply mul_left_cancel₀ hz0
  calc
    z.1 ^ (period n - 1) * z.1 = 1 := hzfact
    _ = w.1 ^ (period n - 1) * w.1 := hwfact.symm
    _ = z.1 ^ (period n - 1) * w.1 := by rw [hprev]

/-- The direct power-coordinate map is an exact root equivalence.  Its
injectivity uses the Sylvester Egyptian identity, not an ambient CRT axiom. -/
noncomputable def sylvesterRootEquiv (n : ℕ) (hn : 1 ≤ n) :
    {z // z ∈ roots (period n)} ≃ ((i : Fin n) → {u // u ∈ roots (q i)}) :=
  Equiv.ofBijective (rootCoordinates n)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨rootCoordinates_injective n hn, by
        have hM : period n ≠ 0 := (Nat.sub_pos_of_lt
          (lt_of_lt_of_le Nat.one_lt_two
            (two_le_sylvester (n + 1) (by omega)))).ne'
        have hrootM : (roots (period n)).card = period n := by
          simpa [roots] using
            (Complex.isPrimitiveRoot_exp (period n) hM).card_nthRootsFinset
        have hrootq (i : Fin n) : (roots (q i)).card = q i := by
          have hq : q i ≠ 0 := (sylvester_pos _).ne'
          simpa [roots] using
            (Complex.isPrimitiveRoot_exp (q i) hq).card_nthRootsFinset
        rw [Fintype.card_coe, hrootM, Fintype.card_pi]
        simp_rw [Fintype.card_coe, hrootq]
        calc
          period n = ∏ i ∈ Finset.range (n + 1), sylvester i :=
            sylvester_sub_one_eq_prod (n + 1) (by omega)
          _ = ∏ i ∈ Finset.range n, sylvester (i + 1) := by
            rw [Finset.prod_range_succ']
            simp [sylvester]
          _ = ∏ i : Fin n, q i := by
            symm
            exact Fin.prod_univ_eq_prod_range (fun i => sylvester (i + 1)) n⟩)

private abbrev supportRoots (n : ℕ) (R : Finset (Fin n)) :=
  {z : ℂ // z ∈ (roots (period n)).filter (fun z => z ≠ 1 ∧
    Finset.univ.filter (fun i : Fin n => z ^ (period n / q i) ≠ 1) = R)}

private abbrev nontrivialCoordinates (n : ℕ) (R : Finset (Fin n)) :=
  (i : {i // i ∈ R}) → {u : ℂ // u ∈ (roots (q i.1)).erase 1}

private def restrictedForward (n : ℕ) (hn : 1 ≤ n) (R : Finset (Fin n)) :
    supportRoots n R → nontrivialCoordinates n R := fun z i =>
  ⟨(sylvesterRootEquiv n hn
      ⟨z.1, (Finset.mem_filter.mp z.2).1⟩ i.1).1,
    Finset.mem_erase.mpr ⟨by
      have hi : i.1 ∈ Finset.univ.filter
          (fun j : Fin n => z.1 ^ (period n / q j) ≠ 1) := by
        rw [(Finset.mem_filter.mp z.2).2.2]
        exact i.2
      exact (Finset.mem_filter.mp hi).2,
      (sylvesterRootEquiv n hn
        ⟨z.1, (Finset.mem_filter.mp z.2).1⟩ i.1).2⟩⟩

private def extendCoordinates (n : ℕ) (R : Finset (Fin n))
    (u : nontrivialCoordinates n R) :
    (i : Fin n) → {v : ℂ // v ∈ roots (q i)} := fun i =>
  if hi : i ∈ R then
    ⟨(u ⟨i, hi⟩).1, (Finset.mem_erase.mp (u ⟨i, hi⟩).2).2⟩
  else
    ⟨1, by
      rw [roots, Polynomial.mem_nthRootsFinset (sylvester_pos _)]
      simp⟩

private def restrictedReverse (n : ℕ) (hn : 1 ≤ n) (R : Finset (Fin n))
    (hR : R.Nonempty) : nontrivialCoordinates n R → supportRoots n R := fun u =>
  let z := (sylvesterRootEquiv n hn).symm (extendCoordinates n R u)
  have hs : Finset.univ.filter (fun i : Fin n =>
      z.1 ^ (period n / q i) ≠ 1) = R := by
    ext i
    have hcoord := congrArg Subtype.val
      (congrFun ((sylvesterRootEquiv n hn).apply_symm_apply
        (extendCoordinates n R u)) i)
    change z.1 ^ (period n / q i) = (extendCoordinates n R u i).1 at hcoord
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ R
    · rw [hcoord]
      simp [extendCoordinates, hi, (Finset.mem_erase.mp (u ⟨i, hi⟩).2).1]
    · rw [hcoord]
      simp [extendCoordinates, hi]
  ⟨z.1, Finset.mem_filter.mpr ⟨z.2, by
      intro hz
      rw [hz] at hs
      have : (Finset.univ.filter fun i : Fin n =>
          (1 : ℂ) ^ (period n / q i) ≠ 1) = ∅ := by simp
      exact hR.ne_empty (hs.symm.trans this),
    hs⟩⟩
/-- Roots having exactly support `R` are equivalent to independently chosen
nontrivial roots in the Sylvester factors indexed by `R`. -/
noncomputable def sylvesterRestrictedRootEquiv (n : ℕ) (hn : 1 ≤ n)
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    supportRoots n R ≃ nontrivialCoordinates n R where
  toFun := restrictedForward n hn R
  invFun := restrictedReverse n hn R hR
  left_inv := by
    intro z
    have hroot :
        (sylvesterRootEquiv n hn).symm
          (extendCoordinates n R (restrictedForward n hn R z)) =
          (⟨z.1, (Finset.mem_filter.mp z.2).1⟩ :
            {x // x ∈ roots (period n)}) := by
      apply (sylvesterRootEquiv n hn).injective
      funext i
      by_cases hi : i ∈ R
      · apply Subtype.ext
        simp [restrictedForward, extendCoordinates, hi]
      · apply Subtype.ext
        have hnot : z.1 ^ (period n / q i) = 1 := by
          by_contra hne
          have : i ∈ R := by
            rw [← (Finset.mem_filter.mp z.2).2.2]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          exact hi this
        simp [extendCoordinates, hi, sylvesterRootEquiv, rootCoordinates, hnot]
    apply Subtype.ext
    exact congrArg (fun x : {x // x ∈ roots (period n)} => x.1) hroot
  right_inv := by
    intro u
    funext i
    apply Subtype.ext
    have hi := i.2
    simp [restrictedForward, restrictedReverse, extendCoordinates, hi]
private abbrev supportPeriod (n : ℕ) (R : Finset (Fin n)) : ℕ :=
  ∏ i ∈ R, q i
/-- A root with support `R` has order dividing the product of the Sylvester
factors in `R`. -/
theorem supportRoot_pow_supportPeriod (n : ℕ) (hn : 1 ≤ n)
    (R : Finset (Fin n)) (z : supportRoots n R) :
    z.1 ^ supportPeriod n R = 1 := by
  have hM : 0 < period n := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hzM : z.1 ^ period n = 1 :=
    (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp
      (Finset.mem_filter.mp z.2).1
  let zS : {x // x ∈ roots (period n)} :=
    ⟨z.1 ^ supportPeriod n R, by
      change z.1 ^ supportPeriod n R ∈
        Polynomial.nthRootsFinset (period n) (1 : ℂ)
      rw [Polynomial.mem_nthRootsFinset hM]
      calc
        (z.1 ^ supportPeriod n R) ^ period n =
            z.1 ^ (supportPeriod n R * period n) := (pow_mul _ _ _).symm
        _ = z.1 ^ (period n * supportPeriod n R) := by rw [Nat.mul_comm]
        _ = (z.1 ^ period n) ^ supportPeriod n R := pow_mul _ _ _
        _ = 1 := by rw [hzM, one_pow]⟩
  let oneRoot : {x // x ∈ roots (period n)} :=
    ⟨1, by
      rw [roots, Polynomial.mem_nthRootsFinset hM]
      simp⟩
  have hcoords : rootCoordinates n zS = rootCoordinates n oneRoot := by
    funext i
    apply Subtype.ext
    change (z.1 ^ supportPeriod n R) ^ (period n / q i) =
      (1 : ℂ) ^ (period n / q i)
    rw [one_pow]
    calc
      (z.1 ^ supportPeriod n R) ^ (period n / q i) =
          z.1 ^ (supportPeriod n R * (period n / q i)) := (pow_mul _ _ _).symm
      _ = z.1 ^ ((period n / q i) * supportPeriod n R) := by
        rw [Nat.mul_comm]
      _ = (z.1 ^ (period n / q i)) ^ supportPeriod n R :=
        pow_mul _ _ _
      _ = 1 := by
        by_cases hi : i ∈ R
        · obtain ⟨k, hk⟩ :=
            Finset.dvd_prod_of_mem (fun j : Fin n => q j) hi
          have hqi : (z.1 ^ (period n / q i)) ^ q i = 1 := by
            have hqiM : q i ∣ period n := by
              rw [show period n = ∏ j : Fin n, q j by
                calc
                  period n = ∏ j ∈ Finset.range (n + 1), sylvester j :=
                    sylvester_sub_one_eq_prod (n + 1) (by omega)
                  _ = ∏ j ∈ Finset.range n, sylvester (j + 1) := by
                    rw [Finset.prod_range_succ']
                    simp [sylvester]
                  _ = ∏ j : Fin n, q j := by
                    symm
                    exact Fin.prod_univ_eq_prod_range
                      (fun j => sylvester (j + 1)) n]
              exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
            calc
              (z.1 ^ (period n / q i)) ^ q i =
                  z.1 ^ ((period n / q i) * q i) := (pow_mul _ _ _).symm
              _ = z.1 ^ period n := congrArg (fun k : ℕ => z.1 ^ k)
                (Nat.div_mul_cancel hqiM)
              _ = 1 := hzM
          calc
            (z.1 ^ (period n / q i)) ^ supportPeriod n R =
                (z.1 ^ (period n / q i)) ^ (q i * k) :=
              congrArg (fun e : ℕ => (z.1 ^ (period n / q i)) ^ e) hk
            _ = ((z.1 ^ (period n / q i)) ^ q i) ^ k :=
              pow_mul _ _ _
            _ = 1 := by rw [hqi, one_pow]
        · have hnot : z.1 ^ (period n / q i) = 1 := by
            by_contra hne
            have : i ∈ R := by
              rw [← (Finset.mem_filter.mp z.2).2.2]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
            exact hi this
          rw [hnot, one_pow]
  have hzSeq : zS = oneRoot := rootCoordinates_injective n hn hcoords
  exact congrArg Subtype.val hzSeq
private def inverseChordPolynomial (m : ℕ) : Polynomial ℂ :=
  Polynomial.C ((m : ℂ)⁻¹) *
    (Polynomial.X ^ m - (Polynomial.X - 1) ^ m)
private lemma inverseChordPolynomial_natDegree (m : ℕ) (hm : 1 ≤ m) :
    (inverseChordPolynomial m).natDegree = m - 1 := by
  have hcoeff_of_lt (k : ℕ) (hk : k < m) :
      (inverseChordPolynomial m).coeff k =
        -((m : ℂ)⁻¹ * ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ))) := by
    rw [inverseChordPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, if_neg hk.ne]
    rw [show (Polynomial.X - 1 : Polynomial ℂ) =
      Polynomial.X + Polynomial.C (-1) by
        rw [sub_eq_add_neg, ← Polynomial.C_1, ← Polynomial.C_neg]]
    rw [Polynomial.coeff_X_add_C_pow]
    ring
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hmk : m ≤ k := by omega
    have hm0 : m ≠ 0 := by omega
    rw [inverseChordPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow]
    by_cases hkm : k = m
    · subst k
      rw [show (Polynomial.X - 1 : Polynomial ℂ) =
        Polynomial.X + Polynomial.C (-1) by
          rw [sub_eq_add_neg, ← Polynomial.C_1, ← Polynomial.C_neg]]
      rw [Polynomial.coeff_X_add_C_pow]
      simp [hm0]
    · have hmlt : m < k := lt_of_le_of_ne hmk (Ne.symm hkm)
      rw [show (Polynomial.X - 1 : Polynomial ℂ) =
        Polynomial.X + Polynomial.C (-1) by
          rw [sub_eq_add_neg, ← Polynomial.C_1, ← Polynomial.C_neg]]
      rw [Polynomial.coeff_X_add_C_pow]
      simp [hkm, Nat.choose_eq_zero_of_lt hmlt, hm0]
  · have hcoeff : (inverseChordPolynomial m).coeff (m - 1) = 1 := by
      rw [hcoeff_of_lt (m - 1) (by omega)]
      rw [Nat.choose_symm hm, Nat.choose_one_right]
      have hsub : m - (m - 1) = 1 := by omega
      rw [hsub]
      norm_num
      have hmC : (m : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
      field_simp
    rw [hcoeff]
    exact one_ne_zero
private def inverseChordRoots (m : ℕ) : Finset ℂ :=
  ((roots m).erase 1).image fun z => (1 - z)⁻¹
private lemma inverseChordPolynomial_eval_inverseChord (m : ℕ) (hm : 1 ≤ m)
    {z : ℂ} (hz : z ∈ (roots m).erase 1) :
    (inverseChordPolynomial m).eval ((1 - z)⁻¹) = 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hzroot : z ^ m = 1 := by
    have hzmem := (Finset.mem_erase.mp hz).2
    exact (Polynomial.mem_nthRootsFinset (by omega) (1 : ℂ)).mp hzmem
  have hz1 : z ≠ 1 := (Finset.mem_erase.mp hz).1
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hshift : (1 - z)⁻¹ - 1 = z * (1 - z)⁻¹ := by
    field_simp [hden]
    ring
  rw [inverseChordPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, hshift, mul_pow, hzroot]
  ring
private lemma inverseChordRoots_esymm (m j : ℕ) (hm : 1 ≤ m) :
    (inverseChordRoots m).val.esymm j =
      (m.choose (j + 1) : ℂ) / (m : ℂ) := by
  have hcoeff_of_lt (k : ℕ) (hk : k < m) :
      (inverseChordPolynomial m).coeff k =
        -((m : ℂ)⁻¹ * ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ))) := by
    rw [inverseChordPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, if_neg hk.ne]
    rw [show (Polynomial.X - 1 : Polynomial ℂ) =
      Polynomial.X + Polynomial.C (-1) by
        rw [sub_eq_add_neg, ← Polynomial.C_1, ← Polynomial.C_neg]]
    rw [Polynomial.coeff_X_add_C_pow]
    ring
  have hcard : (inverseChordRoots m).card = m - 1 := by
    have hm0 : m ≠ 0 := by omega
    have hrootCard : (roots m).card = m := by
      simpa [roots] using
        (Complex.isPrimitiveRoot_exp m hm0).card_nthRootsFinset
    have hone : (1 : ℂ) ∈ roots m := by
      rw [roots, Polynomial.mem_nthRootsFinset (by omega)]
      simp
    rw [inverseChordRoots, Finset.card_image_of_injective _]
    · rw [Finset.card_erase_of_mem hone, hrootCard]
    · intro z w h
      exact sub_right_inj.mp (inv_injective h)
  by_cases hj : j ≤ m - 1
  · have hmonic : (inverseChordPolynomial m).Monic := by
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
        inverseChordPolynomial_natDegree m hm]
      rw [hcoeff_of_lt (m - 1) (by omega),
        Nat.choose_symm hm, Nat.choose_one_right]
      have hsub : m - (m - 1) = 1 := by omega
      rw [hsub]
      norm_num
      have hmC : (m : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
      field_simp
    have hroots : (inverseChordPolynomial m).roots =
        (inverseChordRoots m).val := by
      apply Polynomial.roots_eq_of_degree_eq_card
      · intro t ht
        rw [inverseChordRoots, Finset.mem_image] at ht
        obtain ⟨z, hz, rfl⟩ := ht
        exact inverseChordPolynomial_eval_inverseChord m hm hz
      · rw [hcard]
        rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
          inverseChordPolynomial_natDegree m hm]
    have hcardRoots : Multiset.card (inverseChordPolynomial m).roots =
        (inverseChordPolynomial m).natDegree := by
      rw [hroots]
      change (inverseChordRoots m).card = (inverseChordPolynomial m).natDegree
      rw [hcard, inverseChordPolynomial_natDegree m hm]
    have hv := Polynomial.coeff_eq_esymm_roots_of_card hcardRoots
      (k := m - 1 - j) (by rw [inverseChordPolynomial_natDegree m hm]; omega)
    rw [inverseChordPolynomial_natDegree m hm,
      show m - 1 - (m - 1 - j) = j by omega,
      hmonic.leadingCoeff, one_mul, hroots] at hv
    have hcoeff : (inverseChordPolynomial m).coeff (m - 1 - j) =
        (-1 : ℂ) ^ j * (m.choose (j + 1) : ℂ) / (m : ℂ) := by
      rw [hcoeff_of_lt (m - 1 - j) (by omega)]
      have hsub : m - (m - 1 - j) = j + 1 := by omega
      have hindex : m - 1 - j = m - (j + 1) := by omega
      rw [hsub, hindex, Nat.choose_symm (by omega : j + 1 ≤ m), pow_succ]
      ring
    have hsign : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hsign
    exact hv.symm.trans (by simpa [div_eq_mul_inv, mul_assoc] using hcoeff)
  · have hlt : Multiset.card (inverseChordRoots m).val < j := by
      change (inverseChordRoots m).card < j
      rw [hcard]
      omega
    have hmj : m < j + 1 := by omega
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty j hlt,
      Nat.choose_eq_zero_of_lt hmj]
    simp

private abbrev inverseChordIndex (m : ℕ) :=
  {t : ℂ // t ∈ inverseChordRoots m}

private lemma inverseChord_normSq (m : ℕ) (hm : 1 ≤ m) {z : ℂ}
    (hz : z ∈ (roots m).erase 1) :
    ((((‖1 - z‖ : ℝ)⁻¹ ^ 2 : ℝ)) : ℂ) =
      (1 - z)⁻¹ - (1 - z)⁻¹ ^ 2 := by
  have hzroot : z ^ m = 1 :=
    (Polynomial.mem_nthRootsFinset (by omega) (1 : ℂ)).mp
      (Finset.mem_erase.mp hz).2
  have hz0 : z ≠ 0 := by
    intro hzero
    have hzeroPow : (0 : ℂ) ^ m = 1 := by simpa [hzero] using hzroot
    rw [zero_pow (by omega)] at hzeroPow
    exact zero_ne_one hzeroPow
  have hz1 : z ≠ 1 := (Finset.mem_erase.mp hz).1
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hnorm : ‖z‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hzroot (by omega)
  have hconjmul : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hconj : (starRingEnd ℂ) z = z⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hz0).mp hconjmul
  calc
    ((((‖1 - z‖ : ℝ)⁻¹ ^ 2 : ℝ)) : ℂ) =
        (((‖1 - z‖ : ℝ) : ℂ)⁻¹) ^ 2 := by
      push_cast
      rfl
    _ = ((((‖1 - z‖ : ℝ) : ℂ) ^ 2)⁻¹) := by rw [inv_pow]
    _ = ((Complex.normSq (1 - z) : ℂ))⁻¹ := by
      rw [Complex.normSq_eq_norm_sq]
      norm_cast
    _ = (1 - z)⁻¹ - (1 - z)⁻¹ ^ 2 := by
      rw [Complex.normSq_eq_conj_mul_self, map_sub, map_one, hconj]
      field_simp [hz0, hden]
      ring

private lemma inverseChord_secondAndFourthMoments (m : ℕ) (hm : 2 ≤ m) :
    ((∑ z ∈ (roots m).erase 1, (‖1 - z‖ : ℝ)⁻¹ ^ 2) =
      ((m : ℝ) ^ 2 - 1) / 12) ∧
    ((∑ z ∈ (roots m).erase 1, (‖1 - z‖ : ℝ)⁻¹ ^ 4) =
      ((m : ℝ) ^ 2 - 1) * ((m : ℝ) ^ 2 + 11) / 720) := by
  have hvalues : ((Finset.univ : Finset (inverseChordIndex m)).val.map
      Subtype.val) = (inverseChordRoots m).val := by
    have huniv : (Finset.univ : Finset (inverseChordIndex m)) =
        (inverseChordRoots m).attach := by
      ext t
      simp
    rw [huniv, Finset.attach_val, Multiset.attach_map_val]
  have heval (j : ℕ) :
      (MvPolynomial.eval (fun t : inverseChordIndex m => t.1))
          (MvPolynomial.esymm (inverseChordIndex m) ℂ j) =
        (inverseChordRoots m).val.esymm j := by
    change MvPolynomial.aeval (fun t : inverseChordIndex m => t.1)
      (MvPolynomial.esymm (inverseChordIndex m) ℂ j) = _
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hvalues]
  have hnewton (k : ℕ) (hk : 0 < k) :
      (∑ t : inverseChordIndex m, t.1 ^ k) =
        (-1 : ℂ) ^ (k + 1) * k * (inverseChordRoots m).val.esymm k -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℂ) ^ a.1 * (inverseChordRoots m).val.esymm a.1 *
              ∑ t : inverseChordIndex m, t.1 ^ a.2 := by
    have h := congrArg
      (MvPolynomial.aeval (R := ℂ) (fun t : inverseChordIndex m => t.1))
      (MvPolynomial.psum_eq_mul_esymm_sub_sum
        (inverseChordIndex m) ℂ k hk)
    simpa [MvPolynomial.psum, heval] using h
  have h1 : (∑ t : inverseChordIndex m, t.1) =
      (inverseChordRoots m).val.esymm 1 := by
    have h := hnewton 1 (by omega)
    rw [Finset.sum_filter,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, Set.mem_Ioo] at h
    exact h
  have h2 : (∑ t : inverseChordIndex m, t.1 ^ 2) =
      (inverseChordRoots m).val.esymm 1 ^ 2 -
        2 * (inverseChordRoots m).val.esymm 2 := by
    have h := hnewton 2 (by omega)
    rw [Finset.sum_filter,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, Set.mem_Ioo] at h
    rw [show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ)) =
      (inverseChordRoots m).val.esymm 1 by
        simpa [inverseChordIndex] using h1] at h
    norm_num at h ⊢
    linear_combination h
  have h3 : (∑ t : inverseChordIndex m, t.1 ^ 3) =
      (inverseChordRoots m).val.esymm 1 ^ 3 -
        3 * (inverseChordRoots m).val.esymm 1 *
          (inverseChordRoots m).val.esymm 2 +
        3 * (inverseChordRoots m).val.esymm 3 := by
    have h := hnewton 3 (by omega)
    rw [Finset.sum_filter,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, Set.mem_Ioo] at h
    rw [show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ)) =
          (inverseChordRoots m).val.esymm 1 by
        simpa [inverseChordIndex] using h1,
      show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ) ^ 2) =
          (inverseChordRoots m).val.esymm 1 ^ 2 -
            2 * (inverseChordRoots m).val.esymm 2 by
        simpa [inverseChordIndex] using h2] at h
    norm_num at h ⊢
    linear_combination h
  have h4 : (∑ t : inverseChordIndex m, t.1 ^ 4) =
      (inverseChordRoots m).val.esymm 1 ^ 4 -
        4 * (inverseChordRoots m).val.esymm 1 ^ 2 *
          (inverseChordRoots m).val.esymm 2 +
        2 * (inverseChordRoots m).val.esymm 2 ^ 2 +
        4 * (inverseChordRoots m).val.esymm 1 *
          (inverseChordRoots m).val.esymm 3 -
        4 * (inverseChordRoots m).val.esymm 4 := by
    have h := hnewton 4 (by omega)
    rw [Finset.sum_filter,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, Set.mem_Ioo] at h
    rw [show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ)) =
          (inverseChordRoots m).val.esymm 1 by
        simpa [inverseChordIndex] using h1,
      show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ) ^ 2) =
          (inverseChordRoots m).val.esymm 1 ^ 2 -
            2 * (inverseChordRoots m).val.esymm 2 by
        simpa [inverseChordIndex] using h2,
      show (∑ t ∈ (inverseChordRoots m).attach, (t.1 : ℂ) ^ 3) =
          (inverseChordRoots m).val.esymm 1 ^ 3 -
            3 * (inverseChordRoots m).val.esymm 1 *
              (inverseChordRoots m).val.esymm 2 +
            3 * (inverseChordRoots m).val.esymm 3 by
        simpa [inverseChordIndex] using h3] at h
    norm_num at h ⊢
    linear_combination h
  have hpower (k : ℕ) :
      (∑ z ∈ (roots m).erase 1, ((1 - z)⁻¹ : ℂ) ^ k) =
        ∑ t : inverseChordIndex m, t.1 ^ k := by
    rw [show (∑ t : inverseChordIndex m, t.1 ^ k) =
      ∑ t ∈ inverseChordRoots m, t ^ k by
        simpa [inverseChordIndex] using
          (Finset.sum_attach (inverseChordRoots m) fun t => t ^ k)]
    rw [inverseChordRoots, Finset.sum_image]
    intro z _ w _ h
    exact sub_right_inj.mp (inv_injective h)
  have hchoose (j : ℕ) : ((m.choose j : ℕ) : ℂ) =
      (m.descFactorial j : ℂ) / (j.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hfac : (((j.factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos j).ne'
    field_simp [hfac]
  have hsecondComplex :
      (∑ z ∈ (roots m).erase 1, ((((‖1 - z‖ : ℝ)⁻¹ ^ 2 : ℝ) : ℂ))) =
        (((m : ℝ) ^ 2 - 1) / 12 : ℝ) := by
    calc
      _ = (∑ z ∈ (roots m).erase 1,
          ((1 - z)⁻¹ - (1 - z)⁻¹ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact inverseChord_normSq m (by omega) hz
      _ = (∑ t : inverseChordIndex m, t.1) -
          ∑ t : inverseChordIndex m, t.1 ^ 2 := by
        rw [Finset.sum_sub_distrib]
        have h1 := hpower 1
        rw [hpower 2]
        simpa using h1
      _ = _ := by
        rw [h1, h2,
          inverseChordRoots_esymm m 1 (by omega),
          inverseChordRoots_esymm m 2 (by omega),
          hchoose 2, hchoose 3]
        norm_num [Nat.descFactorial_succ]
        push_cast [Nat.cast_sub (by omega : 1 ≤ m),
          Nat.cast_sub (by omega : 2 ≤ m)]
        have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp [hmC]
        ring
  have hsecond :
      (∑ z ∈ (roots m).erase 1, (‖1 - z‖ : ℝ)⁻¹ ^ 2) =
        ((m : ℝ) ^ 2 - 1) / 12 := by
    exact_mod_cast hsecondComplex
  have hfourthComplex :
      (∑ z ∈ (roots m).erase 1, ((((‖1 - z‖ : ℝ)⁻¹ ^ 4 : ℝ) : ℂ))) =
        ((((m : ℝ) ^ 2 - 1) * ((m : ℝ) ^ 2 + 11) / 720 : ℝ) : ℂ) := by
    calc
      _ = ∑ z ∈ (roots m).erase 1,
          (((1 - z)⁻¹ - (1 - z)⁻¹ ^ 2) ^ 2) := by
        apply Finset.sum_congr rfl
        intro z hz
        calc
          ((((‖1 - z‖ : ℝ)⁻¹ ^ 4 : ℝ)) : ℂ) =
              (((((‖1 - z‖ : ℝ)⁻¹ ^ 2 : ℝ)) : ℂ)) ^ 2 := by
            push_cast
            ring
          _ = (((1 - z)⁻¹ - (1 - z)⁻¹ ^ 2) ^ 2) := by
            rw [inverseChord_normSq m (by omega) hz]
      _ = (∑ t : inverseChordIndex m, t.1 ^ 2) -
          2 * (∑ t : inverseChordIndex m, t.1 ^ 3) +
          ∑ t : inverseChordIndex m, t.1 ^ 4 := by
        calc
          _ = ∑ z ∈ (roots m).erase 1,
              ((1 - z)⁻¹ ^ 2 - 2 * (1 - z)⁻¹ ^ 3 +
                (1 - z)⁻¹ ^ 4) := by
            apply Finset.sum_congr rfl
            intro z _
            ring
          _ = (∑ z ∈ (roots m).erase 1, (1 - z)⁻¹ ^ 2) -
              2 * (∑ z ∈ (roots m).erase 1, (1 - z)⁻¹ ^ 3) +
              ∑ z ∈ (roots m).erase 1, (1 - z)⁻¹ ^ 4 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
          _ = _ := by
            rw [hpower 2, hpower 3, hpower 4]
      _ = _ := by
        rw [h2, h3, h4]
        rw [inverseChordRoots_esymm m 1 (by omega),
          inverseChordRoots_esymm m 2 (by omega),
          inverseChordRoots_esymm m 3 (by omega),
          inverseChordRoots_esymm m 4 (by omega),
          hchoose 2, hchoose 3, hchoose 4, hchoose 5]
        by_cases hm5 : 5 ≤ m
        · have hmC : (m : ℂ) ≠ 0 := by
            exact_mod_cast (show m ≠ 0 by omega)
          norm_num [Nat.descFactorial_succ]
          push_cast [Nat.cast_sub (by omega : 1 ≤ m),
            Nat.cast_sub (by omega : 2 ≤ m),
            Nat.cast_sub (by omega : 3 ≤ m),
            Nat.cast_sub (by omega : 4 ≤ m)]
          field_simp [hmC]
          ring
        · interval_cases m <;> norm_num [Nat.descFactorial_succ, Nat.choose]
  have hfourth :
      (∑ z ∈ (roots m).erase 1, (‖1 - z‖ : ℝ)⁻¹ ^ 4) =
        ((m : ℝ) ^ 2 - 1) * ((m : ℝ) ^ 2 + 11) / 720 := by
    exact_mod_cast hfourthComplex
  exact ⟨hsecond, hfourth⟩
private lemma supportCoordinateSquareSum_le (n : ℕ) (hn : 1 ≤ n)
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    (∑ z : supportRoots n R,
        (∏ i : {i // i ∈ R},
          (‖1 - (sylvesterRestrictedRootEquiv n hn R hR z i).1‖ : ℝ)⁻¹) ^ 2) ≤
      (supportPeriod n R : ℝ) ^ 2 / 12 ^ R.card := by
  calc
    _ = ∑ z : supportRoots n R,
        ∏ i : {i // i ∈ R},
          (‖1 - (sylvesterRestrictedRootEquiv n hn R hR z i).1‖ : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.prod_pow]
    _ = ∏ i : {i // i ∈ R},
        ∑ u : {u : ℂ // u ∈ (roots (q i.1)).erase 1},
          (‖1 - u.1‖ : ℝ)⁻¹ ^ 2 := by
      calc
        _ = ∑ u : nontrivialCoordinates n R,
            ∏ i : {i // i ∈ R}, (‖1 - (u i).1‖ : ℝ)⁻¹ ^ 2 :=
          (sylvesterRestrictedRootEquiv n hn R hR).sum_comp
            (fun u => ∏ i, (‖1 - (u i).1‖ : ℝ)⁻¹ ^ 2)
        _ = _ := by
          simpa [nontrivialCoordinates] using
            (Fintype.prod_sum
              (fun (i : {i // i ∈ R})
                (u : {u : ℂ // u ∈ (roots (q i.1)).erase 1}) =>
                  ((‖1 - u.1‖ : ℝ) ^ 2)⁻¹)).symm
    _ ≤ ∏ i : {i // i ∈ R}, (q i.1 : ℝ) ^ 2 / 12 := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        rw [show (∑ u : {u : ℂ // u ∈ (roots (q i.1)).erase 1},
              (‖1 - u.1‖ : ℝ)⁻¹ ^ 2) =
            ((q i.1 : ℝ) ^ 2 - 1) / 12 by
          calc
            _ = ∑ u ∈ (roots (q i.1)).erase 1,
                (‖1 - u‖ : ℝ)⁻¹ ^ 2 := by
              simpa using (Finset.sum_attach ((roots (q i.1)).erase 1)
                fun u => ((‖1 - u‖ : ℝ) ^ 2)⁻¹)
            _ = _ := (inverseChord_secondAndFourthMoments (q i.1)
              (two_le_sylvester _ (by omega))).1]
        linarith
    _ = _ := by
      rw [Finset.prod_div_distrib, Finset.prod_pow,
        Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      congr 2
      calc
        ∏ i : {i // i ∈ R}, (q i.1 : ℝ) =
            ∏ i ∈ R, (q i : ℝ) := by
          simpa using (Finset.prod_attach R fun i => (q i : ℝ))
        _ = (supportPeriod n R : ℝ) := by
          push_cast
          rfl

private lemma supportFourthSum_le (n : ℕ) (hn : 1 ≤ n)
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    (∑ z : supportRoots n R, (‖1 - z.1‖ : ℝ)⁻¹ ^ 4) ≤
      (supportPeriod n R : ℝ) ^ 4 / 256 := by
  have hS : 2 ≤ supportPeriod n R := by
    obtain ⟨i, hi⟩ := hR
    exact (two_le_sylvester _ (by omega)).trans
      (Nat.le_of_dvd (Finset.prod_pos (fun j _ => sylvester_pos _))
        (Finset.dvd_prod_of_mem (fun j : Fin n => q j) hi))
  calc
    _ = ∑ z ∈ (roots (period n)).filter (fun z => z ≠ 1 ∧
          Finset.univ.filter (fun i : Fin n =>
            z ^ (period n / q i) ≠ 1) = R),
        (‖1 - z‖ : ℝ)⁻¹ ^ 4 := by
      simpa using (Finset.sum_attach
        ((roots (period n)).filter (fun z => z ≠ 1 ∧
          Finset.univ.filter (fun i : Fin n =>
            z ^ (period n / q i) ≠ 1) = R))
        fun z => ((‖1 - z‖ : ℝ) ^ 4)⁻¹)
    _ ≤ ∑ z ∈ (roots (supportPeriod n R)).erase 1,
        (‖1 - z‖ : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        have hz' := Finset.mem_filter.mp hz
        have hpow := supportRoot_pow_supportPeriod n hn R
          ⟨z, hz⟩
        have hSpos : 0 < supportPeriod n R :=
          Finset.prod_pos fun i _ => sylvester_pos _
        rw [Finset.mem_erase]
        refine ⟨hz'.2.1, ?_⟩
        change z ∈ Polynomial.nthRootsFinset (supportPeriod n R) (1 : ℂ)
        rw [Polynomial.mem_nthRootsFinset hSpos]
        exact hpow
      · intro _ _ _
        positivity
    _ ≤ _ := by
      rw [(inverseChord_secondAndFourthMoments (supportPeriod n R) hS).2]
      have hSR : (2 : ℝ) ≤ supportPeriod n R := by exact_mod_cast hS
      have h₁ : 0 ≤ (supportPeriod n R : ℝ) ^ 2 - 4 := by
        nlinarith [sq_nonneg ((supportPeriod n R : ℝ) - 2)]
      have h₂ : 0 ≤ 29 * (supportPeriod n R : ℝ) ^ 2 - 44 := by
        nlinarith [sq_nonneg (supportPeriod n R : ℝ)]
      have := mul_nonneg h₁ h₂
      nlinarith

private lemma supportWeightedSum_le (n : ℕ) (hn : 1 ≤ n)
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    (∑ z : supportRoots n R, (‖1 - z.1‖ : ℝ)⁻¹ ^ 2 *
      ∏ i : {i // i ∈ R},
        (‖1 - z.1 ^ (period n / q i.1)‖ : ℝ)⁻¹) ≤
      (supportPeriod n R : ℝ) ^ 3 /
        (16 * (Real.sqrt 12) ^ R.card) := by
  let a : supportRoots n R → ℝ := fun z => (‖1 - z.1‖ : ℝ)⁻¹ ^ 2
  let b : supportRoots n R → ℝ := fun z =>
    ∏ i : {i // i ∈ R},
      (‖1 - (sylvesterRestrictedRootEquiv n hn R hR z i).1‖ : ℝ)⁻¹
  have ha : (∑ z, a z ^ 2) ≤ (supportPeriod n R : ℝ) ^ 4 / 256 := by
    calc
      _ = ∑ z : supportRoots n R, (‖1 - z.1‖ : ℝ)⁻¹ ^ 4 := by
        apply Finset.sum_congr rfl
        intro z _
        simp [a]
        ring
      _ ≤ _ := supportFourthSum_le n hn R hR
  have hb : (∑ z, b z ^ 2) ≤
      (supportPeriod n R : ℝ) ^ 2 / 12 ^ R.card := by
    simpa [b] using supportCoordinateSquareSum_le n hn R hR
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (supportRoots n R)) a b
  have hs : 0 ≤ (supportPeriod n R : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt 12 := Real.sqrt_pos.2 (by norm_num)
  have hA : Real.sqrt ((supportPeriod n R : ℝ) ^ 4 / 256) =
      (supportPeriod n R : ℝ) ^ 2 / 16 := by
    rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity),
      Real.sq_sqrt (by positivity)]
    ring
  have hB : Real.sqrt ((supportPeriod n R : ℝ) ^ 2 / 12 ^ R.card) =
      (supportPeriod n R : ℝ) / (Real.sqrt 12) ^ R.card := by
    rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity),
      Real.sq_sqrt (by positivity)]
    rw [div_pow, ← pow_mul, Nat.mul_comm R.card 2, pow_mul,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  calc
    _ = ∑ z, a z * b z := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [a, b]
      congr 2
    _ ≤ Real.sqrt (∑ z, a z ^ 2) * Real.sqrt (∑ z, b z ^ 2) := by
      simpa using hcs
    _ ≤ Real.sqrt ((supportPeriod n R : ℝ) ^ 4 / 256) *
        Real.sqrt ((supportPeriod n R : ℝ) ^ 2 / 12 ^ R.card) := by
      gcongr
    _ = _ := by rw [hA, hB]; field_simp

/-- Actual-source fixed-support norm sums for supports one through four. -/
theorem sourceFixedSupportNormSum_bounds (n : ℕ) (hn : 7 ≤ n)
    (R : Finset (Fin n)) (hR : R.Nonempty) (c : ℤ) :
    (R.card ≤ 3 → (c = 0 ∨ c = -1) →
      (∑ z : supportRoots n R, ‖(sourceLocalRootContributionPolynomial
        (n + 1) z.1 c).coeff (n + 1 - 6)‖) ≤
        (supportPeriod n R : ℝ) ^ 2 /
          ((Real.sqrt 12) ^ R.card * (n + 1 - 6).factorial)) ∧
    (R.card = 4 → (∑ z : supportRoots n R,
      ‖(sourceLocalRootContributionPolynomial (n + 1) z.1 c).coeff
        (n + 1 - 6)‖) ≤
        (supportPeriod n R : ℝ) ^ 2 /
          (2304 * (n + 1 - 6).factorial)) := by
  let F : ℝ := (n + 1 - 6).factorial
  let S : ℝ := supportPeriod n R
  let W : supportRoots n R → ℝ := fun z => (‖1 - z.1‖ : ℝ)⁻¹ ^ 2 *
    ∏ i : {i // i ∈ R}, (‖1 - z.1 ^ (period n / q i.1)‖ : ℝ)⁻¹
  have hW : (∑ z, W z) ≤ S ^ 3 / (16 * Real.sqrt 12 ^ R.card) := by
    simpa [W, S] using supportWeightedSum_le n (by omega) R hR
  have hF : F ≠ 0 := by positivity
  have hS : S ≠ 0 := by
    have h : 0 < supportPeriod n R :=
      Finset.prod_pos fun (i : Fin n) _ => sylvester_pos (i.1 + 1)
    dsimp only [S]
    exact_mod_cast h.ne'
  have hsqrt : Real.sqrt 12 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  constructor
  · intro hcard hc
    have hp (z : supportRoots n R) : ‖(sourceLocalRootContributionPolynomial
        (n + 1) z.1 c).coeff (n + 1 - 6)‖ ≤ 16 / (F * S) * W z := by
      have hzcard : (Finset.univ.filter fun i : Fin n =>
          z.1 ^ (period n / q i) ≠ 1).card ≤ 3 := by
        rw [(Finset.mem_filter.mp z.2).2.2]
        exact hcard
      rcases sourceNontrivialRootContribution_card_one_to_three_bound n hn
        z.1 (Finset.mem_filter.mp z.2).1
          (Finset.mem_filter.mp z.2).2.1 c hc hzcard with ⟨_, _, _, _, _, hb⟩
      dsimp only at hb
      rw [(Finset.mem_filter.mp z.2).2.2] at hb
      have hprod : (∏ i ∈ R, ‖1 - z.1 ^ (period n / q i)‖) =
          ∏ i : {i // i ∈ R}, ‖1 - z.1 ^ (period n / q i.1)‖ := by
        symm
        simpa using (Finset.prod_attach R
          fun i => ‖1 - z.1 ^ (period n / q i)‖)
      rw [hprod] at hb
      calc _ ≤ _ := hb
        _ = _ := by
          simp only [F, S, W, div_eq_mul_inv, mul_inv_rev,
            Finset.prod_inv_distrib]
          ring
    calc
      _ ≤ ∑ z, 16 / (F * S) * W z := Finset.sum_le_sum fun z _ => hp z
      _ = 16 / (F * S) * ∑ z, W z := by rw [Finset.mul_sum]
      _ ≤ 16 / (F * S) * (S ^ 3 / (16 * Real.sqrt 12 ^ R.card)) := by
        gcongr
      _ = _ := by field_simp [hF, hS, hsqrt]; ring
  · intro hcard
    have hp (z : supportRoots n R) : ‖(sourceLocalRootContributionPolynomial
        (n + 1) z.1 c).coeff (n + 1 - 6)‖ ≤ 1 / (F * S) * W z := by
      have hzcard : (Finset.univ.filter fun i : Fin n =>
          z.1 ^ (period n / q i) ≠ 1).card = 4 := by
        rw [(Finset.mem_filter.mp z.2).2.2]
        exact hcard
      rcases sourceNontrivialRootContribution_card_four_exact n hn z.1
        (Finset.mem_filter.mp z.2).1
          (Finset.mem_filter.mp z.2).2.1 c hzcard with ⟨_, _, _, _, hb⟩
      dsimp only at hb
      rw [(Finset.mem_filter.mp z.2).2.2] at hb
      have hprod : (∏ i ∈ R, ‖1 - z.1 ^ (period n / q i)‖) =
          ∏ i : {i // i ∈ R}, ‖1 - z.1 ^ (period n / q i.1)‖ := by
        symm
        simpa using (Finset.prod_attach R
          fun i => ‖1 - z.1 ^ (period n / q i)‖)
      rw [hprod] at hb
      calc _ ≤ _ := hb
        _ = _ := by
          simp only [F, S, W, div_eq_mul_inv, mul_inv_rev,
            Finset.prod_inv_distrib]
          ring
    calc
      _ ≤ ∑ z, 1 / (F * S) * W z := Finset.sum_le_sum fun z _ => hp z
      _ = 1 / (F * S) * ∑ z, W z := by rw [Finset.mul_sum]
      _ ≤ 1 / (F * S) * (S ^ 3 / (16 * Real.sqrt 12 ^ R.card)) := by
        gcongr
      _ = _ := by
        rw [hcard]
        norm_num [show Real.sqrt 12 ^ 4 = 144 by
          rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul,
            Real.sq_sqrt (by norm_num)]
          norm_num]
        dsimp only [F, S]
        field_simp [hF, hS]
        push_cast
        rfl

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartFixedSupportBound
