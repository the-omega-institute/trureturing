/- GID: D5/S3/DivergenceSupport/GeneralSupportAdditivity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extend finite classical KL product and power additivity to general support. -/

import Mathlib
import D5.S3.DivergenceSupport.PowerAdditivity
import D5.S3.RenyiDivergence.PowerAdditivity

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT
   Repository declarations read:
   * `D5/S3/Divergence/ClassicalDPI.lean:28-30` defines the real finite-sum
     `klDivergence` used here.
   * `D5/S3/Divergence/ProductAdditivity.lean:29-78` proves the strictly positive
     product theorem and supplies the finite-sum factorization pattern.
   * `D5/S3/DivergenceSupport/PowerAdditivity.lean:28-88` proves strict-support
     power additivity and provides `iid_power_sum_one`.
   * `D5/S3/RenyiDivergence/PowerAdditivity.lean:45-72` defines `IidSpace` and
     `iidPower`, and already proves `iid_power_nonneg`; the stronger result below
     does not need nonnegativity, so that helper need not be duplicated or used.
   * `D5/S3/DivergenceSupport/ZeroSupportDPI.lean:29-236` handles zero terms by
     cases before applying `Real.log_mul`; no theorem there directly implies
     product additivity.
   * `D5/S3/DivergenceSupport/ZeroSupportDefect.lean:30-87` composes the general
     support DPI identity with KL nonnegativity; it does not close this goal.
   Pinned mathlib declarations read:
   * `Mathlib/Data/Fintype/BigOperators.lean:269-283` provides
     `Fintype.sum_prod_type`.
   * `Mathlib/Algebra/BigOperators/Ring/Finset.lean:56-68` provides finite sum
     distribution and `Fintype.sum_mul_sum`.
   * `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:120-139` shows that real
     logarithm is even and that `Real.log_mul` needs only nonzero factors.
   * `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:103-113` uses the
     same zero-factor split, while lines 200-218 state an `ENNReal`-valued
     measure chain rule rather than this repository's real finite-sum theorem.
   Search result:
   * Searches below `D5` and pinned `Mathlib` for KL product/power additivity and
     absolute-continuity variants found no theorem directly closing either goal.
   * Neither source nor reference nonnegativity is needed: absolute continuity
     makes each denominator nonzero wherever the source mass is nonzero, and
     `Real.log_mul` is valid for arbitrary nonzero real factors because it uses
     absolute values. The two named results below therefore omit all redundant
     nonnegativity premises.
-/

namespace D5.S3.DivergenceSupport.GeneralSupportAdditivity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.RenyiDivergence

/-- The repository's finite real-valued KL expression is additive on products under discrete
absolute continuity. The source functions are normalized; no function must be nonnegative, and
the reference functions need not be normalized. -/
theorem kl_divergence_product_additive_of_absolutely_continuous
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι -> Real) (a' b' : κ -> Real)
    (ha_sum : ∑ i, a i = 1) (ha'_sum : ∑ j, a' j = 1)
    (hac : forall i, b i = 0 -> a i = 0)
    (hac' : forall j, b' j = 0 -> a' j = 0) :
    klDivergence (fun z : ι × κ => a z.1 * a' z.2)
        (fun z : ι × κ => b z.1 * b' z.2) =
      klDivergence a b + klDivergence a' b' := by
  classical
  simp only [klDivergence, Fintype.sum_prod_type]
  have hterm (i : ι) (j : κ) :
      a i * a' j * Real.log (a i * a' j / (b i * b' j)) =
        a i * a' j * Real.log (a i / b i) +
          a i * a' j * Real.log (a' j / b' j) := by
    by_cases hai : a i = 0
    · simp [hai]
    by_cases ha'j : a' j = 0
    · simp [ha'j]
    have hbi : b i ≠ 0 := fun h => hai (hac i h)
    have hb'j : b' j ≠ 0 := fun h => ha'j (hac' j h)
    have hratio :
        a i * a' j / (b i * b' j) = (a i / b i) * (a' j / b' j) := by
      field_simp [hbi, hb'j]
    rw [hratio, Real.log_mul (div_ne_zero hai hbi) (div_ne_zero ha'j hb'j)]
    ring
  calc
    (∑ i, ∑ j, a i * a' j * Real.log (a i * a' j / (b i * b' j))) =
        ∑ i, ∑ j,
          (a i * a' j * Real.log (a i / b i) +
            a i * a' j * Real.log (a' j / b' j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = (∑ i, ∑ j, a i * a' j * Real.log (a i / b i)) +
        ∑ i, ∑ j, a i * a' j * Real.log (a' j / b' j) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i, a i * Real.log (a i / b i) * ∑ j, a' j) +
        ∑ j, a' j * Real.log (a' j / b' j) * ∑ i, a i := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = (∑ i, a i * Real.log (a i / b i)) +
        ∑ j, a' j * Real.log (a' j / b' j) := by
      rw [ha_sum, ha'_sum]
      simp

/-- Discrete absolute continuity is preserved by every finite product power. -/
theorem iid_power_absolutely_continuous {ι : Type*}
    (a b : ι -> Real) (hac : forall i, b i = 0 -> a i = 0) :
    forall (n : Nat) (z : IidSpace ι n),
      iidPower b n z = 0 -> iidPower a n z = 0 := by
  intro n
  induction n with
  | zero =>
    intro z hz
    simp [iidPower] at hz
  | succ n ih =>
    intro z hz
    change b z.1 * iidPower b n z.2 = 0 at hz
    change a z.1 * iidPower a n z.2 = 0
    rcases mul_eq_zero.mp hz with hb | hpow
    · simp [hac z.1 hb]
    · simp [ih z.2 hpow]

/-- Repeating a finite normalized source function `n` times multiplies the repository's
real-valued KL expression by `n`, provided it is discretely absolutely continuous with respect to
the reference function. Neither function must be nonnegative, and the reference need not be
normalized. -/
theorem kl_divergence_power_additive_of_absolutely_continuous
    {ι : Type*} [Fintype ι]
    (p q : ι -> Real) (n : Nat)
    (hp_sum : ∑ i, p i = 1)
    (hac : forall i, q i = 0 -> p i = 0) :
    klDivergence (iidPower p n) (iidPower q n) =
      n * klDivergence p q := by
  classical
  induction n with
  | zero => simp [IidSpace, iidPower, klDivergence]
  | succ n ih =>
    change klDivergence
        (fun z : ι × IidSpace ι n => p z.1 * iidPower p n z.2)
        (fun z : ι × IidSpace ι n => q z.1 * iidPower q n z.2) =
      ((n + 1 : Nat) : Real) * klDivergence p q
    calc
      klDivergence
          (fun z : ι × IidSpace ι n => p z.1 * iidPower p n z.2)
          (fun z : ι × IidSpace ι n => q z.1 * iidPower q n z.2) =
        klDivergence p q +
          klDivergence (iidPower p n) (iidPower q n) :=
        kl_divergence_product_additive_of_absolutely_continuous
          p q (iidPower p n) (iidPower q n)
          hp_sum (iid_power_sum_one p hp_sum n) hac
          (iid_power_absolutely_continuous p q hac n)
      _ = ((n + 1 : Nat) : Real) * klDivergence p q := by
        rw [ih]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring

#print axioms kl_divergence_product_additive_of_absolutely_continuous
#print axioms iid_power_absolutely_continuous
#print axioms kl_divergence_power_additive_of_absolutely_continuous

end D5.S3.DivergenceSupport.GeneralSupportAdditivity
