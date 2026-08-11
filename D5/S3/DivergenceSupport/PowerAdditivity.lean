/- GID: D5/S3/DivergenceSupport/PowerAdditivity
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/PowerAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove n-fold additivity of finite classical KL divergence for repeated experiments. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms combined `klDiv`, `Kullback`, and `relativeEntropy`
     with `iid`, `i.i.d.`, `n-fold`, `tensor`, `prod`, `power`, and `pow`.
   * Mathlib provides the measure-valued chain rules `InformationTheory.klDiv_compProd_eq_add`
     and `InformationTheory.klDiv_compProd_left`, but no pinned n-fold theorem for the
     repository's real-valued finite-sum `klDivergence` was found.
   * A repository scan below `D5` found no classical KL power/i.i.d./n-fold additivity
     declaration. It found `IidSpace` and `iidPower` only in the landed
     `D5.S3.RenyiDivergence.PowerAdditivity`, which is imported and reused below.
-/

import D5.S3.Divergence.ProductAdditivity
import D5.S3.RenyiDivergence.PowerAdditivity

namespace D5.S3.DivergenceSupport.PowerAdditivity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ProductAdditivity
open D5.S3.RenyiDivergence

/-- Strict pointwise positivity is preserved by every finite product power. -/
theorem iid_power_pos {ι : Type*} (p : ι -> Real)
    (hp : forall i, 0 < p i) :
    forall (n : Nat) (z : IidSpace ι n), 0 < iidPower p n z := by
  intro n
  induction n with
  | zero =>
    intro z
    norm_num [iidPower]
  | succ n ih =>
    intro z
    exact mul_pos (hp z.1) (ih z.2)

/-- Every finite product power of a normalized mass function is normalized. -/
theorem iid_power_sum_one {ι : Type*} [Fintype ι]
    (p : ι -> Real) (hp_sum : ∑ i, p i = 1) :
    forall n : Nat, ∑ z : IidSpace ι n, iidPower p n z = 1 := by
  intro n
  induction n with
  | zero => simp [IidSpace, iidPower]
  | succ n ih =>
    change (∑ z : ι × IidSpace ι n, p z.1 * iidPower p n z.2) = 1
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hp_sum, ih, one_mul]

/-- Repeating a finite strictly positive probability law `n` times multiplies its classical
KL divergence by `n`. The reference law must be strictly positive but need not be normalized. -/
theorem kl_divergence_power_additive {ι : Type*} [Fintype ι]
    (p q : ι -> Real) (n : Nat)
    (hp_sum : ∑ i, p i = 1)
    (hp : forall i, 0 < p i) (hq : forall i, 0 < q i) :
    klDivergence (iidPower p n) (iidPower q n) =
      n * klDivergence p q := by
  fail_if_success rfl
  fail_if_success simp
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
        kl_divergence_product_additive p q
          (iidPower p n) (iidPower q n)
          hp_sum (iid_power_sum_one p hp_sum n)
          hp hq (iid_power_pos p hp n) (iid_power_pos q hq n)
      _ = ((n + 1 : Nat) : Real) * klDivergence p q := by
        rw [ih]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring

/- On two copies of a uniform Bool law against the constant reference mass `1/4`, the left side
computes to `log 4`, as does twice the one-copy divergence. -/
example :
    klDivergence
        (iidPower (fun _b : Bool => (1 / 2 : Real)) 2)
        (iidPower (fun _b : Bool => (1 / 4 : Real)) 2) =
      2 * klDivergence
        (fun _b : Bool => (1 / 2 : Real))
        (fun _b : Bool => (1 / 4 : Real)) := by
  have hLeft :
      klDivergence
          (iidPower (fun _b : Bool => (1 / 2 : Real)) 2)
          (iidPower (fun _b : Bool => (1 / 4 : Real)) 2) = Real.log 4 := by
    norm_num [klDivergence, IidSpace, iidPower, Fintype.sum_prod_type,
      Fintype.sum_bool]
    have hcard : Fintype.card (IidSpace Bool 2) = 4 := by
      change Fintype.card (Bool × (Bool × PUnit)) = 4
      norm_num [Fintype.card_prod]
    rw [hcard]
    ring
  have hRight :
      2 * klDivergence
          (fun _b : Bool => (1 / 2 : Real))
          (fun _b : Bool => (1 / 4 : Real)) = Real.log 4 := by
    rw [show (4 : Real) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num [klDivergence, Fintype.sum_bool]
    ring
  rw [hLeft, hRight]

#print axioms iid_power_pos
#print axioms iid_power_sum_one
#print axioms kl_divergence_power_additive

end D5.S3.DivergenceSupport.PowerAdditivity
