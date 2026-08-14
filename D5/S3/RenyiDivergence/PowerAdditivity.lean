/- GID: D5/S3/RenyiDivergence/PowerAdditivity
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/PowerAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove n-fold additivity of finite Renyi divergence for repeated experiments. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `Fin.consEquiv`, `Fin.prod_univ_succ`, `Equiv.sum_comp`,
     `Fintype.sum_pow`, `Real.finsetProd_rpow`, `Fintype.sum_prod_type`,
     `Fintype.sum_mul_sum`, and `Finset.prod_nonneg`.
   * The reusable finite-product ingredients are `Fintype.sum_prod_type`,
     `Fintype.sum_mul_sum`, and `Finset.prod_nonneg`. `Fin.consEquiv`, `Equiv.sum_comp`,
     `Fin.prod_univ_succ`, `Fintype.sum_pow`, and `Real.finsetProd_rpow` support the alternative
     `Fin n -> ι` encoding, but that encoding inserts a change-of-variables proof before the frozen
     binary theorem can apply.
   * A repository scan below `D5` for Renyi declarations mentioning `pow`, `power`, `iid`,
     `i.i.d.`, `n-fold`, or `iterate` found no power/i.i.d./n-fold additivity declaration.
-/

import D5.S3.RenyiDivergence.ProductAdditivity

namespace D5.S3.RenyiDivergence

universe u

/-!
An `n`-fold experiment is represented recursively: zero copies have the one-point type `PUnit`,
and `n + 1` copies have type `ι × IidSpace ι n`. The corresponding mass is `1` at zero and
`p z.1 * iidPower p n z.2` at a successor. These two definitions are the minimal interface needed
to make the successor law definitionally identical to the product mass consumed by
`renyi_divergence_product_additive`.

The more conventional `Fin n -> ι` representation avoids definitions, but every induction step
then needs a finite-sum change of variables through `Fin.consEquiv` before the frozen theorem can
be applied. Vectors or length-indexed lists add subtype or length-equality plumbing as well. The
recursive representation keeps the mathematical content -- a right-associated finite product --
and makes the required binary theorem the induction step itself.

The power-sum factorization below propagates the binary theorem's non-vanishing hypothesis: the
`n`-fold power sum is the `n`th natural power of the one-copy sum. No normalization or restriction
on the real order is needed.
-/

/-- Right-associated sample space for `n` independent copies of a finite experiment. -/
def IidSpace (ι : Type u) : Nat -> Type u
  | 0 => PUnit
  | n + 1 => ι × IidSpace ι n

instance instFintypeIidSpace {ι : Type*} [Fintype ι] :
    (n : Nat) -> Fintype (IidSpace ι n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
    @instFintypeProd ι (IidSpace ι n) _ (instFintypeIidSpace n)

/-- Product mass of `n` independent copies, with empty product equal to one. -/
def iidPower {ι : Type*} (p : ι -> Real) : (n : Nat) -> IidSpace ι n -> Real
  | 0, _ => 1
  | n + 1, z => p z.1 * iidPower p n z.2

/-- Pointwise nonnegativity is preserved by every finite product power. -/
theorem iid_power_nonneg {ι : Type*} (p : ι -> Real)
    (hp : forall i, 0 <= p i) :
    forall (n : Nat) (z : IidSpace ι n), 0 <= iidPower p n z := by
  intro n
  induction n with
  | zero =>
    intro z
    norm_num [iidPower]
  | succ n ih =>
    intro z
    exact mul_nonneg (hp z.1) (ih z.2)

/-- The Renyi power sum of `n` independent copies is the `n`th power of the one-copy sum. -/
theorem renyi_power_sum_power {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (n : Nat)
    (hp : forall i, 0 <= p i) (hq : forall i, 0 <= q i) :
    (∑ z : IidSpace ι n,
        (iidPower p n z) ^ alpha * (iidPower q n z) ^ (1 - alpha)) =
      (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ^ n := by
  classical
  induction n with
  | zero =>
    calc
      _ = (iidPower p 0 PUnit.unit) ^ alpha *
          (iidPower q 0 PUnit.unit) ^ (1 - alpha) :=
        Fintype.sum_eq_single PUnit.unit fun z hz =>
          (hz (Subsingleton.elim z PUnit.unit)).elim
      _ = _ := by norm_num [iidPower]
  | succ n ih =>
    change (∑ z : ι × IidSpace ι n,
        (p z.1 * iidPower p n z.2) ^ alpha *
          (q z.1 * iidPower q n z.2) ^ (1 - alpha)) =
      (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ^ (n + 1)
    rw [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ z,
          (p i * iidPower p n z) ^ alpha *
            (q i * iidPower q n z) ^ (1 - alpha)) =
          ∑ i, ∑ z,
            ((p i) ^ alpha * (q i) ^ (1 - alpha)) *
              ((iidPower p n z) ^ alpha * (iidPower q n z) ^ (1 - alpha)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro z _
        rw [Real.mul_rpow (hp i) (iid_power_nonneg p hp n z),
          Real.mul_rpow (hq i) (iid_power_nonneg q hq n z)]
        ring
      _ = (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) *
          ∑ z : IidSpace ι n,
            (iidPower p n z) ^ alpha * (iidPower q n z) ^ (1 - alpha) :=
        (Fintype.sum_mul_sum _ _).symm
      _ = (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) ^ (n + 1) := by
        rw [ih, pow_succ']

/-- Repeating a finite nonnegative experiment `n` times multiplies its Renyi divergence by `n`.
No normalization, power-sum non-vanishing, or order restriction is needed. -/
theorem renyi_divergence_power_additive {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (n : Nat)
    (hp : forall i, 0 <= p i) (hq : forall i, 0 <= q i) :
    renyiDivergence alpha (iidPower p n) (iidPower q n) =
      n * renyiDivergence alpha p q := by
  fail_if_success rfl
  fail_if_success simp
  classical
  by_cases hsum : (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) = 0
  · rw [renyiDivergence, renyiDivergence,
      renyi_power_sum_power alpha p q n hp hq, hsum]
    cases n with
    | zero => norm_num
    | succ n => simp
  · induction n with
    | zero =>
      have hsum_zero :
          (∑ z : IidSpace ι 0,
            (iidPower p 0 z) ^ alpha * (iidPower q 0 z) ^ (1 - alpha)) = 1 := by
        calc
          _ = (iidPower p 0 PUnit.unit) ^ alpha *
              (iidPower q 0 PUnit.unit) ^ (1 - alpha) :=
            Fintype.sum_eq_single PUnit.unit fun z hz =>
              (hz (Subsingleton.elim z PUnit.unit)).elim
          _ = 1 := by norm_num [iidPower]
      rw [renyiDivergence]
      rw [hsum_zero]
      norm_num
    | succ n ih =>
      change renyiDivergence alpha
          (fun z : ι × IidSpace ι n => p z.1 * iidPower p n z.2)
          (fun z : ι × IidSpace ι n => q z.1 * iidPower q n z.2) =
        ((n + 1 : Nat) : Real) * renyiDivergence alpha p q
      have hsum_n :
          (∑ z : IidSpace ι n,
            (iidPower p n z) ^ alpha * (iidPower q n z) ^ (1 - alpha)) ≠ 0 := by
        rw [renyi_power_sum_power alpha p q n hp hq]
        exact pow_ne_zero n hsum
      calc
        renyiDivergence alpha
            (fun z : ι × IidSpace ι n => p z.1 * iidPower p n z.2)
            (fun z : ι × IidSpace ι n => q z.1 * iidPower q n z.2) =
          renyiDivergence alpha p q +
            renyiDivergence alpha (iidPower p n) (iidPower q n) :=
          renyi_divergence_product_additive alpha p q
            (iidPower p n) (iidPower q n) hp hq
            (iid_power_nonneg p hp n) (iid_power_nonneg q hq n) hsum hsum_n
        _ = ((n + 1 : Nat) : Real) * renyiDivergence alpha p q := by
          rw [ih]
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/- On two copies of the Bool point-mass-versus-uniform experiment at order two, the left side
computes to `log 4`, as does twice the one-copy divergence. -/
example :
    renyiDivergence 2
        (iidPower (fun b : Bool => if b then (1 : Real) else 0) 2)
        (iidPower (fun _b : Bool => (1 / 2 : Real)) 2) =
      2 * renyiDivergence 2
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _b : Bool => (1 / 2 : Real)) := by
  have hp_point : forall b : Bool, 0 <= if b then (1 : Real) else 0 := by
    intro b
    cases b <;> norm_num
  have hq_uniform : forall _b : Bool, 0 <= (1 / 2 : Real) := by
    intro b
    norm_num
  have hLeft :
      renyiDivergence 2
          (iidPower (fun b : Bool => if b then (1 : Real) else 0) 2)
          (iidPower (fun _b : Bool => (1 / 2 : Real)) 2) = Real.log 4 := by
    rw [renyiDivergence,
      renyi_power_sum_power 2
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _b : Bool => (1 / 2 : Real)) 2 hp_point hq_uniform]
    norm_num [Fintype.sum_bool]
  have hRight :
      2 * renyiDivergence 2
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) = Real.log 4 := by
    rw [renyi_divergence_two_point_order_two,
      show (4 : Real) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    ring
  rw [hLeft, hRight]

#print axioms iid_power_nonneg
#print axioms renyi_power_sum_power
#print axioms renyi_divergence_power_additive

end D5.S3.RenyiDivergence
