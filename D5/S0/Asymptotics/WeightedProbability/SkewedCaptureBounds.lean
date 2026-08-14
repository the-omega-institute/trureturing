/- GID: D5/S0/Asymptotics/WeightedProbability/SkewedCaptureBounds
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/SkewedCaptureBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Skewed finite listings satisfy exact capture laws and two-sided escape bounds. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches found the uniform cardinal laws in `Diagonal/CaptureCount` and
     the existing one-slot PMF law `SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass`,
     but no theorem combining varying marginals, pair capture, and two-sided bounds.
   * The new real fixed-point mass is connected to the PMF definition by
     `FiniteProductCapture.fixedMass_pmf_toReal`; the one-address clause is therefore a
     typed bridge-compatible specialization, not an unconnected duplicate.
   * Pinned-Mathlib searches found no theorem with the six-conjunct headline shape; this
     module composes the exact product laws and the locally audited Bonferroni bounds.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.SkewedCaptureBounds

open FiniteProductCapture
open FiniteProductPairCapture
open FiniteBonferroni

noncomputable section

variable {A Y : Type*}

/-- Uniform marginals recover the `k n^{-A}` capture law. -/
theorem uniform_capture_probability [Fintype A] [Fintype Y]
    [DecidableEq A] [Nonempty Y] (f : Y -> Y) (a : A) :
    captureProbability (fun _ _ => (Fintype.card Y : Real)⁻¹) f a =
      (Nat.card {y : Y // f y = y} : Real) *
        (Fintype.card Y : Real)⁻¹ ^ Fintype.card A := by
  classical
  rw [capture_probability_exact
    (q := fun _ _ => (Fintype.card Y : Real)⁻¹)
    (hq := fun _ => by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hn : (Fintype.card Y : Real) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp) f a, fixedMass_uniform]
  simp_rw [collisionMass_uniform]
  simp only [Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card {b : A // b ≠ a} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hcard, mul_assoc, ← pow_succ']
  congr 2
  have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

private theorem two_removed_card [Fintype A] [DecidableEq A]
    (a a' : A) (haa' : a ≠ a') :
    Fintype.card {b : A // b ≠ a ∧ b ≠ a'} = Fintype.card A - 2 := by
  classical
  let e : {b : A // b ≠ a ∧ b ≠ a'} ≃
      {b : {b : A // b ≠ a} // b ≠ ⟨a', haa'.symm⟩} :=
    { toFun := fun b => ⟨⟨b.1, b.2.1⟩, by
          intro h
          exact b.2.2 (congrArg Subtype.val h)⟩
      invFun := fun b => ⟨b.1.1, b.1.2, by
          intro h
          apply b.2
          apply Subtype.ext
          exact h⟩
      left_inv := by intro b; rfl
      right_inv := by intro b; rfl }
  calc
    Fintype.card {b : A // b ≠ a ∧ b ≠ a'} =
        Fintype.card {b : {b : A // b ≠ a} // b ≠ ⟨a', haa'.symm⟩} :=
      Fintype.card_congr e
    _ = Fintype.card {b : A // b ≠ a} - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    _ = (Fintype.card A - 1) - 1 := by
      rw [Fintype.card_subtype_compl]
      simp
    _ = Fintype.card A - 2 := by omega

private theorem uniform_pair_capture_probability [Fintype A] [Fintype Y]
    [DecidableEq A] [Nonempty Y]
    (f : Y -> Y) (a a' : A) (haa' : a ≠ a') :
    pairCaptureProbability (fun _ _ => (Fintype.card Y : Real)⁻¹) f a a' =
      (Nat.card {y : Y // f y = y} : Real) ^ 2 *
        (Fintype.card Y : Real)⁻¹ ^ (2 * Fintype.card A) := by
  classical
  rw [pair_capture_probability_exact
    (q := fun _ _ => (Fintype.card Y : Real)⁻¹)
    (hq := fun _ => by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hn : (Fintype.card Y : Real) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp) f a a' haa', fixedSquareMass_uniform, fixedSquareMass_uniform]
  simp_rw [collisionSquareMass_uniform]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [two_removed_card a a' haa']
  let k : Real := Nat.card {y : Y // f y = y}
  let r : Real := (Fintype.card Y : Real)⁻¹
  change (k * r ^ 2) * (k * r ^ 2) * (r ^ 2) ^ (Fintype.card A - 2) =
    k ^ 2 * r ^ (2 * Fintype.card A)
  have hcard : 2 ≤ Fintype.card A := by
    exact Fintype.one_lt_card_iff.mpr ⟨a, a', haa'⟩
  calc
    _ = k ^ 2 * ((r ^ 2) ^ 2 * (r ^ 2) ^ (Fintype.card A - 2)) := by ring
    _ = k ^ 2 * (r ^ 2) ^ (2 + (Fintype.card A - 2)) := by rw [pow_add]
    _ = k ^ 2 * (r ^ 2) ^ Fintype.card A := by congr 2; omega
    _ = k ^ 2 * r ^ (2 * Fintype.card A) := by rw [pow_mul]

/-- Under uniform marginals, distinct capture events are pairwise independent. -/
theorem uniform_capture_pairwise_independent [Fintype A] [Fintype Y]
    [DecidableEq A] [Nonempty Y]
    (f : Y -> Y) (a a' : A) (haa' : a ≠ a') :
    pairCaptureProbability (fun _ _ => (Fintype.card Y : Real)⁻¹) f a a' =
      captureProbability (fun _ _ => (Fintype.card Y : Real)⁻¹) f a *
        captureProbability (fun _ _ => (Fintype.card Y : Real)⁻¹) f a' := by
  rw [uniform_pair_capture_probability f a a' haa',
    uniform_capture_probability f a, uniform_capture_probability f a']
  rw [show 2 * Fintype.card A = Fintype.card A + Fintype.card A by omega, pow_add]
  ring

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent finite event space needs additional elaboration budget.
/-- With one address, escape is exactly one minus the weighted fixed-point mass. -/
theorem one_address_escape_probability [Fintype Y]
    (q : Fin 1 -> Y -> Real)
    (hq_nonneg : forall b y, 0 ≤ q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    escapeProbability q f = 1 - fixedMass q f 0 := by
  have hb := escape_bonferroni_bounds q hq_nonneg hq_sum f
  have hcapture : captureProbability q f 0 = fixedMass q f 0 := by
    rw [capture_probability_exact q hq_sum f 0]
    have hprod : (∏ b : {b : Fin 1 // b ≠ 0}, collisionMass q f b.1) = 1 := by
      apply Finset.prod_eq_one
      intro b _
      exact (b.property (Fin.eq_zero b.1)).elim
    rw [hprod, mul_one]
  have hpairs : pairProbabilitySum q f = 0 := by simp [pairProbabilitySum]
  simp only [Fin.sum_univ_one] at hb
  rw [← hcapture]
  apply le_antisymm
  · calc
      escapeProbability q f ≤
          1 - captureProbability q f 0 + pairProbabilitySum q f := hb.2
      _ = 1 - captureProbability q f 0 := by rw [hpairs, add_zero]
  · exact hb.1

/-- Exact skewed capture laws, escape bounds, the uniform kernel, and the one-address edge. -/
theorem skewed_capture_bounds [Fintype A] [Fintype Y] [LinearOrder A] [Nonempty Y]
    (q : A -> Y -> Real)
    (hq_nonneg : forall b y, 0 ≤ q b y)
    (hq_sum : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) :
    (forall a, captureProbability q f a =
      fixedMass q f a * ∏ b : {b : A // b ≠ a}, collisionMass q f b.1) ∧
    (forall a a', a ≠ a' ->
      pairCaptureProbability q f a a' =
      fixedSquareMass q f a * fixedSquareMass q f a' *
        ∏ b : {b : A // b ≠ a ∧ b ≠ a'}, collisionSquareMass q f b.1) ∧
    (1 - ∑ a, captureProbability q f a ≤ escapeProbability q f ∧
      escapeProbability q f ≤
        1 - ∑ a, captureProbability q f a + pairProbabilitySum q f) ∧
    (forall a, captureProbability (fun (_ : A) (_ : Y) =>
        (Fintype.card Y : Real)⁻¹) f a =
      (Nat.card {y : Y // f y = y} : Real) *
        (Fintype.card Y : Real)⁻¹ ^ Fintype.card A) ∧
    (forall a a', a ≠ a' ->
      pairCaptureProbability (fun (_ : A) (_ : Y) =>
          (Fintype.card Y : Real)⁻¹) f a a' =
        captureProbability (fun (_ : A) (_ : Y) =>
          (Fintype.card Y : Real)⁻¹) f a *
          captureProbability (fun (_ : A) (_ : Y) =>
            (Fintype.card Y : Real)⁻¹) f a') ∧
    (forall (qOne : Fin 1 -> Y -> Real),
      (forall b y, 0 ≤ qOne b y) ->
      (forall b, ∑ y, qOne b y = 1) ->
      escapeProbability qOne f = 1 - fixedMass qOne f 0) := by
  exact ⟨fun a => capture_probability_exact q hq_sum f a,
    fun a a' haa' => pair_capture_probability_exact q hq_sum f a a' haa',
    escape_bonferroni_bounds q hq_nonneg hq_sum f,
    uniform_capture_probability f,
    fun a a' haa' => uniform_capture_pairwise_independent f a a' haa',
    fun qOne hnonneg hsum => one_address_escape_probability qOne hnonneg hsum f⟩

/-- A concrete normalized marginal exercises the headline theorem on a two-by-two model. -/
example :
    captureProbability (fun (_ : Fin 2) (_ : Fin 2) => (1 : Real) / 2) id 0 =
      fixedMass (fun (_ : Fin 2) (_ : Fin 2) => (1 : Real) / 2) id 0 *
        ∏ b : {b : Fin 2 // b ≠ 0},
          collisionMass (fun (_ : Fin 2) (_ : Fin 2) => (1 : Real) / 2) id b.1 := by
  exact (skewed_capture_bounds
    (A := Fin 2) (Y := Fin 2)
    (q := fun _ _ => (1 : Real) / 2)
    (hq_nonneg := by norm_num)
    (hq_sum := by
      intro b
      rw [Fin.sum_univ_two]
      norm_num)
    (f := id)).1 0

/-- The independent finite-listing sample domain is inhabited. -/
example : Sample (Fin 1) Unit := ⟨fun _ => (), fun _ _ => ()⟩

#print axioms uniform_capture_probability
#print axioms uniform_capture_pairwise_independent
#print axioms one_address_escape_probability
#print axioms skewed_capture_bounds

end

end D5.S0.Asymptotics.WeightedProbability.SkewedCaptureBounds
