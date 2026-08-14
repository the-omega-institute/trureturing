/- GID: D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct captured rows have exact weighted pair mass and uniform specializations. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches for `pairCaptureProbability`, `fixedSquareMass`, and
     `collisionSquareMass` found no pre-existing declaration outside this proposal.
   * Pinned-Mathlib searches found the finite dependent product/sum factorization used
     below, but no exact two-row weighted twisted-diagonal capture formula.
   * The proof reuses `constrainedRows_weight_sum` from the one-row module and derives
     the second-order factors rather than installing them by definition.
-/

import D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.FiniteProductPairCapture

open FiniteProductCapture

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

private theorem rowWeight_target_eq [Fintype A] [DecidableEq A]
    (q : A -> Y -> Real) (f : Y -> Y) (X : A -> Y) (a : A) :
    rowWeight q a (targetRows f X a) =
      ∏ b, if b = a then 1 else q b (f (X b)) := by
  change (∏ b : {b : A // b ≠ a}, q b.1 (f (X b.1))) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun b => if b = a then 1 else q b (f (X b))) a]
  simp only [if_pos, one_mul]
  apply Finset.prod_congr rfl
  intro b _
  rw [if_neg b.property]

/-- Exact two-address capture probability; distinct rows produce the squared masses. -/
theorem pair_capture_probability_exact [Fintype A] [Fintype Y] [DecidableEq A]
    (q : A -> Y -> Real) (hq : forall b, ∑ y, q b y = 1)
    (f : Y -> Y) (a a' : A) (haa' : a ≠ a') :
    pairCaptureProbability q f a a' =
      fixedSquareMass q f a * fixedSquareMass q f a' *
        ∏ b : {b : A // b ≠ a ∧ b ≠ a'}, collisionSquareMass q f b.1 := by
  classical
  rw [pairCaptureProbability, eventProbability, Fintype.sum_prod_type]
  have hinner : forall X : A -> Y,
      (∑ R : (a : A) -> OffRow A Y a,
        if Captured f (X, R) a ∧ Captured f (X, R) a' then
          sampleWeight q (X, R) else 0) =
      if f (X a) = X a ∧ f (X a') = X a' then
        (∏ b, q b (X b)) *
          (rowWeight q a (targetRows f X a) *
            rowWeight q a' (targetRows f X a')) else 0 := by
    intro X
    by_cases hfixed : f (X a) = X a ∧ f (X a') = X a'
    · rcases hfixed with ⟨hfa, hfa'⟩
      simp only [captured_iff_twisted_diagonal, hfa, hfa', true_and, if_true]
      simp_rw [sampleWeight]
      calc
        (∑ R : (a : A) -> OffRow A Y a,
            if R a = targetRows f X a ∧ R a' = targetRows f X a' then
              (∏ b, q b (X b)) * ∏ i, rowWeight q i (R i) else 0) =
            (∏ b, q b (X b)) *
          (∑ R : (a : A) -> OffRow A Y a,
            if R a = targetRows f X a ∧ R a' = targetRows f X a' then
              ∏ i, rowWeight q i (R i) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro R _
              split <;> simp_all
        _ = _ := by
          rw [show (∑ R : (a : A) -> OffRow A Y a,
                if R a = targetRows f X a ∧ R a' = targetRows f X a' then
                  ∏ i, rowWeight q i (R i) else 0) =
              rowWeight q a (targetRows f X a) *
                rowWeight q a' (targetRows f X a') by
            simpa [haa'] using
              constrainedRows_weight_sum q hq {a, a'} (targetRows f X)]
    · push Not at hfixed
      by_cases hfa : f (X a) = X a
      · have hfa' : f (X a') ≠ X a' := hfixed hfa
        simp [captured_iff_twisted_diagonal, hfa, hfa']
      · simp [captured_iff_twisted_diagonal, hfa]
  simp_rw [hinner]
  have hsummand : forall X : A -> Y,
      (if f (X a) = X a ∧ f (X a') = X a' then
          (∏ b, q b (X b)) *
            (rowWeight q a (targetRows f X a) *
              rowWeight q a' (targetRows f X a')) else 0) =
      ∏ b, if b = a then
        (if f (X b) = X b then q b (X b) ^ 2 else 0)
      else if b = a' then
        (if f (X b) = X b then q b (X b) ^ 2 else 0)
      else q b (X b) * q b (f (X b)) ^ 2 := by
    intro X
    by_cases hfa : f (X a) = X a
    · by_cases hfa' : f (X a') = X a'
      · rw [if_pos ⟨hfa, hfa'⟩, rowWeight_target_eq, rowWeight_target_eq]
        rw [← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro b _
        by_cases hba : b = a
        · subst b; simp [hfa, haa', pow_two]
        · by_cases hba' : b = a'
          · subst b; simp [hfa', haa'.symm, pow_two]
          · simp [hba, hba']; ring
      · rw [if_neg (by simp [hfa, hfa'])]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ a')
        simp [hfa', haa'.symm]
    · rw [if_neg (by simp [hfa])]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [hfa]
  simp_rw [hsummand]
  calc
    (∑ X : A -> Y, ∏ b, if b = a then
        (if f (X b) = X b then q b (X b) ^ 2 else 0)
      else if b = a' then
        (if f (X b) = X b then q b (X b) ^ 2 else 0)
      else q b (X b) * q b (f (X b)) ^ 2) =
        ∏ b, ∑ y, if b = a then
          (if f y = y then q b y ^ 2 else 0)
        else if b = a' then
          (if f y = y then q b y ^ 2 else 0)
        else q b y * q b (f y) ^ 2 := by
      symm
      exact Fintype.prod_sum fun b y => if b = a then
        (if f y = y then q b y ^ 2 else 0) else if b = a' then
          (if f y = y then q b y ^ 2 else 0) else q b y * q b (f y) ^ 2
    _ = _ := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun b => ∑ y, if b = a then
        (if f y = y then q b y ^ 2 else 0)
      else if b = a' then
        (if f y = y then q b y ^ 2 else 0)
      else q b y * q b (f y) ^ 2) a]
      simp only [if_pos]
      rw [Fintype.prod_eq_mul_prod_subtype_ne
        (fun b : {b : A // b ≠ a} => ∑ y,
          if b.1 = a then (if f y = y then q b.1 y ^ 2 else 0)
          else if b.1 = a' then (if f y = y then q b.1 y ^ 2 else 0)
          else q b.1 y * q b.1 (f y) ^ 2) ⟨a', haa'.symm⟩]
      simp only [haa'.symm, if_false, if_pos]
      have hprod :
          (∏ b : {b : {b : A // b ≠ a} // b ≠ ⟨a', haa'.symm⟩}, ∑ y,
              if b.1.1 = a then (if f y = y then q b.1.1 y ^ 2 else 0)
              else if b.1.1 = a' then (if f y = y then q b.1.1 y ^ 2 else 0)
              else q b.1.1 y * q b.1.1 (f y) ^ 2) =
            ∏ b : {b : {b : A // b ≠ a} // b ≠ ⟨a', haa'.symm⟩},
              collisionSquareMass q f b.1.1 := by
        apply Finset.prod_congr rfl
        intro b _
        have hba' : b.1.1 ≠ a' := by
          intro h
          apply b.property
          apply Subtype.ext
          exact h
        simp [b.1.property, hba', collisionSquareMass]
      conv_lhs => rhs; rhs; rw [hprod]
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
      have heq :
          (∏ b : {b : {b : A // b ≠ a} // b ≠ ⟨a', haa'.symm⟩},
              collisionSquareMass q f b.1.1) =
            ∏ b : {b : A // b ≠ a ∧ b ≠ a'}, collisionSquareMass q f b.1 := by
        symm
        simpa [e] using Equiv.prod_comp e (fun b => collisionSquareMass q f b.1.1)
      rw [heq]
      simp only [fixedSquareMass]
      ring

private theorem fixedPowerMass_uniform [Fintype Y] (f : Y -> Y) (e : Nat) :
    (∑ y : Y, if f y = y then (Fintype.card Y : Real)⁻¹ ^ e else 0) =
      (Nat.card {y : Y // f y = y} : Real) * (Fintype.card Y : Real)⁻¹ ^ e := by
  classical
  have hcard : ((Finset.univ.filter fun y : Y => f y = y).card : Real) =
      Nat.card {y : Y // f y = y} := by
    norm_cast
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype (fun y : Y => f y = y)).symm
  calc
    _ = (Finset.univ.filter (fun y : Y => f y = y)).sum
          (fun _ => (Fintype.card Y : Real)⁻¹ ^ e) := by
      simpa using (Finset.sum_filter (s := Finset.univ) (fun y : Y => f y = y)
        (fun _ => (Fintype.card Y : Real)⁻¹ ^ e)).symm
    _ = ((Finset.univ.filter fun y : Y => f y = y).card : Real) *
        (Fintype.card Y : Real)⁻¹ ^ e := by simp
    _ = _ := by rw [hcard]

theorem fixedMass_uniform [Fintype Y] (f : Y -> Y) (a : A) :
    fixedMass (fun _ _ => (Fintype.card Y : Real)⁻¹) f a =
      (Nat.card {y : Y // f y = y} : Real) * (Fintype.card Y : Real)⁻¹ := by
  simpa [fixedMass] using fixedPowerMass_uniform f 1
theorem collisionMass_uniform [Fintype Y] [Nonempty Y] (f : Y -> Y) (b : A) :
    collisionMass (fun _ _ => (Fintype.card Y : Real)⁻¹) f b =
      (Fintype.card Y : Real)⁻¹ := by
  rw [collisionMass]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hn : (Fintype.card Y : Real) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
theorem fixedSquareMass_uniform [Fintype Y] (f : Y -> Y) (a : A) :
    fixedSquareMass (fun _ _ => (Fintype.card Y : Real)⁻¹) f a =
      (Nat.card {y : Y // f y = y} : Real) * (Fintype.card Y : Real)⁻¹ ^ 2 := by
  simpa [fixedSquareMass] using fixedPowerMass_uniform f 2
theorem collisionSquareMass_uniform [Fintype Y] [Nonempty Y] (f : Y -> Y) (b : A) :
    collisionSquareMass (fun _ _ => (Fintype.card Y : Real)⁻¹) f b =
      (Fintype.card Y : Real)⁻¹ ^ 2 := by
  rw [collisionSquareMass]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hn : (Fintype.card Y : Real) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

#print axioms pair_capture_probability_exact

end

end D5.S0.Asymptotics.WeightedProbability.FiniteProductPairCapture
