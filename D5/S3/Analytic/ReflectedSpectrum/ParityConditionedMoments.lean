/- GID: D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Parity fibers have uniform proper moments and opposite full-product moments. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * Exact-name and whole-statement-shape searches on current `origin/dev` found
     no `paritySign`, `parityFiber`, `parityLaw`, `parityMarginalMass`, or either
     public theorem below outside `X_Frontier`.
   * The current in-flight module and atom inventories contain neither target;
     the sole token hit, `TerminalShellParityLaw`, is unrelated.
   * Pinned Mathlib supplies finite sums and products, coordinate updates,
     `Finset.sum_involution`, and finite-cardinality lemmas, but no packaged
     parity-fiber moment theorem with the two probability laws below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

open scoped BigOperators

/-- The sign encoded by a binary coordinate: zero is negative and one is positive. -/
def paritySign (b : Fin 2) : ℤ := if b = 0 then -1 else 1

/-- Binary strings whose coordinate-sign product is the prescribed parity. -/
def parityFiber (d : ℕ) (ε : ℤ) : Finset (Fin d → Fin 2) :=
  Finset.univ.filter (fun x => (∏ i, paritySign (x i)) = ε)

/-- The uniform rational law on one parity fiber. -/
def parityLaw (d : ℕ) (ε : ℤ) (x : Fin d → Fin 2) : ℚ :=
  if x ∈ parityFiber d ε then ((2 : ℚ) ^ (d - 1))⁻¹ else 0

private def bitFlip (b : Fin 2) : Fin 2 := Equiv.swap 0 1 b

private def flipCoord {d : ℕ} (j : Fin d) (x : Fin d → Fin 2) : Fin d → Fin 2 :=
  Function.update x j (bitFlip (x j))

/-- Flip one coordinate in a subset and one outside it. -/
private def flipTwo {d : ℕ} (a b : Fin d) (x : Fin d → Fin 2) : Fin d → Fin 2 :=
  flipCoord b (flipCoord a x)

private lemma paritySign_cases (b : Fin 2) : paritySign b = -1 ∨ paritySign b = 1 := by
  fin_cases b <;> simp [paritySign]

private lemma bitFlip_ne (b : Fin 2) : bitFlip b ≠ b := by
  fin_cases b <;> simp [bitFlip]

private lemma paritySign_bitFlip (b : Fin 2) : paritySign (bitFlip b) = -paritySign b := by
  fin_cases b <;> simp [bitFlip, paritySign]

private lemma bitFlip_involutive : Function.Involutive bitFlip := by
  intro b
  fin_cases b <;> simp [bitFlip]

private lemma flipCoord_involutive {d : ℕ} (j : Fin d) : Function.Involutive (flipCoord j) := by
  intro x
  funext i
  by_cases hij : i = j
  · subst i
    simpa [flipCoord] using bitFlip_involutive (x j)
  · simp [flipCoord, hij]

private lemma flipCoord_comm {d : ℕ} {a b : Fin d} (hab : a ≠ b) (x : Fin d → Fin 2) :
    flipCoord a (flipCoord b x) = flipCoord b (flipCoord a x) := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [flipCoord, hab, hab.symm]
  · by_cases hib : i = b
    · subst i
      simp [flipCoord, hab, hab.symm]
    · simp [flipCoord, hia, hib]

private lemma flipTwo_involutive {d : ℕ} {a b : Fin d} (hab : a ≠ b) :
    Function.Involutive (flipTwo a b) := by
  intro x
  calc
    flipTwo a b (flipTwo a b x) =
        flipCoord b (flipCoord a (flipCoord b (flipCoord a x))) := rfl
    _ = flipCoord b (flipCoord b (flipCoord a (flipCoord a x))) := by
      rw [flipCoord_comm hab]
    _ = x := by rw [flipCoord_involutive, flipCoord_involutive]

private lemma prod_paritySign_cases {d : ℕ} (s : Finset (Fin d)) (x : Fin d → Fin 2) :
    (∏ i ∈ s, paritySign (x i)) = -1 ∨ (∏ i ∈ s, paritySign (x i)) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases paritySign_cases (x a) with h | h <;>
        rcases ih with ih | ih <;> simp [h, ih]

private lemma fullProduct_flipCoord {d : ℕ} (j : Fin d) (x : Fin d → Fin 2) :
    (∏ i, paritySign (flipCoord j x i)) = -(∏ i, paritySign (x i)) := by
  classical
  have hfun :
      (fun i => paritySign (flipCoord j x i)) =
        Function.update (fun i => paritySign (x i)) j (paritySign (bitFlip (x j))) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [flipCoord]
    · simp [flipCoord, hij]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j), paritySign_bitFlip]
  ring

private lemma subsetProduct_flipCoord_of_mem {d : ℕ} {A : Finset (Fin d)} {j : Fin d}
    (hj : j ∈ A) (x : Fin d → Fin 2) :
    (∏ i ∈ A, paritySign (flipCoord j x i)) = -(∏ i ∈ A, paritySign (x i)) := by
  classical
  have hfun :
      (fun i => paritySign (flipCoord j x i)) =
        Function.update (fun i => paritySign (x i)) j (paritySign (bitFlip (x j))) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [flipCoord]
    · simp [flipCoord, hij]
  rw [hfun, Finset.prod_update_of_mem hj,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj, paritySign_bitFlip]
  ring

private lemma subsetProduct_flipCoord_of_notMem {d : ℕ} {A : Finset (Fin d)} {j : Fin d}
    (hj : j ∉ A) (x : Fin d → Fin 2) :
    (∏ i ∈ A, paritySign (flipCoord j x i)) = ∏ i ∈ A, paritySign (x i) := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := by
    intro h
    exact hj (h ▸ hi)
  simp [flipCoord, hij]

private lemma fullProduct_flipTwo {d : ℕ} (a b : Fin d) (x : Fin d → Fin 2) :
    (∏ i, paritySign (flipTwo a b x i)) = ∏ i, paritySign (x i) := by
  rw [flipTwo, fullProduct_flipCoord, fullProduct_flipCoord]
  ring

private lemma subsetProduct_flipTwo {d : ℕ} {A : Finset (Fin d)} {a b : Fin d}
    (ha : a ∈ A) (hb : b ∉ A) (x : Fin d → Fin 2) :
    (∏ i ∈ A, paritySign (flipTwo a b x i)) = -(∏ i ∈ A, paritySign (x i)) := by
  rw [flipTwo, subsetProduct_flipCoord_of_notMem hb, subsetProduct_flipCoord_of_mem ha]

private lemma mem_parityFiber {d : ℕ} {ε : ℤ} {x : Fin d → Fin 2} :
    x ∈ parityFiber d ε ↔ (∏ i, paritySign (x i)) = ε := by
  simp [parityFiber]

private lemma parityFiber_neg_card_eq_pos_card {d : ℕ} (hd : 0 < d) :
    (parityFiber d (-1)).card = (parityFiber d 1).card := by
  let j : Fin d := ⟨0, hd⟩
  refine Finset.card_bij' (fun x _ => flipCoord j x) (fun x _ => flipCoord j x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_parityFiber, fullProduct_flipCoord, (mem_parityFiber.mp hx)]
    norm_num
  · intro x hx
    rw [mem_parityFiber, fullProduct_flipCoord, (mem_parityFiber.mp hx)]
  · intro x hx
    exact flipCoord_involutive j x
  · intro x hx
    exact flipCoord_involutive j x

private lemma parityFiber_card {d : ℕ} (hd : 0 < d) (ε : ℤ)
    (hε : ε = -1 ∨ ε = 1) :
    (parityFiber d ε).card = 2 ^ (d - 1) := by
  have htotal : (parityFiber d (-1)).card + (parityFiber d 1).card = 2 ^ d := by
    have hdisjoint : Disjoint (parityFiber d (-1)) (parityFiber d 1) := by
      rw [Finset.disjoint_left]
      intro x hxneg hxpos
      have hn := mem_parityFiber.mp hxneg
      have hp := mem_parityFiber.mp hxpos
      omega
    have hunion : parityFiber d (-1) ∪ parityFiber d 1 = Finset.univ := by
      ext x
      simp only [Finset.mem_union, mem_parityFiber, Finset.mem_univ, iff_true]
      exact prod_paritySign_cases Finset.univ x
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
    simp
  have heq := parityFiber_neg_card_eq_pos_card hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  simp only [Nat.succ_sub_one] at hε ⊢
  rw [pow_succ] at htotal
  rcases hε with rfl | rfl <;> omega

private lemma properMoment_sum_zero {d : ℕ} (ε : ℤ) (A : Finset (Fin d))
    (hA : A.Nonempty) (hAproper : A ≠ Finset.univ) :
    (∑ x ∈ parityFiber d ε, ∏ i ∈ A, paritySign (x i)) = 0 := by
  classical
  obtain ⟨a, ha⟩ := hA
  have hbExists : ∃ b : Fin d, b ∉ A := by
    by_contra h
    push Not at h
    apply hAproper
    ext i
    simp [h i]
  obtain ⟨b, hb⟩ := hbExists
  have hab : a ≠ b := by
    intro h
    subst b
    exact hb ha
  refine Finset.sum_involution (fun x _ => flipTwo a b x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [subsetProduct_flipTwo ha hb]
    ring
  · intro x hx hnonzero heq
    have hpoint := congr_fun heq a
    exact bitFlip_ne (x a) (by simpa [flipTwo, flipCoord, hab] using hpoint)
  · intro x hx
    rw [mem_parityFiber, fullProduct_flipTwo]
    exact mem_parityFiber.mp hx
  · intro x hx
    exact flipTwo_involutive hab x

private lemma fullMoment_sum {d : ℕ} (ε : ℤ) :
    (∑ x ∈ parityFiber d ε, ∏ i : Fin d, paritySign (x i)) =
      ε * ((parityFiber d ε).card : ℤ) := by
  calc
    (∑ x ∈ parityFiber d ε, ∏ i : Fin d, paritySign (x i)) =
        ∑ _x ∈ parityFiber d ε, ε := by
          apply Finset.sum_congr rfl
          intro x hx
          exact mem_parityFiber.mp hx
    _ = ε * ((parityFiber d ε).card : ℤ) := by simp [mul_comm]

/-- A nonempty parity fiber has half the cube, every nonempty proper product
moment cancels, and the full product is fixed by the parity condition. -/
theorem parity_conditioned_moments (k : ℕ) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    (parityFiber (k + 1) ε).card = 2 ^ k ∧
      (∀ A : Finset (Fin (k + 1)), A.Nonempty → A ≠ Finset.univ →
        (∑ x ∈ parityFiber (k + 1) ε, ∏ i ∈ A, paritySign (x i)) = 0) ∧
      (∑ x ∈ parityFiber (k + 1) ε, ∏ i : Fin (k + 1), paritySign (x i)) =
        ε * ((parityFiber (k + 1) ε).card : ℤ) := by
  have hcard := parityFiber_card (Nat.succ_pos k) ε hε
  simp only [Nat.succ_sub_one] at hcard
  exact ⟨hcard, properMoment_sum_zero ε, fullMoment_sum ε⟩

/-- The mass assigned by a parity law to a prescribed coordinate restriction. -/
def parityMarginalMass (d : ℕ) (ε : ℤ) (A : Finset (Fin d))
    (y : Fin d → Fin 2) : ℚ :=
  ∑ x : Fin d → Fin 2, if (∀ i ∈ A, x i = y i) then parityLaw d ε x else 0

private lemma parityLaw_expectation_eq {d : ℕ} (ε : ℤ) (f : (Fin d → Fin 2) → ℚ) :
    (∑ x, parityLaw d ε x * f x) =
      ((2 : ℚ) ^ (d - 1))⁻¹ * ∑ x ∈ parityFiber d ε, f x := by
  classical
  simp [parityLaw, Finset.mul_sum]

private lemma parityLaw_flip_neg_eq_pos {d : ℕ} (j : Fin d) (x : Fin d → Fin 2) :
    parityLaw d (-1) (flipCoord j x) = parityLaw d 1 x := by
  rcases prod_paritySign_cases Finset.univ x with h | h <;>
    simp [parityLaw, mem_parityFiber, fullProduct_flipCoord, h]

private lemma flipCoord_agrees_iff {d : ℕ} {A : Finset (Fin d)} {j : Fin d}
    (hj : j ∉ A) (x y : Fin d → Fin 2) :
    (∀ i ∈ A, flipCoord j x i = y i) ↔ ∀ i ∈ A, x i = y i := by
  constructor
  · intro h i hi
    have hij : i ≠ j := by
      intro e
      exact hj (e ▸ hi)
    simpa [flipCoord, hij] using h i hi
  · intro h i hi
    have hij : i ≠ j := by
      intro e
      exact hj (e ▸ hi)
    simpa [flipCoord, hij] using h i hi

private lemma parityMarginalMass_neg_eq_pos {d : ℕ} (A : Finset (Fin d))
    (hAproper : A ≠ Finset.univ) (y : Fin d → Fin 2) :
    parityMarginalMass d (-1) A y = parityMarginalMass d 1 A y := by
  classical
  have hbExists : ∃ b : Fin d, b ∉ A := by
    by_contra h
    push Not at h
    apply hAproper
    ext i
    simp [h i]
  obtain ⟨b, hb⟩ := hbExists
  let e : (Fin d → Fin 2) ≃ (Fin d → Fin 2) :=
    Equiv.ofBijective (flipCoord b) (flipCoord_involutive b).bijective
  calc
    parityMarginalMass d (-1) A y =
        ∑ x : Fin d → Fin 2,
          if (∀ i ∈ A, e x i = y i) then parityLaw d (-1) (e x) else 0 := by
            exact (e.sum_comp fun x =>
              if (∀ i ∈ A, x i = y i) then parityLaw d (-1) x else 0).symm
    _ = parityMarginalMass d 1 A y := by
      apply Finset.sum_congr rfl
      intro x hx
      change (if (∀ i ∈ A, flipCoord b x i = y i) then
          parityLaw d (-1) (flipCoord b x) else 0) = _
      by_cases h : ∀ i ∈ A, x i = y i
      · have hf : ∀ i ∈ A, flipCoord b x i = y i :=
          (flipCoord_agrees_iff hb x y).2 h
        rw [if_pos hf, if_pos h, parityLaw_flip_neg_eq_pos]
      · have hf : ¬∀ i ∈ A, flipCoord b x i = y i := by
          intro hf
          exact h ((flipCoord_agrees_iff hb x y).1 hf)
        simp [h, hf]

private lemma properMoment_expectation_zero_of_sum {d : ℕ} (ε : ℤ)
    (A : Finset (Fin d))
    (hsum : (∑ x ∈ parityFiber d ε, ∏ i ∈ A, paritySign (x i)) = 0) :
    (∑ x, parityLaw d ε x * ((∏ i ∈ A, paritySign (x i)) : ℚ)) = 0 := by
  rw [parityLaw_expectation_eq]
  have hsumQ : (∑ x ∈ parityFiber d ε,
      ((∏ i ∈ A, paritySign (x i)) : ℚ)) = 0 := by
    exact_mod_cast hsum
  rw [hsumQ]
  ring

private lemma parityLaw_total_mass_of_card {d : ℕ} (ε : ℤ)
    (hcard : (parityFiber d ε).card = 2 ^ (d - 1)) :
    (∑ x, parityLaw d ε x) = 1 := by
  have hexpect := parityLaw_expectation_eq (d := d) ε
    (fun _ : Fin d → Fin 2 => (1 : ℚ))
  simp only [mul_one] at hexpect
  rw [hexpect]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]
  rw [Nat.cast_pow]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

private lemma fullMoment_expectation_of_sum {d : ℕ} (ε : ℤ)
    (hcard : (parityFiber d ε).card = 2 ^ (d - 1))
    (hsum : (∑ x ∈ parityFiber d ε, ∏ i : Fin d, paritySign (x i)) =
      ε * ((parityFiber d ε).card : ℤ)) :
    (∑ x, parityLaw d ε x * ((∏ i : Fin d, paritySign (x i)) : ℚ)) = ε := by
  rw [parityLaw_expectation_eq]
  have hsumQ : (∑ x ∈ parityFiber d ε,
      ((∏ i : Fin d, paritySign (x i)) : ℚ)) =
        (ε : ℚ) * (parityFiber d ε).card := by
    exact_mod_cast hsum
  rw [hsumQ, hcard]
  have hpow : ((2 : ℚ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  norm_cast
  ring

/-- The two uniform parity laws are probability laws with identical proper
marginals and moments, while their full-product expectations are opposite. -/
theorem parity_conditioned_probability_form (k : ℕ) :
    ((∑ x, parityLaw (k + 1) (-1) x) = 1 ∧
      (∑ x, parityLaw (k + 1) 1 x) = 1) ∧
    (∀ A : Finset (Fin (k + 1)), A.Nonempty → A ≠ Finset.univ →
      (∑ x, parityLaw (k + 1) (-1) x * ((∏ i ∈ A, paritySign (x i)) : ℚ)) = 0 ∧
      (∑ x, parityLaw (k + 1) 1 x * ((∏ i ∈ A, paritySign (x i)) : ℚ)) = 0) ∧
    (∑ x, parityLaw (k + 1) (-1) x *
      ((∏ i : Fin (k + 1), paritySign (x i)) : ℚ)) = -1 ∧
    (∑ x, parityLaw (k + 1) 1 x *
      ((∏ i : Fin (k + 1), paritySign (x i)) : ℚ)) = 1 ∧
    (∀ A : Finset (Fin (k + 1)), A ≠ Finset.univ → ∀ y : Fin (k + 1) → Fin 2,
      parityMarginalMass (k + 1) (-1) A y = parityMarginalMass (k + 1) 1 A y) := by
  have hneg := parity_conditioned_moments k (-1) (Or.inl rfl)
  have hpos := parity_conditioned_moments k 1 (Or.inr rfl)
  have hnegCard : (parityFiber (k + 1) (-1)).card = 2 ^ ((k + 1) - 1) := by
    simpa only [Nat.succ_sub_one] using hneg.1
  have hposCard : (parityFiber (k + 1) 1).card = 2 ^ ((k + 1) - 1) := by
    simpa only [Nat.succ_sub_one] using hpos.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨parityLaw_total_mass_of_card (-1) hnegCard,
      parityLaw_total_mass_of_card 1 hposCard⟩
  · intro A hA hAproper
    exact ⟨properMoment_expectation_zero_of_sum (-1) A (hneg.2.1 A hA hAproper),
      properMoment_expectation_zero_of_sum 1 A (hpos.2.1 A hA hAproper)⟩
  · exact fullMoment_expectation_of_sum (-1) hnegCard hneg.2.2
  · exact fullMoment_expectation_of_sum 1 hposCard hpos.2.2
  · exact parityMarginalMass_neg_eq_pos

/-- Fidelity witness: both allowed parity hypotheses are satisfiable. -/
example : ((-1 : ℤ) = -1 ∨ (-1 : ℤ) = 1) ∧ ((1 : ℤ) = -1 ∨ (1 : ℤ) = 1) :=
  ⟨Or.inl rfl, Or.inr rfl⟩

/-- Fidelity witness: every positive-dimensional binary cube is inhabited. -/
example (k : ℕ) : Fin (k + 1) → Fin 2 := fun _ => 0

#print axioms parity_conditioned_moments
#print axioms parity_conditioned_probability_form

end D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
