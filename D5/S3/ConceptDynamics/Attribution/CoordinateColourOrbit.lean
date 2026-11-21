/- GID: D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/CoordinateColourOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fourfold divisibility of invariant colour-pair counts. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling

/-! Count the colour pairs supported on each orbit of two Boolean profiles. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit

open D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling

variable {I : Type*} [Fintype I]

open Classical in
private theorem eval_single (p : I → Bool) (i : I) (a : ZMod 2) :
    shift p (Pi.single i a) = if p i then 0 else a := by
  unfold shift
  rw [sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · exact fun h => (h (mem_univ i)).elim

private theorem lift_on_pivot (p q : I → Bool) (i j : I) (hi : p i = false)
    (hq : q i = true) (hj : q j = false) (a b : ZMod 2) :
    ∃ v : I → ZMod 2, shift p v = a ∧ shift q v = b := by
  classical
  let extra := if p j then (0 : ZMod 2) else b
  refine ⟨Pi.single i (a - extra) + Pi.single j b, ?_, ?_⟩
  · rw [shift_add, eval_single, eval_single, hi]
    change a - extra + extra = a
    exact sub_add_cancel a extra
  · simp only [shift_add, eval_single, hq, hj, Bool.false_eq_true, ite_false, ite_true, zero_add]

private theorem shifts_surjective (p q : I → Bool) (different : p ≠ q)
    (someFalseP : ∃ j, p j = false) (someFalseQ : ∃ j, q j = false) :
    Function.Surjective (fun v : I → ZMod 2 => (shift p v, shift q v)) := by
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := by
    by_contra! all
    exact different (funext all)
  rintro ⟨a, b⟩
  obtain ⟨j, jp⟩ := someFalseP
  obtain ⟨k, kq⟩ := someFalseQ
  cases hp : p i <;> cases hq : q i
  · exact (hi (hp.trans hq.symm)).elim
  · obtain ⟨v, ha, hb⟩ := lift_on_pivot p q i k hp hq kq a b
    exact ⟨v, Prod.ext ha hb⟩
  · obtain ⟨v, hb, ha⟩ := lift_on_pivot q p i j hq hp jp b a
    exact ⟨v, Prod.ext ha hb⟩
  · exact (hi (hp.trans hq.symm)).elim

private theorem four_dvd_colour_count (m : Output I → Output I → ℕ)
    (inv : ∀ (g : Acting I) x y, m (g • x) (g • y) = m x y)
    (p q : I → Bool) (different : p ≠ q)
    (someFalseP : ∃ j, p j = false) (someFalseQ : ∃ j, q j = false) :
    4 ∣ ∑ c : ZMod 2, ∑ d : ZMod 2, m ⟨p, c⟩ ⟨q, d⟩ := by
  have constant (c d : ZMod 2) : m ⟨p, c⟩ ⟨q, d⟩ = m ⟨p, 0⟩ ⟨q, 0⟩ := by
    obtain ⟨v, hv⟩ := shifts_surjective p q different someFalseP someFalseQ (c, d)
    have ha := congrArg Prod.fst hv
    have hb := congrArg Prod.snd hv
    change shift p v = c at ha
    change shift q v = d at hb
    have same := inv (Multiplicative.ofAdd v) ⟨p, 0⟩ ⟨q, 0⟩
    change m ⟨p, shift p v + 0⟩ ⟨q, shift q v + 0⟩ = m ⟨p, 0⟩ ⟨q, 0⟩ at same
    simpa only [add_zero, ha, hb] using same
  simp_rw [constant, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  exact ⟨m ⟨p, 0⟩ ⟨q, 0⟩, by omega⟩


open Classical in
private noncomputable def selectedPair (p q : I → Bool) (r : ZMod 2 → ZMod 2 → Prop)
    (x y : Output I) : ℕ :=
  if x.profile = p ∧ y.profile = q ∧ r x.colour y.colour then 1 else 0

private theorem selectedPair_invariant (p q : I → Bool) (r : ZMod 2 → ZMod 2 → Prop)
    (stable : ∀ v c d, r (shift p v + c) (shift q v + d) ↔ r c d) :
    ∀ (g : Acting I) x y, selectedPair p q r (g • x) (g • y) = selectedPair p q r x y := by
  classical
  intro g x y
  unfold selectedPair
  apply if_congr ?_ rfl rfl
  change (x.profile = p ∧ y.profile = q ∧
      r (shift x.profile g.toAdd + x.colour) (shift y.profile g.toAdd + y.colour)) ↔
      x.profile = p ∧ y.profile = q ∧ r x.colour y.colour
  by_cases hx : x.profile = p
  · by_cases hy : y.profile = q
    · simp only [hx, hy, true_and, stable]
    · simp [hy]
  · simp [hx]

private theorem all_true_shift (p : I → Bool) (h : ∀ i, p i = true) (v : I → ZMod 2) :
    shift p v = 0 := by
  simp [shift, h]

attribute [local instance 10000] Classical.propDecidable

theorem universally_four_dvd_iff (p q : I → Bool) :
    (∀ m : Output I → Output I → ℕ,
      (∀ (g : Acting I) x y, m (g • x) (g • y) = m x y) →
      4 ∣ ∑ c : ZMod 2, ∑ d : ZMod 2, m ⟨p, c⟩ ⟨q, d⟩) ↔
      p ≠ q ∧ (∃ j, p j = false) ∧ (∃ j, q j = false) := by
  constructor
  · intro h
    have contradiction' (r : ZMod 2 → ZMod 2 → Prop)
        (stable : ∀ v c d, r (shift p v + c) (shift q v + d) ↔ r c d)
        (count : (∑ c : ZMod 2, ∑ d : ZMod 2, if r c d then (1 : ℕ) else 0) = 2) : False := by
      have div := h (selectedPair p q r) (selectedPair_invariant p q r stable)
      have reduce (c d : ZMod 2) :
          selectedPair p q r ⟨p, c⟩ ⟨q, d⟩ = if r c d then 1 else 0 := by
        simp [selectedPair]
      simp_rw [reduce] at div
      rw [count] at div
      exact Nat.not_succ_le_self 2
        (Nat.le_trans (Nat.le_succ 3) (Nat.le_of_dvd (Nat.zero_lt_succ 1) div))
    have countOne (a : ZMod 2) :
        (∑ d : ZMod 2, if a = d then (1 : ℕ) else 0) = 1 := by
      rw [sum_eq_single a]
      · simp
      · intro d _ ne
        simp [Ne.symm ne]
      · simp
    refine ⟨?_, ?_, ?_⟩
    · intro equal
      apply contradiction' (fun c d => c = d)
      · intro v c d
        rw [equal, add_right_inj]
      · calc
          _ = ∑ _ : ZMod 2, (1 : ℕ) := sum_congr rfl fun c _ => countOne c
          _ = _ := by simp [ZMod.card]
    · by_contra! none
      have alwaysTrue (i : I) : p i = true := by
        cases hpi : p i
        · exact (none i hpi).elim
        · rfl
      apply contradiction' (fun c _ => c = 0)
      · intro v c d
        rw [all_true_shift p alwaysTrue, zero_add]
      · simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        simp [mul_comm]
    · by_contra! none
      have alwaysTrue (i : I) : q i = true := by
        cases hqi : q i
        · exact (none i hqi).elim
        · rfl
      apply contradiction' (fun _ d => d = 0)
      · intro v c d
        rw [all_true_shift q alwaysTrue, zero_add]
      · have zeroCount : (∑ d : ZMod 2, if d = 0 then (1 : ℕ) else 0) = 1 := by
          calc
            _ = ∑ d : ZMod 2, if 0 = d then (1 : ℕ) else 0 := by
              apply sum_congr rfl
              intro d _
              by_cases dz : d = 0
              · simp [dz]
              · simp [dz, Ne.symm dz]
            _ = _ := countOne 0
        change (∑ _ : ZMod 2, ∑ d : ZMod 2, if d = 0 then (1 : ℕ) else 0) = 2
        rw [zeroCount]
        simp [ZMod.card]
  · rintro ⟨different, someFalseP, someFalseQ⟩ m inv
    exact four_dvd_colour_count m inv p q different someFalseP someFalseQ

end D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
