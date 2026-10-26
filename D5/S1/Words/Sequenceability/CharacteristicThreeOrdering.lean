/- GID: D5/S1/Words/Sequenceability/CharacteristicThreeOrdering
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/CharacteristicThreeOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Transported field cycles give opposite-hole words with nonzero proper intervals. -/

import D5.S1.Words.Sequenceability.CharacteristicThreeCycle

/-! Coefficient-one words obtained from the actual finite-field cycle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicThreeOrdering

open Function Finset
open D5.S1.Words.Sequenceability.CharacteristicThreeCycle

variable {K A : Type*} [Field K] [Fintype K] [CharP K 3] [AddCommGroup A]

omit [Fintype K] [CharP K 3] in
private theorem vertex_injective : Injective (vertex (K := K)) := by
  rintro ⟨b, t⟩ ⟨c, u⟩ h
  have hh : ((b : K), t) = ((c : K), u) := h
  exact Prod.ext (Units.ext (congrArg Prod.fst hh)) (congrArg (fun z : K × ZMod 3 => z.2) hh)

omit [Fintype K] [CharP K 3] in
private theorem excluded_iff (φ : K × ZMod 3 ≃+ A) {x : A}
    (hx : φ (0, 1) = x) (z : K × ZMod 3) :
    (φ z ≠ 0 ∧ φ z ≠ x ∧ φ z ≠ -x) ↔ z.1 ≠ 0 := by
  rcases z with ⟨b, t⟩
  constructor
  · rintro ⟨hzero, hplus, hminus⟩ rfl
    fin_cases t
    · exact hzero (map_zero φ)
    · exact hplus hx
    · apply hminus
      rw [← hx, ← map_neg]
      congr 1
      apply Prod.ext
      · simp
      · change (2 : ZMod 3) = -1
        decide
  · intro hb
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have := congrArg Prod.fst (φ.injective (h.trans (map_zero φ).symm))
      exact hb this
    · intro h
      have := congrArg Prod.fst (φ.injective (h.trans hx.symm))
      exact hb this
    · intro h
      have he : φ (b, t) = φ (-(0, 1)) := by
        rw [map_neg, hx]
        exact h
      have := congrArg Prod.fst (φ.injective he)
      exact hb (by simpa using this)

/-- An additive coordinate equivalence fixing the missing direction transports the full word. -/
theorem exists_transported_ordering (φ : K × ZMod 3 ≃+ A) (x : A)
    (hx : φ (0, 1) = x) :
    let M := 3 * (Fintype.card K - 1)
    ∃ w : ℕ → A,
      Injective (fun i : Fin M => w i.val) ∧
      Set.range (fun i : Fin M => w i.val) = {y | y ≠ 0 ∧ y ≠ x ∧ y ≠ -x} ∧
      Injective (fun k : Fin M => ∑ i ∈ range k.val, w i) ∧
      (∑ i ∈ range M, w i) = 0 ∧
      (∀ a b : ℕ, a < b → b ≤ M → (a ≠ 0 ∨ b ≠ M) →
        (∑ i ∈ Ico a b, w i) ≠ 0) := by
  classical
  obtain ⟨a, ha, hord, hL, heven, e, he, hreturn, hlabel, hdiff⟩ :=
    exists_cycle_inventory (K := K)
  let M := 3 * (Fintype.card K - 1)
  let v : ℕ → A := fun n => φ (vertex ((step a)^[n] (1, 0)))
  let w : ℕ → A := fun n => v (n + 1) - v n
  have hw (i : Fin M) : w i.val = φ (vertex (label a ha (e i))) := by
    dsimp only [w, v]
    rw [iterate_succ_apply', ← he i, ← map_sub, hdiff]
  have hv0 : v M = v 0 := by dsimp only [v, M]; rw [hreturn]; rfl
  have hvinj : Injective (fun i : Fin M => v i.val) := by
    intro i j h
    apply e.injective
    apply vertex_injective
    apply φ.injective
    simpa only [he] using h
  have hwinj : Injective (fun i : Fin M => w i.val) := by
    intro i j h
    simp_rw [hw] at h
    exact hlabel.injective (vertex_injective (φ.injective h))
  have hsum (n : ℕ) : (∑ i ∈ range n, w i) = v n - v 0 := by
    exact sum_range_sub v n
  refine ⟨w, hwinj, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨i, rfl⟩
      change w i.val ≠ 0 ∧ w i.val ≠ x ∧ w i.val ≠ -x
      rw [hw]
      apply (excluded_iff φ hx _).mpr
      exact Units.ne_zero _
    · intro hy
      let z := φ.symm y
      have hz : z.1 ≠ 0 := (excluded_iff φ hx z).mp (by simpa [z] using hy)
      obtain ⟨i, hi⟩ := hlabel.surjective (Units.mk0 z.1 hz, z.2)
      refine ⟨i, ?_⟩
      change w i.val = y
      change label a ha (e i) = (Units.mk0 z.1 hz, z.2) at hi
      rw [hw, hi]
      change φ z = y
      exact φ.apply_symm_apply y
  · intro i j h
    apply hvinj
    simpa only [hsum, sub_left_inj] using h
  · rw [hsum, hv0, sub_self]
  · intro c d hcd hd hproper hzero
    have hsumI : (∑ i ∈ Ico c d, w i) = v d - v c := by
      rw [sum_Ico_eq_sub _ hcd.le, hsum, hsum]
      abel
    have heq : v d = v c := sub_eq_zero.mp (hsumI.symm.trans hzero)
    by_cases hdM : d = M
    · subst d
      have hc : c < M := hcd
      have hc0 : c ≠ 0 := by simpa [M] using hproper
      have hi : (⟨c, hc⟩ : Fin M) = ⟨0, by omega⟩ :=
        hvinj (by simpa only [hv0] using heq.symm)
      exact hc0 (congrArg Fin.val hi)
    · have hd' : d < M := by omega
      have hi : (⟨d, hd'⟩ : Fin M) = ⟨c, by omega⟩ := hvinj heq
      have hh : d = c := congrArg Fin.val hi
      omega

#print axioms exists_transported_ordering

end D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
