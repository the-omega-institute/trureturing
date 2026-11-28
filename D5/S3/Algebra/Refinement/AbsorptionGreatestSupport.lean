/- GID: D5/S3/Algebra/Refinement/AbsorptionGreatestSupport
   generality: G
   mirror-B: none(waiver:covered-by-absorption-greatest-support-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero absorbed summands characterize greatest supports in every finite additive-observation fiber. -/

module

public import D5.S3.Algebra.Refinement.FiniteTransport
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Finset.Order
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Tactic.FinCases

/-!
Omega original.

Nonzero absorbed summands characterize greatest supports in every finite
additive-observation fiber. All operations are those of the original monoids.
-/

@[expose] public section

namespace Omega.Refinement.Absorption

universe u v w

variable {K : Type u} [AddCommMonoid K]

/-- Absorbed nonzero summands join feasible supports without changing any
additive observation. The coordinate carrier need not be finite. -/
theorem fiber_support_union (hc : Conical K)
    (ha : ∀ x : K, x ≠ 0 → ∃ e : K, e ≠ 0 ∧ x + e = x)
    {I : Type v} {T : Type w} [AddMonoid T]
    (F : (I → K) →+ T) (p q : I → K) (hpq : F p = F q) :
    ∃ r : I → K, F r = F p ∧
      Function.support r = Function.support p ∪ Function.support q := by
  classical
  have he : ∀ x : K, ∃ e : K, (e = 0 ↔ x = 0) ∧ x + e = x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx], by simp⟩
    · obtain ⟨e, he, hxe⟩ := ha x hx
      exact ⟨e, by simp [he, hx], hxe⟩
  choose e he0 headd using fun i => he (q i)
  have hqe : q + e = q := funext headd
  refine ⟨p + e, ?_, ?_⟩
  · calc
      F (p + e) = F p + F e := F.map_add _ _
      _ = F q + F e := by rw [hpq]
      _ = F (q + e) := (F.map_add _ _).symm
      _ = F p := by rw [hqe, hpq]
  · ext i
    change p i + e i ≠ 0 ↔ p i ≠ 0 ∨ q i ≠ 0
    constructor
    · intro h
      by_contra hn
      push Not at hn
      exact h (by rw [hn.1, (he0 i).mpr hn.2, zero_add])
    · rintro (h | h) hz
      · exact h (hc _ _ hz).1
      · exact h ((he0 i).mp (hc _ _ hz).2)

/-- Exact characterization using all finite powers and all additive targets
in the coefficient universe, including empty powers and the trivial monoid. -/
theorem absorption_iff_universal_greatest_support (hc : Conical K) :
    (∀ x : K, x ≠ 0 → ∃ e : K, e ≠ 0 ∧ x + e = x) ↔
      (∀ (n : ℕ) (T : Type u) [AddMonoid T]
        (F : (Fin n → K) →+ T) (p : Fin n → K),
        ∃ r : Fin n → K, F r = F p ∧
          ∀ q : Fin n → K, F q = F p → ∀ i : Fin n, q i ≠ 0 → r i ≠ 0) := by
  classical
  constructor
  · intro ha n T _ F p
    let V := {q : Fin n → K // F q = F p}
    let base : V := ⟨p, rfl⟩
    let : Nonempty V := ⟨base⟩
    let s : V → Set (Fin n) := fun q => Function.support q.val
    have hd : Directed (· ⊆ ·) s := by
      intro a b
      obtain ⟨r, hrF, hrs⟩ := fiber_support_union hc ha F a.val b.val
        (a.property.trans b.property.symm)
      refine ⟨⟨r, hrF.trans a.property⟩, ?_, ?_⟩
      · intro i hi
        change i ∈ Function.support r
        rw [hrs]
        exact Or.inl hi
      · intro i hi
        change i ∈ Function.support r
        rw [hrs]
        exact Or.inr hi
    let c : Fin n → V := fun i =>
      if h : ∃ q : V, q.val i ≠ 0 then Classical.choose h else base
    obtain ⟨r, hr⟩ := hd.finset_le (Finset.univ.image c)
    refine ⟨r.val, r.property, ?_⟩
    intro q hq i hi
    have hex : ∃ q : V, q.val i ≠ 0 := ⟨⟨q, hq⟩, hi⟩
    have hci : (c i).val i ≠ 0 := by
      dsimp [c]
      rw [dite_eq_left hex]
      exact Classical.choose_spec hex
    exact hr (c i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hci
  · intro hh x hx
    by_contra hn
    have hrigid : ∀ e : K, x + e = x → e = 0 := by
      intro e he
      by_contra he0
      exact hn ⟨e, he0, he⟩
    let p : Fin 2 → K := fun i => if i = 0 then x else 0
    let q : Fin 2 → K := fun i => if i = 1 then x else 0
    let S : (Fin 2 → K) → Prop := fun a => a = p ∨ a = q
    have hp (a : Fin 2 → K) : S (p + a) ↔ a = 0 := by
      constructor
      · rintro (h | h)
        · have h0 : a 0 = 0 := hrigid _ (by simpa [p] using congrFun h 0)
          have h1 : a 1 = 0 := by simpa [p] using congrFun h 1
          funext i
          fin_cases i <;> assumption
        · exact (hx (hc _ _ (by simpa [p, q] using congrFun h 0)).1).elim
      · rintro rfl
        exact Or.inl (add_zero p)
    have hq (a : Fin 2 → K) : S (q + a) ↔ a = 0 := by
      constructor
      · rintro (h | h)
        · exact (hx (hc _ _ (by simpa [p, q] using congrFun h 1)).1).elim
        · have h0 : a 0 = 0 := by simpa [q] using congrFun h 0
          have h1 : a 1 = 0 := hrigid _ (by simpa [q] using congrFun h 1)
          funext i
          fin_cases i <;> assumption
      · rintro rfl
        exact Or.inr (add_zero q)
    let C : AddCon (Fin 2 → K) := {
      r := fun a b => ∀ c, S (a + c) ↔ S (b + c)
      iseqv := ⟨fun _ _ => Iff.rfl, fun h c => (h c).symm,
        fun h h' c => (h c).trans (h' c)⟩
      add' := by
        intro a b c d hab hcd e
        have h₁ : S ((a + c) + e) ↔ S ((b + c) + e) := by
          simpa [add_assoc] using hab (c + e)
        have h₂ : S ((b + c) + e) ↔ S ((b + d) + e) := by
          simpa [add_assoc, add_comm, add_left_comm] using hcd (b + e)
        exact h₁.trans h₂ }
    have hpq : C.mk' p = C.mk' q := by
      apply Quotient.sound
      intro a
      exact (hp a).trans (hq a).symm
    obtain ⟨r, hr, hg⟩ := hh 2 C.Quotient C.mk' p
    have hrS : S r := by
      have hrel : C r p := Quotient.exact hr
      have hz := hrel 0
      have hS : S r ↔ S p := by simpa using hz
      exact hS.mpr (Or.inl rfl)
    have hr0 : r 0 ≠ 0 := hg p rfl 0 (by simpa [p] using hx)
    have hr1 : r 1 ≠ 0 := hg q hpq.symm 1 (by simpa [q] using hx)
    rcases hrS with rfl | rfl
    · exact hr1 (by simp [p])
    · exact hr0 (by simp [q])

end Omega.Refinement.Absorption
