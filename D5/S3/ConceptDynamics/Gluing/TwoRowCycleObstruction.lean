/- GID: D5/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Induced cycles support at most two Boolean rows with equal full overlaps and empty join. -/

import Mathlib.Data.Set.Image
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Boolean local relations on scopes containing an induced cycle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.TwoRowCycleObstruction

universe u v

private noncomputable def phase {V : Type v} (A : Set V) (z l x : V) : Bool :=
  @decide (z ∈ A ∧ x = l) (Classical.propDecidable _)

private theorem endpoints {V : Type v} {m : ℕ} (hm : 4 ≤ m + 1)
    (c : Fin (m + 1) → V) (A : Set V)
    (hch : ∀ i j : Fin (m + 1), i ≠ j → c i ∈ A → c j ∈ A →
      finRotate (m + 1) i = j ∨ finRotate (m + 1) j = i)
    (hz : c 0 ∈ A) (hl : c (Fin.last m) ∈ A)
    (i : Fin (m + 1)) (hi : c i ∈ A) : i = 0 ∨ i = Fin.last m := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases hlast : i = Fin.last m
  · exact Or.inr hlast
  have h01 : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have ha := hch 0 i (Ne.symm h0) hz hi
  have hb := hch (Fin.last m) i (Ne.symm hlast) hl hi
  have hr0 := coe_finRotate_of_ne_last h01
  have hri := coe_finRotate_of_ne_last hlast
  simp only [Fin.val_zero, Fin.val_last] at hr0 hri
  rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals
    have ea := congrArg Fin.val ha
    have eb := congrArg Fin.val hb
    simp only [finRotate_last, Fin.val_zero, Fin.val_last] at ea eb
    omega

private theorem overlap_charge {V : Type v} {m : ℕ}
    (c : Fin (m + 1) → V) (A B : Set V)
    (hA : c 0 ∈ A → c (Fin.last m) ∈ A →
      ∀ i, c i ∈ A → i = 0 ∨ i = Fin.last m)
    (hB : c 0 ∈ B → c (Fin.last m) ∈ B →
      ∀ i, c i ∈ B → i = 0 ∨ i = Fin.last m)
    (i j : Fin (m + 1)) (hiA : c i ∈ A) (hiB : c i ∈ B)
    (hjA : c j ∈ A) (hjB : c j ∈ B) :
    Bool.xor (phase A (c 0) (c (Fin.last m)) (c i))
        (phase B (c 0) (c (Fin.last m)) (c i)) =
      Bool.xor (phase A (c 0) (c (Fin.last m)) (c j))
        (phase B (c 0) (c (Fin.last m)) (c j)) := by
  classical
  by_cases hzA : c 0 ∈ A <;> by_cases hzB : c 0 ∈ B
  · simp [phase, hzA, hzB]
  · have heq : (c i = c (Fin.last m)) ↔ (c j = c (Fin.last m)) := by
      constructor
      · intro hi
        rcases hA hzA (hi ▸ hiA) j hjA with hj | hj
        · exact (hzB (hj ▸ hjB)).elim
        · exact congrArg c hj
      · intro hj
        rcases hA hzA (hj ▸ hjA) i hiA with hi | hi
        · exact (hzB (hi ▸ hiB)).elim
        · exact congrArg c hi
    simp [phase, hzA, hzB, heq]
  · have heq : (c i = c (Fin.last m)) ↔ (c j = c (Fin.last m)) := by
      constructor
      · intro hi
        rcases hB hzB (hi ▸ hiB) j hjB with hj | hj
        · exact (hzA (hj ▸ hjA)).elim
        · exact congrArg c hj
      · intro hj
        rcases hB hzB (hj ▸ hjB) i hiB with hi | hi
        · exact (hzA (hi ▸ hiA)).elim
        · exact congrArg c hi
    simp [phase, hzA, hzB, heq]
  · simp [phase, hzA, hzB]

private noncomputable def row {V : Type v} {m : ℕ}
    (c : Fin (m + 1) → V) (A : Set V) (b : Bool) : A → Bool := by
  classical
  exact fun x => if x.val ∈ Set.range c then
    Bool.xor b (phase A (c 0) (c (Fin.last m)) x.val) else false

private def rows {V : Type v} {m : ℕ} (c : Fin (m + 1) → V) (A : Set V) :
    Set (A → Bool) := Set.range (row c A)

private theorem rows_cycle {V : Type v} {m : ℕ}
    (c : Fin (m + 1) → V) (A : Set V) (r : A → Bool) (hr : r ∈ rows c A) :
    ∃ b : Bool, ∀ (i : Fin (m + 1)) (hi : c i ∈ A),
      r ⟨c i, hi⟩ = Bool.xor b (phase A (c 0) (c (Fin.last m)) (c i)) := by
  classical
  obtain ⟨b, rfl⟩ := hr
  exact ⟨b, fun i hi => by simp [row]⟩

private theorem extend_row {V : Type v} {m : ℕ}
    (c : Fin (m + 1) → V) (A B : Set V)
    (hA : c 0 ∈ A → c (Fin.last m) ∈ A →
      ∀ i, c i ∈ A → i = 0 ∨ i = Fin.last m)
    (hB : c 0 ∈ B → c (Fin.last m) ∈ B →
      ∀ i, c i ∈ B → i = 0 ∨ i = Fin.last m)
    (r : A → Bool) (hr : r ∈ rows c A) :
    ∃ t ∈ rows c B, ∀ (x : V) (hxA : x ∈ A) (hxB : x ∈ B),
      t ⟨x, hxB⟩ = r ⟨x, hxA⟩ := by
  classical
  obtain ⟨b, rfl⟩ := hr
  let pA := phase A (c 0) (c (Fin.last m))
  let pB := phase B (c 0) (c (Fin.last m))
  have choose_phase : ∃ d : Bool, ∀ (i : Fin (m + 1)),
      c i ∈ A → c i ∈ B → Bool.xor b (pA (c i)) = Bool.xor d (pB (c i)) := by
    by_cases h : ∃ i, c i ∈ A ∧ c i ∈ B
    · obtain ⟨j, hjA, hjB⟩ := h
      refine ⟨Bool.xor b (Bool.xor (pA (c j)) (pB (c j))), ?_⟩
      intro i hiA hiB
      have hc := overlap_charge c A B hA hB i j hiA hiB hjA hjB
      change Bool.xor (pA (c i)) (pB (c i)) =
        Bool.xor (pA (c j)) (pB (c j)) at hc
      rw [← hc]
      simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    · exact ⟨false, fun i hiA hiB => (h ⟨i, hiA, hiB⟩).elim⟩
  obtain ⟨d, hd⟩ := choose_phase
  refine ⟨row c B d, ⟨d, rfl⟩, ?_⟩
  intro x hxA hxB
  by_cases hx : x ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hx
    simpa only [row, Set.mem_range_self, ↓reduceIte, pA, pB] using
      (hd i hxA hxB).symm
  · simp only [row, hx, ↓reduceIte]

/-- An induced cycle of length at least four admits one or two Boolean rows per scope,
with equal projections onto every complete intersection and empty global join. -/
theorem two_row_cycle_obstruction (E : Type u) (V : Type v)
    (S : E → Set V) (n : ℕ) (hn : 4 ≤ n) (c : Fin n → V)
    (hc : Function.Injective c)
    (hedge : ∀ i : Fin n, ∃ e : E, c i ∈ S e ∧ c (finRotate n i) ∈ S e)
    (hchord : ∀ (e : E) (i j : Fin n), i ≠ j → c i ∈ S e → c j ∈ S e →
      finRotate n i = j ∨ finRotate n j = i) :
    ∃ R : (e : E) → Set (S e → Bool),
      (∀ e, ∃ r0 r1 : S e → Bool, R e = {r0, r1}) ∧
      (∀ e f, (fun r : S e → Bool => fun x : ↥(S e ∩ S f) =>
          r ⟨x.val, x.property.1⟩) '' R e =
        (fun r : S f → Bool => fun x : ↥(S e ∩ S f) =>
          r ⟨x.val, x.property.2⟩) '' R f) ∧
      ¬ ∃ g : V → Bool, ∀ e, (fun x : S e => g x.val) ∈ R e := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    have geom (e : E) := endpoints hn c (S e) (hchord e)
    refine ⟨fun e => rows c (S e), ?_, ?_, ?_⟩
    · intro e
      refine ⟨row c (S e) false, row c (S e) true, ?_⟩
      ext r
      constructor
      · rintro ⟨b, rfl⟩
        cases b <;> simp
      · intro hr
        rcases Set.mem_insert_iff.mp hr with hr | hr
        · exact ⟨false, hr.symm⟩
        · exact ⟨true, (Set.mem_singleton_iff.mp hr).symm⟩
    · intro e f
      apply Set.Subset.antisymm
      · rintro _ ⟨r, hr, rfl⟩
        obtain ⟨t, ht, heq⟩ := extend_row c (S e) (S f) (geom e) (geom f) r hr
        refine ⟨t, ht, ?_⟩
        funext x
        exact heq x.val x.property.1 x.property.2
      · rintro _ ⟨r, hr, rfl⟩
        obtain ⟨t, ht, heq⟩ := extend_row c (S f) (S e) (geom f) (geom e) r hr
        refine ⟨t, ht, ?_⟩
        funext x
        exact heq x.val x.property.2 x.property.1
    · rintro ⟨g, hg⟩
      have hzlast : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_last] at this
        omega
      have step (i : Fin (m + 1)) (hi : i ≠ Fin.last m) :
          g (c i) = g (c (finRotate (m + 1) i)) := by
        obtain ⟨e, hei, her⟩ := hedge i
        obtain ⟨b, hb⟩ := rows_cycle c (S e) _ (hg e)
        have hb0 := hb i hei
        have hb1 := hb (finRotate (m + 1) i) her
        have h0 : c i ≠ c (Fin.last m) := fun h => hi (hc h)
        by_cases hz : c 0 ∈ S e
        · have hr : c (finRotate (m + 1) i) ≠ c (Fin.last m) := by
            intro h
            have hri := hc h
            have hlast := hri ▸ her
            rcases geom e hz hlast i hei with hi0 | hil
            · subst i
              have hval := congrArg Fin.val hri
              have hrot := coe_finRotate_of_ne_last hzlast
              simp only [Fin.val_zero, Fin.val_last] at hval hrot
              omega
            · exact hi hil
          simp only [phase, h0, hr, and_false, decide_false, Bool.xor_false] at hb0 hb1
          exact hb0.trans hb1.symm
        · simp only [phase, hz, false_and, decide_false, Bool.xor_false] at hb0 hb1
          exact hb0.trans hb1.symm
      have all_eq (i : Fin (m + 1)) : g (c i) = g (c 0) := by
        induction i using Fin.induction with
        | zero => rfl
        | succ i ih =>
          have hne : i.castSucc ≠ Fin.last m := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          have hrot : finRotate (m + 1) i.castSucc = i.succ := by
            simpa using finRotate_of_lt i.isLt
          exact (hrot ▸ step i.castSucc hne).symm.trans ih
      obtain ⟨e, hel, he0⟩ := hedge (Fin.last m)
      rw [finRotate_last] at he0
      obtain ⟨b, hb⟩ := rows_cycle c (S e) _ (hg e)
      have hb0 := hb 0 he0
      have hbl := hb (Fin.last m) hel
      have hcl : c 0 ≠ c (Fin.last m) := fun h => hzlast (hc h)
      have heq := all_eq (Fin.last m)
      simp only [phase, he0, hcl, and_false, decide_false, Bool.xor_false] at hb0
      simp [phase, he0] at hbl
      rw [hb0, hbl] at heq
      cases b <;> contradiction

end D5.S3.ConceptDynamics.Gluing.TwoRowCycleObstruction

#print axioms D5.S3.ConceptDynamics.Gluing.TwoRowCycleObstruction.two_row_cycle_obstruction
