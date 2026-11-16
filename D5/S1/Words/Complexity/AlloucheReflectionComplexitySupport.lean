/- GID: D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/AlloucheReflectionComplexitySupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked mirrors transfer bounded factor increments to reflection increments. -/

/-
admission_basis: escape-witness
fiberSurplus: proof_shape: bind-only; escape_witness: none;
  consumers: Conjecture28.Graph.fiberWeight_sum and FixedForestSlotGraph.fiber_surplus.
mirrorFactorLinear: proof_shape: content; escape_witness: mirror_factor_decomposition.
reflectionBoundOfMirrorBound: proof_shape: content;
  escape_witness: mirror_factor_decomposition and walk_loop_removal_count.
Direct frozen dependencies: D5/S1/Words/Complexity/MorseHedlund.wordFactor
  statement_id=sha256:ac48653820670fcfa251876138fb18e7748093ca0d6fa2b0830e368730a3d908;
  D5/S1/Words/Complexity/MorseHedlund.wordFactorSet
  statement_id=sha256:bdef94a82837126cfe47f0537675bf25b70c1f37d1e0d6b98c990bef5aa4e08f;
  D5/S1/Words/Complexity/MorseHedlund.mem_wordFactorSet
  statement_id=sha256:18b041274f0eacdf0d0af311c4d451ed4008722c6716babae2498a94451dd019.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/29928
The reflection relation and quotient count use the source expressions without reversal closure.
-/

import D5.S1.Words.Complexity.MorseHedlund

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport

open D5.S1.Words.Complexity

/-- Fiber surplus counts histories beyond their first occurrence, not visits. -/
theorem fiberSurplus {X Y : Type*} [DecidableEq Y]
    (a : Finset X) (f : X → Y) :
    (∑ y ∈ a.image f, ((a.filter (fun x => f x = y)).card - 1)) =
      a.card - (a.image f).card := by
  classical
  rw [Finset.sum_tsub_distrib]
  · rw [← Finset.card_eq_sum_card_image f a]
    simp
  · intro y hy
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hy
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, he⟩⟩

/-- Definition 1 restricted to words of the same length: v = u or v = u^R.
The source uses positions 1,...,n; Fin.rev implements the same reversal at positions 0,...,n-1. -/
def ReflectivelyEquivalent {A : Type*} {n : ℕ} (u v : Fin n → A) : Prop :=
  v = u ∨ v = u ∘ Fin.rev

/-- Definition 3: the number of equivalence classes of occurring length-n factors.
Quot restricts the reflection relation to the source's actual factor set; it does not require
that the language contain the reverse of every factor. -/
noncomputable def reflectionComplexity {A : Type*} [Fintype A] (x : ℕ → A) (n : ℕ) : ℕ :=
  Nat.card (Quot (fun u v : ↥(wordFactorSet x n) => ReflectivelyEquivalent u.val v.val))

end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
section Mirror
open D5.S1.Words.Complexity
variable {A : Type*} [Fintype A]
attribute [local instance] Classical.propDecidable

private def reverseWord {n : ℕ} (w : Fin n → A) : Fin n → A := w ∘ Fin.rev
private noncomputable def symFactors (x : ℕ → A) (n : ℕ) : Finset (Fin n → A) := by
  classical
  exact wordFactorSet x n ∪ (wordFactorSet x n).image reverseWord

def mirrorWord (x : ℕ → A) (i : ℤ) : Option A :=
  if i = 0 then none else some (x (i.natAbs - 1))

def intFactor (z : ℤ → Option A) (n : ℕ) (i : ℤ) : Fin n → Option A :=
  fun k => z (i + k.val)

noncomputable def intFactorSet (z : ℤ → Option A) (n : ℕ) : Finset (Fin n → Option A) := by
  classical
  exact Finset.univ.filter fun w => ∃ i, w = intFactor z n i

private def liftWord {n : ℕ} (w : Fin n → A) : Fin n → Option A := Option.some ∘ w

private def markedFactor (x : ℕ → A) (n : ℕ) (j : Fin n) : Fin n → Option A :=
  intFactor (mirrorWord x) n (-(j.val : ℤ))

omit [Fintype A] in
private theorem mirror_none_iff (x : ℕ → A) (i : ℤ) :
    mirrorWord x i = none ↔ i = 0 := by
  simp [mirrorWord]

omit [Fintype A] in
private theorem mirror_pos (x : ℕ → A) (i : ℕ) :
    mirrorWord x ((i : ℤ) + 1) = some (x i) := by
  exact Option.mem_def.mp rfl

omit [Fintype A] in
private theorem mirror_neg (x : ℕ → A) (i : ℕ) :
    mirrorWord x (-((i : ℤ) + 1)) = some (x i) := by
  exact mirror_pos x i

private theorem mem_intFactorSet {z : ℤ → Option A} {n : ℕ} {w : Fin n → Option A} :
    w ∈ intFactorSet z n ↔ ∃ i, w = intFactor z n i := by
  classical
  simp [intFactorSet]

omit [Fintype A] in
private theorem marked_none_iff (x : ℕ → A) (n : ℕ) (j k : Fin n) :
    markedFactor x n j k = none ↔ k = j := by
  rw [markedFactor, intFactor, mirror_none_iff]
  constructor
  · intro h; apply Fin.ext; omega
  · intro h; subst k; omega

omit [Fintype A] in
private theorem marked_injective (x : ℕ → A) (n : ℕ) :
    Function.Injective (markedFactor x n) := by
  intro j k h
  have hj : markedFactor x n j j = none := (marked_none_iff x n j j).mpr rfl
  rw [h] at hj
  exact (marked_none_iff x n k j).mp hj

omit [Fintype A] in
private theorem lift_injective (n : ℕ) :
    Function.Injective (@liftWord A n) := by
  exact (Option.some_injective A).comp_left

omit [Fintype A] in
private theorem intFactor_pos (x : ℕ → A) (n i : ℕ) :
    intFactor (mirrorWord x) n ((i : ℤ) + 1) = liftWord (wordFactor x n i) := by
  funext k
  simp only [intFactor, liftWord, Function.comp_apply, wordFactor]
  rw [show (i : ℤ) + 1 + (k.val : ℤ) = ((i + k.val : ℕ) : ℤ) + 1 by push_cast; omega]
  exact mirror_pos x (i + k.val)


omit [Fintype A] in
private theorem intFactor_neg (x : ℕ → A) (n i : ℕ) :
    intFactor (mirrorWord x) n (-((i + n : ℕ) : ℤ)) =
      liftWord (reverseWord (wordFactor x n i)) := by
  funext k
  simp only [intFactor, liftWord, reverseWord, Function.comp_apply, wordFactor]
  have hk := k.isLt
  have hr : (k.rev.val : ℤ) = (n : ℤ) - 1 - k.val := by
    simp only [Fin.val_rev]
    omega
  rw [show -((i + n : ℕ) : ℤ) + k.val = -(((i + k.rev.val : ℕ) : ℤ) + 1) by
    push_cast
    omega]
  exact mirror_neg x (i + k.rev.val)

private theorem mirror_factor_decomposition (x : ℕ → A) (n : ℕ) :
    intFactorSet (mirrorWord x) n =
      (symFactors x n).image liftWord ∪ Finset.univ.image (markedFactor x n) := by
  classical
  ext w
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hw
    obtain ⟨i, rfl⟩ := mem_intFactorSet.mp hw
    by_cases hipos : 0 < i
    · let a : ℕ := i.toNat - 1
      have hi : i = (a : ℤ) + 1 := by dsimp [a]; omega
      left
      refine ⟨wordFactor x n a, ?_, ?_⟩
      · apply Finset.mem_union_left
        exact mem_wordFactorSet.mpr ⟨a, rfl⟩
      · rw [hi, intFactor_pos]
    · by_cases hileft : i + n ≤ 0
      · let a : ℕ := (-i).toNat - n
        have hi : i = -((a + n : ℕ) : ℤ) := by dsimp [a]; omega
        left
        refine ⟨reverseWord (wordFactor x n a), ?_, ?_⟩
        · apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨wordFactor x n a, mem_wordFactorSet.mpr ⟨a, rfl⟩, rfl⟩
        · rw [hi, intFactor_neg]
      · right
        let j : Fin n := ⟨(-i).toNat, by omega⟩
        refine ⟨j, ?_⟩
        have hi : -(j.val : ℤ) = i := by dsimp [j]; omega
        simp only [markedFactor, hi]
  · rintro (⟨u, hu, rfl⟩ | ⟨j, rfl⟩)
    · change u ∈ wordFactorSet x n ∪ (wordFactorSet x n).image reverseWord at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hu
        exact mem_intFactorSet.mpr ⟨(i : ℤ) + 1, (intFactor_pos x n i).symm⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hv
        exact mem_intFactorSet.mpr ⟨-((i + n : ℕ) : ℤ), (intFactor_neg x n i).symm⟩
    · exact mem_intFactorSet.mpr ⟨-(j.val : ℤ), rfl⟩

private theorem mirror_components_disjoint (x : ℕ → A) (n : ℕ) :
    Disjoint ((symFactors x n).image liftWord) (Finset.univ.image (markedFactor x n)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
  have hn := (marked_none_iff x n j j).mpr rfl
  rw [heq] at hn
  simp only [liftWord, Function.comp_apply, Option.some_ne_none] at hn

/-- The exact marked-mirror count, including the empty factor. -/
private theorem mirror_factor_card (x : ℕ → A) (n : ℕ) :
    (intFactorSet (mirrorWord x) n).card = (symFactors x n).card + n := by
  classical
  rw [mirror_factor_decomposition, Finset.card_union_of_disjoint (mirror_components_disjoint x n),
    Finset.card_image_of_injective _ (lift_injective n),
    Finset.card_image_of_injective _ (marked_injective x n), Finset.card_univ,
    Fintype.card_fin]

private theorem sym_factor_card_le (x : ℕ → A) (n : ℕ) :
    (symFactors x n).card ≤ 2 * (wordFactorSet x n).card := by
  classical
  calc
    (symFactors x n).card ≤ (wordFactorSet x n).card + ((wordFactorSet x n).image reverseWord).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * (wordFactorSet x n).card := by
      have h := Finset.card_image_le (s := wordFactorSet x n) (f := reverseWord)
      omega

/-- The construction preserves linear complexity. -/
theorem mirrorFactorLinear (x : ℕ → A) (C : ℕ)
    (hC : ∀ n, (wordFactorSet x n).card ≤ C * (n + 1)) (n : ℕ) :
    (intFactorSet (mirrorWord x) n).card ≤ (2 * C + 1) * (n + 1) := by
  rw [mirror_factor_card]
  have hs := sym_factor_card_le x n
  have hc := hC n
  nlinarith


end Mirror
end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
section Orbit
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
variable {A : Type*}
attribute [local instance] Classical.propDecidable

private noncomputable def code {n : ℕ} (w : Fin n → A) : Finset (Fin n → A) :=
  {w, w ∘ Fin.rev}

private theorem reverse_twice {n : ℕ} (w : Fin n → A) :
    (w ∘ Fin.rev) ∘ Fin.rev = w := by
  funext k
  simp only [Function.comp_apply, Fin.rev_rev]

private theorem code_reverse {n : ℕ} (w : Fin n → A) :
    code (w ∘ Fin.rev) = code w := by
  simp only [code, reverse_twice, Finset.pair_comm]

private theorem code_eq_iff {n : ℕ} (u v : Fin n → A) :
    code u = code v ↔ ReflectivelyEquivalent u v := by
  constructor
  · intro h
    have hv : v ∈ code v := by simp [code]
    rw [← h] at hv
    simpa only [code, Finset.mem_insert, Finset.mem_singleton, ReflectivelyEquivalent] using hv
  · rintro (rfl | rfl)
    · rfl
    · exact (code_reverse u).symm

private theorem reflection_card_codes [Fintype A] (x : ℕ → A) (n : ℕ) :
    reflectionComplexity x n = ((wordFactorSet x n).image code).card := by
  classical
  let s := wordFactorSet x n
  let f : ↥s → ↥(s.image code) :=
    fun u => ⟨code u.val, Finset.mem_image_of_mem code u.property⟩
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨w, hw, hc⟩ := Finset.mem_image.mp c.property
    exact ⟨⟨w, hw⟩, Subtype.ext hc⟩
  let equiv := (Quot.congrRight (fun u v : ↥s => by
    change ReflectivelyEquivalent u.val v.val ↔ f u = f v
    rw [Subtype.ext_iff]
    exact (code_eq_iff u.val v.val).symm)).trans
      (Setoid.quotientKerEquivOfSurjective f hf)
  rw [reflectionComplexity, Nat.card_congr equiv,
    Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Counting reflection orbits of a reversal-closed finite set. -/
private theorem twice_codes_card {n : ℕ} (s : Finset (Fin n → A))
    (hs : ∀ w ∈ s, w ∘ Fin.rev ∈ s) :
    2 * (s.image code).card = s.card + (s.filter fun w => w ∘ Fin.rev = w).card := by
  classical
  let p : (Fin n → A) → Prop := fun w => w ∘ Fin.rev = w
  have hfiber (w : Fin n → A) (hw : w ∈ s) :
      s.filter (fun v => code v = code w) = code w := by
    ext v
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hv, h⟩
      have he := (code_eq_iff w v).mp h.symm
      simpa only [ReflectivelyEquivalent, code, Finset.mem_insert, Finset.mem_singleton] using he
    · intro hv
      have he : ReflectivelyEquivalent w v := by
        simpa only [ReflectivelyEquivalent, code, Finset.mem_insert, Finset.mem_singleton] using hv
      refine ⟨?_, (code_eq_iff w v).mpr he |>.symm⟩
      rcases he with rfl | rfl
      · exact hw
      · exact hs w hw
  have hfiberp (w : Fin n → A) (hw : w ∈ s) :
      (s.filter p).filter (fun v => code v = code w) = (code w).filter p := by
    calc
      _ = (s.filter fun v => code v = code w).filter p := by
        exact Finset.filter_comm p (fun v => code v = code w) s
      _ = _ := congrArg (fun t : Finset (Fin n → A) => t.filter p) (hfiber w hw)
  have hlocal (w : Fin n → A) : (code w).card + ((code w).filter p).card = 2 := by
    by_cases h : w ∘ Fin.rev = w
    · simp [code, p, h, Finset.filter_singleton]
    · have h' : w ≠ w ∘ Fin.rev := Ne.symm h
      simp [code, p, h, h', reverse_twice, Finset.filter_insert, Finset.filter_singleton]
  have hsum := Finset.card_eq_sum_card_image code s
  have hpsum : (s.filter p).card =
      ∑ c ∈ s.image code, ((s.filter p).filter fun w => code w = c).card :=
    Finset.card_eq_sum_card_fiberwise fun w hw =>
      Finset.mem_image_of_mem code (Finset.mem_filter.mp hw).1
  change 2 * (s.image code).card = s.card + (s.filter p).card
  rw [hsum, hpsum, ← Finset.sum_add_distrib]
  calc
    2 * (s.image code).card = ∑ _c ∈ s.image code, 2 := by simp; omega
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
      rw [hfiber w hw, hfiberp w hw]
      exact (hlocal w).symm

end Orbit
end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport

namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
section Walk

/-- A walk visiting every vertex still needs at least V-1 edges after removing
any specified family of loops. The edge type may contain parallel edges. -/
private theorem walk_loop_removal_count {V E : Type*} [Fintype V] [Fintype E]
    (v : ℕ → V) (e : ℕ → E) (hvisit : Function.Surjective v)
    (hends : ∀ i j, e i = e j →
      (v i = v j ∧ v (i + 1) = v (j + 1)) ∨
      (v i = v (j + 1) ∧ v (i + 1) = v j))
    (loops : Finset E) (hloops : ∀ i, e i ∈ loops → v i = v (i + 1)) :
    Fintype.card V + loops.card ≤ Fintype.card E + 1 := by
  classical
  let first (a : V) : ℕ := Nat.find (hvisit a)
  have hfirst (a : V) : v (first a) = a := Nat.find_spec (hvisit a)
  have hmin (a : V) {i : ℕ} (hi : v i = a) : first a ≤ i := Nat.find_min' (hvisit a) hi
  have hpos (a : V) (ha : a ≠ v 0) : 0 < first a := by
    exact (Nat.find_pos (hvisit a)).mpr (Ne.symm ha)
  have hsucc (a : V) (ha : a ≠ v 0) : first a - 1 + 1 = first a := by
    exact Nat.sub_add_cancel (hpos a ha)
  have hprev (a : V) (ha : a ≠ v 0) : v (first a - 1) ≠ a := by
    intro h
    have := hmin a h
    have := hpos a ha
    omega
  let assign : {a : V // a ≠ v 0} → ↥(Finset.univ \ loops) := fun a =>
    ⟨e (first a.val - 1), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro h
      have he := hloops (first a.val - 1) h
      rw [hsucc a.val a.property, hfirst] at he
      exact hprev a.val a.property he⟩⟩
  have hinj : Function.Injective assign := by
    intro a b hab
    have he : e (first a.val - 1) = e (first b.val - 1) := congrArg Subtype.val hab
    rcases hends _ _ he with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · apply Subtype.ext
      simpa only [hsucc a.val a.property, hsucc b.val b.property, hfirst] using h₁
    · rw [hsucc b.val b.property, hfirst] at h₀
      rw [hsucc a.val a.property, hfirst] at h₁
      have hm₀ := hmin b.val h₀
      have hm₁ := hmin a.val h₁.symm
      have hp₀ := hpos a.val a.property
      have hp₁ := hpos b.val b.property
      omega
  have hcard := Fintype.card_le_of_injective assign hinj
  have hvert : Fintype.card {a : V // a ≠ v 0} + 1 = Fintype.card V := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter fun a : V => a ≠ v 0) = Finset.univ.erase (v 0) := by
      exact Finset.filter_ne' Finset.univ (v 0)
    rw [hset]
    simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ (v 0))
  have hedge : (Finset.univ \ loops).card + loops.card = Fintype.card E := by
    simpa only [Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ loops)
  simp only [Fintype.card_coe] at hcard
  omega

end Walk
end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport


namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
section Reduction
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
variable {A : Type*} [Fintype A]
attribute [local instance] Classical.propDecidable

private noncomputable def palFactors (x : ℕ → A) (n : ℕ) : Finset (Fin n → A) :=
  (symFactors x n).filter fun w => w ∘ Fin.rev = w

private theorem symFactors_reverse (x : ℕ → A) (n : ℕ)
    (w : Fin n → A) (hw : w ∈ symFactors x n) : w ∘ Fin.rev ∈ symFactors x n := by
  classical
  change w ∈ wordFactorSet x n ∪ (wordFactorSet x n).image reverseWord at hw
  change w ∘ Fin.rev ∈ wordFactorSet x n ∪ (wordFactorSet x n).image reverseWord
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_union_left
    simpa only [reverseWord, D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.reverse_twice] using hv

private theorem sym_codes_eq (x : ℕ → A) (n : ℕ) :
    (symFactors x n).image code = (wordFactorSet x n).image code := by
  classical
  ext c
  constructor
  · rintro hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    change w ∈ wordFactorSet x n ∪ (wordFactorSet x n).image reverseWord at hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_image_of_mem code hw
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨v, hv, (D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_reverse v).symm⟩
  · rintro hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_image_of_mem
    exact Finset.mem_union_left _ hw

private theorem reflection_orbit_count (x : ℕ → A) (n : ℕ) :
    2 * reflectionComplexity x n = (symFactors x n).card + (palFactors x n).card := by
  have h := twice_codes_card (symFactors x n) (symFactors_reverse x n)
  rw [sym_codes_eq, ← D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.reflection_card_codes] at h
  exact h



omit [Fintype A] in
private theorem prefix_reverse {n : ℕ} (w : Fin (n + 1) → A) :
    Fin.init (w ∘ Fin.rev) = Fin.tail w ∘ Fin.rev := by
  funext k
  simp only [Fin.init, Fin.tail, Function.comp_apply, Fin.rev_castSucc]

omit [Fintype A] in
private theorem suffix_reverse {n : ℕ} (w : Fin (n + 1) → A) :
    Fin.tail (w ∘ Fin.rev) = Fin.init w ∘ Fin.rev := by
  funext k
  simp only [Fin.init, Fin.tail, Function.comp_apply, Fin.rev_succ]

omit [Fintype A] in
private theorem prefix_factor (x : ℕ → A) (n i : ℕ) :
    Fin.init (wordFactor x (n + 1) i) = wordFactor x n i := by
  exact List.ofFn_inj.mp rfl

omit [Fintype A] in
private theorem suffix_factor (x : ℕ → A) (n i : ℕ) :
    Fin.tail (wordFactor x (n + 1) i) = wordFactor x n (i + 1) := by
  funext k
  simp only [Fin.tail, wordFactor, Fin.val_succ]
  congr 1
  omega


private noncomputable def vertexAt (x : ℕ → A) (n i : ℕ) : ↥((wordFactorSet x n).image code) :=
  ⟨code (wordFactor x n i), Finset.mem_image_of_mem code (mem_wordFactorSet.mpr ⟨i, rfl⟩)⟩

private theorem vertexAt_surjective (x : ℕ → A) (n : ℕ) :
    Function.Surjective (vertexAt x n) := by
  intro c
  obtain ⟨w, hw, hc⟩ := Finset.mem_image.mp c.property
  obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hw
  exact ⟨i, Subtype.ext hc⟩

private theorem edge_endpoints (x : ℕ → A) (n i j : ℕ)
    (he : vertexAt x (n + 1) i = vertexAt x (n + 1) j) :
    (vertexAt x n i = vertexAt x n j ∧ vertexAt x n (i + 1) = vertexAt x n (j + 1)) ∨
    (vertexAt x n i = vertexAt x n (j + 1) ∧ vertexAt x n (i + 1) = vertexAt x n j) := by
  have hc := congrArg Subtype.val he
  have hr := (D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_eq_iff (wordFactor x (n + 1) i) (wordFactor x (n + 1) j)).mp hc
  rcases hr with h | h
  · left
    constructor
    · apply Subtype.ext
      exact congrArg code (congrArg Fin.init h).symm
    · apply Subtype.ext
      simpa only [vertexAt, suffix_factor] using congrArg code (congrArg Fin.tail h).symm
  · right
    have hp := congrArg code (congrArg Fin.init h)
    have hs := congrArg code (congrArg Fin.tail h)
    simp only [prefix_reverse, suffix_reverse, prefix_factor, suffix_factor, D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_reverse] at hp hs
    exact ⟨Subtype.ext hs.symm, Subtype.ext hp.symm⟩

private noncomputable def palindromeEdge (x : ℕ → A) (n : ℕ) (w : ↥(palFactors x (n + 1))) :
    ↥((wordFactorSet x (n + 1)).image code) :=
  ⟨code w.val, by
    rw [← sym_codes_eq]
    exact Finset.mem_image_of_mem code (Finset.mem_filter.mp w.property).1⟩

private theorem palindromeEdge_injective (x : ℕ → A) (n : ℕ) :
    Function.Injective (palindromeEdge x n) := by
  intro u v h
  apply Subtype.ext
  have he := (D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_eq_iff u.val v.val).mp (congrArg Subtype.val h)
  rcases he with he | he
  · exact he.symm
  · have hp := (Finset.mem_filter.mp u.property).2
    exact (he.trans hp).symm

private theorem palindromeEdge_is_loop (x : ℕ → A) (n i : ℕ)
    (hi : vertexAt x (n + 1) i ∈ Finset.univ.image (palindromeEdge x n)) :
    vertexAt x n i = vertexAt x n (i + 1) := by
  classical
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hi
  have hc : code w.val = code (wordFactor x (n + 1) i) := congrArg Subtype.val he
  have hr := (D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_eq_iff w.val (wordFactor x (n + 1) i)).mp hc
  have hp := (Finset.mem_filter.mp w.property).2
  have hwfactor : wordFactor x (n + 1) i = w.val := by
    rcases hr with hr | hr
    · exact hr
    · exact hr.trans hp
  have hpal : wordFactor x (n + 1) i ∘ Fin.rev = wordFactor x (n + 1) i := by
    rw [hwfactor]
    exact hp
  apply Subtype.ext
  have hpre := congrArg code (congrArg Fin.init hpal)
  simpa only [vertexAt, prefix_reverse, prefix_factor, suffix_factor, D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.code_reverse] using hpre.symm

/-- The quotient walk remains connected after deleting all palindromic loops. -/
private theorem reflection_loop_count (x : ℕ → A) (n : ℕ) :
    reflectionComplexity x n + (palFactors x (n + 1)).card ≤ reflectionComplexity x (n + 1) + 1 := by
  classical
  have h := walk_loop_removal_count (vertexAt x n) (vertexAt x (n + 1))
    (vertexAt_surjective x n) (edge_endpoints x n)
    (Finset.univ.image (palindromeEdge x n)) (palindromeEdge_is_loop x n)
  rw [Finset.card_image_of_injective _ (palindromeEdge_injective x n), Finset.card_univ,
    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
    ← D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.reflection_card_codes, ← D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport.reflection_card_codes] at h
  exact h

end Reduction
end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport


namespace D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
section Reduction
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
variable {A : Type*} [Fintype A]

/-- A bounded derivative for the exact marked mirror suffices for bounded reflection differences. -/
theorem reflectionBoundOfMirrorBound (x : ℕ → A) (D : ℕ)
    (hD : ∀ n, (intFactorSet (mirrorWord x) (n + 1)).card ≤
      (intFactorSet (mirrorWord x) n).card + D) :
    ∃ B : ℕ, ∀ n : ℕ,
      Int.natAbs ((reflectionComplexity x (n + 1) : ℤ) - (reflectionComplexity x n : ℤ)) ≤ B := by
  refine ⟨D + 1, ?_⟩
  intro n
  have h₀ := reflection_orbit_count x n
  have h₁ := reflection_orbit_count x (n + 1)
  have hloop := reflection_loop_count x n
  have hmirror := hD n
  rw [mirror_factor_card, mirror_factor_card] at hmirror
  have hlower : reflectionComplexity x n ≤ reflectionComplexity x (n + 1) + 1 :=
    Nat.le_of_add_right_le hloop
  have hupper : reflectionComplexity x (n + 1) ≤ reflectionComplexity x n + D + 1 := by omega
  omega

end Reduction
end D5.S1.Words.Complexity.AlloucheReflectionComplexitySupport
