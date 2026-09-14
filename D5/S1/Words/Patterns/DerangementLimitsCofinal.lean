/- GID: D5/S1/Words/Patterns/DerangementLimitsCofinal
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/DerangementLimitsCofinal
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded decreasing tails yield derangement limits cofinal below one. -/

import D5.S1.Words.Patterns.DerangementRatioNonconvergence
import Mathlib.Tactic.Linarith

/-!
# Derangement limits cofinal below one

The permutation with tail length `a` is `(a+1,...,n,a,...,1)` in one-based
notation. Bounding `a` gives a hereditary permutation class. At sufficiently
large lengths its `k+1` members include exactly `k` derangements.

These unbounded symbolic arguments concern arbitrary lengths and parameters;
they are not finite enumeration, checkers, numerical reductions, or certified
finite instances (utility: none).
-/

namespace D5.S1.Words.Patterns.DerangementLimitsCofinal

open D5.S1.Words.Patterns.DerangementRatioNonconvergence
open Filter Topology

/-- An increasing block of high values followed by a decreasing tail of low values. -/
def tailPerm (n a : ℕ) (ha : a ≤ n) : Equiv.Perm (Fin n) where
  toFun i := ⟨if i.val < n - a then a + i.val else n - 1 - i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
  invFun j := ⟨if a ≤ j.val then j.val - a else n - 1 - j.val, by
    have := j.isLt
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    have := i.isLt
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    dsimp
    have := j.isLt
    split_ifs <;> omega

/-- Every contained pattern has the same form, with a tail no longer than the original. -/
theorem pattern_tailPerm {m n a : ℕ} (ha : a ≤ n) {σ : Equiv.Perm (Fin m)}
    (h : Contains σ (tailPerm n a ha)) :
    ∃ t : ℕ, ∃ ht : t ≤ m, t ≤ a ∧ σ = tailPerm m t ht := by
  classical
  obtain ⟨f, hf⟩ := h
  have hex : ∃ b : ℕ, ∀ i : Fin m, b ≤ i.val → n - a ≤ (f i).val :=
    ⟨m, fun i hi => by have := i.isLt; omega⟩
  let b := Nat.find hex
  have hb : b ≤ m := Nat.find_le (fun i hi => by have := i.isLt; omega)
  have htail (i : Fin m) (hi : b ≤ i.val) : n - a ≤ (f i).val :=
    Nat.find_spec hex i hi
  have hcut (i : Fin m) : (f i).val < n - a ↔ i.val < b := by
    constructor
    · intro hi
      by_contra hbi
      have := htail i (by omega)
      omega
    · intro hi
      by_contra hfi
      have hp : ∀ j : Fin m, i.val ≤ j.val → n - a ≤ (f j).val := by
        intro j hij
        have hm := f.monotone (show i ≤ j from hij)
        change (f i).val ≤ (f j).val at hm
        omega
      have : b ≤ i.val := Nat.find_le hp
      omega
  let liftTail (i : Fin (m - b)) : Fin m := ⟨b + i.val, by have := i.isLt; omega⟩
  let tailMap (i : Fin (m - b)) : Fin a :=
    ⟨(f (liftTail i)).val - (n - a), by
      have hlow := htail (liftTail i) (by dsimp [liftTail]; omega)
      have hhigh := (f (liftTail i)).isLt
      omega⟩
  have hinj : Function.Injective tailMap := by
    intro i j hij
    have hv := congrArg Fin.val hij
    change (f (liftTail i)).val - (n - a) = (f (liftTail j)).val - (n - a) at hv
    have hi := htail (liftTail i) (by dsimp [liftTail]; omega)
    have hj := htail (liftTail j) (by dsimp [liftTail]; omega)
    have heq : f (liftTail i) = f (liftTail j) := Fin.ext (by omega)
    have heq' := congrArg Fin.val (f.injective heq)
    apply Fin.ext
    dsimp [liftTail] at heq'
    omega
  have hsize : m - b ≤ a := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective tailMap hinj
  refine ⟨m - b, by omega, hsize, ?_⟩
  have hinc (d c : ℕ) (hc : c ≤ d) (i j : Fin d) (hij : i < j) :
      tailPerm d c hc i < tailPerm d c hc j ↔ j.val < d - c := by
    change (if i.val < d - c then c + i.val else d - 1 - i.val) <
      (if j.val < d - c then c + j.val else d - 1 - j.val) ↔ _
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    split_ifs <;> omega
  have hlt : ∀ i j, σ i < σ j ↔ tailPerm m (m - b) (by omega) i <
      tailPerm m (m - b) (by omega) j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hf, hinc n a ha (f i) (f j) (f.strictMono hij),
        hinc m (m - b) (by omega) i j hij, hcut]
      omega
    · exact ⟨fun h => (lt_irrefl _ h).elim, fun h => (lt_irrefl _ h).elim⟩
    · have hp : σ i ≠ σ j := fun he => (ne_of_lt hji) (σ.injective he).symm
      have hs : tailPerm m (m - b) (by omega) i ≠
          tailPerm m (m - b) (by omega) j :=
        fun he => (ne_of_lt hji) ((tailPerm m (m - b) (by omega)).injective he).symm
      have hrev : σ j < σ i ↔ tailPerm m (m - b) (by omega) j <
          tailPerm m (m - b) (by omega) i := by
        rw [hf, hinc n a ha (f j) (f i) (f.strictMono hji),
          hinc m (m - b) (by omega) j i hji, hcut]
        omega
      constructor
      · intro hij
        exact lt_of_le_of_ne (le_of_not_gt (fun hji' => (not_lt_of_ge hij.le) (hrev.mpr hji'))) hs
      · intro hij
        exact lt_of_le_of_ne (le_of_not_gt (fun hji' => (not_lt_of_ge hij.le) (hrev.mp hji'))) hp
  have hmono : StrictMono (fun i => tailPerm m (m - b) (by omega) (σ.symm i)) := by
    intro i j hij
    exact (hlt _ _).mp (by simpa only [Equiv.apply_symm_apply] using hij)
  apply Equiv.ext
  intro i
  have heq := hmono.apply_eq (x := σ i)
  rw [Equiv.symm_apply_apply] at heq
  exact heq.symm

/-- The actual permutation class with decreasing tail length bounded by `k`. -/
def boundedTailClass (k : ℕ) : PermClass where
  mem n := {π | ∃ a : ℕ, ∃ ha : a ≤ n, a ≤ k ∧ π = tailPerm n a ha}
  downset := by
    intro m n σ π hπ hcontains
    obtain ⟨a, ha, hak, rfl⟩ := hπ
    obtain ⟨t, ht, hta, rfl⟩ := pattern_tailPerm ha hcontains
    exact ⟨t, ht, hta.trans hak, rfl⟩

open Classical in
/-- Beyond the common threshold there are exactly `k+1` members and `k` derangements. -/
theorem boundedTailClass_counts (k n : ℕ) (hn : 2 * k + 2 < n) :
    Fintype.card ((boundedTailClass k).mem n) = k + 1 ∧
    Fintype.card {π : (boundedTailClass k).mem n // IsDerangement π.val} = k := by
  have hn0 : 0 < n := by omega
  let mk (a : Fin (k + 1)) : (boundedTailClass k).mem n :=
    ⟨tailPerm n a.val (by have := a.isLt; omega),
      a.val, (by have := a.isLt; omega), (by have := a.isLt; omega), rfl⟩
  have hfirst (a : Fin (k + 1)) : ((mk a).val ⟨0, hn0⟩).val = a.val := by
    change (if 0 < n - a.val then a.val + 0 else n - 1 - 0) = a.val
    rw [if_pos (by have := a.isLt; omega)]
    omega
  have hinj : Function.Injective mk := by
    intro a b hab
    apply Fin.ext
    have heq := congrArg (fun π : (boundedTailClass k).mem n => (π.val ⟨0, hn0⟩).val) hab
    simpa only [hfirst] using heq
  have hsurj : Function.Surjective mk := by
    rintro ⟨π, a, ha, hak, rfl⟩
    refine ⟨⟨a, by omega⟩, ?_⟩
    rfl
  have hfree (a : Fin (k + 1)) : IsDerangement (mk a).val ↔ a.val ≠ 0 := by
    change (∀ i : Fin n, (mk a).val i ≠ i) ↔ a.val ≠ 0
    constructor
    · intro h ha0
      apply h ⟨0, hn0⟩
      apply Fin.ext
      exact (hfirst a).trans ha0
    · intro ha0 i hfixed
      have heq := congrArg Fin.val hfixed
      change (if i.val < n - a.val then a.val + i.val else n - 1 - i.val) = i.val at heq
      have hi := i.isLt
      have ha := a.isLt
      split_ifs at heq <;> omega
  let mkD (a : Fin k) : {π : (boundedTailClass k).mem n // IsDerangement π.val} :=
    ⟨mk ⟨a.val + 1, by have := a.isLt; omega⟩,
      (hfree _).mpr (by dsimp; omega)⟩
  have hinjD : Function.Injective mkD := by
    intro a b hab
    have heq := hinj (congrArg Subtype.val hab)
    have hval := congrArg Fin.val heq
    apply Fin.ext
    dsimp at hval
    omega
  have hsurjD : Function.Surjective mkD := by
    intro π
    obtain ⟨a, ha⟩ := hsurj π.val
    have hapos : a.val ≠ 0 := (hfree a).mp (ha.symm ▸ π.property)
    refine ⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩
    apply Subtype.ext
    change mk ⟨a.val - 1 + 1, _⟩ = π.val
    have heq : (⟨a.val - 1 + 1, by have := a.isLt; omega⟩ : Fin (k + 1)) = a :=
      Fin.ext (by dsimp; omega)
    rw [heq, ha]
  exact ⟨(Fintype.card_congr (Equiv.ofBijective mk ⟨hinj, hsurj⟩)).symm.trans
      (Fintype.card_fin _),
    (Fintype.card_congr (Equiv.ofBijective mkD ⟨hinjD, hsurjD⟩)).symm.trans
      (Fintype.card_fin _)⟩

/-- Achieved derangement limits of hereditary permutation classes are cofinal below one. -/
theorem exists_derangement_limit_between (q : ℝ) (hq : q < 1) :
    ∃ C : PermClass, ∃ l : ℝ, q < l ∧ l < 1 ∧
      (∀ n, (C.mem n).Nonempty) ∧ Tendsto (ratio C) atTop (nhds l) := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (q / (1 - q))
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hbound := (div_lt_iff₀ (sub_pos.mpr hq)).mp hk
  refine ⟨boundedTailClass k, (k : ℝ) / ((k : ℝ) + 1),
    (lt_div_iff₀ hpos).mpr (by nlinarith),
    (div_lt_one hpos).mpr (by linarith), ?_, ?_⟩
  · intro n
    exact ⟨tailPerm n 0 (Nat.zero_le n), 0, Nat.zero_le n, Nat.zero_le k, rfl⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2 * k + 2)] with n hn
    obtain ⟨hall, hder⟩ := boundedTailClass_counts k n hn
    simp only [ratio, hall, hder, Nat.cast_add, Nat.cast_one]

#print axioms tailPerm
#print axioms pattern_tailPerm
#print axioms boundedTailClass
#print axioms boundedTailClass_counts
#print axioms exists_derangement_limit_between

end D5.S1.Words.Patterns.DerangementLimitsCofinal
