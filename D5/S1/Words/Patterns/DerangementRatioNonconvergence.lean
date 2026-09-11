/- GID: D5/S1/Words/Patterns/DerangementRatioNonconvergence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/DerangementRatioNonconvergence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Decreasing permutations form a class with a nonconvergent derangement ratio. -/

import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A literal negative answer to Vatter's Question 4.3

The class Av(12) consists of the decreasing permutations. It is a downset for
pattern containment, has exactly one permutation at each length, and that
permutation is a derangement exactly at even lengths. Its derangement ratio
therefore does not converge.

This is a literal counterexample to the question as stated; the author may
have had nontrivial (e.g. infinite-growth) classes in mind. This module claims
only the refutation of the universally quantified statement, not of any
strengthening restricted to such classes.

All arguments are unbounded symbolic proofs, not bounded enumeration,
checkers, numerical reductions, or certified finite instances (utility: none).
The source is Question 4.3 of arXiv:2602.16355v2, as quoted in the task;
the counterexample proof is derived here.
-/

namespace D5.S1.Words.Patterns.DerangementRatioNonconvergence

open scoped Classical
open Filter Topology

/-- Pattern containment preserves the relative order of values at embedded positions. -/
def Contains {k n : ℕ} (σ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ i j, σ i < σ j ↔ π (f i) < π (f j)

/-- A permutation class is a length-indexed family closed under pattern containment. -/
structure PermClass where
  mem : (n : ℕ) → Set (Equiv.Perm (Fin n))
  downset : ∀ k n σ π, π ∈ mem n → Contains σ π → σ ∈ mem k

/-- Mathlib's fixed-point-free predicate on permutations. -/
def IsDerangement {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  π ∈ derangements (Fin n)

private theorem av12_downset {k n : ℕ}
    {σ : Equiv.Perm (Fin k)} {π : Equiv.Perm (Fin n)}
    (hπ : ∀ i j, i < j → π j < π i) (hcontains : Contains σ π) :
    ∀ i j, i < j → σ j < σ i := by
  obtain ⟨positions, hpositions⟩ := hcontains
  intro i j hij
  exact (hpositions j i).mpr (hπ (positions i) (positions j) (positions.strictMono hij))

/-- Av(12), expressed as the class of strictly decreasing permutations. -/
def Av12 : PermClass where
  mem n := {π | ∀ i j : Fin n, i < j → π j < π i}
  downset := fun _ _ _ _ hπ hcontains => av12_downset hπ hcontains

/-- The only decreasing permutation of each length is reversal. -/
theorem av12_mem_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    π ∈ Av12.mem n ↔ π = Fin.revPerm := by
  constructor
  · intro hπ
    have hanti : StrictAnti π := hπ
    have hmono : StrictMono (fun i => Fin.rev (π i)) := Fin.rev_strictAnti.comp hanti
    apply Equiv.ext
    intro i
    have hfixed := hmono.apply_eq (x := i)
    simpa using congrArg Fin.rev hfixed
  · rintro rfl
    exact Fin.rev_strictAnti

/-- Reversal fixes precisely a middle position. -/
theorem rev_fixed_iff {n : ℕ} (i : Fin n) :
    Fin.revPerm i = i ↔ 2 * i.val + 1 = n := by
  change Fin.rev i = i ↔ _
  rw [Fin.ext_iff, Fin.val_rev]
  have hbound := i.isLt
  omega

/-- Reversal is fixed-point-free exactly at even lengths, including zero. -/
theorem rev_isDerangement_iff (n : ℕ) :
    IsDerangement (Fin.revPerm : Equiv.Perm (Fin n)) ↔ Even n := by
  change (∀ i : Fin n, Fin.revPerm i ≠ i) ↔ Even n
  constructor
  · intro hfree
    by_contra hodd
    have hparity : n % 2 ≠ 0 := by simpa [Nat.even_iff] using hodd
    have hmid : n / 2 < n := by omega
    exact hfree ⟨n / 2, hmid⟩ ((rev_fixed_iff _).mpr (by dsimp; omega))
  · intro heven i hfixed
    have hmiddle := (rev_fixed_iff i).mp hfixed
    have hparity := Nat.even_iff.mp heven
    omega

/-- Every length slice of Av(12) has cardinality one. -/
theorem card_av12 (n : ℕ) : Fintype.card (Av12.mem n) = 1 := by
  have hset : Av12.mem n = {Fin.revPerm} := by
    ext π
    exact av12_mem_iff π
  rw [hset]
  simp

/-- The derangement slice has cardinality one at even lengths and zero otherwise. -/
theorem card_derangements_av12 (n : ℕ) :
    Fintype.card {π : Av12.mem n // IsDerangement π.val} = if Even n then 1 else 0 := by
  have hrev : (Fin.revPerm : Equiv.Perm (Fin n)) ∈ Av12.mem n :=
    (av12_mem_iff _).mpr rfl
  have : Subsingleton (Av12.mem n) := ⟨fun π σ => Subtype.ext
    ((av12_mem_iff π.val).mp π.property |>.trans ((av12_mem_iff σ.val).mp σ.property).symm)⟩
  split_ifs with heven
  · let witness : {π : Av12.mem n // IsDerangement π.val} :=
      ⟨⟨Fin.revPerm, hrev⟩, (rev_isDerangement_iff n).mpr heven⟩
    let : Unique {π : Av12.mem n // IsDerangement π.val} :=
      ⟨⟨witness⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique
  · have : IsEmpty {π : Av12.mem n // IsDerangement π.val} := ⟨by
      intro π
      have hfree := π.property
      rw [(av12_mem_iff π.val.val).mp π.val.property] at hfree
      exact heven ((rev_isDerangement_iff n).mp hfree)⟩
    exact Fintype.card_eq_zero

/-- The real ratio of derangements to all members of the length slice. -/
noncomputable def ratio (C : PermClass) (n : ℕ) : ℝ :=
  (Fintype.card {π : C.mem n // IsDerangement π.val} : ℝ) / Fintype.card (C.mem n)

/-- The Av(12) ratio alternates with parity, also at length zero. -/
theorem ratio_av12 (n : ℕ) : ratio Av12 n = if Even n then 1 else 0 := by
  rw [ratio, card_derangements_av12, card_av12]
  split_ifs <;> simp

/-- Literal refutation of Question 4.3, without additional growth hypotheses. -/
theorem vatter_question_4_3_answer_no :
    ¬ ∃ L : ℝ, Tendsto (ratio Av12) atTop (nhds L) := by
  rintro ⟨L, hlimit⟩
  have heven_top : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have hodd_top : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have heven : (fun k : ℕ => ratio Av12 (2 * k)) = fun _ => (1 : ℝ) := by
    funext k
    rw [ratio_av12, if_pos (by exact ⟨k, by omega⟩)]
  have hodd : (fun k : ℕ => ratio Av12 (2 * k + 1)) = fun _ => (0 : ℝ) := by
    funext k
    rw [ratio_av12, if_neg (by rw [Nat.even_iff]; omega)]
  have hone : L = 1 := tendsto_nhds_unique (hlimit.comp heven_top)
    (by simpa only [Function.comp_def, heven] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)))
  have hzero : L = 0 := tendsto_nhds_unique (hlimit.comp hodd_top)
    (by simpa only [Function.comp_def, hodd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)))
  exact one_ne_zero (hone.symm.trans hzero)

/-- Some permutation class has a nonconvergent derangement ratio. -/
theorem exists_permClass_ratio_not_convergent :
    ∃ C : PermClass, ¬ ∃ L : ℝ, Tendsto (ratio C) atTop (nhds L) :=
  ⟨Av12, vatter_question_4_3_answer_no⟩

#print axioms av12_mem_iff
#print axioms rev_fixed_iff
#print axioms rev_isDerangement_iff
#print axioms card_av12
#print axioms card_derangements_av12
#print axioms ratio_av12
#print axioms vatter_question_4_3_answer_no
#print axioms exists_permClass_ratio_not_convergent

end D5.S1.Words.Patterns.DerangementRatioNonconvergence
