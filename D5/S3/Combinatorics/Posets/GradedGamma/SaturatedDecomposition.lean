/- GID: D5/S3/Combinatorics/Posets/GradedGamma/SaturatedDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/SaturatedDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.Tuple.Sort]
   utility: none
   digest: Every graded extension belongs to one saturated run-relation fiber. -/

import D5.S3.Combinatorics.Posets.GradedGamma.SaturatedRuns
import D5.S3.Combinatorics.Posets.GradedGamma.CanonicalPartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α : Type*} [Fintype α] [PartialOrder α] [GradeOrder ℕ α]

/-- A run index cannot be skipped: a parity change increments the index by
one, while consecutive vertices of the same parity remain in one run. -/
theorem runIndex_reaches (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) (k : ℕ) (hk : k ≤ runIndex e i) :
    ∃ j : Fin (Fintype.card α), j ≤ i ∧ runIndex e j = k := by
  classical
  have hstep : ∀ t : ℕ, (ht : t < Fintype.card α) →
      ∀ k ≤ runIndex e ⟨t, ht⟩,
        ∃ j : Fin (Fintype.card α), j ≤ ⟨t, ht⟩ ∧ runIndex e j = k := by
    intro t
    induction t with
    | zero =>
        intro ht k hk
        have hzero : runIndex e ⟨0, ht⟩ = 0 := by simp [runIndex]
        refine ⟨⟨0, ht⟩, le_rfl, ?_⟩
        omega
    | succ t ih =>
        intro ht k hk
        have hprev : t < Fintype.card α := by omega
        have hrec := runIndex_succ e
          (⟨t, by omega⟩ : Fin (Fintype.card α - 1))
        have hdiff : runIndex e ⟨t + 1, ht⟩ ≤
            runIndex e ⟨t, hprev⟩ + 1 := by
          change runIndex e ⟨t + 1, ht⟩ =
            runIndex e ⟨t, hprev⟩ +
              (if parityBoundary e ⟨t, by omega⟩ then 1 else 0) at hrec
          rw [hrec]
          split_ifs <;> omega
        by_cases hsmall : k ≤ runIndex e ⟨t, hprev⟩
        · obtain ⟨j, hj, hindex⟩ := ih hprev k hsmall
          exact ⟨j, by exact le_trans hj (by exact Fin.mk_le_mk.mpr (by omega)),
            hindex⟩
        · refine ⟨⟨t + 1, ht⟩, le_rfl, ?_⟩
          omega
  exact hstep i.val i.isLt k hk

def runRelation (e : EnumeratingExtension α) : Finset (α × α) := by
  classical
  exact Finset.univ.filter fun p => runLE e p.1 p.2

def RunSignature (α : Type*) [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] : Type _ :=
  {Q : Finset (α × α) // ∃ e : EnumeratingExtension α, runRelation e = Q}

noncomputable instance : Fintype (RunSignature α) := by
  classical
  unfold RunSignature
  infer_instance

def RunCompatible (Q : RunSignature α) (e' : EnumeratingExtension α) : Prop :=
  ∀ x y : α, x ≠ y → (x, y) ∈ Q.1 → e'.1.symm x < e'.1.symm y

noncomputable instance (Q : RunSignature α) :
    Fintype {e' : EnumeratingExtension α // RunCompatible Q e'} := by
  classical
  infer_instance

/-- Permutations of extension positions that keep every parity-run fiber fixed. -/
def RunPerm (e : EnumeratingExtension α) : Type _ :=
  {σ : Equiv.Perm (Fin (Fintype.card α)) //
    ∀ i, runIndex e (σ i) = runIndex e i}

noncomputable instance (e : EnumeratingExtension α) : Fintype (RunPerm e) := by
  classical
  unfold RunPerm
  infer_instance

/-- Compatible linear extensions are precisely permutations within the
representative's parity runs. -/
def compatibleExtensionPermEquiv (e : EnumeratingExtension α) :
    {e' : EnumeratingExtension α //
      ∀ x y : α,
        runIndex e (e.1.symm x) < runIndex e (e.1.symm y) →
          e'.1.symm x < e'.1.symm y} ≃ RunPerm e := by
  classical
  have hmono : Monotone (runIndex e) := by
    intro i j hij
    unfold runIndex
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨lt_of_lt_of_le hk.1 hij, hk.2⟩
  let fromPerm (p : RunPerm e) :
      {e' : EnumeratingExtension α //
        ∀ x y : α,
          runIndex e (e.1.symm x) < runIndex e (e.1.symm y) →
            e'.1.symm x < e'.1.symm y} := by
    let σ := p.1
    have hpres (i : Fin (Fintype.card α)) :
        runIndex e (σ.symm i) = runIndex e i := by
      have hi := p.2 (σ.symm i)
      change runIndex e (σ (σ.symm i)) = runIndex e (σ.symm i) at hi
      rw [Equiv.apply_symm_apply] at hi
      exact hi.symm
    have horder {x y : α}
        (hxy : runIndex e (e.1.symm x) < runIndex e (e.1.symm y)) :
        σ.symm (e.1.symm x) < σ.symm (e.1.symm y) := by
      by_contra hn
      have hrev : σ.symm (e.1.symm y) ≤ σ.symm (e.1.symm x) :=
        le_of_not_gt hn
      have hm := hmono hrev
      rw [hpres, hpres] at hm
      exact (not_le_of_gt hxy) hm
    let f : Fin (Fintype.card α) ≃ α := σ.trans e.1
    have hext : ∀ ⦃x y : α⦄, x < y → f.symm x < f.symm y := by
      intro x y hxy
      have hr := runLE_extends e hxy
      have hi : runIndex e (e.1.symm x) < runIndex e (e.1.symm y) := by
        rcases hr with heq | hlt
        · exact False.elim (hxy.ne heq)
        · exact hlt
      change σ.symm (e.1.symm x) < σ.symm (e.1.symm y)
      exact horder hi
    refine ⟨⟨f, hext⟩, ?_⟩
    intro x y hxy
    change σ.symm (e.1.symm x) < σ.symm (e.1.symm y)
    exact horder hxy
  refine {
    toFun := fun s => ⟨s.1.1.trans e.1.symm,
      compatible_run_word e s.1 s.2⟩
    invFun := fromPerm
    left_inv := ?_
    right_inv := ?_ }
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [fromPerm]
  · intro p
    apply Subtype.ext
    ext i
    simp [fromPerm]

/-- Run number as a finite index; empty index fibers are harmless. -/
def runBucket (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) : Fin (Fintype.card α) := by
  classical
  have hs : runIndex e i ≤ Fintype.card α - 1 := by
    unfold runIndex
    simpa only [Fintype.card_fin, Finset.card_univ] using
      (Finset.card_le_card (Finset.filter_subset
        (s := (Finset.univ : Finset (Fin (Fintype.card α - 1))))
        (p := fun k => k.val < i.val ∧ parityBoundary e k)))
  exact ⟨runIndex e i, by have hi := i.isLt; omega⟩

/-- The positions belonging to a specified run. -/
def RunPosition (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α)) : Type _ :=
  {i : Fin (Fintype.card α) // runBucket e i = k}

instance (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α)) : LinearOrder (RunPosition e k) := by
  unfold RunPosition
  infer_instance

noncomputable instance (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α)) : Fintype (RunPosition e k) := by
  classical
  unfold RunPosition
  infer_instance

/-- Every run occupies an interval of extension positions. -/
theorem runBucket_interval (e : EnumeratingExtension α)
    (i j t : Fin (Fintype.card α)) (hit : i ≤ t) (htj : t ≤ j)
    (hij : runBucket e i = runBucket e j) :
    runBucket e t = runBucket e i := by
  have hmono : Monotone (runBucket e) := by
    intro u v huv
    apply Fin.le_iff_val_le_val.mpr
    change runIndex e u ≤ runIndex e v
    unfold runIndex
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨lt_of_lt_of_le hk.1 huv, hk.2⟩
  exact le_antisymm ((hmono htj).trans_eq hij.symm) (hmono hit)

/-- The occupied run fibers are exactly the indices reached before the last
position; this also accounts for the empty fibers in the product type. -/
theorem runPosition_nonempty_iff (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α)) :
    Nonempty (RunPosition e k) ↔
      k.val ≤ runIndex e ⟨Fintype.card α - 1, by
        have := k.isLt
        omega⟩ := by
  classical
  have hlast : 0 < Fintype.card α := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  constructor
  · rintro ⟨⟨i, hi⟩⟩
    have hle : i ≤ (⟨Fintype.card α - 1, by omega⟩ : Fin (Fintype.card α)) := by
      apply Fin.le_iff_val_le_val.mpr
      have := i.isLt
      change i.val ≤ Fintype.card α - 1
      omega
    have hmono : runIndex e i ≤
        runIndex e ⟨Fintype.card α - 1, by omega⟩ := by
      unfold runIndex
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨lt_of_lt_of_le ht.1 hle, ht.2⟩
    have hk := congrArg Fin.val hi
    exact hk.symm.trans_le hmono
  · intro hk
    obtain ⟨i, _, hi⟩ := runIndex_reaches e
      ⟨Fintype.card α - 1, by omega⟩ k.val hk
    exact ⟨⟨i, Fin.ext hi⟩⟩

/-- A run-preserving permutation splits uniquely into independent
permutations of its run fibers. -/
def runPermFiberEquiv (e : EnumeratingExtension α) :
    RunPerm e ≃
      (∀ k : Fin (Fintype.card α), Equiv.Perm (RunPosition e k)) := by
  classical
  let B : (Σ k : Fin (Fintype.card α), RunPosition e k) ≃
      Fin (Fintype.card α) := Equiv.sigmaFiberEquiv (runBucket e)
  let split (p : RunPerm e)
      (k : Fin (Fintype.card α)) : Equiv.Perm (RunPosition e k) :=
    p.1.subtypeEquiv (fun i => by
      change runBucket e i = k ↔ runBucket e (p.1 i) = k
      have hi : runBucket e (p.1 i) = runBucket e i := by
        apply Fin.ext
        exact p.2 i
      rw [hi])
  let join (f : ∀ k : Fin (Fintype.card α),
      Equiv.Perm (RunPosition e k)) : RunPerm e := by
    let σ : Equiv.Perm (Fin (Fintype.card α)) :=
      B.symm.trans ((Equiv.Perm.sigmaCongrRight f).trans B)
    refine ⟨σ, ?_⟩
    intro i
    have hi : runBucket e (σ i) = runBucket e i := by
      change runBucket e ((f (runBucket e i) ⟨i, rfl⟩).1) = runBucket e i
      exact (f (runBucket e i) ⟨i, rfl⟩).2
    exact congrArg Fin.val hi
  refine {
    toFun := split
    invFun := join
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    apply Subtype.ext
    ext i
    dsimp [join, split, B, Equiv.sigmaFiberEquiv,
      Equiv.Perm.sigmaCongrRight]
    rfl
  · intro f
    funext k
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change (f (runBucket e i.1) ⟨i.1, rfl⟩).1 = (f k i).1
    rcases i with ⟨j, hj⟩
    change runBucket e j = k at hj
    subst k
    rfl

/- Canonical relabelling changes a boundary descent according to the
departing run's parity; within a run it preserves the original descent. -/
open Classical in
theorem parityLabel_descent_at_run (e : EnumeratingExtension α)
    (ω : α → ℕ) (hbound : ∀ x, ω x < Fintype.card α)
    (hfirst : ∀ h : 0 < Fintype.card α,
      grade ℕ (e ⟨0, h⟩) % 2 = 0)
    (i : Fin (Fintype.card α - 1)) :
    descent (parityLabel ω) e i ↔
      if parityBoundary e i then
        runIndex e ⟨i.val, by omega⟩ % 2 = 1
      else descent ω e i := by
  classical
  let x := e ⟨i.val, by omega⟩
  let y := e ⟨i.val + 1, by omega⟩
  have hx := hbound x
  have hy := hbound y
  have hpar := runIndex_parity e hfirst ⟨i.val, by omega⟩
  change runIndex e ⟨i.val, by omega⟩ % 2 = grade ℕ x % 2 at hpar
  have hpx : grade ℕ x % 2 < 2 := Nat.mod_lt _ (by omega)
  have hpy : grade ℕ y % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hb : parityBoundary e i
  · have hneq : grade ℕ x % 2 ≠ grade ℕ y % 2 := hb
    by_cases hzero : grade ℕ x % 2 = 0
    · have hone : grade ℕ y % 2 = 1 := by omega
      simp only [if_pos hb]
      change (parityLabel ω x > parityLabel ω y) ↔ _
      simp only [parityLabel, if_pos hzero, if_neg (by omega : grade ℕ y % 2 ≠ 0)]
      omega
    · have hone : grade ℕ x % 2 = 1 := by omega
      have hzero' : grade ℕ y % 2 = 0 := by omega
      simp only [if_pos hb]
      change (parityLabel ω x > parityLabel ω y) ↔ _
      simp only [parityLabel, if_neg hzero, if_pos hzero']
      omega
  · have heq : grade ℕ x % 2 = grade ℕ y % 2 := by
      simpa only [parityBoundary, not_ne_iff] using hb
    by_cases hzero : grade ℕ x % 2 = 0
    · have hzero' : grade ℕ y % 2 = 0 := heq ▸ hzero
      simp only [if_neg hb]
      change (parityLabel ω x > parityLabel ω y) ↔ ω x > ω y
      simp [parityLabel, hzero, hzero']
    · have hzero' : grade ℕ y % 2 ≠ 0 := by omega
      simp only [if_neg hb]
      change (parityLabel ω x > parityLabel ω y) ↔ ω x > ω y
      simp only [parityLabel, if_neg hzero, if_neg hzero']
      omega

/-- The saturated run orders give a disjoint exhaustive decomposition of
all labelled linear extensions. -/
def saturatedExtensionEquiv :
    (Σ Q : RunSignature α,
      {e' : EnumeratingExtension α // RunCompatible Q e'}) ≃
        EnumeratingExtension α := by
  classical
  have hown (e : EnumeratingExtension α) :
      RunCompatible (⟨runRelation e, ⟨e, rfl⟩⟩ : RunSignature α) e := by
    intro x y hne hmem
    have hrun : runLE e x y := by simpa [runRelation] using hmem
    rcases hrun with hxy | hxy
    · exact False.elim (hne hxy)
    · by_contra hn
      have hrev : e.1.symm y ≤ e.1.symm x := le_of_not_gt hn
      have hmono : runIndex e (e.1.symm y) ≤
          runIndex e (e.1.symm x) := by
        unfold runIndex
        apply Finset.card_le_card
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact ⟨lt_of_lt_of_le hk.1 hrev, hk.2⟩
      exact (not_le_of_gt hxy) hmono
  refine {
    toFun := fun s => s.2.1
    invFun := fun e => ⟨⟨runRelation e, ⟨e, rfl⟩⟩, ⟨e, hown e⟩⟩
    right_inv := by intro e; rfl
    left_inv := ?_ }
  intro ⟨Q, ⟨e', hc⟩⟩
  obtain ⟨rep, hrep⟩ := Q.2
  have hcompat : ∀ x y : α,
      runIndex rep (rep.1.symm x) < runIndex rep (rep.1.symm y) →
        e'.1.symm x < e'.1.symm y := by
    intro x y hlt
    have hne : x ≠ y := by
      intro h
      subst y
      exact (Nat.lt_irrefl _) hlt
    apply hc x y hne
    rw [← hrep]
    simp only [runRelation, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr hlt
  have hrel : runRelation e' = Q.1 := by
    have hword := compatible_run_word rep e' hcompat
    have hrun := (compatible_run_index rep e' hcompat).1
    have heq (x y : α) : runLE e' x y ↔ runLE rep x y := by
      have hvertex (z : α) :
          runIndex e' (e'.1.symm z) = runIndex rep (rep.1.symm z) := by
        calc
          runIndex e' (e'.1.symm z) = runIndex rep (e'.1.symm z) := hrun _
          _ = runIndex rep (rep.1.symm (e' (e'.1.symm z))) :=
            (hword _).symm
          _ = runIndex rep (rep.1.symm z) := by simp
      simp only [runLE, hvertex x, hvertex y]
    calc
      runRelation e' = runRelation rep := by
        ext p
        rcases p with ⟨x, y⟩
        simpa [runRelation] using (heq x y)
      _ = Q.1 := hrep
  rcases Q with ⟨q, hq⟩
  dsimp at hrel
  subst q
  rfl

end
end D5.S3.Combinatorics.Posets.GradedGamma
