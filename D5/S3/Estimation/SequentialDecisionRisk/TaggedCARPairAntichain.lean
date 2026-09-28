/- GID: D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-pair tagged CAR profiles form an antichain under common simulation. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds
import Mathlib.Order.Partition.Finpartition

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.TaggedCARPairAntichain

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds

variable {Q K : Type*} [Fintype Q] [Fintype K] [DecidableEq K]

/-- Only actual states are included; a missing fiber contributes no states. -/
abbrev ActualRow (A : Q → Finset K) := Σ q, {i : K // i ∈ A q}

/-- All nonempty subsets of each actual fiber, with their readout tags. -/
abbrev TaggedBlock (A : Q → Finset K) :=
  Σ q, {B : Finset K // B.Nonempty ∧ B ⊆ A q}

/-- Incidence includes the visible readout tag. -/
def occurs {A : Q → Finset K} (q : Q) (i : K) (B : TaggedBlock A) : Prop :=
  B.1 = q ∧ i ∈ B.2.1

open Classical in
/-- CAR imposes normalization only on actual rows, including zero weight letters. -/
structure CARProfile (A : Q → Finset K) where
  weight : TaggedBlock A → ℝ
  nonneg : ∀ B, 0 ≤ weight B
  mass : ∀ q i, i ∈ A q → (∑ B, if occurs q i B then weight B else 0) = 1

open Classical in
/-- The literal row on the entire tagged output alphabet. -/
def row {A : Q → Finset K} (w : CARProfile A) (s : ActualRow A)
    (B : TaggedBlock A) : ℝ :=
  if occurs s.1 s.2.1 B then w.weight B else 0

open Classical in
/-- Contributions from other tags vanish, so this is the sum over blocks of `A q`. -/
def pairMass {A : Q → Finset K} (w : CARProfile A) (q : Q) (i j : K) : ℝ :=
  ∑ B, if occurs q i B ∧ occurs q j B then w.weight B else 0

/-- Restrict the same random global partition to every actual fiber. This is the
linear image of its probability law, with the CAR equations proved internally.
The family may in particular be all partitions sufficient for a fixed target.
No converse from arbitrary CAR profiles to such partition laws is asserted. -/
def partitionProfile {R : Type*} [Fintype R] (A : Q → Finset K)
    (P : R → Finpartition (Finset.univ : Finset K))
    (p : R → ℝ) (hp : ∀ r, 0 ≤ p r) (hsum : ∑ r, p r = 1) : CARProfile A := by
  classical
  let localP (r : R) (q : Q) : Finpartition (A q) :=
    (P r).restrict (Finset.subset_univ (A q))
  refine ⟨(fun B => ∑ r, if B.2.1 ∈ (localP r B.1).parts then p r else 0), ?_, ?_⟩
  · intro B
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> first | exact hp r | exact le_rfl
  · intro q i hi
    calc
      (∑ B : TaggedBlock A, if occurs q i B then
          ∑ r, if B.2.1 ∈ (localP r B.1).parts then p r else 0 else 0) =
          ∑ r, ∑ B : TaggedBlock A,
            if occurs q i B ∧ B.2.1 ∈ (localP r B.1).parts then p r else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro B _
        by_cases h : occurs q i B <;> simp [h]
      _ = ∑ r, p r := by
        apply Finset.sum_congr rfl
        intro r _
        let D : TaggedBlock A := ⟨q, ⟨(localP r q).part i,
          (localP r q).part_nonempty.mpr hi, (localP r q).part_subset i⟩⟩
        have hiD : occurs q i D := ⟨rfl, (localP r q).mem_part hi⟩
        have hD : D.2.1 ∈ (localP r D.1).parts := (localP r q).part_mem.mpr hi
        rw [Finset.sum_eq_single D]
        · simp [hiD, hD]
        · intro B _ hB
          apply if_neg
          rintro ⟨hinc, hpart⟩
          apply hB
          rcases B with ⟨q', B, hB'⟩
          change q' = q ∧ i ∈ B at hinc
          obtain ⟨hq, hiB⟩ := hinc
          subst q'
          have heq : (localP r q).part i = B :=
            (localP r q).part_eq_of_mem hpart hiB
          exact congrArg (Sigma.mk q) (Subtype.ext heq.symm)
        · simp
      _ = 1 := hsum

/-- One unrestricted common stochastic simulator and equal within-fiber pair masses
force equality on every tagged block. Neither tag preservation nor subset support
is imposed on the simulator, including its zero weight input rows. -/
theorem equal_weights_of_common_simulator
    (A : Q → Finset K) (w v : CARProfile A)
    (H : FiniteMarkovKernel (TaggedBlock A) (TaggedBlock A))
    (simulation : ∀ s : ActualRow A, ∀ C,
      channelOutput H.1 (row w s) C = row v s C)
    (pairs : ∀ q i j, i ∈ A q → j ∈ A q → i ≠ j →
      pairMass w q i j = pairMass v q i j) :
    w.weight = v.weight := by
  classical
  let f : TaggedBlock A → TaggedBlock A → ℝ := fun B C => w.weight B * H.1 B C
  have nonnegative (B C : TaggedBlock A) : 0 ≤ f B C :=
    mul_nonneg (w.nonneg B) (H.2.1 B C)
  have rowmass (B : TaggedBlock A) : ∑ C, f B C = w.weight B := by
    simp only [f, ← Finset.mul_sum, H.2.2 B, mul_one]
  have column (q : Q) (i : K) (hi : i ∈ A q) (C : TaggedBlock A) :
      (∑ B, if occurs q i B then f B C else 0) =
        if occurs q i C then v.weight C else 0 := by
    simpa only [channelOutput, row, ite_mul, zero_mul] using
      simulation ⟨q, ⟨i, hi⟩⟩ C
  have forbidden (B C : TaggedBlock A) (i : K) (hi : i ∈ B.2.1)
      (hn : ¬ occurs B.1 i C) : f B C = 0 := by
    have h := column B.1 i (B.2.2.2 hi) C
    rw [if_neg hn] at h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun D (_ : D ∈ Finset.univ) =>
        show 0 ≤ (if occurs B.1 i D then f D C else 0) from
          by split_ifs <;> first | exact nonnegative D C | exact le_rfl)).mp h
        B (Finset.mem_univ B)
    simpa [occurs, hi] using hterm
  have support (B C : TaggedBlock A) (hf : f B C ≠ 0) :
      B.1 = C.1 ∧ B.2.1 ⊆ C.2.1 := by
    constructor
    · obtain ⟨i, hi⟩ := B.2.2.1
      by_contra hn
      exact hf (forbidden B C i hi (fun h => hn h.1.symm))
    · intro i hi
      by_contra hn
      exact hf (forbidden B C i hi (fun h => hn h.2))
  have preserves (q : Q) (i : K) (B C : TaggedBlock A)
      (hf : f B C ≠ 0) (hi : occurs q i B) : occurs q i C :=
    ⟨(support B C hf).1.symm.trans hi.1, (support B C hf).2 hi.2⟩
  let deficit (q : Q) (i j : K) (B C : TaggedBlock A) : ℝ :=
    if occurs q i B ∧ ¬ occurs q j B ∧ occurs q i C ∧ occurs q j C ∧
        B.2.1 ⊆ C.2.1 then f B C else 0
  have deficit_nonneg (q : Q) (i j : K) (B C : TaggedBlock A) :
      0 ≤ deficit q i j B C := by
    dsimp [deficit]
    split_ifs <;> first | exact nonnegative B C | exact le_rfl
  have pair_difference (q : Q) (i j : K) (hi : i ∈ A q) :
      pairMass v q i j - pairMass w q i j = ∑ C, ∑ B, deficit q i j B C := by
    have target : pairMass v q i j =
        ∑ C, ∑ B, if occurs q i B ∧ occurs q j C then f B C else 0 := by
      unfold pairMass
      apply Finset.sum_congr rfl
      intro C _
      by_cases hj : occurs q j C
      · simpa only [hj, and_true] using (column q i hi C).symm
      · simp [hj]
    have source : pairMass w q i j =
        ∑ C, ∑ B, if occurs q i B ∧ occurs q j B then f B C else 0 := by
      rw [Finset.sum_comm]
      unfold pairMass
      apply Finset.sum_congr rfl
      intro B _
      by_cases h : occurs q i B ∧ occurs q j B
      · simp [h, rowmass]
      · simp [h]
    rw [target, source, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro B _
    by_cases hz : f B C = 0
    · simp [hz, deficit]
    have hBC := (support B C hz).2
    by_cases hb : occurs q i B
    · have hc := preserves q i B C hz hb
      by_cases hb' : occurs q j B
      · have hc' := preserves q j B C hz hb'
        simp [deficit, hb, hb', hc, hc', hBC]
      · by_cases hc' : occurs q j C <;>
          simp [deficit, hb, hb', hc, hc', hBC]
    · simp [deficit, hb]
  have diagonal (B C : TaggedBlock A) (hne : B ≠ C) : f B C = 0 := by
    by_contra hf
    obtain ⟨htag, hsub⟩ := support B C hf
    have hsets : B.2.1 ≠ C.2.1 := by
      intro heq
      apply hne
      rcases B with ⟨bq, B, hb⟩
      rcases C with ⟨cq, C, hc⟩
      dsimp at htag heq
      subst cq
      subst C
      rfl
    obtain ⟨i, hi⟩ := B.2.2.1
    obtain ⟨j, hj, hj'⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hsets)
    have hij : i ≠ j := by rintro rfl; exact hj' hi
    have hjA : j ∈ A B.1 := by rw [htag]; exact C.2.2.2 hj
    have zero_fixed : (∑ D, ∑ E, deficit B.1 i j E D) = 0 := by
      rw [← pair_difference B.1 i j (B.2.2.2 hi),
        ← pairs B.1 i j (B.2.2.2 hi) hjA hij, sub_self]
    have zC := (Finset.sum_eq_zero_iff_of_nonneg
      (fun D (_ : D ∈ Finset.univ) => Finset.sum_nonneg
        (fun E _ => deficit_nonneg B.1 i j E D))).mp zero_fixed C (Finset.mem_univ C)
    have zB := (Finset.sum_eq_zero_iff_of_nonneg
      (fun E (_ : E ∈ Finset.univ) => deficit_nonneg B.1 i j E C)).mp
        zC B (Finset.mem_univ B)
    exact hf (by simpa [deficit, occurs, hi, hj, hj', htag, hsub, hsub hi] using zB)
  funext C
  obtain ⟨i, hi⟩ := C.2.2.1
  have hw : w.weight C = f C C := by
    rw [← rowmass C]
    apply Finset.sum_eq_single C
    · intro D _ hD
      exact diagonal C D (Ne.symm hD)
    · simp
  have hv := column C.1 i (C.2.2.2 hi) C
  have hsum : (∑ B, if occurs C.1 i B then f B C else 0) = f C C := by
    rw [Finset.sum_eq_single C]
    · simp [occurs, hi]
    · intro B _ hB
      rw [diagonal B C hB]
      simp
    · simp
  rw [hsum, if_pos (show occurs C.1 i C from ⟨rfl, hi⟩)] at hv
  exact hw.trans hv

#print axioms equal_weights_of_common_simulator
#print axioms partitionProfile

end D5.S3.Estimation.SequentialDecisionRisk.TaggedCARPairAntichain
