/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partitions into retained singletons and free pairs correspond bijectively to partial pairings. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs

/-! The combinatorial correspondence identifying the degree-zero collision terms. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- The labels in one quotient block of a partition of the positions. -/
def partitionLabelBlock {k : ℕ} (σ : Setoid (Fin k)) (B : Quotient σ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => Quotient.mk σ i = B)

private theorem mem_partitionLabelBlock {k : ℕ} (σ : Setoid (Fin k))
    (B : Quotient σ) (i : Fin k) :
    i ∈ partitionLabelBlock σ B ↔ Quotient.mk σ i = B := by
  simp [partitionLabelBlock]

/-- Distinct quotient blocks give distinct nonempty label fibers. -/
theorem partitionLabelBlock_injective {k : ℕ} (σ : Setoid (Fin k)) :
    Function.Injective (partitionLabelBlock σ) := by
  intro B D h
  have hi : B.out ∈ partitionLabelBlock σ B :=
    (mem_partitionLabelBlock σ B B.out).2 (Quotient.out_eq B)
  rw [h] at hi
  exact (Quotient.out_eq B).symm.trans ((mem_partitionLabelBlock σ D B.out).1 hi)

/-- A partition whose retained blocks are singletons and whose other blocks are pairs. -/
structure PairingPartitionData (k : ℕ) where
  partition : Setoid (Fin k)
  retained : Finset (Quotient partition)
  sizes : ∀ B, mult (Quotient.mk partition) B = if B ∈ retained then 1 else 2

/-- The free blocks of a degree-zero collision partition, regarded as unordered pairs. -/
def pairingPartitionPairs {k : ℕ} (D : PairingPartitionData k) : Finset (Finset (Fin k)) :=
  D.retainedᶜ.image (partitionLabelBlock D.partition)

/-- The free two-element blocks form a partial pairing. -/
theorem pairingPartitionPairs_isPartial {k : ℕ} (D : PairingPartitionData k) :
    IsPartialPairing Finset.univ (pairingPartitionPairs D) := by
  refine ⟨?_, ?_, Finset.subset_univ _⟩
  · intro e he
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp he
    change mult (Quotient.mk D.partition) B = 2
    simpa only [if_neg (Finset.mem_compl.mp hB)] using D.sizes B
  · intro e he d hd hed
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hd
    apply Finset.disjoint_left.mpr
    intro i hiB hiC
    have hBC : B = C := ((mem_partitionLabelBlock D.partition B i).1 hiB).symm.trans
      ((mem_partitionLabelBlock D.partition C i).1 hiC)
    exact hed (congrArg (partitionLabelBlock D.partition) hBC)

/-- The support of the partial pairing is exactly the positions in unretained blocks. -/
theorem pairingPartitionPairs_support {k : ℕ} (D : PairingPartitionData k) :
    pairingSupport (pairingPartitionPairs D) =
      Finset.univ.filter (fun i => Quotient.mk D.partition i ∉ D.retained) := by
  ext i
  simp only [pairingSupport, Finset.mem_biUnion, id_eq, pairingPartitionPairs,
    Finset.mem_image, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, ⟨B, hB, rfl⟩, hi⟩
    simpa only [(mem_partitionLabelBlock D.partition B i).1 hi] using hB
  · intro hi
    exact ⟨partitionLabelBlock D.partition (Quotient.mk D.partition i),
      ⟨Quotient.mk D.partition i, hi, rfl⟩,
      (mem_partitionLabelBlock D.partition _ i).2 rfl⟩

private theorem pairingPartition_relation {k : ℕ} (D : PairingPartitionData k)
    (i j : Fin k) :
    D.partition i j ↔ i = j ∨
      ∃ e ∈ pairingPartitionPairs D, i ∈ e ∧ j ∈ e := by
  constructor
  · intro hij
    have hq : Quotient.mk D.partition i = Quotient.mk D.partition j := Quotient.sound hij
    by_cases hi : i ∈ pairingSupport (pairingPartitionPairs D)
    · rw [pairingPartitionPairs_support] at hi
      have hB : Quotient.mk D.partition i ∉ D.retained := (Finset.mem_filter.mp hi).2
      exact Or.inr ⟨partitionLabelBlock D.partition (Quotient.mk D.partition i),
        Finset.mem_image.mpr ⟨_, Finset.mem_compl.mpr hB, rfl⟩,
        (mem_partitionLabelBlock D.partition _ i).2 rfl,
        (mem_partitionLabelBlock D.partition _ j).2 hq.symm⟩
    · have hB : Quotient.mk D.partition i ∈ D.retained := by
        by_contra hn
        apply hi
        rw [pairingPartitionPairs_support]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      have hcard : (partitionLabelBlock D.partition (Quotient.mk D.partition i)).card = 1 := by
        change mult (Quotient.mk D.partition) (Quotient.mk D.partition i) = 1
        simpa only [if_pos hB] using D.sizes (Quotient.mk D.partition i)
      exact Or.inl ((Finset.card_le_one.mp hcard.le) i
        ((mem_partitionLabelBlock D.partition _ i).2 rfl) j
        ((mem_partitionLabelBlock D.partition _ j).2 hq.symm))
  · rintro (rfl | ⟨e, he, hi, hj⟩)
    · exact D.partition.refl i
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp he
      exact Quotient.exact (((mem_partitionLabelBlock D.partition B i).1 hi).trans
        ((mem_partitionLabelBlock D.partition B j).1 hj).symm)

private theorem pairingPartitionPairs_injective {k : ℕ} :
    Function.Injective (pairingPartitionPairs (k := k)) := by
  intro D E h
  have hpart : D.partition = E.partition := by
    apply Setoid.ext
    intro i j
    rw [pairingPartition_relation, pairingPartition_relation, h]
  cases D with
  | mk σ S hs =>
    cases E with
    | mk τ T ht =>
      dsimp only at hpart
      subst τ
      have hST : S = T := by
        ext B
        have hS := hs B
        have hT := ht B
        by_cases hBS : B ∈ S <;> by_cases hBT : B ∈ T <;> simp_all
      subst T
      rfl

private def partialPairingSetoid {k : ℕ} (P : Finset (Finset (Fin k)))
    (hP : IsPartialPairing Finset.univ P) : Setoid (Fin k) where
  r i j := i = j ∨ ∃ e ∈ P, i ∈ e ∧ j ∈ e
  iseqv := ⟨fun i => Or.inl rfl, by
    rintro i j (hij | ⟨e, he, hi, hj⟩)
    · exact Or.inl hij.symm
    · exact Or.inr ⟨e, he, hj, hi⟩, by
    rintro i j l (rfl | ⟨e, he, hi, hj⟩) hjl
    · exact hjl
    rcases hjl with rfl | ⟨d, hd, hjd, hl⟩
    · exact Or.inr ⟨e, he, hi, hj⟩
    have hed : e = d := by
      by_contra hn
      exact Finset.disjoint_left.mp (hP.2.1 he hd hn) hj hjd
    subst d
    exact Or.inr ⟨e, he, hi, hl⟩⟩

private theorem partialPairingSetoid_block {k : ℕ} (P : Finset (Finset (Fin k)))
    (hP : IsPartialPairing Finset.univ P) (e : Finset (Fin k)) (he : e ∈ P)
    (i : Fin k) (hi : i ∈ e) :
    partitionLabelBlock (partialPairingSetoid P hP)
      (Quotient.mk (partialPairingSetoid P hP) i) = e := by
  ext j
  rw [mem_partitionLabelBlock]
  constructor
  · intro hji
    have hrel := Quotient.exact hji
    change j = i ∨ ∃ d ∈ P, j ∈ d ∧ i ∈ d at hrel
    rcases hrel with rfl | ⟨d, hd, hjd, hid⟩
    · exact hi
    · have hde : d = e := by
        by_contra hn
        exact Finset.disjoint_left.mp (hP.2.1 hd he hn) hid hi
      simpa only [hde] using hjd
  · intro hj
    exact Quotient.sound (Or.inr ⟨e, he, hj, hi⟩)

private theorem partialPairingSetoid_singleton {k : ℕ} (P : Finset (Finset (Fin k)))
    (hP : IsPartialPairing Finset.univ P) (i : Fin k)
    (hi : ¬ ∃ e ∈ P, i ∈ e) :
    partitionLabelBlock (partialPairingSetoid P hP)
      (Quotient.mk (partialPairingSetoid P hP) i) = {i} := by
  ext j
  rw [mem_partitionLabelBlock, Finset.mem_singleton]
  constructor
  · intro hji
    have hrel := Quotient.exact hji
    change j = i ∨ ∃ d ∈ P, j ∈ d ∧ i ∈ d at hrel
    rcases hrel with hji | ⟨d, hd, hjd, hid⟩
    · exact hji
    · exact (hi ⟨d, hd, hid⟩).elim
  · intro hji
    subst j
    rfl

private def partitionDataOfPairing {k : ℕ} (P : Finset (Finset (Fin k)))
    (hP : IsPartialPairing Finset.univ P) : PairingPartitionData k where
  partition := partialPairingSetoid P hP
  retained := Finset.univ.filter (fun B => mult (Quotient.mk (partialPairingSetoid P hP)) B = 1)
  sizes := by
    intro B
    have hout := Quotient.out_eq B
    by_cases hi : ∃ e ∈ P, B.out ∈ e
    · obtain ⟨e, he, hi⟩ := hi
      have hf := partialPairingSetoid_block P hP e he B.out hi
      rw [hout] at hf
      have hm : mult (Quotient.mk (partialPairingSetoid P hP)) B = 2 := by
        change (partitionLabelBlock (partialPairingSetoid P hP) B).card = 2
        rw [hf]
        exact hP.1 e he
      simp [hm]
    · have hf := partialPairingSetoid_singleton P hP B.out hi
      rw [hout] at hf
      have hm : mult (Quotient.mk (partialPairingSetoid P hP)) B = 1 := by
        change (partitionLabelBlock (partialPairingSetoid P hP) B).card = 1
        rw [hf]
        exact Finset.card_singleton _
      simp [hm]

private theorem pairingPartitionPairs_of_pairing {k : ℕ} (P : Finset (Finset (Fin k)))
    (hP : IsPartialPairing Finset.univ P) :
    pairingPartitionPairs (partitionDataOfPairing P hP) = P := by
  change ((Finset.univ.filter (fun B : Quotient (partialPairingSetoid P hP) =>
    mult (Quotient.mk (partialPairingSetoid P hP)) B = 1))ᶜ.image
      (partitionLabelBlock (partialPairingSetoid P hP))) = P
  ext e
  constructor
  · intro he
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp he
    have hn : mult (Quotient.mk (partialPairingSetoid P hP)) B ≠ 1 := by
      simpa only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using hB
    by_cases hi : ∃ d ∈ P, B.out ∈ d
    · obtain ⟨d, hd, hi⟩ := hi
      have hf := partialPairingSetoid_block P hP d hd B.out hi
      rw [Quotient.out_eq B] at hf
      simpa only [hf] using hd
    · have hf := partialPairingSetoid_singleton P hP B.out hi
      rw [Quotient.out_eq B] at hf
      exfalso
      apply hn
      change (partitionLabelBlock (partialPairingSetoid P hP) B).card = 1
      rw [hf]
      exact Finset.card_singleton _
  · intro he
    have hec : e.card = 2 := hP.1 e he
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
    have hf := partialPairingSetoid_block P hP e he i hi
    refine Finset.mem_image.mpr ⟨Quotient.mk (partialPairingSetoid P hP) i, ?_, hf⟩
    apply Finset.mem_compl.mpr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change mult (Quotient.mk (partialPairingSetoid P hP))
      (Quotient.mk (partialPairingSetoid P hP) i) ≠ 1
    change (partitionLabelBlock (partialPairingSetoid P hP)
      (Quotient.mk (partialPairingSetoid P hP) i)).card ≠ 1
    rw [hf, hec]
    decide

/-- Degree-zero collision partitions are in a cardinality-preserving bijection with
unordered partial pairings: every free block gives one edge and every uncovered label
gives one retained singleton. -/
theorem pairingPartitionPairs_bijective {k : ℕ} :
    Function.Bijective (fun D : PairingPartitionData k =>
      (⟨pairingPartitionPairs D, pairingPartitionPairs_isPartial D⟩ :
        {P : Finset (Finset (Fin k)) // IsPartialPairing Finset.univ P})) ∧
      ∀ D : PairingPartitionData k, (pairingPartitionPairs D).card = D.retainedᶜ.card := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro D E h
    exact pairingPartitionPairs_injective (congrArg Subtype.val h)
  · intro P
    refine ⟨partitionDataOfPairing P.val P.property, ?_⟩
    exact Subtype.ext (pairingPartitionPairs_of_pairing P.val P.property)
  · intro D
    exact Finset.card_image_of_injective D.retainedᶜ (partitionLabelBlock_injective D.partition)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
