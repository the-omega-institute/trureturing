/- GID: D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   generality: G
   mirror-B: D5/B/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition, mathlib/module/Mathlib.Data.Fintype.BigOperators, mathlib/module/Mathlib.Data.Fintype.Perm, mathlib/module/Mathlib.Algebra.Ring.Parity]
   utility: none
   digest: Marked set partitions and the odd-even mixed-block product conjecture. -/
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Parity
namespace D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
open Finset
/-- Set partitions of an `r`-element labelled set. -/
abbrev SetPartition (r : ℕ) := Finpartition (univ : Finset (Fin r))
/-- Stirling numbers of the second kind, defined by their partition cardinality. -/
def stirling2 (r i : ℕ) : ℕ := Fintype.card {P : SetPartition r // P.parts.card = i}
/-- A set partition together with exactly `k` distinguished blocks. -/
abbrev MarkedPartition (r k : ℕ) := Σ P : SetPartition r, {M : Finset P.parts // M.card = k}
/-- The number of partitions of an `r`-set with exactly `k` distinguished blocks. -/
def markedPartitions (r k : ℕ) : ℕ := Fintype.card (MarkedPartition r k)
/-- OEIS A049020 in its Stirling-number form. -/
def A049020 (r k : ℕ) : ℕ := ∑ i ∈ range (r + 1), stirling2 r i * i.choose k
/-- Marking `k` blocks after partitioning gives the Stirling-binomial formula for A049020. -/
theorem markedPartitions_eq_A049020 (r k : ℕ) : markedPartitions r k = A049020 r k := by
  classical rw [markedPartitions, A049020]
  change Fintype.card (Σ P : SetPartition r, {M : Finset P.parts // M.card = k}) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_finset_len]
  simp_rw [Fintype.card_coe]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (SetPartition r))) (t := range (r + 1)) (g := fun P : SetPartition r => P.parts.card) (f := fun P : SetPartition r => P.parts.card.choose k)]
  · apply sum_congr rfl
    intro i hi
    calc
      ∑ P : SetPartition r with P.parts.card = i, P.parts.card.choose k = ((univ.filter fun P : SetPartition r => P.parts.card = i).card) * i.choose k := by
            apply Finset.sum_const_nat
            intro P hP
            rw [(mem_filter.mp hP).2]
      _ = stirling2 r i * i.choose k := by congr 1; simp [stirling2, Fintype.card_subtype]
  · intro P _
    rw [mem_range]; exact Nat.lt_succ_of_le (by simpa using P.card_parts_le_card)
/-- The canonical `n`-element parity-labelled set: the left summand labels odd entries. -/
abbrev ParityIndex (n : ℕ) := Fin ((n + 1) / 2) ⊕ Fin (n / 2)
/-- A block after `Finset.sumEquiv`: its coordinates are the odd and even restrictions. -/
abbrev ParityBlock (n : ℕ) := Finset (Fin ((n + 1) / 2)) × Finset (Fin (n / 2))
/-- Parity-labelled partitions transported by `Finset.sumEquiv` to the product lattice. -/
abbrev ParityPartition (n : ℕ) := Finpartition ((univ : Finset (Fin ((n + 1) / 2))), (univ : Finset (Fin (n / 2))))
/-- A block is mixed when it contains both an odd-labelled and an even-labelled entry. -/
def IsMixedBlock {n : ℕ} (b : ParityBlock n) : Prop := b.1.Nonempty ∧ b.2.Nonempty
/-- Number of odd-even mixed blocks in a parity-labelled set partition. -/
noncomputable def mixedBlockCount {n : ℕ} (P : ParityPartition n) : ℕ := by classical exact (P.parts.filter IsMixedBlock).card
/-- Partitions of `[n]` having exactly `k` odd-even mixed blocks. -/
abbrev MixedParityPartition (n k : ℕ) := {P : ParityPartition n // mixedBlockCount P = k}
/-- OEIS A124418's `T(n,k)`, defined as the cardinality in its `%N` line. -/
noncomputable def T (n k : ℕ) : ℕ := Fintype.card (MixedParityPartition n k)
/-- A block of `Fin n` is mixed when `x : Fin n` represents `x.val + 1 ∈ {1, ..., n}`. -/ def IsMixedBlockFin {n : ℕ} (b : Finset (Fin n)) : Prop := (∃ x ∈ b, Odd (x.val + 1)) ∧ (∃ x ∈ b, Even (x.val + 1))
/-- The literal `%N` object: partitions of `{1, ..., n}` with `k` mixed blocks. -/ noncomputable def Tfin (n k : ℕ) : ℕ := by classical exact Fintype.card {P : Finpartition (univ : Finset (Fin n)) // (P.parts.filter IsMixedBlockFin).card = k}
/-- The parity-split model `T` is identical to the literal `Fin n` model `Tfin`. -/ theorem T_eq_Tfin (n k : ℕ) : T n k = Tfin n k := by classical
  let e : Fin n ≃ ParityIndex n := {
    toFun := fun x => if h : Even x.val then Sum.inl ⟨x.val / 2, by rw [Nat.even_iff] at h; omega⟩ else Sum.inr ⟨x.val / 2, by rw [Nat.even_iff] at h; omega⟩
    invFun := fun x => match x with | Sum.inl i => ⟨2 * i.val, by omega⟩ | Sum.inr i => ⟨2 * i.val + 1, by omega⟩
    left_inv := by
      intro x
      by_cases h : Even x.val
      · simp only [h, ↓reduceDIte]; apply Fin.ext; simpa [mul_comm] using Nat.div_two_mul_two_of_even h
      · simp only [h, ↓reduceDIte]; apply Fin.ext; exact Nat.two_mul_div_two_add_one_of_odd (Nat.not_even_iff_odd.mp h)
    right_inv := by
      intro x
      rcases x with i | i
      · simp
      · simp; apply Fin.ext; show (2 * i.val + 1) / 2 = i.val; exact (by rw [Nat.add_comm, Nat.add_mul_div_left, Nat.div_eq_of_lt] <;> omega) }
  let ef : Finset (Fin n) ≃o Finset (ParityIndex n) := { toFun := fun b => b.map e.toEmbedding, invFun := fun b => b.map e.symm.toEmbedding, left_inv := by intro b; simp [Finset.map_map], right_inv := by intro b; simp [Finset.map_map], map_rel_iff' := by simp }; let es : Finset (Fin n) ≃o ParityBlock n := ef.trans Finset.sumEquiv
  let ep : Finpartition (univ : Finset (Fin n)) ≃ ParityPartition n := { toFun := fun P => (P.map es).copy (by apply Prod.ext <;> simp [es, ef]), invFun := fun P => (P.map es.symm).copy (by simp [es, ef]), left_inv := by intro P; apply Finpartition.ext; change es.toEquiv.finsetCongr.invFun (es.toEquiv.finsetCongr.toFun P.parts) = P.parts; exact es.toEquiv.finsetCongr.left_inv P.parts, right_inv := by intro P; apply Finpartition.ext; change es.toEquiv.finsetCongr.toFun (es.toEquiv.finsetCongr.invFun P.parts) = P.parts; exact es.toEquiv.finsetCongr.right_inv P.parts }
  have mixed_iff (b : Finset (Fin n)) : IsMixedBlock (es b) ↔ IsMixedBlockFin b := by
    simp only [IsMixedBlock, IsMixedBlockFin, es, ef, OrderIso.trans_apply, Finset.sumEquiv_apply_fst, Finset.sumEquiv_apply_snd]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rw [Finset.mem_toLeft] at hi; rw [Finset.mem_toRight] at hj; change Sum.inl i ∈ b.map e.toEmbedding at hi; change Sum.inr j ∈ b.map e.toEmbedding at hj; obtain ⟨x, hx, hxi⟩ := Finset.mem_map.mp hi; obtain ⟨y, hy, hyj⟩ := Finset.mem_map.mp hj; have he : Even x.val := (by by_contra h; simp [e, h] at hxi); have ho : Odd y.val := (by by_contra h; have he' : Even y.val := Nat.not_odd_iff_even.mp h; simp [e, he'] at hyj); exact ⟨⟨x, hx, he.add_one⟩, ⟨y, hy, ho.add_one⟩⟩
    · rintro ⟨⟨x, hx, hxo⟩, ⟨y, hy, hye⟩⟩; have hxe : Even x.val := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hxo); have hyo : Odd y.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hye); exact ⟨⟨⟨x.val / 2, by rw [Nat.even_iff] at hxe; omega⟩, by rw [Finset.mem_toLeft]; change Sum.inl ⟨x.val / 2, _⟩ ∈ b.map e.toEmbedding; exact Finset.mem_map.mpr ⟨x, hx, by simp [e, hxe]⟩⟩, ⟨⟨y.val / 2, by rw [Nat.odd_iff] at hyo; omega⟩, by rw [Finset.mem_toRight]; change Sum.inr ⟨y.val / 2, _⟩ ∈ b.map e.toEmbedding; exact Finset.mem_map.mpr ⟨y, hy, by simp [e, Nat.not_even_iff_odd.mpr hyo]⟩⟩⟩
  have count_eq (P : Finpartition (univ : Finset (Fin n))) : mixedBlockCount (ep P) = (P.parts.filter IsMixedBlockFin).card := by rw [mixedBlockCount]; change ((P.parts.map es.toEmbedding).filter IsMixedBlock).card = _; rw [Finset.filter_map, Finset.card_map]; congr 1; ext b; simp only [Finset.mem_filter]; exact and_congr_right (fun _ => mixed_iff b)
  let E : MixedParityPartition n k ≃ {P : Finpartition (univ : Finset (Fin n)) // (P.parts.filter IsMixedBlockFin).card = k} := { toFun := fun P => ⟨ep.symm P.1, by rw [← count_eq]; simpa using P.2⟩, invFun := fun P => ⟨ep P.1, by simpa [count_eq] using P.2⟩, left_inv := by intro P; apply Subtype.ext; simp, right_inv := by intro P; apply Subtype.ext; simp }; exact Fintype.card_congr E
/-- The marked blocks carried by a marked partition. -/
abbrev MarkedBlocks {r k : ℕ} (P : MarkedPartition r k) := P.2.1
/-- Restrict to odd and even entries, mark the mixed-derived blocks, and pair their halves. -/
abbrev RestrictionPairingData (n k : ℕ) := Σ odd : MarkedPartition ((n + 1) / 2) k, Σ even : MarkedPartition (n / 2) k, MarkedBlocks odd ≃ MarkedBlocks even
private noncomputable def leftRestriction {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : Finpartition (univ : Finset α) := by
  refine Finpartition.ofExistsUnique ((P.parts.image Prod.fst).erase ∅) (by simp) ?_ (by simp)
  intro a _
  have hsup : P.parts.sup Prod.fst = (univ : Finset α) := by
    simpa using P.sup_parts_apply (fun _ _ => rfl) rfl
  have ha : a ∈ P.parts.sup Prod.fst := by simp [hsup]
  obtain ⟨q, hq, haq⟩ := Finset.mem_sup.mp ha
  refine ⟨q.1, ⟨Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp ⟨a, haq⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩, haq⟩, ?_⟩
  rintro t ⟨ht, hat⟩
  have htimage : t ∈ P.parts.image Prod.fst := (Finset.mem_erase.mp ht).2
  obtain ⟨r, hr, hrt⟩ := Finset.mem_image.mp htimage
  subst t
  have hqr : q = r := by
    by_contra hne
    have hd := P.disjoint hq hr hne
    change Disjoint q r at hd
    rw [Prod.disjoint_iff] at hd; exact (Finset.not_disjoint_iff.mpr ⟨a, haq, hat⟩) hd.1
  exact (congrArg Prod.fst hqr).symm
private noncomputable def rightRestriction {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : Finpartition (univ : Finset β) := by
  refine Finpartition.ofExistsUnique ((P.parts.image Prod.snd).erase ∅) (by simp) ?_ (by simp)
  intro b _
  have hsup : P.parts.sup Prod.snd = (univ : Finset β) := by
    simpa using P.sup_parts_apply (fun _ _ => rfl) rfl
  have hb : b ∈ P.parts.sup Prod.snd := by simp [hsup]
  obtain ⟨q, hq, hbq⟩ := Finset.mem_sup.mp hb
  refine ⟨q.2, ⟨Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp ⟨b, hbq⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩, hbq⟩, ?_⟩
  rintro t ⟨ht, hbt⟩
  have htimage : t ∈ P.parts.image Prod.snd := (Finset.mem_erase.mp ht).2
  obtain ⟨r, hr, hrt⟩ := Finset.mem_image.mp htimage
  subst t
  have hqr : q = r := by
    by_contra hne
    have hd := P.disjoint hq hr hne
    change Disjoint q r at hd
    rw [Prod.disjoint_iff] at hd; exact (Finset.not_disjoint_iff.mpr ⟨b, hbq, hbt⟩) hd.2
  exact (congrArg Prod.snd hqr).symm
private def mixedParts {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (P : Finpartition (s, t)) : Finset (Finset α × Finset β) := P.parts.filter fun p => p.1.Nonempty ∧ p.2.Nonempty
private noncomputable def mixedToLeftEmbedding {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : {p // p ∈ mixedParts P} ↪ (leftRestriction P).parts where
  toFun p := ⟨p.1.1, by
    change p.1.1 ∈ (P.parts.image Prod.fst).erase ∅
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp p.2).2.1.ne_empty, Finset.mem_image.mpr ⟨p.1, (Finset.mem_filter.mp p.2).1, rfl⟩⟩⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hpq : p.1.1 = q.1.1 := congrArg Subtype.val h
    by_contra hpq'
    have hd := P.disjoint (Finset.mem_filter.mp p.2).1 (Finset.mem_filter.mp q.2).1 hpq'
    change Disjoint p.1 q.1 at hd
    rw [Prod.disjoint_iff] at hd
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp p.2).2.1
    exact (Finset.not_disjoint_iff.mpr ⟨a, ha, hpq ▸ ha⟩) hd.1
private noncomputable def mixedToRightEmbedding {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : {p // p ∈ mixedParts P} ↪ (rightRestriction P).parts where
  toFun p := ⟨p.1.2, by
    change p.1.2 ∈ (P.parts.image Prod.snd).erase ∅
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp p.2).2.2.ne_empty, Finset.mem_image.mpr ⟨p.1, (Finset.mem_filter.mp p.2).1, rfl⟩⟩⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hpq : p.1.2 = q.1.2 := congrArg Subtype.val h
    by_contra hpq'
    have hd := P.disjoint (Finset.mem_filter.mp p.2).1 (Finset.mem_filter.mp q.2).1 hpq'
    change Disjoint p.1 q.1 at hd
    rw [Prod.disjoint_iff] at hd
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp p.2).2.2
    exact (Finset.not_disjoint_iff.mpr ⟨b, hb, hpq ▸ hb⟩) hd.2
private noncomputable def leftMarkedParts {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : Finset (leftRestriction P).parts := (mixedParts P).attach.map (mixedToLeftEmbedding P)
private noncomputable def rightMarkedParts {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : Finset (rightRestriction P).parts := (mixedParts P).attach.map (mixedToRightEmbedding P)
private noncomputable def mixedLeftEquiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : {p // p ∈ mixedParts P} ≃ {b // b ∈ leftMarkedParts P} := Equiv.ofBijective (fun p => ⟨mixedToLeftEmbedding P p, by simp [leftMarkedParts]⟩)
    ⟨fun _ _ h => (mixedToLeftEmbedding P).injective (congrArg Subtype.val h), by
      intro b
      obtain ⟨p, hp, hpb⟩ := Finset.mem_map.mp b.2
      exact ⟨p, Subtype.ext hpb⟩⟩
private noncomputable def mixedRightEquiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (P : Finpartition ((univ : Finset α), (univ : Finset β))) : {p // p ∈ mixedParts P} ≃ {b // b ∈ rightMarkedParts P} := Equiv.ofBijective (fun p => ⟨mixedToRightEmbedding P p, by simp [rightMarkedParts]⟩)
    ⟨fun _ _ h => (mixedToRightEmbedding P).injective (congrArg Subtype.val h), by
      intro b
      obtain ⟨p, hp, hpb⟩ := Finset.mem_map.mp b.2
      exact ⟨p, Subtype.ext hpb⟩⟩
private noncomputable def leftMarkedPartition {n k : ℕ} (P : MixedParityPartition n k) : MarkedPartition ((n + 1) / 2) k := by
  classical
  refine ⟨leftRestriction P.1, leftMarkedParts P.1, ?_⟩
  ·
    rw [leftMarkedParts, Finset.card_map, Finset.card_attach]
    have hm : mixedParts P.1 = P.1.parts.filter IsMixedBlock := by
      ext p
      simp only [mixedParts, Finset.mem_filter]
      change (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty) ↔ (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty)
      rfl
    rw [hm]; exact P.2
private noncomputable def rightMarkedPartition {n k : ℕ} (P : MixedParityPartition n k) : MarkedPartition (n / 2) k := by
  classical
  refine ⟨rightRestriction P.1, rightMarkedParts P.1, ?_⟩
  ·
    rw [rightMarkedParts, Finset.card_map, Finset.card_attach]
    have hm : mixedParts P.1 = P.1.parts.filter IsMixedBlock := by
      ext p
      simp only [mixedParts, Finset.mem_filter]
      change (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty) ↔ (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty)
      rfl
    rw [hm]; exact P.2
private noncomputable def restrictionData {n k : ℕ} (P : MixedParityPartition n k) : RestrictionPairingData n k := ⟨leftMarkedPartition P, rightMarkedPartition P, (mixedLeftEquiv P.1).symm.trans (mixedRightEquiv P.1)⟩
private noncomputable def markedValues {α : Type*} [Fintype α] [DecidableEq α]
    {P : Finpartition (univ : Finset α)} (M : Finset P.parts) : Finset (Finset α) := M.image Subtype.val
private noncomputable def gluedSumParts {n k : ℕ} (D : RestrictionPairingData n k) : Finset (Finset (ParityIndex n)) := ((D.1.1.parts \ markedValues D.1.2.1).image fun b => b.disjSum ∅) ∪ (((D.2.1.1.parts \ markedValues D.2.1.2.1).image fun b => (∅ : Finset _).disjSum b) ∪
      D.1.2.1.attach.image fun b => b.1.1.disjSum (D.2.2 b).1.1)
private noncomputable def gluedSumPartition {n k : ℕ} (D : RestrictionPairingData n k) : Finpartition (univ : Finset (ParityIndex n)) := by
  classical
  refine Finpartition.ofExistsUnique (gluedSumParts D) (by simp) ?_ ?_
  · intro x _
    cases x with
    | inl a =>
        let ob : D.1.1.parts := ⟨D.1.1.part a, by simp⟩
        by_cases hm : ob ∈ D.1.2.1
        · let block := ob.1.disjSum (D.2.2 ⟨ob, hm⟩).1.1
          refine ⟨block, ⟨?_, by simp [block, ob]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right; right; exact Finset.mem_image.mpr ⟨⟨ob, hm⟩, by simp, rfl⟩
          · rintro t ⟨ht, hat⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              have hap : a ∈ p := by simpa using hat
              have hpo : p = ob.1 := (D.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hap).symm
              exfalso; apply (Finset.mem_sdiff.mp hp).2
              exact Finset.mem_image.mpr ⟨ob, hm, hpo.symm⟩
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              simp at hat
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hap : a ∈ p.1.1 := by simpa using hat
              have hpo : p.1.1 = ob.1 := (D.1.1.part_eq_of_mem p.1.2 hap).symm
              have hpe : p = (⟨ob, hm⟩ : MarkedBlocks D.1) := by
                apply Subtype.ext; apply Subtype.ext; exact hpo
              subst p
              rfl
        · let block := ob.1.disjSum (∅ : Finset (Fin (n / 2)))
          refine ⟨block, ⟨?_, by simp [block, ob]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            left; apply Finset.mem_image.mpr
            exact ⟨ob.1, Finset.mem_sdiff.mpr ⟨ob.2, by
              intro hv
              obtain ⟨p, hp, hpo⟩ := Finset.mem_image.mp hv
              apply hm
              have hpeq : p = ob := Subtype.ext hpo
              simpa [hpeq] using hp⟩, rfl⟩
          · rintro t ⟨ht, hat⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              have hap : a ∈ p := by simpa using hat
              have hpo : p = ob.1 := (D.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hap).symm
              simp [block, hpo]
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              simp at hat
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hap : a ∈ p.1.1 := by simpa using hat
              have hpo : p.1.1 = ob.1 := (D.1.1.part_eq_of_mem p.1.2 hap).symm
              exfalso; apply hm
              have hpob : p.1 = ob := Subtype.ext hpo
              simpa [hpob] using p.2
    | inr b =>
        let eb : D.2.1.1.parts := ⟨D.2.1.1.part b, by simp⟩
        by_cases hm : eb ∈ D.2.1.2.1
        · let pre : MarkedBlocks D.1 := D.2.2.symm ⟨eb, hm⟩
          let block := pre.1.1.disjSum eb.1
          refine ⟨block, ⟨?_, by simp [block, eb]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right; right; exact Finset.mem_image.mpr ⟨pre, by simp, by simp [block, pre]⟩
          · rintro t ⟨ht, hbt⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              simp at hbt
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              have hbp : b ∈ p := by simpa using hbt
              have hpe : p = eb.1 := (D.2.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hbp).symm
              exfalso; apply (Finset.mem_sdiff.mp hp).2
              exact Finset.mem_image.mpr ⟨eb, hm, hpe.symm⟩
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hbp : b ∈ (D.2.2 p).1.1 := by simpa using hbt
              have hpe : (D.2.2 p).1.1 = eb.1 := (D.2.1.1.part_eq_of_mem (D.2.2 p).1.2 hbp).symm
              have hpeq : D.2.2 p = (⟨eb, hm⟩ : MarkedBlocks D.2.1) := by
                apply Subtype.ext; apply Subtype.ext; exact hpe
              have hp : p = pre := by
                apply D.2.2.injective; simpa [pre] using hpeq
              subst p
              simp [block, pre]
        · let block := (∅ : Finset (Fin ((n + 1) / 2))).disjSum eb.1
          refine ⟨block, ⟨?_, by simp [block, eb]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right; left; apply Finset.mem_image.mpr
            exact ⟨eb.1, Finset.mem_sdiff.mpr ⟨eb.2, by
              intro hv
              obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hv
              apply hm
              have hpeq : p = eb := Subtype.ext hpe
              simpa [hpeq] using hp⟩, rfl⟩
          · rintro t ⟨ht, hbt⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              simp at hbt
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              have hbp : b ∈ p := by simpa using hbt
              have hpe : p = eb.1 := (D.2.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hbp).symm
              simp [block, hpe]
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hbp : b ∈ (D.2.2 p).1.1 := by simpa using hbt
              have hpe : (D.2.2 p).1.1 = eb.1 := (D.2.1.1.part_eq_of_mem (D.2.2 p).1.2 hbp).symm
              exfalso; apply hm
              have heq : (D.2.2 p).1 = eb := Subtype.ext hpe
              simpa [heq] using (D.2.2 p).2
  · simp only [gluedSumParts, Finset.mem_union]
    rintro h
    rcases h with hodd | heven | hmixed
    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp hodd
      have hpe : p = ∅ := (Finset.disjSum_eq_empty.mp h).1
      have hempty : (∅ : Finset (Fin ((n + 1) / 2))) ∈ D.1.1.parts := by
        rw [← hpe]; exact (Finset.mem_sdiff.mp hp).1
      exact D.1.1.bot_notMem hempty
    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp heven
      have hpe : p = ∅ := (Finset.disjSum_eq_empty.mp h).2
      have hempty : (∅ : Finset (Fin (n / 2))) ∈ D.2.1.1.parts := by
        rw [← hpe]; exact (Finset.mem_sdiff.mp hp).1
      exact D.2.1.1.bot_notMem hempty
    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp hmixed
      have hpe : p.1.1 = ∅ := (Finset.disjSum_eq_empty.mp h).1
      have hempty : (∅ : Finset (Fin ((n + 1) / 2))) ∈ D.1.1.parts := by
        rw [← hpe]; exact p.1.2
      exact D.1.1.bot_notMem hempty
private noncomputable def gluedPartition {n k : ℕ} (D : RestrictionPairingData n k) : ParityPartition n := ((gluedSumPartition D).map Finset.sumEquiv).copy (by
    apply Prod.ext <;> simp)
private noncomputable def gluedMixedEmbedding {n k : ℕ} (D : RestrictionPairingData n k) : MarkedBlocks D.1 ↪ ParityBlock n where
  toFun b := (b.1.1, (D.2.2 b).1.1)
  inj' := by
    intro p q h
    apply Subtype.ext; apply Subtype.ext; exact congrArg Prod.fst h
private theorem glued_mixed_parts {n k : ℕ} (D : RestrictionPairingData n k) : mixedParts (gluedPartition D) = D.1.2.1.attach.map (gluedMixedEmbedding D) := by
  classical
  ext p
  simp only [mixedParts, gluedPartition, Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨b, hb, hbp⟩, hp⟩
    subst p
    simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts] at hb
    simp only [gluedSumParts, Finset.mem_union] at hb
    rcases hb with hodd | heven | hmixed
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hodd
      have hp' := hp.2
      change (a.disjSum (∅ : Finset (Fin (n / 2)))).toRight.Nonempty at hp'
      rw [Finset.toRight_disjSum] at hp'; exact (Finset.not_nonempty_empty hp').elim
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp heven
      have hp' := hp.1
      change ((∅ : Finset (Fin ((n + 1) / 2))).disjSum a).toLeft.Nonempty at hp'
      rw [Finset.toLeft_disjSum] at hp'; exact (Finset.not_nonempty_empty hp').elim
    · obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hmixed
      subst b
      refine ⟨a, by simp, ?_⟩
      apply Prod.ext
      · change a.1.1 = (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).1
        simp
      · change (D.2.2 a).1.1 = (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).2
        simp
  · rintro ⟨a, ha, hap⟩
    subst p
    refine ⟨?_, ?_⟩
    · refine ⟨a.1.1.disjSum (D.2.2 a).1.1, ?_, ?_⟩
      · simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union]
        right; right; exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
      · apply Prod.ext
        · change (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).1 = a.1.1
          simp
        · change (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).2 = (D.2.2 a).1.1
          simp
    · exact ⟨D.1.1.nonempty_of_mem_parts a.1.2, D.2.1.1.nonempty_of_mem_parts (D.2.2 a).1.2⟩
private noncomputable def gluedMixedPartition {n k : ℕ} (D : RestrictionPairingData n k) : MixedParityPartition n k := by
  classical
  refine ⟨gluedPartition D, ?_⟩
  rw [mixedBlockCount]
  have hm : (gluedPartition D).parts.filter IsMixedBlock = mixedParts (gluedPartition D) := by
    ext p
    simp [mixedParts, IsMixedBlock]
  rw [hm, glued_mixed_parts, Finset.card_map, Finset.card_attach]; exact D.1.2.2
private theorem glued_restriction {n k : ℕ} (P : MixedParityPartition n k) : gluedMixedPartition (restrictionData P) = P := by
  classical
  apply Subtype.ext; apply Finpartition.ext
  ext q
  simp only [gluedMixedPartition, gluedPartition, Finpartition.copy_parts, Finpartition.parts_map, gluedSumPartition, Finpartition.ofExistsUnique_parts, Finset.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [gluedSumParts, Finset.mem_union] at hb
    rcases hb with hodd | heven | hmixed
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hodd
      have hapart := (Finset.mem_sdiff.mp ha).1
      change a ∈ (P.1.parts.image Prod.fst).erase ∅ at hapart
      obtain ⟨_, haimage⟩ := Finset.mem_erase.mp hapart
      obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp haimage
      have hpempty : p.2 = ∅ := by
        by_contra hpne
        have hpmixed : p ∈ mixedParts P.1 := Finset.mem_filter.mpr
          ⟨hp, ⟨Finset.nonempty_iff_ne_empty.mpr (hpa ▸ (Finset.mem_erase.mp hapart).1), Finset.nonempty_iff_ne_empty.mpr hpne⟩⟩
        apply (Finset.mem_sdiff.mp ha).2; apply Finset.mem_image.mpr
        let m : (leftRestriction P.1).parts := mixedToLeftEmbedding P.1 ⟨p, hpmixed⟩
        refine ⟨m, ?_, ?_⟩
        · change m ∈ leftMarkedParts P.1
          simp [m, leftMarkedParts]
        · change m.1 = a
          exact hpa
      change Finset.sumEquiv (a.disjSum ∅) ∈ P.1.parts
      have heq : Finset.sumEquiv (a.disjSum ∅) = p := by
        apply Prod.ext
        · rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum, hpa]
        · rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum, hpempty]
      rw [heq]; exact hp
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp heven
      have hapart := (Finset.mem_sdiff.mp ha).1
      change a ∈ (P.1.parts.image Prod.snd).erase ∅ at hapart
      obtain ⟨_, haimage⟩ := Finset.mem_erase.mp hapart
      obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp haimage
      have hpempty : p.1 = ∅ := by
        by_contra hpne
        have hpmixed : p ∈ mixedParts P.1 := Finset.mem_filter.mpr
          ⟨hp, ⟨Finset.nonempty_iff_ne_empty.mpr hpne, Finset.nonempty_iff_ne_empty.mpr (hpa ▸ (Finset.mem_erase.mp hapart).1)⟩⟩
        apply (Finset.mem_sdiff.mp ha).2; apply Finset.mem_image.mpr
        let m : (rightRestriction P.1).parts := mixedToRightEmbedding P.1 ⟨p, hpmixed⟩
        refine ⟨m, ?_, ?_⟩
        · change m ∈ rightMarkedParts P.1
          simp [m, rightMarkedParts]
        · change m.1 = a
          exact hpa
      change Finset.sumEquiv ((∅ : Finset _).disjSum a) ∈ P.1.parts
      have heq : Finset.sumEquiv ((∅ : Finset _).disjSum a) = p := by
        apply Prod.ext
        · rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum, hpempty]
        · rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum, hpa]
      rw [heq]; exact hp
    · obtain ⟨m, hm, hmb⟩ := Finset.mem_image.mp hmixed
      subst b
      let p : {p // p ∈ mixedParts P.1} := (mixedLeftEquiv P.1).symm m
      have hleft := (mixedLeftEquiv P.1).apply_symm_apply m
      have hleft' : m.1.1 = p.1.1 := by
        exact (congrArg (fun z => z.1.1) hleft).symm
      have heq : Finset.sumEquiv (m.1.1.disjSum ((restrictionData P).2.2 m).1.1) = p.1 := by
        apply Prod.ext
        · simpa using hleft'
        · simp only [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum, restrictionData]
          change ((mixedRightEquiv P.1) p).1.1 = p.1.2
          rfl
      change Finset.sumEquiv (m.1.1.disjSum ((restrictionData P).2.2 m).1.1) ∈ P.1.parts
      rw [heq]; exact (Finset.mem_filter.mp p.2).1
  · intro hq
    by_cases ho : q.1.Nonempty
    · by_cases he : q.2.Nonempty
      · let p : {p // p ∈ mixedParts P.1} := ⟨q, Finset.mem_filter.mpr ⟨hq, ho, he⟩⟩
        let m : MarkedBlocks (restrictionData P).1 := (mixedLeftEquiv P.1) p
        refine ⟨m.1.1.disjSum ((restrictionData P).2.2 m).1.1, ?_, ?_⟩
        · simp only [gluedSumParts, Finset.mem_union]
          right; right; exact Finset.mem_image.mpr ⟨m, Finset.mem_attach _ m, rfl⟩
        · apply Prod.ext
          · change (Finset.sumEquiv (m.1.1.disjSum ((restrictionData P).2.2 m).1.1)).1 = q.1
            rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum]
            rfl
          · change (Finset.sumEquiv (m.1.1.disjSum ((restrictionData P).2.2 m).1.1)).2 = q.2
            rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum]
            dsimp only [m, restrictionData]
            have hpair : ((mixedLeftEquiv P.1).symm.trans (mixedRightEquiv P.1)) ((mixedLeftEquiv P.1) p) = (mixedRightEquiv P.1) p := by
              rw [Equiv.trans_apply, Equiv.symm_apply_apply]
            calc
              _ = ((mixedRightEquiv P.1) p).1.1 := congrArg (fun z => z.1.1) hpair
              _ = q.2 := rfl
      · have heq : q.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        have hleft : q.1 ∈ (leftRestriction P.1).parts := by
          change q.1 ∈ (P.1.parts.image Prod.fst).erase ∅
          exact Finset.mem_erase.mpr ⟨ho.ne_empty, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
        have hnot : q.1 ∉ markedValues (leftMarkedParts P.1) := by
          intro hmark
          obtain ⟨m, hm, hmq⟩ := Finset.mem_image.mp hmark
          change m ∈ leftMarkedParts P.1 at hm
          obtain ⟨p, hp, hpm⟩ := Finset.mem_map.mp hm
          have hpleft : p.1.1 = q.1 := by
            calc
              p.1.1 = m.1 := congrArg Subtype.val hpm
              _ = q.1 := hmq
          have hpq : p.1 = q := by
            by_contra hpq'
            have hd := P.1.disjoint (Finset.mem_filter.mp p.2).1 hq hpq'
            change Disjoint p.1 q at hd
            rw [Prod.disjoint_iff] at hd
            obtain ⟨a, ha⟩ := ho
            exact (Finset.not_disjoint_iff.mpr ⟨a, hpleft ▸ ha, ha⟩) hd.1
          have hpnonempty := (Finset.mem_filter.mp p.2).2.2
          rw [hpq, heq] at hpnonempty; exact Finset.not_nonempty_empty hpnonempty
        refine ⟨q.1.disjSum (∅ : Finset _), ?_, ?_⟩
        · simp only [gluedSumParts, Finset.mem_union]
          left; exact Finset.mem_image.mpr
            ⟨q.1, Finset.mem_sdiff.mpr ⟨hleft, hnot⟩, rfl⟩
        · apply Prod.ext
          · change (Finset.sumEquiv (q.1.disjSum (∅ : Finset _))).1 = q.1
            rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum]
          · change (Finset.sumEquiv (q.1.disjSum (∅ : Finset _))).2 = q.2
            rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum, heq]
    · have hoeq : q.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp ho
      by_cases he : q.2.Nonempty
      · have hright : q.2 ∈ (rightRestriction P.1).parts := by
          change q.2 ∈ (P.1.parts.image Prod.snd).erase ∅
          exact Finset.mem_erase.mpr ⟨he.ne_empty, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
        have hnot : q.2 ∉ markedValues (rightMarkedParts P.1) := by
          intro hmark
          obtain ⟨m, hm, hmq⟩ := Finset.mem_image.mp hmark
          change m ∈ rightMarkedParts P.1 at hm
          obtain ⟨p, hp, hpm⟩ := Finset.mem_map.mp hm
          have hpright : p.1.2 = q.2 := by
            calc
              p.1.2 = m.1 := congrArg Subtype.val hpm
              _ = q.2 := hmq
          have hpq : p.1 = q := by
            by_contra hpq'
            have hd := P.1.disjoint (Finset.mem_filter.mp p.2).1 hq hpq'
            change Disjoint p.1 q at hd
            rw [Prod.disjoint_iff] at hd
            obtain ⟨b, hb⟩ := he
            exact (Finset.not_disjoint_iff.mpr ⟨b, hpright ▸ hb, hb⟩) hd.2
          have hpnonempty := (Finset.mem_filter.mp p.2).2.1
          rw [hpq, hoeq] at hpnonempty; exact Finset.not_nonempty_empty hpnonempty
        refine ⟨(∅ : Finset _).disjSum q.2, ?_, ?_⟩
        · simp only [gluedSumParts, Finset.mem_union]
          right; left; exact Finset.mem_image.mpr
            ⟨q.2, Finset.mem_sdiff.mpr ⟨hright, hnot⟩, rfl⟩
        · apply Prod.ext
          · change (Finset.sumEquiv ((∅ : Finset _).disjSum q.2)).1 = q.1
            rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum, hoeq]
          · change (Finset.sumEquiv ((∅ : Finset _).disjSum q.2)).2 = q.2
            rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum]
      · have heq : q.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        have hbot : q = (⊥ : ParityBlock n) := by
          apply Prod.ext
          · exact hoeq
          · exact heq
        exfalso; exact P.1.bot_notMem (hbot ▸ hq)
private theorem leftRestriction_glued {n k : ℕ} (D : RestrictionPairingData n k) : leftRestriction (gluedPartition D) = D.1.1 := by
  classical
  apply Finpartition.ext
  ext a
  simp only [leftRestriction, Finpartition.ofExistsUnique_parts, Finset.mem_erase, Finset.mem_image, gluedPartition, Finpartition.copy_parts, Finpartition.parts_map]
  constructor
  · rintro ⟨ha, p, hp, hpa⟩
    obtain ⟨b, hb, hbp⟩ := Finset.mem_map.mp hp
    subst p
    simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union] at hb
    rcases hb with hodd | heven | hmixed
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hodd
      change (Finset.sumEquiv (q.disjSum (∅ : Finset (Fin (n / 2))))).1 = a at hpa
      rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum] at hpa
      rw [← hpa]; exact (Finset.mem_sdiff.mp hq).1
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp heven
      exfalso; apply ha
      change (Finset.sumEquiv ((∅ : Finset (Fin ((n + 1) / 2))).disjSum q)).1 = a at hpa
      rw [Finset.sumEquiv_apply_fst, Finset.toLeft_disjSum] at hpa; exact hpa.symm
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hmixed
      have haq : q.1.1 = a := by simpa using hpa
      rw [← haq]; exact q.1.2
  · intro ha
    have hane : a ≠ ∅ := (D.1.1.nonempty_of_mem_parts ha).ne_empty
    refine ⟨hane, ?_⟩
    by_cases hm : a ∈ markedValues D.1.2.1
    · obtain ⟨m, hmmarked, hma⟩ := Finset.mem_image.mp hm
      let mm : MarkedBlocks D.1 := ⟨m, hmmarked⟩
      let b := mm.1.1.disjSum (D.2.2 mm).1.1
      refine ⟨Finset.sumEquiv b, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        refine ⟨b, ?_, rfl⟩
        simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union]
        right; right; exact Finset.mem_image.mpr ⟨mm, Finset.mem_attach _ mm, rfl⟩
      · change b.toLeft = a
        dsimp only [b]; rw [Finset.toLeft_disjSum]; exact hma
    · let b := a.disjSum (∅ : Finset (Fin (n / 2)))
      refine ⟨Finset.sumEquiv b, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        refine ⟨b, ?_, rfl⟩
        simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union]
        left; exact Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨ha, hm⟩, rfl⟩
      · change b.toLeft = a
        dsimp only [b]; rw [Finset.toLeft_disjSum]
private theorem rightRestriction_glued {n k : ℕ} (D : RestrictionPairingData n k) : rightRestriction (gluedPartition D) = D.2.1.1 := by
  classical
  apply Finpartition.ext
  ext a
  simp only [rightRestriction, Finpartition.ofExistsUnique_parts, Finset.mem_erase, Finset.mem_image, gluedPartition, Finpartition.copy_parts, Finpartition.parts_map]
  constructor
  · rintro ⟨ha, p, hp, hpa⟩
    obtain ⟨b, hb, hbp⟩ := Finset.mem_map.mp hp
    subst p
    simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union] at hb
    rcases hb with hodd | heven | hmixed
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hodd
      exfalso; apply ha
      change (Finset.sumEquiv (q.disjSum (∅ : Finset (Fin (n / 2))))).2 = a at hpa
      rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum] at hpa; exact hpa.symm
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp heven
      change (Finset.sumEquiv ((∅ : Finset (Fin ((n + 1) / 2))).disjSum q)).2 = a at hpa
      rw [Finset.sumEquiv_apply_snd, Finset.toRight_disjSum] at hpa
      rw [← hpa]; exact (Finset.mem_sdiff.mp hq).1
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hmixed
      have haq : (D.2.2 q).1.1 = a := by simpa using hpa
      rw [← haq]; exact (D.2.2 q).1.2
  · intro ha
    have hane : a ≠ ∅ := (D.2.1.1.nonempty_of_mem_parts ha).ne_empty
    refine ⟨hane, ?_⟩
    by_cases hm : a ∈ markedValues D.2.1.2.1
    · obtain ⟨m, hmmarked, hma⟩ := Finset.mem_image.mp hm
      let mm : MarkedBlocks D.2.1 := ⟨m, hmmarked⟩
      let p : MarkedBlocks D.1 := D.2.2.symm mm
      let b := p.1.1.disjSum mm.1.1
      refine ⟨Finset.sumEquiv b, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        refine ⟨b, ?_, rfl⟩
        simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union]
        right; right; apply Finset.mem_image.mpr
        refine ⟨p, Finset.mem_attach _ p, ?_⟩
        simp [b, p, mm]
      · change b.toRight = a
        dsimp only [b]; rw [Finset.toRight_disjSum]; exact hma
    · let b := (∅ : Finset (Fin ((n + 1) / 2))).disjSum a
      refine ⟨Finset.sumEquiv b, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        refine ⟨b, ?_, rfl⟩
        simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts, Finset.mem_union]
        right; left; exact Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨ha, hm⟩, rfl⟩
      · change b.toRight = a
        dsimp only [b]; rw [Finset.toRight_disjSum]
private theorem leftMarkedValues_glued {n k : ℕ} (D : RestrictionPairingData n k) : markedValues (leftMarkedParts (gluedPartition D)) = markedValues D.1.2.1 := by
  classical
  ext a
  simp only [markedValues, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, hma⟩
    change m ∈ leftMarkedParts (gluedPartition D) at hm
    obtain ⟨p, hp, hpm⟩ := Finset.mem_map.mp hm
    have hpin : p.1 ∈ D.1.2.1.attach.map (gluedMixedEmbedding D) := by
      rw [← glued_mixed_parts D]; exact p.2
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hpin
    refine ⟨q.1, q.2, ?_⟩
    calc
      q.1.1 = p.1.1 := congrArg Prod.fst hqp
      _ = m.1 := congrArg Subtype.val hpm
      _ = a := hma
  · rintro ⟨m, hm, hma⟩
    let q : MarkedBlocks D.1 := ⟨m, hm⟩
    let block : ParityBlock n := gluedMixedEmbedding D q
    have hblock : block ∈ mixedParts (gluedPartition D) := by
      rw [glued_mixed_parts D]; exact Finset.mem_map.mpr ⟨q, Finset.mem_attach _ q, rfl⟩
    let p : {b // b ∈ mixedParts (gluedPartition D)} := ⟨block, hblock⟩
    let lm : (leftRestriction (gluedPartition D)).parts := mixedToLeftEmbedding (gluedPartition D) p
    refine ⟨lm, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
    · calc
        lm.1 = p.1.1 := rfl
        _ = block.1 := rfl
        _ = q.1.1 := rfl
        _ = m.1 := rfl
        _ = a := hma
private theorem rightMarkedValues_glued {n k : ℕ} (D : RestrictionPairingData n k) : markedValues (rightMarkedParts (gluedPartition D)) = markedValues D.2.1.2.1 := by
  classical
  ext a
  simp only [markedValues, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, hma⟩
    change m ∈ rightMarkedParts (gluedPartition D) at hm
    obtain ⟨p, hp, hpm⟩ := Finset.mem_map.mp hm
    have hpin : p.1 ∈ D.1.2.1.attach.map (gluedMixedEmbedding D) := by
      rw [← glued_mixed_parts D]; exact p.2
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hpin
    refine ⟨(D.2.2 q).1, (D.2.2 q).2, ?_⟩
    calc (D.2.2 q).1.1 = p.1.2 := congrArg Prod.snd hqp
      _ = m.1 := congrArg Subtype.val hpm
      _ = a := hma
  · rintro ⟨m, hm, hma⟩
    let q : MarkedBlocks D.2.1 := ⟨m, hm⟩
    let pre : MarkedBlocks D.1 := D.2.2.symm q
    let block : ParityBlock n := gluedMixedEmbedding D pre
    have hblock : block ∈ mixedParts (gluedPartition D) := by
      rw [glued_mixed_parts D]; exact Finset.mem_map.mpr ⟨pre, Finset.mem_attach _ pre, rfl⟩
    let p : {b // b ∈ mixedParts (gluedPartition D)} := ⟨block, hblock⟩
    let rm : (rightRestriction (gluedPartition D)).parts := mixedToRightEmbedding (gluedPartition D) p
    refine ⟨rm, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨p, Finset.mem_attach _ p, rfl⟩
    · calc
        rm.1 = (D.2.2 pre).1.1 := rfl
        _ = q.1.1 := congrArg (fun z => z.1.1) (D.2.2.apply_symm_apply q)
        _ = a := hma
private theorem leftMarkedPartition_glued {n k : ℕ} (D : RestrictionPairingData n k) : leftMarkedPartition (gluedMixedPartition D) = D.1 := by
  classical
  let L := leftMarkedPartition (gluedMixedPartition D)
  have marked_heq : ∀ (P Q : SetPartition ((n + 1) / 2)) (hP : P = Q) (M : {M : Finset P.parts // M.card = k}) (N : {N : Finset Q.parts // N.card = k}), markedValues M.1 = markedValues N.1 → M ≍ N := by
    intro P Q hP M N hvalues
    subst Q
    apply heq_of_eq; apply Subtype.ext; exact Finset.image_injective Subtype.val_injective hvalues
  refine Sigma.ext (leftRestriction_glued D) ?_
  exact marked_heq L.1 D.1.1 (leftRestriction_glued D) L.2 D.1.2 (leftMarkedValues_glued D)
private theorem rightMarkedPartition_glued {n k : ℕ} (D : RestrictionPairingData n k) : rightMarkedPartition (gluedMixedPartition D) = D.2.1 := by
  classical
  let R := rightMarkedPartition (gluedMixedPartition D)
  have marked_heq : ∀ (P Q : SetPartition (n / 2)) (hP : P = Q) (M : {M : Finset P.parts // M.card = k}) (N : {N : Finset Q.parts // N.card = k}), markedValues M.1 = markedValues N.1 → M ≍ N := by
    intro P Q hP M N hvalues
    subst Q
    apply heq_of_eq; apply Subtype.ext; exact Finset.image_injective Subtype.val_injective hvalues
  refine Sigma.ext (rightRestriction_glued D) ?_
  exact marked_heq R.1 D.2.1.1 (rightRestriction_glued D) R.2 D.2.1.2 (rightMarkedValues_glued D)
private theorem restrictionPairing_glued {n k : ℕ} (D : RestrictionPairingData n k) : (restrictionData (gluedMixedPartition D)).2.2 ≍ D.2.2 := by
  classical
  let P := gluedMixedPartition D
  let L := leftMarkedPartition P
  let R := rightMarkedPartition P
  let F : MarkedBlocks L ≃ MarkedBlocks R := (mixedLeftEquiv (gluedPartition D)).symm.trans (mixedRightEquiv (gluedPartition D))
  have hL : L = D.1 := by simpa [L, P] using leftMarkedPartition_glued D
  have hR : R = D.2.1 := by simpa [R, P] using rightMarkedPartition_glued D
  have hA : ↥(MarkedBlocks L) = ↥(MarkedBlocks D.1) := congrArg (fun Q : MarkedPartition ((n + 1) / 2) k => {b // b ∈ MarkedBlocks Q}) hL
  have hB : ↥(MarkedBlocks R) = ↥(MarkedBlocks D.2.1) := congrArg (fun Q : MarkedPartition (n / 2) k => {b // b ∈ MarkedBlocks Q}) hR
  have equiv_heq : ∀ (A A' B B' : Type) (hA : A = A') (hB : B = B') (f : A ≃ B) (g : A' ≃ B'), (∀ (x : A) (x' : A'), x ≍ x' → f x ≍ g x') → f ≍ g := by
    intro A A' B B' hA' hB' f g hfg
    subst A'
    subst B'
    apply heq_of_eq; apply Equiv.ext
    intro x
    exact eq_of_heq (hfg x x (HEq.refl x))
  have raw_of_heq : ∀ (O O' : MarkedPartition ((n + 1) / 2) k) (hO : O = O') (x : MarkedBlocks O) (x' : MarkedBlocks O'), x ≍ x' → x.1.1 = x'.1.1 := by
    intro O O' hO x x' hxx
    subst O'
    exact congrArg (fun z : MarkedBlocks O => z.1.1) (eq_of_heq hxx)
  have heq_of_raw : ∀ (E E' : MarkedPartition (n / 2) k) (hE : E = E') (y : MarkedBlocks E) (y' : MarkedBlocks E'), y.1.1 = y'.1.1 → y ≍ y' := by
    intro E E' hE y y' hraw
    subst E'
    apply heq_of_eq; apply Subtype.ext; apply Subtype.ext; exact hraw
  change F ≍ D.2.2
  refine equiv_heq (MarkedBlocks L) (MarkedBlocks D.1) (MarkedBlocks R) (MarkedBlocks D.2.1) hA hB F D.2.2 ?_
  intro x x' hxx
  let p : {b // b ∈ mixedParts (gluedPartition D)} := (mixedLeftEquiv (gluedPartition D)).symm x
  have hpin : p.1 ∈ D.1.2.1.attach.map (gluedMixedEmbedding D) := by
    rw [← glued_mixed_parts D]; exact p.2
  obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hpin
  have hpx : p.1.1 = x.1.1 := by
    calc
      p.1.1 = ((mixedLeftEquiv (gluedPartition D)) p).1.1 := rfl
      _ = x.1.1 := congrArg (fun z => z.1.1) ((mixedLeftEquiv (gluedPartition D)).apply_symm_apply x)
  have hxxraw : x.1.1 = x'.1.1 := raw_of_heq L D.1 hL x x' hxx
  have hqraw : q.1.1 = x'.1.1 := by
    calc
      q.1.1 = p.1.1 := congrArg Prod.fst hqp
      _ = x.1.1 := hpx
      _ = x'.1.1 := hxxraw
  have hqx : q = x' := by
    apply Subtype.ext; apply Subtype.ext; exact hqraw
  have hout : (F x).1.1 = (D.2.2 x').1.1 := by
    calc (F x).1.1 = p.1.2 := rfl
      _ = (D.2.2 q).1.1 := (congrArg Prod.snd hqp).symm
      _ = (D.2.2 x').1.1 := by rw [hqx]
  exact heq_of_raw R D.2.1 hR (F x) (D.2.2 x') hout
private theorem restriction_glued {n k : ℕ} (D : RestrictionPairingData n k) : restrictionData (gluedMixedPartition D) = D := by
  classical
  let X := restrictionData (gluedMixedPartition D)
  have hO : X.1 = D.1 := by
    simpa [X, restrictionData] using leftMarkedPartition_glued D
  have hE : X.2.1 = D.2.1 := by
    simpa [X, restrictionData] using rightMarkedPartition_glued D
  have hpair : X.2.2 ≍ D.2.2 := by
    simpa [X] using restrictionPairing_glued D
  have data_ext : ∀ (O O' : MarkedPartition ((n + 1) / 2) k) (hO : O = O') (E E' : MarkedPartition (n / 2) k) (hE : E = E') (f : MarkedBlocks O ≃ MarkedBlocks E) (g : MarkedBlocks O' ≃ MarkedBlocks E'), f ≍ g → (⟨O, ⟨E, f⟩⟩ : RestrictionPairingData n k) = ⟨O', ⟨E', g⟩⟩ := by
    intro O O' hO' E E' hE' f g hfg
    subst O'
    subst E'
    have hfg' : f = g := eq_of_heq hfg
    subst g
    rfl
  exact data_ext X.1 D.1 hO X.2.1 D.2.1 hE X.2.2 D.2.2 hpair
/-- Restriction with marked odd/even blocks is inverse to gluing paired blocks. -/
noncomputable def mixedRestrictionEquiv (n k : ℕ) : MixedParityPartition n k ≃ RestrictionPairingData n k where
  toFun := restrictionData
  invFun := gluedMixedPartition
  left_inv := glued_restriction
  right_inv := restriction_glued
/-- Hanna's A124418 formula counts marked odd/even restrictions and their bijections. -/
theorem hanna_a124418 : ∀ n k, k ≤ n / 2 → T n k = Nat.factorial k * A049020 (n / 2) k * A049020 ((n + 1) / 2) k := by
  classical
  intro n k _hk
  have pairing_card (O : MarkedPartition ((n + 1) / 2) k) (E : MarkedPartition (n / 2) k) : Fintype.card (MarkedBlocks O ≃ MarkedBlocks E) = Nat.factorial k := by
    let e : MarkedBlocks O ≃ MarkedBlocks E := Fintype.equivOfCardEq (by
      simpa only [Fintype.card_coe] using O.2.2.trans E.2.2.symm)
    calc
      Fintype.card (MarkedBlocks O ≃ MarkedBlocks E) = Nat.factorial (Fintype.card (MarkedBlocks O)) := Fintype.card_equiv e
      _ = Nat.factorial O.2.1.card := congrArg Nat.factorial (Fintype.card_coe (MarkedBlocks O))
      _ = Nat.factorial k := congrArg Nat.factorial O.2.2
  calc
    T n k = Fintype.card (RestrictionPairingData n k) := by
      exact Fintype.card_congr (mixedRestrictionEquiv n k)
    _ = ∑ O : MarkedPartition ((n + 1) / 2) k, ∑ E : MarkedPartition (n / 2) k, Fintype.card (MarkedBlocks O ≃ MarkedBlocks E) := by
      rw [Fintype.card_sigma]; apply Finset.sum_congr rfl
      intro O _
      rw [Fintype.card_sigma]
    _ = Nat.factorial k * markedPartitions (n / 2) k * markedPartitions ((n + 1) / 2) k := by
      simp_rw [pairing_card]
      simp only [Finset.sum_const, Finset.card_univ]
      change Fintype.card (MarkedPartition ((n + 1) / 2) k) * (Fintype.card (MarkedPartition (n / 2) k) * Nat.factorial k) = _
      simp only [markedPartitions]
      ac_rfl
    _ = Nat.factorial k * A049020 (n / 2) k * A049020 ((n + 1) / 2) k := by
      rw [markedPartitions_eq_A049020, markedPartitions_eq_A049020]
#print axioms markedPartitions_eq_A049020
#print axioms T_eq_Tfin
#print axioms hanna_a124418
end D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
