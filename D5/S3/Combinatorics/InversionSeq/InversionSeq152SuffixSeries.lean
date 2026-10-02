/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries
   mirror-E: none(waiver:first-label-suffix-counting)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: First-label and multiplicity bijections enumerate actual bounded right suffixes. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Multiplicity
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Labels
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152SuffixSeries

open D5.S3.Combinatorics.InversionSeq.InversionSeq152Multiplicity
open D5.S3.Combinatorics Nonnesting

set_option maxHeartbeats 2400000 in
theorem first_label_suffix_enumeration (lower height : ℕ) :
    let suffix := 1 + PowerSeries.X * PowerSeries.mk fun size =>
      (Nat.card {word : List ℕ // word.length = size + 1 ∧ word.Nodup ∧
        (∀ value ∈ word, lower < value) ∧
        (∀ index < word.length, word.getD index 0 ≤ lower + height + 1 + index) ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] word ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] word} : ℚ)
    let binary := PowerSeries.mk fun size => (2 : ℚ) ^ size
    2 * (1 - PowerSeries.X) * suffix = 1 + binary ^ height := by
  classical
  let Actual (size : ℕ) := {word : List ℕ // word.length = size + 1 ∧ word.Nodup ∧
    (∀ value ∈ word, lower < value) ∧
    (∀ index < word.length, word.getD index 0 ≤ lower + height + 1 + index) ∧
    ¬ NonnestingDefs.Occurs [3, 1, 2] word ∧ ¬ NonnestingDefs.Occurs [3, 2, 1] word}
  have hrotatePerm (blocks : List (List ℕ)) :
      (blocks.flatMap (fun block => block.rotate 1)).Perm blocks.flatten := by
    induction blocks with
    | nil => exact List.Perm.refl []
    | cons block rest ih =>
      simpa only [List.flatMap_cons, List.flatten_cons] using
        (List.rotate_perm block 1).append ih
  have hrotateAvoid : ∀ blocks : List (List ℕ),
      (∀ block ∈ blocks, block ≠ []) → blocks.flatten.Pairwise (· < ·) →
      ¬ NonnestingDefs.Occurs [3, 1, 2] (blocks.flatMap (fun block => block.rotate 1)) ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] (blocks.flatMap (fun block => block.rotate 1)) := by
    intro blocks
    induction blocks with
    | nil =>
      intro _ _
      simp [NonnestingDefs.Occurs, ArrowWilfDefs.Contains]
    | cons block blocks ih =>
      intro hne hsorted
      have hbne := hne block (by simp)
      cases block with
      | nil => exact (hbne rfl).elim
      | cons minimum before =>
        have hs : (minimum :: (before ++ blocks.flatten)).Pairwise (· < ·) := hsorted
        obtain ⟨hmin, hrest⟩ := List.pairwise_cons.mp hs
        obtain ⟨hbefore, hblocks, hbetween⟩ := List.pairwise_append.mp hrest
        have htail := ih (fun item hitem => hne item (by simp [hitem])) hblocks
        have hp := hrotatePerm blocks
        have hn : (before ++ minimum ::
            blocks.flatMap (fun block => block.rotate 1)).Nodup := by
          have hpfull := hrotatePerm ((minimum :: before) :: blocks)
          simp only [List.flatMap_cons, List.rotate_cons_succ, List.rotate_zero,
            List.append_assoc, List.singleton_append] at hpfull
          exact hpfull.nodup_iff.mpr hs.nodup
        have hm : ∀ value ∈ before ++ minimum ::
            blocks.flatMap (fun block => block.rotate 1), minimum ≤ value := by
          intro value hvalue
          rcases List.mem_append.mp hvalue with hpre | hpost
          · exact Nat.le_of_lt (hmin value (by simp [hpre]))
          · rcases List.mem_cons.mp hpost with rfl | hpost
            · exact le_rfl
            · exact Nat.le_of_lt (hmin value (by simp [hp.mem_iff.mp hpost]))
        have hsep : ∀ first ∈ before,
            ∀ second ∈ blocks.flatMap (fun block => block.rotate 1), first < second := by
          intro first hf second hs
          exact hbetween first hf second (hp.mem_iff.mp hs)
        simpa only [List.flatMap_cons, List.rotate_cons_succ, List.rotate_zero,
          List.append_assoc, List.singleton_append] using
          (InversionSeq152Rotation.minimum_rotation_split _ _ _ hn hm).mpr
            ⟨hbefore, hsep, htail⟩
  have hactualCount (size : ℕ) : Nat.card (Actual size) =
      Nat.card {blocks : List (List ℕ) // blocks.flatten.length = size + 1 ∧
        blocks.flatten.Pairwise (· ≤ ·) ∧
        (∀ label ∈ blocks.flatten, lower ≤ label ∧ label ≤ lower + height) ∧
        (∀ block ∈ blocks, block ≠ []) ∧
        ∀ block ∈ blocks, ∀ label ∈ block.tail, label < lower + height} := by
    let Rotations := {blocks : List (List ℕ) // blocks.flatten.length = size + 1 ∧
      (∀ block ∈ blocks, block ≠ []) ∧ blocks.flatten.Pairwise (· < ·) ∧
      (∀ value ∈ blocks.flatten, lower < value) ∧
      ∀ index < (blocks.flatMap (fun block => block.rotate 1)).length,
        (blocks.flatMap (fun block => block.rotate 1)).getD index 0 ≤
          lower + height + 1 + index}
    let rotate (blocks : Rotations) : Actual size := by
      have hperm := hrotatePerm blocks.1
      have hn : (blocks.1.flatMap (fun block => block.rotate 1)).Nodup := by
        apply hperm.nodup_iff.mpr
        exact blocks.2.2.2.1.nodup
      have havoid := hrotateAvoid blocks.1 blocks.2.2.1 blocks.2.2.2.1
      refine ⟨blocks.1.flatMap (fun block => block.rotate 1), ?_, hn, ?_,
        blocks.2.2.2.2.2, havoid⟩
      · exact hperm.length_eq.trans blocks.2.1
      · intro value hvalue
        exact blocks.2.2.2.2.1 value (hperm.mem_iff.mp hvalue)
    have hsurjective : Function.Surjective rotate := by
      intro word
      obtain ⟨blocks, hb, huniq⟩ :=
        (InversionSeq152Rotation.rotation_blocks_unique word.1 word.2.2.1).mp
          word.2.2.2.2.2
      have hp := hrotatePerm blocks
      have hsource : blocks.flatten.length = size + 1 ∧
          (∀ block ∈ blocks, block ≠ []) ∧ blocks.flatten.Pairwise (· < ·) ∧
          (∀ value ∈ blocks.flatten, lower < value) ∧
          ∀ index < (blocks.flatMap (fun block => block.rotate 1)).length,
            (blocks.flatMap (fun block => block.rotate 1)).getD index 0 ≤
              lower + height + 1 + index := by
        refine ⟨?_, hb.1, hb.2.1, ?_, ?_⟩
        · rw [← hp.length_eq, ← hb.2.2]; exact word.2.1
        · intro value hvalue
          apply word.2.2.2.1 value
          rw [hb.2.2]
          exact hp.mem_iff.mpr hvalue
        · rw [← hb.2.2]; exact word.2.2.2.2.1
      exact ⟨⟨blocks, hsource⟩, Subtype.ext hb.2.2.symm⟩
    have hinjective : Function.Injective rotate := by
      intro first second heq
      have hword := congrArg Subtype.val heq
      have hu := (InversionSeq152Rotation.rotation_blocks_unique (rotate first).1
        (rotate first).2.2.1).mp (rotate first).2.2.2.2.2
      apply Subtype.ext
      exact hu.unique ⟨first.2.2.1, first.2.2.2.1, rfl⟩
        ⟨second.2.2.1, second.2.2.2.1, hword⟩
    obtain ⟨labelEquiv⟩ := InversionSeq152Labels.sorted_label_bijection
      (size + 1) lower (lower + height)
    exact Nat.card_congr
      ((Equiv.ofBijective rotate ⟨hinjective, hsurjective⟩).symm.trans labelEquiv)
  let unary : PowerSeries ℚ := PowerSeries.mk fun _ => 1
  let binary : PowerSeries ℚ := PowerSeries.mk fun size => (2 : ℚ) ^ size
  let Tails (alphabet size : ℕ) :=
    {word : List (Fin (alphabet + 1) × Bool) // word.length = size ∧
      word.Pairwise (fun first second => first.1 ≤ second.1) ∧
      ∀ entry ∈ word, entry.1.val = alphabet → entry.2 = false}
  have htailFinite (alphabet size : ℕ) : Finite (Tails alphabet size) := by
    apply Finite.of_injective
      (fun word : Tails alphabet size =>
        Equiv.vectorEquivFin (Fin (alphabet + 1) × Bool) size
          ⟨word.1, word.2.1⟩)
    intro first second heq
    exact Subtype.ext (congrArg
      (fun vector : List.Vector (Fin (alphabet + 1) × Bool) size => vector.1)
      ((Equiv.vectorEquivFin _ _).injective heq))
  have (alphabet size : ℕ) : Finite (Tails alphabet size) := htailFinite alphabet size
  have htailCount (alphabet size : ℕ) :
      (Nat.card (Tails alphabet size) : ℚ) =
        PowerSeries.coeff size (unary * binary ^ alphabet) := by
    let permitted (label : Fin (alphabet + 1)) : Prop := label.val < alphabet
    let Counts := {counts : Fin (alphabet + 1) → ℕ // ∑ label, counts label = size}
    let Diagonal :=
      {counts : Fin (alphabet + 1) →₀ ℕ //
        counts ∈ Finset.finsuppAntidiag Finset.univ size}
    let countEquiv : Counts ≃ Diagonal :=
      { toFun := fun counts => ⟨Finsupp.equivFunOnFinite.symm counts.1, by
          simpa only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
            Finsupp.coe_equivFunOnFinite_symm] using counts.2⟩
        invFun := fun counts => ⟨counts.1, (Finset.mem_finsuppAntidiag.mp counts.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun counts => Subtype.ext
          (Finsupp.equivFunOnFinite.left_inv counts.1) }
    let : Fintype Diagonal :=
      Fintype.ofFinset (Finset.finsuppAntidiag Finset.univ size) (fun _ => Iff.rfl)
    let : Fintype Counts := Fintype.ofEquiv Diagonal countEquiv.symm
    obtain ⟨regroup, _, hfibers⟩ :=
      ordered_choice_multiplicity_bijection permitted size
    have hallowed (label : Fin (alphabet + 1)) : ¬ permitted label ↔ label.val = alphabet := by
      dsimp [permitted]
      omega
    let rephrase : Tails alphabet size ≃
        {word : List (Fin (alphabet + 1) × Bool) // word.length = size ∧
          word.Pairwise (fun first second => first.1 ≤ second.1) ∧
          ∀ entry ∈ word, ¬ permitted entry.1 → entry.2 = false} :=
      { toFun := fun word => ⟨word.1, word.2.1, word.2.2.1,
          fun entry hentry hnot => word.2.2.2 entry hentry ((hallowed entry.1).mp hnot)⟩
        invFun := fun word => ⟨word.1, word.2.1, word.2.2.1,
          fun entry hentry heq => word.2.2.2 entry hentry ((hallowed entry.1).mpr heq)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have (counts : Counts) : Finite
        (∀ label, {bits : List Bool // bits.length = counts.1 label ∧
          (¬ permitted label → ∀ bit ∈ bits, bit = false)}) := by
      have (label : Fin (alphabet + 1)) : Finite
          {bits : List Bool // bits.length = counts.1 label ∧
            (¬ permitted label → ∀ bit ∈ bits, bit = false)} := by
        apply Finite.of_injective
          (fun bits : {bits : List Bool // bits.length = counts.1 label ∧
            (¬ permitted label → ∀ bit ∈ bits, bit = false)} =>
            Equiv.vectorEquivFin Bool (counts.1 label) ⟨bits.1, bits.2.1⟩)
        intro first second heq
        exact Subtype.ext (congrArg
          (fun vector : List.Vector Bool (counts.1 label) => vector.1)
          ((Equiv.vectorEquivFin _ _).injective heq))
      infer_instance
    let series (label : Fin (alphabet + 1)) : PowerSeries ℚ :=
      PowerSeries.mk fun degree => (if permitted label then 2 else 1 : ℚ) ^ degree
    have hprod : (∏ label, series label) = unary * binary ^ alphabet := by
      rw [Fin.prod_univ_castSucc]
      have hcast (label : Fin alphabet) : series label.castSucc = binary := by
        apply PowerSeries.ext
        intro degree
        simp [series, binary, permitted, label.isLt]
      have hlast : series (Fin.last alphabet) = unary := by
        apply PowerSeries.ext
        intro degree
        simp [series, unary, permitted]
      simp only [hcast, hlast, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_comm _ _
    rw [Nat.card_congr (rephrase.trans regroup), Nat.card_sigma]
    simp only [hfibers, Nat.cast_sum, Nat.cast_prod, Nat.cast_pow]
    rw [← hprod, PowerSeries.coeff_prod]
    conv_rhs =>
      rw [Finset.sum_subtype
        (Finset.finsuppAntidiag (Finset.univ : Finset (Fin (alphabet + 1))) size)
        (fun _ => Iff.rfl)]
    change _ = ∑ counts : Diagonal, ∏ label, PowerSeries.coeff (counts.1 label) (series label)
    apply Fintype.sum_equiv countEquiv
    intro counts
    apply Finset.prod_congr rfl
    intro label _
    dsimp only [countEquiv]
    simp only [series, PowerSeries.coeff_mk]
    split_ifs <;> norm_num
    rfl
  let Words (size : ℕ) :=
    {word : List (Fin (height + 1) × Bool) // word.length = size + 1 ∧
      word.Pairwise (fun first second => first.1 ≤ second.1) ∧
      (word.getD 0 (0, false)).2 = false ∧
      ∀ entry ∈ word, entry.1.val = height → entry.2 = false}
  let Free (labels : List (Fin (height + 1))) :=
    {word : List (Fin (height + 1) × Bool) // word.map Prod.fst = labels ∧
      ∀ entry ∈ word, entry.1.val = height → entry.2 = false}
  have hfree (labels : List (Fin (height + 1))) :
      Finite (Free labels) ∧
        Nat.card (Free labels) = 2 ^ labels.countP (fun label => label.val < height) := by
    induction labels with
    | nil =>
      let empty : Free [] ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨[], by simp⟩
          left_inv := by
            intro word
            apply Subtype.ext
            exact (List.map_eq_nil_iff.mp word.2.1).symm
          right_inv := fun _ => rfl }
      refine ⟨Finite.of_equiv Unit empty.symm, ?_⟩
      rw [Nat.card_congr empty]
      simp
    | cons label labels ih =>
      have : Finite (Free labels) := ih.1
      let Bits := {bit : Bool // label.val = height → bit = false}
      let split : Free (label :: labels) ≃ Bits × Free labels :=
        { toFun := fun word => by
            cases heq : word.1 with
            | nil => have hm := word.2.1; simp [heq] at hm
            | cons entry rest =>
              have hm := word.2.1
              rw [heq, List.map_cons] at hm
              have hfirst := (List.cons.inj hm).1
              refine (⟨entry.2, ?_⟩, ⟨rest, (List.cons.inj hm).2, ?_⟩)
              · intro htop
                exact word.2.2 entry (by rw [heq]; simp) (by simpa [hfirst] using htop)
              · intro item hitem
                exact word.2.2 item (by rw [heq]; simp [hitem])
          invFun := fun pair => ⟨(label, pair.1.1) :: pair.2.1, by
            refine ⟨by simp [pair.2.2.1], ?_⟩
            intro entry hentry
            rcases List.mem_cons.mp hentry with rfl | hentry
            · exact pair.1.2
            · exact pair.2.2.2 entry hentry⟩
          left_inv := by
            rintro ⟨word, hword⟩
            cases word with
            | nil => simp at hword
            | cons entry rest =>
              apply Subtype.ext
              have heq := (List.cons.inj hword.1).1
              dsimp
              congr 1
              exact Prod.ext heq.symm rfl
          right_inv := by
            rintro ⟨bit, rest⟩
            rfl }
      have : Finite (Free (label :: labels)) :=
        Finite.of_equiv (Bits × Free labels) split.symm
      refine ⟨this, ?_⟩
      rw [Nat.card_congr split, Nat.card_prod, ih.2, List.countP_cons]
      by_cases hsmall : label.val < height
      · let forget : Bits ≃ Bool :=
          { toFun := Subtype.val
            invFun := fun bit => ⟨bit, fun heq => by omega⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr forget]
        simp [hsmall, Nat.card_eq_fintype_card, pow_succ, mul_comm]
      · have htop : label.val = height := by have := label.isLt; omega
        let forced : Bits ≃ Unit :=
          { toFun := fun _ => ()
            invFun := fun _ => ⟨false, by simp⟩
            left_inv := fun bit => Subtype.ext (bit.2 htop).symm
            right_inv := fun _ => rfl }
        rw [Nat.card_congr forced]
        simp [hsmall]
  have (labels : List (Fin (height + 1))) : Finite (Free labels) := (hfree labels).1
  let Labels (size : ℕ) := {labels : List (Fin (height + 1)) //
    labels.length = size + 1 ∧ labels.Pairwise (· ≤ ·)}
  have hlabelsFinite (size : ℕ) : Finite (Labels size) := by
    apply Finite.of_injective (fun labels : Labels size =>
      Equiv.vectorEquivFin (Fin (height + 1)) (size + 1) ⟨labels.1, labels.2.1⟩)
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun vector : List.Vector (Fin (height + 1)) (size + 1) => vector.1)
      ((Equiv.vectorEquivFin _ _).injective heq)
  let Partitions (size : ℕ) := {blocks : List (List ℕ) //
    blocks.flatten.length = size + 1 ∧ blocks.flatten.Pairwise (· ≤ ·) ∧
    (∀ label ∈ blocks.flatten, label ≤ height) ∧ (∀ block ∈ blocks, block ≠ []) ∧
    ∀ block ∈ blocks, ∀ label ∈ block.tail, label < height}
  have hpartitionCount (size : ℕ) : Nat.card (Partitions size) = Nat.card (Words size) := by
    let : Fintype (Labels size) := Fintype.ofFinite (Labels size)
    let parts (labels : Labels size) :=
      {blocks : List (List ℕ) // (∀ block ∈ blocks, block ≠ []) ∧
        blocks.flatten = labels.1.map Fin.val ∧
        ∀ block ∈ blocks, ∀ label ∈ block.tail, label < height}
    let toFin (label : ℕ) : Fin (height + 1) := Fin.ofNat (height + 1) label
    have hval (label : ℕ) (hlabel : label ≤ height) : (toFin label).val = label := by
      simp [toFin, Nat.mod_eq_of_lt (by omega : label < height + 1)]
    let flatten (partition : Partitions size) : Labels size := by
      refine ⟨partition.1.flatten.map toFin,
        by simpa only [List.length_map] using partition.2.1, ?_⟩
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem _ partition.2.2.1
      intro left right hleft hright horder
      change (toFin left).val ≤ (toFin right).val
      rw [hval left (partition.2.2.2.1 left hleft),
        hval right (partition.2.2.2.1 right hright)]
      exact horder
    have hflatten (partition : Partitions size) :
        (flatten partition).1.map Fin.val = partition.1.flatten := by
      dsimp only [flatten]
      rw [List.map_map]
      calc
        _ = partition.1.flatten.map id := List.map_congr_left fun label hlabel =>
          hval label (partition.2.2.2.1 label hlabel)
        _ = _ := List.map_id _
    let partitionEquiv : Partitions size ≃ Σ labels : Labels size, parts labels :=
      { toFun := fun partition => ⟨flatten partition,
          ⟨partition.1, partition.2.2.2.2.1, (hflatten partition).symm,
            partition.2.2.2.2.2⟩⟩
        invFun := fun data => ⟨data.2.1, by
          refine ⟨?_, ?_, ?_, data.2.2.1, data.2.2.2.2⟩
          all_goals rw [data.2.2.2.1]
          · simpa using data.1.2.1
          · exact List.pairwise_map.mpr (data.1.2.2.imp (fun horder => horder))
          · intro label hlabel
            obtain ⟨original, _, rfl⟩ := List.mem_map.mp hlabel
            have := original.isLt
            omega⟩
        left_inv := fun _ => rfl
        right_inv := by
          intro data
          apply Sigma.ext
          · apply Subtype.ext
            dsimp only [flatten]
            rw [data.2.2.2.1, List.map_map]
            calc
              _ = data.1.1.map id := List.map_congr_left fun label _ => by
                apply Fin.ext
                exact hval label.val (by have := label.isLt; omega)
              _ = _ := List.map_id _
          · apply (Subtype.heq_iff_coe_eq (fun blocks => by
              dsimp only
              rw [hflatten, data.2.2.2.1])).mpr
            rfl }
    have (labels : Labels size) : Finite (parts labels) := by
      obtain ⟨equivalence⟩ :=
        InversionSeq152Cuts.independent_join_bijection (labels.1.map Fin.val) height
      exact Finite.of_equiv _ equivalence.symm
    let decorated (labels : Labels size) :=
      {word : Words size // word.1.map Prod.fst = labels.1}
    let project (word : Words size) : Labels size :=
      ⟨word.1.map Prod.fst, by simp [word.2.1],
        List.pairwise_map.mpr word.2.2.1⟩
    have hdecorated (labels : Labels size) :
        Nonempty (decorated labels ≃ Free labels.1.tail) := by
      have hn : labels.1 ≠ [] := by intro heq; have := labels.2.1; simp [heq] at this
      let first := labels.1.head hn
      have heq : labels.1 = first :: labels.1.tail := (List.cons_head_tail hn).symm
      refine ⟨{
        toFun := fun data => ⟨data.1.1.tail, ?_, ?_⟩
        invFun := fun rest => ⟨⟨(first, false) :: rest.1, ?_, ?_, rfl, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := fun _ => rfl }⟩
      · simpa only [List.map_tail] using congrArg List.tail data.2
      · intro entry hentry
        exact data.1.2.2.2.2 entry (List.mem_of_mem_tail hentry)
      · have hl := congrArg List.length rest.2.1
        have hlabels := labels.2.1
        rw [heq, List.length_cons] at hlabels
        simp only [List.length_map] at hl
        simp only [List.length_cons]
        omega
      · apply List.pairwise_map.mp
        rw [List.map_cons, rest.2.1, ← heq]
        exact labels.2.2
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · simp
        · exact rest.2.2 entry hentry
      · simp only [List.map_cons, rest.2.1, ← heq]
      · intro data
        obtain ⟨⟨word, hword⟩, hmap⟩ := data
        apply Subtype.ext
        apply Subtype.ext
        cases word with
        | nil => simp at hword
        | cons entry rest =>
          have hfirst : entry.1 = first := by
            rw [List.map_cons, heq] at hmap
            exact (List.cons.inj hmap).1
          have hflag := hword.2.2.1
          simp only [List.getD_cons_zero] at hflag
          change (first, false) :: rest = entry :: rest
          congr 1
          exact Prod.ext hfirst.symm hflag.symm
    have (labels : Labels size) : Finite (decorated labels) := by
      obtain ⟨equivalence⟩ := hdecorated labels
      exact Finite.of_equiv _ equivalence.symm
    let fiberEquiv (labels : Labels size) :
        {word : Words size // project word = labels} ≃ decorated labels :=
      { toFun := fun word => ⟨word.1, congrArg Subtype.val word.2⟩
        invFun := fun word => ⟨word.1, Subtype.ext word.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have (labels : Labels size) : Finite {word : Words size // project word = labels} :=
      Finite.of_equiv _ (fiberEquiv labels).symm
    rw [Nat.card_congr partitionEquiv,
      ← Nat.card_congr (Equiv.sigmaFiberEquiv project), Nat.card_sigma, Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro labels _
    obtain ⟨partition⟩ :=
      InversionSeq152Cuts.independent_join_bijection (labels.1.map Fin.val) height
    obtain ⟨decoration⟩ := hdecorated labels
    rw [Nat.card_congr partition, Nat.card_fin,
      Nat.card_congr ((fiberEquiv labels).trans decoration), (hfree labels.1.tail).2]
    simp only [← List.map_tail, List.countP_map, Function.comp_def]
  have hsplit (size : ℕ) :
      Nonempty (Words size ≃ Σ first : Fin (height + 1), Tails (height - first.val) size) := by
    let raise (first : Fin (height + 1)) (entry : Fin (height - first.val + 1) × Bool) :
        Fin (height + 1) × Bool :=
      (⟨first.val + entry.1.val, by have := first.isLt; have := entry.1.isLt; omega⟩,
        entry.2)
    let lower (first : Fin (height + 1)) (entry : Fin (height + 1) × Bool) :
        Fin (height - first.val + 1) × Bool :=
      (⟨entry.1.val - first.val, by have := entry.1.isLt; omega⟩, entry.2)
    have hraiseLower (first : Fin (height + 1)) (entry : Fin (height + 1) × Bool)
        (hbound : first ≤ entry.1) : raise first (lower first entry) = entry := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [raise, lower]
        have : first.val ≤ entry.1.val := hbound
        omega
      · rfl
    have hlowerRaise (first : Fin (height + 1))
        (entry : Fin (height - first.val + 1) × Bool) :
        lower first (raise first entry) = entry := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [raise, lower]
        omega
      · rfl
    let pack (first : Fin (height + 1)) (tail : Tails (height - first.val) size) :
        Words size := by
      refine ⟨(first, false) :: tail.1.map (raise first), ?_, ?_, rfl, ?_⟩
      · simp [tail.2.1]
      · apply List.pairwise_cons.mpr
        constructor
        · intro entry hentry
          obtain ⟨original, _, rfl⟩ := List.mem_map.mp hentry
          change first.val ≤ first.val + original.1.val
          omega
        · apply List.pairwise_map.mpr
          apply tail.2.2.1.imp
          intro left right horder
          change first.val + left.1.val ≤ first.val + right.1.val
          exact Nat.add_le_add_left horder _
      · intro entry hentry heq
        rcases List.mem_cons.mp hentry with rfl | hentry
        · rfl
        · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hentry
          apply tail.2.2.2 original horiginal
          dsimp [raise] at heq
          have := first.isLt
          omega
    let unpack (word : Words size) :
        Σ first : Fin (height + 1), Tails (height - first.val) size := by
      match heq : word.1 with
      | [] =>
        have := word.2.1
        simp [heq] at this
      | entry :: rest =>
        have hs := word.2.2.1
        rw [heq] at hs
        have hp := (List.pairwise_cons.mp hs).1
        refine ⟨entry.1, ⟨rest.map (lower entry.1), ?_, ?_, ?_⟩⟩
        · have hl := word.2.1
          rw [heq, List.length_cons] at hl
          simp only [List.length_map]
          omega
        · apply List.pairwise_map.mpr
          apply (List.pairwise_cons.mp hs).2.imp
          intro left right horder
          change left.1.val - entry.1.val ≤ right.1.val - entry.1.val
          exact Nat.sub_le_sub_right horder _
        · intro item hitem htop
          obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hitem
          apply word.2.2.2.2 original (by rw [heq]; exact List.mem_cons_of_mem _ horiginal)
          have hb : entry.1.val ≤ original.1.val := hp original horiginal
          dsimp [lower] at htop
          have := entry.1.isLt
          omega
    refine ⟨{
      toFun := unpack
      invFun := fun data => pack data.1 data.2
      left_inv := ?_
      right_inv := ?_ }⟩
    · intro word
      obtain ⟨word, hword⟩ := word
      cases word with
      | nil => simp at hword
      | cons entry rest =>
        apply Subtype.ext
        have hp := hword.2.1
        have hf := hword.2.2.1
        simp only [List.getD_cons_zero] at hf
        dsimp only [unpack, pack]
        change (entry.1, false) ::
          (rest.map (lower entry.1)).map (raise entry.1) = entry :: rest
        congr 1
        · exact Prod.ext rfl hf.symm
        · rw [List.map_map]
          calc
            _ = rest.map id := List.map_congr_left fun item hitem =>
              hraiseLower entry.1 item ((List.pairwise_cons.mp hp).1 item hitem)
            _ = rest := List.map_id _
    · rintro ⟨first, tail⟩
      dsimp only [unpack, pack]
      apply congrArg (Sigma.mk first)
      apply Subtype.ext
      change (tail.1.map (raise first)).map (lower first) = tail.1
      rw [List.map_map]
      calc
        _ = tail.1.map id := List.map_congr_left (fun item _ => hlowerRaise first item)
        _ = tail.1 := List.map_id _
  have hcount (size : ℕ) :
      (Nat.card (Words size) : ℚ) =
        PowerSeries.coeff size
          (unary * ∑ index ∈ Finset.range (height + 1), binary ^ index) := by
    obtain ⟨split⟩ := hsplit size
    rw [Nat.card_congr split, Nat.card_sigma, Nat.cast_sum]
    simp only [htailCount]
    rw [Finset.mul_sum, map_sum]
    have hreverse :
        (∑ first : Fin (height + 1),
          PowerSeries.coeff size (unary * binary ^ (height - first.val))) =
        ∑ first : Fin (height + 1),
          PowerSeries.coeff size (unary * binary ^ first.val) := by
      simpa only [Equiv.coe_fn_mk, Fin.rev, Nat.add_sub_add_right] using
        (Equiv.sum_comp
          (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ : Equiv.Perm (Fin (height + 1)))
          (fun first : Fin (height + 1) =>
            PowerSeries.coeff size (unary * binary ^ first.val)))
    rw [hreverse]
    exact (Finset.sum_range
      (fun index : ℕ => PowerSeries.coeff size (unary * binary ^ index))).symm
  have hseries :
      (PowerSeries.mk fun size => (Nat.card (Words size) : ℚ)) =
        unary * ∑ index ∈ Finset.range (height + 1), binary ^ index := by
    apply PowerSeries.ext
    intro size
    simpa using hcount size
  have hgeom (weight : ℚ) :
      (1 - PowerSeries.C weight * PowerSeries.X) *
        (PowerSeries.mk fun size => weight ^ size) = 1 := by
    apply PowerSeries.ext
    intro size
    cases size with
    | zero => simp
    | succ size =>
      simp only [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one,
        Nat.succ_ne_zero, ite_false, pow_succ]
      ring
  have hunary : (1 - PowerSeries.X) * unary = 1 := by
    simpa [unary] using hgeom 1
  have hbinary : (1 - 2 * PowerSeries.X) * binary = 1 := by
    simpa [binary, map_ofNat] using hgeom 2
  have hsum :
      2 * PowerSeries.X * (∑ index ∈ Finset.range (height + 1), binary ^ index) =
        binary ^ height - (1 - 2 * PowerSeries.X) := by
    have htel := geom_sum_mul binary (height + 1)
    have hmul := congrArg (fun series : PowerSeries ℚ =>
      series * (1 - 2 * PowerSeries.X)) htel
    rw [pow_succ] at hmul
    have hcancel : binary * (1 - 2 * PowerSeries.X) = 1 := by
      simpa only [mul_comm] using hbinary
    simp only [sub_mul, mul_assoc, hcancel, mul_one] at hmul
    linear_combination hmul
  let Shifted (size : ℕ) := {blocks : List (List ℕ) //
    blocks.flatten.length = size + 1 ∧ blocks.flatten.Pairwise (· ≤ ·) ∧
    (∀ label ∈ blocks.flatten, lower ≤ label ∧ label ≤ lower + height) ∧
    (∀ block ∈ blocks, block ≠ []) ∧
    ∀ block ∈ blocks, ∀ label ∈ block.tail, label < lower + height}
  have hshift (size : ℕ) : Nonempty (Shifted size ≃ Partitions size) := by
    let down (blocks : List (List ℕ)) := blocks.map (List.map (fun label => label - lower))
    let up (blocks : List (List ℕ)) := blocks.map (List.map (fun label => lower + label))
    have hdown (blocks : Shifted size) : down blocks.1 ∈ {blocks |
        blocks.flatten.length = size + 1 ∧ blocks.flatten.Pairwise (· ≤ ·) ∧
        (∀ label ∈ blocks.flatten, label ≤ height) ∧
        (∀ block ∈ blocks, block ≠ []) ∧
        ∀ block ∈ blocks, ∀ label ∈ block.tail, label < height} := by
      have hflat : (down blocks.1).flatten =
          blocks.1.flatten.map (fun label => label - lower) := by
        exact List.map_flatten.symm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hflat, List.length_map]
        exact blocks.2.1
      · rw [hflat]
        exact List.pairwise_map.mpr
          (blocks.2.2.1.imp (fun horder => Nat.sub_le_sub_right horder lower))
      · intro label hlabel
        rw [hflat] at hlabel
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hlabel
        have := blocks.2.2.2.1 original horiginal
        omega
      · intro block hblock
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hblock
        exact fun heq => blocks.2.2.2.2.1 original horiginal (List.map_eq_nil_iff.mp heq)
      · intro block hblock label hlabel
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hblock
        rw [← List.map_tail] at hlabel
        obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hlabel
        have hb := blocks.2.2.2.1 entry
          (List.mem_flatten.mpr ⟨original, horiginal, List.mem_of_mem_tail hentry⟩)
        have ht := blocks.2.2.2.2.2 original horiginal entry hentry
        omega
    have hup (blocks : Partitions size) : up blocks.1 ∈ {blocks |
        blocks.flatten.length = size + 1 ∧ blocks.flatten.Pairwise (· ≤ ·) ∧
        (∀ label ∈ blocks.flatten, lower ≤ label ∧ label ≤ lower + height) ∧
        (∀ block ∈ blocks, block ≠ []) ∧
        ∀ block ∈ blocks, ∀ label ∈ block.tail, label < lower + height} := by
      have hflat : (up blocks.1).flatten = blocks.1.flatten.map (fun label => lower + label) :=
        List.map_flatten.symm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hflat, List.length_map]
        exact blocks.2.1
      · rw [hflat]
        exact List.pairwise_map.mpr
          (blocks.2.2.1.imp (fun horder => Nat.add_le_add_left horder lower))
      · intro label hlabel
        rw [hflat] at hlabel
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hlabel
        have := blocks.2.2.2.1 original horiginal
        omega
      · intro block hblock
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hblock
        exact fun heq => blocks.2.2.2.2.1 original horiginal (List.map_eq_nil_iff.mp heq)
      · intro block hblock label hlabel
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hblock
        rw [← List.map_tail] at hlabel
        obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hlabel
        have ht := blocks.2.2.2.2.2 original horiginal entry hentry
        omega
    refine ⟨{
      toFun := fun blocks => ⟨down blocks.1, hdown blocks⟩
      invFun := fun blocks => ⟨up blocks.1, hup blocks⟩
      left_inv := ?_
      right_inv := ?_ }⟩
    · intro blocks
      apply Subtype.ext
      dsimp only [up, down]
      rw [List.map_map]
      calc
        _ = blocks.1.map id := List.map_congr_left fun block hblock => by
          dsimp only [Function.comp_def, id_eq]
          rw [List.map_map]
          calc
            _ = block.map id := List.map_congr_left fun label hlabel => by
              have := blocks.2.2.2.1 label (List.mem_flatten.mpr ⟨block, hblock, hlabel⟩)
              dsimp only [Function.comp_def, id_eq]
              omega
            _ = block := List.map_id _
        _ = blocks.1 := List.map_id _
    · intro blocks
      apply Subtype.ext
      dsimp only [up, down]
      rw [List.map_map]
      simp only [Function.comp_def, List.map_map, Nat.add_sub_cancel_left,
        List.map_id_fun', List.map_id]
  have hactualSeries :
      PowerSeries.mk (fun size => (Nat.card (Actual size) : ℚ)) =
        PowerSeries.mk (fun size => (Nat.card (Shifted size) : ℚ)) := by
    apply PowerSeries.ext
    intro size
    simp only [PowerSeries.coeff_mk, hactualCount]
    rfl
  change 2 * (1 - PowerSeries.X) *
    (1 + PowerSeries.X * PowerSeries.mk (fun size => (Nat.card (Actual size) : ℚ))) = _
  rw [hactualSeries]
  have hpartSeries :
      PowerSeries.mk (fun size => (Nat.card (Shifted size) : ℚ)) =
        PowerSeries.mk (fun size => (Nat.card (Words size) : ℚ)) := by
    apply PowerSeries.ext
    intro size
    obtain ⟨shift⟩ := hshift size
    simp only [PowerSeries.coeff_mk, Nat.card_congr shift, hpartitionCount]
  rw [hpartSeries]
  rw [hseries]
  calc
    _ = 2 * (1 - PowerSeries.X) +
        2 * PowerSeries.X *
          (∑ index ∈ Finset.range (height + 1), binary ^ index) := by
      linear_combination
        (2 * PowerSeries.X *
          (∑ index ∈ Finset.range (height + 1), binary ^ index)) * hunary
    _ = _ := by rw [hsum]; ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq152SuffixSeries
