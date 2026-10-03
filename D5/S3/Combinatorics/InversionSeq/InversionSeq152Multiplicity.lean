/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity
   mirror-E: none(waiver:ordered-choice-multiplicities)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Ordered label choices biject independent multiplicities with binary choice fibers. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Cuts
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Multiplicity

theorem ordered_choice_multiplicity_bijection {α : Type*} [Fintype α] [LinearOrder α]
    (permitted : α → Prop) [DecidablePred permitted] (size : ℕ) :
    ∃ equivalence :
      {word : List (α × Bool) // word.length = size ∧
        word.Pairwise (fun first second => first.1 ≤ second.1) ∧
        ∀ entry ∈ word, ¬ permitted entry.1 → entry.2 = false} ≃
      Σ multiplicity : {counts : α → ℕ // ∑ label, counts label = size},
        ∀ label, {bits : List Bool // bits.length = multiplicity.1 label ∧
          (¬ permitted label → ∀ bit ∈ bits, bit = false)},
      (∀ word label, ((equivalence word).2 label).1 =
        (word.1.filter (fun entry => entry.1 = label)).map Prod.snd) ∧
      (∀ multiplicity : {counts : α → ℕ // ∑ label, counts label = size},
        Nat.card (∀ label, {bits : List Bool // bits.length = multiplicity.1 label ∧
          (¬ permitted label → ∀ bit ∈ bits, bit = false)}) =
        ∏ label, (if permitted label then 2 else 1) ^ multiplicity.1 label) := by
  classical
  let keys := (Finset.univ : Finset α).sort (· ≤ ·)
  let collect (word : List (α × Bool)) (label : α) :=
    (word.filter (fun entry => entry.1 = label)).map Prod.snd
  let assemble (choices : α → List Bool) :=
    keys.flatMap (fun label => (choices label).map (fun bit => (label, bit)))
  have hkeys : keys.Pairwise (· < ·) :=
    (Finset.sortedLT_sort (Finset.univ : Finset α)).pairwise
  have hkeymem (label : α) : label ∈ keys := by simp [keys]
  have hpack (word : List (α × Bool)) (label : α) :
      (collect word label).map (fun bit => (label, bit)) =
        word.filter (fun entry => entry.1 = label) := by
    dsimp only [collect]
    rw [List.map_map]
    calc
      _ = (word.filter (fun entry => entry.1 = label)).map id := by
        apply List.map_congr_left
        intro entry hentry
        have heq : entry.1 = label := by simpa using (List.mem_filter.mp hentry).2
        exact Prod.ext heq.symm rfl
      _ = _ := List.map_id _
  have hregroup : ∀ labels : List α, labels.Pairwise (· < ·) →
      ∀ word : List (α × Bool),
      word.Pairwise (fun first second => first.1 ≤ second.1) →
      (∀ entry ∈ word, entry.1 ∈ labels) →
      labels.flatMap (fun label => word.filter (fun entry => entry.1 = label)) = word := by
    intro labels
    induction labels with
    | nil =>
      intro hlabels word hword hmem
      cases word with
      | nil => rfl
      | cons entry rest => exact (List.not_mem_nil (hmem entry (by simp))).elim
    | cons label labels ih =>
      intro hlabels word hword hmem
      have hlabels' := List.pairwise_cons.mp hlabels
      have hsplit : ∀ input : List (α × Bool),
          input.Pairwise (fun first second => first.1 ≤ second.1) →
          (∀ entry ∈ input, entry.1 ∈ label :: labels) →
          input.filter (fun entry => entry.1 = label) ++
            input.filter (fun entry => entry.1 ≠ label) = input := by
        intro input
        induction input with
        | nil => simp
        | cons first rest ihword =>
          intro hsorted hmembers
          have hp := List.pairwise_cons.mp hsorted
          have hrestmem : ∀ entry ∈ rest, entry.1 ∈ label :: labels :=
            fun entry hentry => hmembers entry (List.mem_cons_of_mem _ hentry)
          by_cases heq : first.1 = label
          · simpa [heq] using congrArg (List.cons first) (ihword hp.2 hrestmem)
          · have hfirstmem : first.1 ∈ labels := by
              simpa [heq] using hmembers first (by simp)
            have hfirstgt := hlabels'.1 first.1 hfirstmem
            have hrestne : ∀ entry ∈ rest, entry.1 ≠ label := by
              intro entry hentry hequal
              have := hp.1 entry hentry
              rw [hequal] at this
              exact (not_le_of_gt hfirstgt) this
            have hempty : rest.filter (fun entry => entry.1 = label) = [] :=
              List.filter_eq_nil_iff.mpr (fun entry hentry => by
                simpa using hrestne entry hentry)
            have hself : rest.filter (fun entry => entry.1 ≠ label) = rest :=
              List.filter_eq_self.mpr (fun entry hentry => by
                simpa using hrestne entry hentry)
            have hdec : decide (first.1 ≠ label) = true := by simpa using heq
            simp only [List.filter_cons, heq, decide_false, hdec,
              Bool.false_eq_true, ite_false, ite_true, hempty, hself, List.nil_append]
      have hremaining : ∀ entry ∈ word.filter (fun entry => entry.1 ≠ label),
          entry.1 ∈ labels := by
        intro entry hentry
        have hm := List.mem_filter.mp hentry
        have hne : entry.1 ≠ label := by simpa using hm.2
        simpa [hne] using hmem entry hm.1
      have hrest := ih hlabels'.2 (word.filter (fun entry => entry.1 ≠ label))
        (hword.filter _) hremaining
      have hfilters : ∀ other ∈ labels,
          (word.filter (fun entry => entry.1 ≠ label)).filter
              (fun entry => entry.1 = other) =
            word.filter (fun entry => entry.1 = other) := by
        intro other hother
        have hne : other ≠ label := ne_of_gt (hlabels'.1 other hother)
        rw [List.filter_filter]
        congr 1
        funext entry
        by_cases heq : entry.1 = other
        · simp [heq, hne]
        · simp [heq]
      rw [List.flatMap_cons]
      have heqrest : labels.flatMap
          (fun other => word.filter (fun entry => entry.1 = other)) =
          word.filter (fun entry => entry.1 ≠ label) := by
        rw [← hrest]
        apply List.flatMap_congr
        intro other hother
        exact (hfilters other hother).symm
      rw [heqrest]
      exact hsplit word hword hmem
  have hassemble_collect (word : List (α × Bool))
      (hword : word.Pairwise (fun first second => first.1 ≤ second.1)) :
      assemble (collect word) = word := by
    change keys.flatMap (fun label => (collect word label).map
      (fun bit => (label, bit))) = word
    calc
      _ = keys.flatMap (fun label => word.filter (fun entry => entry.1 = label)) := by
        apply List.flatMap_congr
        intro label _
        exact hpack word label
      _ = word := hregroup keys hkeys word hword (fun entry _ => hkeymem entry.1)
  have hcollect_assemble (choices : α → List Bool) (label : α) :
      collect (assemble choices) label = choices label := by
    have hselect : ∀ labels : List α, labels.Nodup → label ∈ labels →
        collect (labels.flatMap (fun key => (choices key).map (fun bit => (key, bit))))
          label = choices label := by
      intro labels
      induction labels with
      | nil => simp
      | cons first rest ih =>
        intro hnodup hmem
        have hn := List.nodup_cons.mp hnodup
        by_cases heq : first = label
        · subst first
          have hempty : collect
              (rest.flatMap (fun key => (choices key).map (fun bit => (key, bit))))
              label = [] := by
            simp only [collect, List.filter_flatMap, List.map_flatMap]
            apply List.flatMap_eq_nil_iff.mpr
            intro key hkey
            have hne : key ≠ label := by intro h; subst key; exact hn.1 hkey
            simp [List.filter_map, Function.comp_def, hne]
          simp [List.flatMap_cons, collect, List.filter_append, List.map_append,
            List.filter_map, Function.comp_def, hempty]
        · have hlabel : label ∈ rest := (List.mem_cons.mp hmem).resolve_left (Ne.symm heq)
          have htail := ih hn.2 hlabel
          simpa [List.flatMap_cons, collect, List.filter_append, List.map_append,
            List.filter_map, Function.comp_def, heq] using htail
    exact hselect keys hkeys.nodup (hkeymem label)
  have hassemble_sorted (choices : α → List Bool) :
      (assemble choices).Pairwise (fun first second => first.1 ≤ second.1) := by
    have hsorted : ∀ labels : List α, labels.Pairwise (· < ·) →
        (labels.flatMap (fun key => (choices key).map (fun bit => (key, bit)))).Pairwise
          (fun first second => first.1 ≤ second.1) := by
      intro labels
      induction labels with
      | nil => simp
      | cons first rest ih =>
        intro hp
        have hp' := List.pairwise_cons.mp hp
        rw [List.flatMap_cons, List.pairwise_append]
        refine ⟨?_, ih hp'.2, ?_⟩
        · apply List.pairwise_map.mpr
          exact List.pairwise_of_forall (fun _ _ => le_rfl)
        · intro left hleft right hright
          obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hleft
          obtain ⟨key, hkey, hright⟩ := List.mem_flatMap.mp hright
          obtain ⟨other, _, rfl⟩ := List.mem_map.mp hright
          exact le_of_lt (hp'.1 key hkey)
    exact hsorted keys hkeys
  have hassemble_length (choices : α → List Bool) :
      (assemble choices).length = ∑ label, (choices label).length := by
    simp only [assemble, List.length_flatMap, List.length_map]
    have heq := List.sum_toFinset (fun label => (choices label).length) hkeys.nodup
    simpa [keys] using heq.symm
  let Words := {word : List (α × Bool) // word.length = size ∧
    word.Pairwise (fun first second => first.1 ≤ second.1) ∧
    ∀ entry ∈ word, ¬ permitted entry.1 → entry.2 = false}
  let Families := {choices : α → List Bool //
    (∑ label, (choices label).length) = size ∧
    ∀ label, ¬ permitted label → ∀ bit ∈ choices label, bit = false}
  have hforward (word : Words) :
      (∑ label, (collect word.1 label).length) = size ∧
      ∀ label, ¬ permitted label → ∀ bit ∈ collect word.1 label, bit = false := by
    refine ⟨?_, ?_⟩
    · rw [← hassemble_length, hassemble_collect word.1 word.2.2.1]
      exact word.2.1
    · intro label hnot bit hbit
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hbit
      have hm := List.mem_filter.mp hentry
      have heq : entry.1 = label := by simpa using hm.2
      exact word.2.2.2 entry hm.1 (by simpa [heq] using hnot)
  have hbackward (family : Families) :
      (assemble family.1).length = size ∧
      (assemble family.1).Pairwise (fun first second => first.1 ≤ second.1) ∧
      ∀ entry ∈ assemble family.1, ¬ permitted entry.1 → entry.2 = false := by
    refine ⟨(hassemble_length family.1).trans family.2.1,
      hassemble_sorted family.1, ?_⟩
    intro entry hentry hnot
    obtain ⟨label, _, hentry⟩ := List.mem_flatMap.mp hentry
    obtain ⟨bit, hbit, rfl⟩ := List.mem_map.mp hentry
    exact family.2.2 label hnot bit hbit
  let regroup : Words ≃ Families :=
    { toFun := fun word => ⟨collect word.1, hforward word⟩
      invFun := fun family => ⟨assemble family.1, hbackward family⟩
      left_inv := fun word => Subtype.ext (hassemble_collect word.1 word.2.2.1)
      right_inv := fun family => Subtype.ext (funext (hcollect_assemble family.1)) }
  let Multiplicities := Σ multiplicity : {counts : α → ℕ // ∑ label, counts label = size},
    ∀ label, {bits : List Bool // bits.length = multiplicity.1 label ∧
      (¬ permitted label → ∀ bit ∈ bits, bit = false)}
  let bundle : Families ≃ Multiplicities :=
    { toFun := fun family =>
        ⟨⟨fun label => (family.1 label).length, family.2.1⟩,
          fun label => ⟨family.1 label, rfl, family.2.2 label⟩⟩
      invFun := fun data => ⟨fun label => (data.2 label).1, by
        refine ⟨?_, fun label => (data.2 label).2.2⟩
        simpa only [(data.2 _).2.1] using data.1.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro data
        apply Sigma.ext
        · apply Subtype.ext
          exact funext (fun label => (data.2 label).2.1)
        · apply Function.hfunext rfl
          intro label other heq
          cases heq
          apply (Subtype.heq_iff_coe_eq (fun bits => by
            dsimp only
            rw [(data.2 label).2.1])).mpr
          rfl }
  refine ⟨regroup.trans bundle, ?_, ?_⟩
  · intro word label
    rfl
  · intro multiplicity
    rw [Nat.card_pi]
    apply Finset.prod_congr rfl
    intro label _
    let count := multiplicity.1 label
    by_cases hp : permitted label
    · let forget : {bits : List Bool // bits.length = count ∧
          (¬ permitted label → ∀ bit ∈ bits, bit = false)} ≃ List.Vector Bool count :=
        { toFun := fun bits => ⟨bits.1, bits.2.1⟩
          invFun := fun bits => ⟨bits.1, bits.2, fun hnot => (hnot hp).elim⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr (forget.trans (Equiv.vectorEquivFin Bool count)), Nat.card_fun]
      simp [hp, Nat.card_eq_fintype_card, count]
    · let unique : {bits : List Bool // bits.length = count ∧
          (¬ permitted label → ∀ bit ∈ bits, bit = false)} ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨List.replicate count false, by simp⟩
          left_inv := by
            intro bits
            apply Subtype.ext
            exact (List.eq_replicate_iff.mpr ⟨bits.2.1, bits.2.2 hp⟩).symm
          right_inv := fun _ => rfl }
      rw [Nat.card_congr unique]
      simp [hp, Nat.card_eq_fintype_card]

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Multiplicity
