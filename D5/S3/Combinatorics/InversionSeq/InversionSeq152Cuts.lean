/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Cuts
   mirror-E: none(waiver:independent-permitted-block-joins)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: Permitted joins independently enumerate the interval partitions of a label list. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Labels
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Cuts

theorem independent_join_bijection (labels : List ℕ) (upper : ℕ) :
    Nonempty
      ({blocks : List (List ℕ) // (∀ block ∈ blocks, block ≠ []) ∧
        blocks.flatten = labels ∧
        (∀ block ∈ blocks, ∀ label ∈ block.tail, label < upper)} ≃
      Fin (2 ^ (labels.tail.countP (fun label => label < upper)))) := by
  classical
  let Part := fun word : List ℕ =>
    {blocks : List (List ℕ) // (∀ block ∈ blocks, block ≠ []) ∧
      blocks.flatten = word ∧
      (∀ block ∈ blocks, ∀ label ∈ block.tail, label < upper)}
  have hparse (first : ℕ) (rest : List ℕ) (partition : Part (first :: rest)) :
      ∃ inside more, partition.val = (first :: inside) :: more ∧
        inside ++ more.flatten = rest := by
    obtain ⟨pieces, hp⟩ := partition
    cases pieces with
    | nil => simp at hp
    | cons block more =>
      cases block with
      | nil => exact (hp.1 [] (by simp) rfl).elim
      | cons minimum inside =>
        have heq := List.cons.inj hp.2.1
        exact ⟨inside, more, by simp [heq.1], heq.2⟩
  let hcut (first : ℕ) (rest : List ℕ) : Part rest → Part (first :: rest) := by
    intro partition
    refine ⟨[first] :: partition.val, ?_, ?_, ?_⟩
    · intro block hblock
      rcases List.mem_cons.mp hblock with rfl | hblock
      · simp
      · exact partition.property.1 block hblock
    · simpa using congrArg (List.cons first) partition.property.2.1
    · intro block hblock label hlabel
      rcases List.mem_cons.mp hblock with rfl | hblock
      · simp at hlabel
      · exact partition.property.2.2 block hblock label hlabel
  let hjoin (first second : ℕ) (rest : List ℕ) (hsecond : second < upper) :
      Part (second :: rest) → Part (first :: second :: rest) := by
    intro partition
    refine ⟨partition.val.modifyHead (List.cons first), ?_⟩
    obtain ⟨inside, more, heq, hrest⟩ := hparse second rest partition
    refine ⟨?_, ?_, ?_⟩
    all_goals rw [heq]; simp only [List.modifyHead_cons]
    · intro block hblock
      rcases List.mem_cons.mp hblock with rfl | hblock
      · simp
      · exact partition.property.1 block (by rw [heq]; simp [hblock])
    · simp only [List.flatten_cons, List.cons_append]
      rw [hrest]
    · intro block hblock label hlabel
      rcases List.mem_cons.mp hblock with rfl | hblock
      · rcases List.mem_cons.mp hlabel with rfl | hlabel
        · exact hsecond
        · exact partition.property.2.2 (second :: inside) (by rw [heq]; simp)
            label hlabel
      · exact partition.property.2.2 block (by rw [heq]; simp [hblock]) label hlabel
  have hcutVal (first : ℕ) (rest : List ℕ) (partition : Part rest) :
      (hcut first rest partition).val = [first] :: partition.val := rfl
  have hjoinVal (first second : ℕ) (rest : List ℕ) (hsecond : second < upper)
      (partition : Part (second :: rest)) :
      (hjoin first second rest hsecond partition).val =
        partition.val.modifyHead (List.cons first) := rfl
  let hremove (first : ℕ) (rest : List ℕ) (inside : List ℕ)
      (more : List (List ℕ)) (partition : Part (first :: rest))
      (heq : partition.val = (first :: inside) :: more) (hrest : inside ++ more.flatten = rest)
      (hnonempty : inside ≠ []) : Part rest := by
    refine ⟨inside :: more, ?_, ?_, ?_⟩
    · intro block hblock
      rcases List.mem_cons.mp hblock with rfl | hblock
      · exact hnonempty
      · exact partition.property.1 block (by rw [heq]; simp [hblock])
    · exact hrest
    · intro block hblock label hlabel
      rcases List.mem_cons.mp hblock with rfl | hblock
      · exact partition.property.2.2 (first :: block) (by rw [heq]; simp)
          label (List.mem_of_mem_tail hlabel)
      · exact partition.property.2.2 block (by rw [heq]; simp [hblock]) label hlabel
  let hdrop (first : ℕ) (rest : List ℕ) (more : List (List ℕ))
      (partition : Part (first :: rest)) (heq : partition.val = [first] :: more)
      (hrest : more.flatten = rest) : Part rest := by
    refine ⟨more, ?_, hrest, ?_⟩
    · intro block hblock
      exact partition.property.1 block (by rw [heq]; simp [hblock])
    · intro block hblock label hlabel
      exact partition.property.2.2 block (by rw [heq]; simp [hblock]) label hlabel
  have hstep (first second : ℕ) (rest : List ℕ) (hsecond : second < upper) :
      Nonempty (Part (first :: second :: rest) ≃
        (Part (second :: rest) ⊕ Part (second :: rest))) := by
    let insert : (Part (second :: rest) ⊕ Part (second :: rest)) →
        Part (first :: second :: rest) :=
      Sum.elim (hcut first (second :: rest)) (hjoin first second rest hsecond)
    have hinjective : Function.Injective insert := by
      intro left right heq
      have hvalues := congrArg Subtype.val heq
      cases left with
      | inl left =>
        cases right with
        | inl right =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact (List.cons.inj hvalues).2
        | inr right =>
          obtain ⟨inside, more, hright, _⟩ := hparse second rest right
          simp only [insert, Sum.elim_inl, Sum.elim_inr, hcutVal, hjoinVal,
            hright, List.modifyHead_cons] at hvalues
          have := (List.cons.inj (List.cons.inj hvalues).1).2
          simp at this
      | inr left =>
        cases right with
        | inl right =>
          obtain ⟨inside, more, hleft, _⟩ := hparse second rest left
          simp only [insert, Sum.elim_inl, Sum.elim_inr, hcutVal, hjoinVal,
            hleft, List.modifyHead_cons] at hvalues
          have := (List.cons.inj (List.cons.inj hvalues).1).2
          simp at this
        | inr right =>
          obtain ⟨leftInside, leftMore, hleft, _⟩ := hparse second rest left
          obtain ⟨rightInside, rightMore, hright, _⟩ := hparse second rest right
          simp only [insert, Sum.elim_inr, hjoinVal, hleft, hright,
            List.modifyHead_cons] at hvalues
          obtain ⟨hhead, hmore⟩ := List.cons.inj hvalues
          have hinside := (List.cons.inj (List.cons.inj hhead).2).2
          apply congrArg Sum.inr
          apply Subtype.ext
          rw [hleft, hright, hinside, hmore]
    have hsurjective : Function.Surjective insert := by
      intro partition
      obtain ⟨inside, more, heq, hrest⟩ := hparse first (second :: rest) partition
      cases inside with
      | nil =>
        let remaining := hdrop first (second :: rest) more partition heq hrest
        refine ⟨Sum.inl remaining, ?_⟩
        apply Subtype.ext
        exact heq.symm
      | cons minimum tail =>
        obtain ⟨hminimum, htail⟩ := List.cons.inj hrest
        subst minimum
        let remaining := hremove first (second :: rest) (second :: tail) more
          partition heq hrest (by simp)
        refine ⟨Sum.inr remaining, ?_⟩
        apply Subtype.ext
        simpa [insert, remaining, hjoinVal, hremove] using heq.symm
    exact ⟨(Equiv.ofBijective insert ⟨hinjective, hsurjective⟩).symm⟩
  have hforced (first second : ℕ) (rest : List ℕ) (hsecond : ¬ second < upper) :
      Nonempty (Part (first :: second :: rest) ≃ Part (second :: rest)) := by
    have hinjective : Function.Injective (hcut first (second :: rest)) := by
      intro left right heq
      apply Subtype.ext
      exact (List.cons.inj (congrArg Subtype.val heq)).2
    have hsurjective : Function.Surjective (hcut first (second :: rest)) := by
      intro partition
      obtain ⟨inside, more, heq, hrest⟩ := hparse first (second :: rest) partition
      cases inside with
      | nil =>
        refine ⟨hdrop first (second :: rest) more partition heq hrest, ?_⟩
        apply Subtype.ext
        exact heq.symm
      | cons minimum tail =>
        have hminimum := (List.cons.inj hrest).1
        subst minimum
        exact (hsecond (partition.property.2.2 (first :: second :: tail)
          (by rw [heq]; simp) second (by simp))).elim
    exact ⟨(Equiv.ofBijective (hcut first (second :: rest))
      ⟨hinjective, hsurjective⟩).symm⟩
  have hnil (partition : Part []) : partition.val = [] := by
    cases hpieces : partition.val with
    | nil => rfl
    | cons block more =>
      have hflat := partition.property.2.1
      rw [hpieces, List.flatten_cons] at hflat
      have hempty := List.append_eq_nil_iff.mp hflat
      exact (partition.property.1 block (by rw [hpieces]; simp) hempty.1).elim
  have hempty : Nonempty (Part [] ≃ Fin 1) := by
    refine ⟨{
      toFun := fun _ => 0
      invFun := fun _ => ⟨[], by simp⟩
      left_inv := fun partition => Subtype.ext (hnil partition).symm
      right_inv := fun index => Fin.ext (by omega) }⟩
  have hsingle (first : ℕ) : Nonempty (Part [first] ≃ Fin 1) := by
    have hval (partition : Part [first]) : partition.val = [[first]] := by
      obtain ⟨inside, more, heq, hrest⟩ := hparse first [] partition
      obtain ⟨hinside, hmore⟩ := List.append_eq_nil_iff.mp hrest
      have hmore' : more = [] := hnil ⟨more, by
        refine ⟨?_, hmore, ?_⟩
        · intro block hblock
          exact partition.property.1 block (by rw [heq]; simp [hblock])
        · intro block hblock label hlabel
          exact partition.property.2.2 block (by rw [heq]; simp [hblock]) label hlabel⟩
      simpa [hinside, hmore'] using heq
    refine ⟨{
      toFun := fun _ => 0
      invFun := fun _ => ⟨[[first]], by simp⟩
      left_inv := fun partition => Subtype.ext (hval partition).symm
      right_inv := fun index => Fin.ext (by omega) }⟩
  have hresult : ∀ word : List ℕ,
      Nonempty (Part word ≃ Fin (2 ^ (word.tail.countP (fun label => label < upper)))) := by
    intro word
    induction word with
    | nil => simpa using hempty
    | cons first rest ih =>
      cases rest with
      | nil => simpa using hsingle first
      | cons second rest =>
        by_cases hsecond : second < upper
        · obtain ⟨step⟩ := hstep first second rest hsecond
          obtain ⟨remaining⟩ := ih
          refine ⟨step.trans ((Equiv.sumCongr remaining remaining).trans
            (finSumFinEquiv.trans (finCongr ?_)))⟩
          simp [hsecond, Nat.pow_succ]
          omega
        · obtain ⟨step⟩ := hforced first second rest hsecond
          obtain ⟨remaining⟩ := ih
          refine ⟨step.trans (remaining.trans (finCongr ?_))⟩
          simp [hsecond]
  exact hresult labels

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Cuts
