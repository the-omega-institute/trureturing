/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Prefix
   mirror-E: none(waiver:running-maximum-bijection)
   anchors: []
   utility: none
   digest: Running maxima and retained strict increases biject the two Catalan prefix classes. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Right

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Prefix

def retainIncreases (previous : ℕ) : List ℕ → List ℕ
  | [] => []
  | value :: rest =>
    (if previous < value then value else 0) :: retainIncreases value rest

theorem catalan_prefix_bijection (size maximum : ℕ) :
    Nonempty
      ({word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
        word.Pairwise (fun first second => first = 0 ∨ second = 0 ∨ first < second) ∧
        word.foldr max 0 = maximum} ≃
      {word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
        word.Pairwise (· ≤ ·) ∧ word.foldr max 0 = maximum}) := by
  have hscancons (previous value : ℕ) (rest : List ℕ) :
      ((value :: rest).scanl max previous).tail =
        max previous value :: (rest.scanl max (max previous value)).tail := by
    cases rest <;> simp [List.scanl_cons]
  have hrun : ∀ word : List ℕ, ∀ previous base : ℕ,
      previous ≤ base →
      (∀ index < word.length, word.getD index 0 ≤ base + index) →
      word.Pairwise (fun first second => first = 0 ∨ second = 0 ∨ first < second) →
      (∀ value ∈ word, value = 0 ∨ previous < value) →
      let output := (word.scanl max previous).tail
      output.length = word.length ∧ output.Pairwise (· ≤ ·) ∧
      (∀ value ∈ output, previous ≤ value) ∧
      (∀ index < output.length, output.getD index 0 ≤ base + index) ∧
      max previous (output.foldr max 0) = max previous (word.foldr max 0) ∧
      retainIncreases previous output = word := by
    intro word
    induction word with
    | nil => intro previous base hprev hbound hpair hvalues; simp [retainIncreases]
    | cons value rest ih =>
      intro previous base hprev hbound hpair hvalues
      have hvalue : value ≤ base := by simpa using hbound 0 (by simp)
      have hcase : value = 0 ∨ previous < value := hvalues value (by simp)
      have htailbound : ∀ index < rest.length,
          rest.getD index 0 ≤ (base + 1) + index := by
        intro index hindex
        have := hbound (index + 1) (by simp; omega)
        simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have htailvalues : ∀ entry ∈ rest, entry = 0 ∨ max previous value < entry := by
        intro entry hentry
        rcases hvalues entry (by simp [hentry]) with heq | hpos
        · exact Or.inl heq
        · have hp := (List.pairwise_cons.mp hpair).1 entry hentry
          rcases hcase with hzero | hpositive
          · exact Or.inr (by simpa [hzero] using hpos)
          · rcases hp with hzero | heq | hlt
            · omega
            · exact Or.inl heq
            · exact Or.inr (by omega)
      obtain ⟨hlen, hmono, hentries, hb, hm, hinverse⟩ :=
        ih (max previous value) (base + 1) (by omega) htailbound
          (List.pairwise_cons.mp hpair).2 htailvalues
      dsimp only
      rw [hscancons]
      refine ⟨by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨hentries, hmono⟩
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · omega
        · have := hentries entry hentry
          omega
      · intro index hindex
        cases index with
        | zero => simp only [List.getD_cons_zero]; omega
        | succ index =>
          have hindex' : index < (rest.scanl max (max previous value)).tail.length := by
            simpa using hindex
          have := hb index hindex'
          simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · simpa only [List.foldr_cons, ← max_assoc, max_self] using hm
      · simp only [retainIncreases, hinverse]
        rcases hcase with rfl | hpositive
        · simp
        · simp [max_eq_right (by omega : previous ≤ value), hpositive]
  have hretain : ∀ word : List ℕ, ∀ previous base : ℕ,
      (∀ index < word.length, word.getD index 0 ≤ base + index) →
      word.Pairwise (· ≤ ·) → (∀ value ∈ word, previous ≤ value) →
      let output := retainIncreases previous word
      output.length = word.length ∧
      output.Pairwise (fun first second => first = 0 ∨ second = 0 ∨ first < second) ∧
      (∀ value ∈ output, value = 0 ∨ previous < value) ∧
      (∀ index < output.length, output.getD index 0 ≤ base + index) ∧
      max previous (output.foldr max 0) = max previous (word.foldr max 0) ∧
      (output.scanl max previous).tail = word := by
    intro word
    induction word with
    | nil => intro previous base hbound hpair hvalues; simp [retainIncreases]
    | cons value rest ih =>
      intro previous base hbound hpair hvalues
      have hprev : previous ≤ value := hvalues value (by simp)
      have hvalue : value ≤ base := by simpa using hbound 0 (by simp)
      have htailbound : ∀ index < rest.length,
          rest.getD index 0 ≤ (base + 1) + index := by
        intro index hindex
        have := hbound (index + 1) (by simp; omega)
        simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      obtain ⟨hlen, hpair', hentries, hb, hm, hinverse⟩ :=
        ih value (base + 1) htailbound (List.pairwise_cons.mp hpair).2
          (List.pairwise_cons.mp hpair).1
      dsimp only
      simp only [retainIncreases]
      by_cases hstrict : previous < value
      · simp only [if_pos hstrict]
        refine ⟨by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hpair'⟩
          intro entry hentry
          rcases hentries entry hentry with rfl | hlt
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hlt)
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact Or.inr hstrict
          · rcases hentries entry hentry with rfl | hlt
            · exact Or.inl rfl
            · exact Or.inr (by omega)
        · intro index hindex
          cases index with
          | zero => simpa using hvalue
          | succ index =>
            have := hb index (by simpa using hindex)
            simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
        · simp only [List.foldr_cons, ← max_assoc, max_eq_right hprev]
          exact hm
        · rw [hscancons, max_eq_right hprev, hinverse]
      · simp only [if_neg hstrict]
        have heq : previous = value := by omega
        subst previous
        refine ⟨by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
        · apply List.pairwise_cons.mpr
          exact ⟨fun entry hentry => Or.inl rfl, hpair'⟩
        · intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact Or.inl rfl
          · exact hentries entry hentry
        · intro index hindex
          cases index with
          | zero => simp
          | succ index =>
            have := hb index (by simpa using hindex)
            simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
        · simpa only [List.foldr_cons, Nat.max_zero, ← max_assoc, max_self] using hm
        · rw [hscancons, Nat.max_zero, hinverse]
  refine ⟨{
    toFun := fun word => ?_
    invFun := fun word => ?_
    left_inv := ?_
    right_inv := ?_ }⟩
  · refine ⟨(word.val.scanl max 0).tail, ?_⟩
    obtain ⟨hlen, hmono, _, hb, hm, _⟩ := hrun word.val 0 0 (by omega)
      (by simpa only [InversionSeqDefs.IsInversionSeq, Nat.zero_add]
        using word.property.2.1) word.property.2.2.1
      (by intro value hvalue; omega)
    exact ⟨hlen.trans word.property.1,
      by simpa [InversionSeqDefs.IsInversionSeq] using hb,
      hmono, by simpa using hm.trans (by simpa using word.property.2.2.2)⟩
  · refine ⟨retainIncreases 0 word.val, ?_⟩
    obtain ⟨hlen, hpair, _, hb, hm, _⟩ := hretain word.val 0 0
      (by simpa only [InversionSeqDefs.IsInversionSeq, Nat.zero_add]
        using word.property.2.1) word.property.2.2.1
      (by intro value hvalue; omega)
    exact ⟨hlen.trans word.property.1,
      by simpa [InversionSeqDefs.IsInversionSeq] using hb,
      hpair, by simpa using hm.trans (by simpa using word.property.2.2.2)⟩
  · intro word
    apply Subtype.ext
    exact (hrun word.val 0 0 (by omega)
      (by simpa only [InversionSeqDefs.IsInversionSeq, Nat.zero_add]
        using word.property.2.1)
      word.property.2.2.1 (by intro value hvalue; omega)).2.2.2.2.2
  · intro word
    apply Subtype.ext
    exact (hretain word.val 0 0
      (by simpa only [InversionSeqDefs.IsInversionSeq, Nat.zero_add]
        using word.property.2.1)
      word.property.2.2.1 (by intro value hvalue; omega)).2.2.2.2.2

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Prefix
