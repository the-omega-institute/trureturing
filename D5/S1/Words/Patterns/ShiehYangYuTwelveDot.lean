/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDot
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDot
   mirror-E: none(waiver:machine-permutation-count)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Excursion reflection and up-step subsets count all permutations sorted by the machine. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotPaths
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDot

open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDyck
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotPaths
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotMachine
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs

theorem result : ShiehYangYuTwelveDotDefs.claim := by
  classical
  have decorated_path_equiv (size : ℕ) :
      {z : Σ word : List ℕ, {marks : Finset ℕ // marks ⊆ recordCuts word} //
        z.1.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] z.1} ≃
        {z : Σ path : DyckWord, Fin (excursions path).length → Bool //
          z.1.semilength = size} := by
    classical
    have subset_bits (records : Finset ℕ) :
        {marks : Finset ℕ // marks ⊆ records} ≃ (Fin records.card → Bool) := by
      let indices := (records.orderIsoOfFin rfl).toEquiv
      let selected (bits : Fin records.card → Bool) : Finset ℕ :=
        (Finset.univ.filter (fun index => bits index = true)).image
          (fun index => (indices index).val)
      have inside (bits : Fin records.card → Bool) : selected bits ⊆ records := by
        intro value member
        obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp member
        exact (indices index).property
      have marked (bits : Fin records.card → Bool) (index : Fin records.card) :
          (indices index).val ∈ selected bits ↔ bits index = true := by
        constructor
        · intro member
          obtain ⟨other, eligible, equal⟩ := Finset.mem_image.mp member
          have same : other = index := indices.injective (Subtype.ext equal)
          subst other
          exact (Finset.mem_filter.mp eligible).2
        · intro bit
          exact Finset.mem_image.mpr ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bit⟩,
            rfl⟩
      refine ⟨fun marks index => decide ((indices index).val ∈ marks.val),
        fun bits => ⟨selected bits, inside bits⟩, ?_, ?_⟩
      · intro marks
        apply Subtype.ext
        apply Finset.ext
        intro value
        by_cases member : value ∈ records
        · let index := indices.symm ⟨value, member⟩
          have recovered : (indices index).val = value :=
            congrArg Subtype.val (indices.apply_symm_apply ⟨value, member⟩)
          rw [← recovered, marked]
          simp only [decide_eq_true_eq]
        · exact iff_of_false (fun selected_member => member (inside _ selected_member))
            (fun marks_member => member (marks.property marks_member))
      · intro bits
        funext index
        change decide ((indices index).val ∈ selected bits) = bits index
        simp only [marked]
        cases bits index <;> rfl
    let avoiding := {word : List ℕ //
      word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word}
    let paths := {path : DyckWord // path.semilength = size}
    have transport (first_size second_size : ℕ)
        (first : {word : List ℕ // word.Perm (List.range' 1 first_size) ∧
          ¬ Occurs [2, 3, 1] word})
        (second : {word : List ℕ // word.Perm (List.range' 1 second_size) ∧
          ¬ Occurs [2, 3, 1] word})
        (sizes : first_size = second_size) (words : first.val = second.val) :
        (avoiding_encode first_size first).val =
          (avoiding_encode second_size second).val := by
      subst second_size
      rw [Subtype.ext words]
    let plain : avoiding ≃ paths :=
      { toFun := avoiding_encode size
        invFun := fun path => ⟨(avoiding_decode path.val).val, by
          simpa only [path.property] using (avoiding_decode path.val).property⟩
        left_inv := fun word => Subtype.ext (avoiding_inverse.1 size word)
        right_inv := fun path => by
          apply Subtype.ext
          exact (transport size path.val.semilength _ (avoiding_decode path.val)
            path.property.symm rfl).trans (avoiding_inverse.2.1 path.val) }
    let unpack := Equiv.subtypeSigmaEquiv
      (fun word : List ℕ => {marks : Finset ℕ // marks ⊆ recordCuts word})
      (fun word => word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word)
    let colors : (Σ word : avoiding, {marks : Finset ℕ // marks ⊆ recordCuts word.val}) ≃
        (Σ word : avoiding, Fin (recordCuts word.val).card → Bool) :=
      Equiv.sigmaCongrRight (fun word => subset_bits (recordCuts word.val))
    let transfer : (Σ word : avoiding, Fin (recordCuts word.val).card → Bool) ≃
        (Σ path : paths, Fin (excursions path.val).length → Bool) :=
      Equiv.sigmaCongr plain (fun word =>
        Equiv.piCongrLeft (fun _ => Bool)
          (finCongr (avoiding_inverse.2.2 size word)))
    let pack := (Equiv.subtypeSigmaEquiv
      (fun path : DyckWord => Fin (excursions path).length → Bool)
      (fun path => path.semilength = size)).symm
    exact unpack.trans (colors.trans (transfer.trans pack))
  let colored_lists : (Σ pieces : List DyckWord, Fin pieces.length → Bool) ≃
      List (Bool × DyckWord) := by
    refine
      { toFun := fun pieces => List.ofFn (fun index => (pieces.2 index, pieces.1.get index))
        invFun := fun pieces => ⟨pieces.map Prod.snd,
          fun index => (pieces.get ⟨index.val, by simpa using index.isLt⟩).1⟩
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨pieces, bits⟩
      have interiors :
          (List.ofFn (fun index => (bits index, pieces.get index))).map Prod.snd = pieces := by
        simpa only [List.map_ofFn, Function.comp_def] using List.ofFn_get pieces
      apply Sigma.ext interiors
      apply (Fin.heq_fun_iff (congrArg List.length interiors)).mpr
      intro index
      simp only [List.get_ofFn]
      rfl
    · intro pieces
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_map]
      · intro index first_bound second_bound
        simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_map]
  let colored : (Σ path : DyckWord, Fin (excursions path).length → Bool) ≃
      (Σ pieces : List DyckWord, Fin pieces.length → Bool) :=
    Equiv.sigmaCongr excursion_equiv
    (fun path => Equiv.refl (Fin (excursions path).length → Bool))
  let forests := colored.trans colored_lists
  have interiors (pieces : Σ entries : List DyckWord, Fin entries.length → Bool) :
      (colored_lists pieces).map Prod.snd = pieces.1 := by
    change (List.ofFn (fun index => (pieces.2 index, pieces.1.get index))).map Prod.snd = _
    simpa only [List.map_ofFn, Function.comp_def] using List.ofFn_get pieces.1
  have assembly_weight : ∀ pieces : List DyckWord,
      ((pieces.map DyckWord.nest).sum).semilength =
        (pieces.map (fun piece => piece.semilength + 1)).sum := by
    intro pieces
    induction pieces with
    | nil => rfl
    | cons piece pieces induction =>
      rw [List.map_cons, List.sum_cons, DyckWord.semilength_add,
        DyckWord.semilength_nest, induction, List.map_cons, List.sum_cons]
  have forest_weight (object : Σ path : DyckWord, Fin (excursions path).length → Bool) :
      ((forests object).map (fun piece => piece.2.semilength + 1)).sum =
        object.1.semilength := by
    have recovered := excursion_equiv.left_inv object.1
    change ((excursions object.1).map DyckWord.nest).sum = object.1 at recovered
    have alphabet := interiors (colored object)
    change (forests object).map Prod.snd = excursions object.1 at alphabet
    calc
      _ = (((forests object).map Prod.snd).map (fun piece => piece.semilength + 1)).sum := by
        simp only [List.map_map, Function.comp_def]
      _ = ((excursions object.1).map (fun piece => piece.semilength + 1)).sum := by
        rw [alphabet]
      _ = object.1.semilength := by rw [← assembly_weight, recovered]
  have step_total : ∀ word : List DyckStep,
      word.count DyckStep.U + word.count DyckStep.D = word.length := by
    intro word
    induction word with
    | nil => rfl
    | cons step word induction => cases step <;> simp_all <;> omega
  have up_indices : ∀ word : List DyckStep,
      (Finset.univ.filter (fun index : Fin word.length => word.get index = DyckStep.U)).card =
        word.count DyckStep.U := by
    intro word
    induction word with
    | nil => simp
    | cons step word induction =>
      rw [Finset.card_filter]
      change (∑ index : Fin (word.length + 1),
        if (step :: word).get index = DyckStep.U then 1 else 0) = _
      rw [Fin.sum_univ_succ]
      change (if step = DyckStep.U then 1 else 0) +
        (∑ index : Fin word.length, if word.get index = DyckStep.U then 1 else 0) = _
      rw [← Finset.card_filter, induction]
      cases step <;> simp [Nat.add_comm]
  intro size positive
  obtain ⟨length, size_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  subst size
  let colored_restricted :
      {z : Σ path : DyckWord, Fin (excursions path).length → Bool //
        z.1.semilength = length} ≃
      {pieces : List (Bool × DyckWord) //
        (pieces.map (fun piece => piece.2.semilength + 1)).sum = length} :=
    Equiv.subtypeEquiv forests (fun object => by rw [forest_weight object])
  let bridges := {word : List DyckStep //
    word.count DyckStep.U = length ∧ word.count DyckStep.D = length}
  let subsets := ↥((Finset.univ : Finset (Fin (2 * length))).powersetCard length)
  have bridge_subsets : bridges ≃ subsets := by
    have word_length (word : bridges) : word.val.length = 2 * length := by
      have total := step_total word.val
      rw [word.property.1, word.property.2] at total
      omega
    let selected (word : bridges) : Finset (Fin (2 * length)) :=
      Finset.univ.filter (fun index => word.val[index.val]'(by
        rw [word_length word]; exact index.isLt) = DyckStep.U)
    have selected_card (word : bridges) : (selected word).card = length := by
      have transport (word : List DyckStep) (amount : ℕ) (equal : word.length = amount) :
          (Finset.univ.filter (fun index : Fin amount =>
            word[index.val]'(equal.symm ▸ index.isLt) = DyckStep.U)).card =
          word.count DyckStep.U := by
        subst amount
        exact up_indices word
      exact (transport word.val _ (word_length word)).trans word.property.1
    let build (marks : subsets) : List DyckStep :=
      List.ofFn (fun index : Fin (2 * length) =>
        if index ∈ marks.val then DyckStep.U else DyckStep.D)
    have build_up (marks : subsets) : (build marks).count DyckStep.U = length := by
      have indices := up_indices (build marks)
      have transport (amount : ℕ) (bits : Fin amount → DyckStep) :
          (Finset.univ.filter (fun index : Fin (List.ofFn bits).length =>
            (List.ofFn bits).get index = DyckStep.U)).card =
            (Finset.univ.filter (fun index => bits index = DyckStep.U)).card := by
        apply Finset.card_equiv (finCongr (List.length_ofFn))
        intro index
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_ofFn]
        rfl
      rw [transport] at indices
      have alphabet : (Finset.univ.filter (fun index : Fin (2 * length) =>
          (if index ∈ marks.val then DyckStep.U else DyckStep.D) = DyckStep.U)) =
          marks.val := by
        ext index
        simp
      rw [alphabet] at indices
      exact indices.symm.trans (Finset.mem_powersetCard.mp marks.property).2
    have build_down (marks : subsets) : (build marks).count DyckStep.D = length := by
      have total := step_total (build marks)
      have amount : (build marks).length = 2 * length := List.length_ofFn
      rw [build_up marks, amount] at total
      omega
    refine
      { toFun := fun word => ⟨selected word,
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, selected_card word⟩⟩
        invFun := fun marks => ⟨build marks, build_up marks, build_down marks⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro word
      apply Subtype.ext
      apply List.ext_getElem
      · exact List.length_ofFn.trans (word_length word).symm
      · intro index built_bound word_bound
        change (List.ofFn (fun index : Fin (2 * length) =>
          if index ∈ selected word then DyckStep.U else DyckStep.D))[index] = word.val[index]
        rw [List.getElem_ofFn]
        simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
        cases word.val[index] <;> simp
    · intro marks
      apply Subtype.ext
      apply Finset.ext
      intro index
      change index ∈ selected ⟨build marks, build_up marks, build_down marks⟩ ↔ _
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
        build, List.getElem_ofFn]
      simp
  let equivalence := (machine_record_equiv length).trans
    ((decorated_path_equiv length).trans
      (colored_restricted.trans ((signed_bridge_equiv length).trans bridge_subsets)))
  have cardinal := Nat.card_congr equivalence
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at cardinal
  change (sortable (length + 1)).ncard = (2 * (length + 1) - 2).choose (length + 1 - 1)
  exact cardinal

end D5.S1.Words.Patterns.ShiehYangYuTwelveDot
