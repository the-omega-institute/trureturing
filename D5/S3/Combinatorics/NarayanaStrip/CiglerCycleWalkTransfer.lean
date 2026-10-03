/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer
   mirror-E: none(waiver:labeled-transfer-matrix)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Notation]
   utility: none
   digest: Labeled weighted words realize powers of their aggregated transition matrix. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionPairing
import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkDefs
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer

open scoped BigOperators
open CiglerStripExpansionDefs CiglerStripExpansionPairing CiglerCycleWalkDefs

noncomputable def wordContribution {State Label : Type*} [DecidableEq State]
    (next : State → Label → State) (cost : State → Label → ℤ)
    (target : State) : State → List Label → ℤ
  | start, [] => if start = target then 1 else 0
  | start, label :: rest =>
    cost start label * wordContribution next cost target (next start label) rest

theorem weighted_walks_eq_pow {State Label : Type*} [Fintype State] [DecidableEq State]
    [Fintype Label] (next : State → Label → State) (cost : State → Label → ℤ)
    (size : ℕ) (start target : State) :
    (∑ word : Fin size → Label, wordContribution next cost target start (List.ofFn word)) =
      ((Matrix.of fun source destination =>
        ∑ label, if next source label = destination then cost source label else 0) ^ size)
          start target := by
  classical
  let transfer : Matrix State State ℤ := Matrix.of fun source destination =>
    ∑ label, if next source label = destination then cost source label else 0
  change _ = (transfer ^ size) start target
  induction size generalizing start with
  | zero => simp [wordContribution, Matrix.one_apply]
  | succ size induction_hyp =>
    rw [← (Fin.consEquiv fun _ : Fin (size + 1) => Label).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons,
      wordContribution]
    simp_rw [← Finset.mul_sum, induction_hyp]
    rw [pow_succ', Matrix.mul_apply]
    simp only [transfer, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro label _
    simp

noncomputable def pairedTransition (bound : ℕ) (start : Fin bound)
    (block : Bool × Bool) : Fin bound × ℤ :=
  match block with
  | (true, true) =>
    if upper : start.val + 1 < bound then (⟨start.val + 1, upper⟩, 1) else (start, 0)
  | (false, false) =>
    if lower : 0 < start.val then
      (⟨start.val - 1, by omega⟩, -1) else (start, 0)
  | _ => (start, (-1) ^ start.val)

noncomputable def pairedAdj (bound : ℕ) : Matrix (Fin bound) (Fin bound) ℤ :=
  Matrix.of fun start target =>
    ∑ block : Bool × Bool,
      if (pairedTransition bound start block).1 = target then
        (pairedTransition bound start block).2 else 0

theorem paired_strip_eq_pow (bound size : ℕ) (positive : 1 ≤ bound) :
    signedStrip (2 * bound) (size + 1) =
      (pairedAdj bound ^ size) ⟨0, positive⟩ ⟨0, positive⟩ := by
  classical
  let zero : Fin bound := ⟨0, positive⟩
  let delta (block : Bool × Bool) : ℤ :=
    if block.1 then (if block.2 then 1 else 0) else (if block.2 then 0 else -1)
  let valid (start target : ℤ) (blocks : List (Bool × Bool)) : Prop :=
    (∀ index ≤ blocks.length,
      0 ≤ start + coarseHeight blocks index ∧ start + coarseHeight blocks index < bound) ∧
      start + coarseHeight blocks blocks.length = target
  have valid_cons (start target : ℤ) (block : Bool × Bool)
      (rest : List (Bool × Bool)) :
      valid start target (block :: rest) ↔
        0 ≤ start ∧ start < bound ∧ valid (start + delta block) target rest := by
    have heights (index : ℕ) : coarseHeight (block :: rest) (index + 1) =
        delta block + coarseHeight rest index := by
      simp [coarseHeight, delta, List.take_succ_cons]
    constructor
    · intro hypothesis
      have initial := hypothesis.1 0 (by simp)
      refine ⟨by simpa [coarseHeight] using initial.1,
        by simpa [coarseHeight] using initial.2, ?_, ?_⟩
      · intro index bounded
        have prefixBounds := hypothesis.1 (index + 1) (by simp; omega)
        simpa [heights, add_assoc] using prefixBounds
      · simpa [List.length_cons, heights, add_assoc] using hypothesis.2
    · rintro ⟨lower, upper, prefixes, terminal⟩
      constructor
      · intro index bounded
        cases index with
        | zero => simpa [coarseHeight] using And.intro lower upper
        | succ index =>
          have prefixBounds := prefixes index (by simp at bounded; omega)
          simpa [heights, add_assoc] using prefixBounds
      · simpa [List.length_cons, heights, add_assoc] using terminal
  have contribution (blocks : List (Bool × Bool)) (start target : Fin bound) :
      wordContribution (fun state block => (pairedTransition bound state block).1)
        (fun state block => (pairedTransition bound state block).2)
        target start blocks =
      if valid start.val target.val blocks then
        (motzkinWeight true start.val blocks).eval 1 else 0 := by
    induction blocks generalizing start with
    | nil =>
      have equal : valid start.val target.val [] ↔ start = target := by
        simp only [valid, List.length_nil, coarseHeight, List.take_nil, List.map_nil,
          List.sum_nil, add_zero]
        constructor
        · intro hypothesis
          exact Fin.ext (by exact_mod_cast hypothesis.2)
        · intro hypothesis
          subst target
          exact ⟨fun _ _ => ⟨by omega, by exact_mod_cast start.isLt⟩, rfl⟩
      simp [wordContribution, motzkinWeight, equal]
    | cons block rest induction_hyp =>
      rw [wordContribution]
      simp only [pairedTransition] at induction_hyp
      rcases block with ⟨first, second⟩
      cases first <;> cases second
      · by_cases lower : 0 < start.val
        · simp only [pairedTransition, dif_pos lower]
          rw [induction_hyp]
          have shifted : ((start.val - 1 : ℕ) : ℤ) = (start.val : ℤ) - 1 := by omega
          have validity : valid start.val target.val ((false, false) :: rest) ↔
              valid (start.val - 1 : ℕ) target.val rest := by
            rw [valid_cons]
            simp only [delta, Bool.false_eq_true, if_false, shifted]
            constructor <;> intro hypothesis
            · simpa [sub_eq_add_neg] using hypothesis.2.2
            · exact ⟨by omega, by exact_mod_cast start.isLt,
                by simpa [sub_eq_add_neg] using hypothesis⟩
          simp [motzkinWeight, Polynomial.eval_mul, validity]
        · have invalid : ¬valid start.val target.val ((false, false) :: rest) := by
            intro hypothesis
            have first := hypothesis.1 1 (by simp)
            simp [coarseHeight] at first
            omega
          simp [pairedTransition, lower, invalid]
      · simp only [pairedTransition]
        rw [induction_hyp]
        have validity : valid start.val target.val ((false, true) :: rest) ↔
            valid start.val target.val rest := by
          rw [valid_cons]
          simp [delta, show (0 : ℤ) ≤ start.val by omega,
            show (start.val : ℤ) < bound by exact_mod_cast start.isLt]
        simp [motzkinWeight, Polynomial.eval_mul, validity]
      · simp only [pairedTransition]
        rw [induction_hyp]
        have validity : valid start.val target.val ((true, false) :: rest) ↔
            valid start.val target.val rest := by
          rw [valid_cons]
          simp [delta, show (0 : ℤ) ≤ start.val by omega,
            show (start.val : ℤ) < bound by exact_mod_cast start.isLt]
        simp [motzkinWeight, Polynomial.eval_mul, validity]
      · by_cases upper : start.val + 1 < bound
        · simp only [pairedTransition, dif_pos upper]
          rw [induction_hyp]
          have validity : valid start.val target.val ((true, true) :: rest) ↔
              valid (start.val + 1 : ℕ) target.val rest := by
            rw [valid_cons]
            simp only [delta, if_true, Nat.cast_add, Nat.cast_one]
            constructor <;> intro hypothesis
            · exact hypothesis.2.2
            · exact ⟨by omega, by exact_mod_cast start.isLt, hypothesis⟩
          simp [motzkinWeight, validity]
        · have invalid : ¬valid start.val target.val ((true, true) :: rest) := by
            intro hypothesis
            have first := hypothesis.1 1 (by simp)
            simp [coarseHeight] at first
            omega
          simp [pairedTransition, upper, invalid]
  have zero_valid (blocks : List (Bool × Bool)) :
      valid 0 0 blocks ↔ IsMotzkinStrip (bound - 1) blocks := by
    simp only [valid, IsMotzkinStrip, zero_add]
    have upper (height : ℤ) : height < bound ↔ height ≤ (bound - 1 : ℕ) := by
      omega
    simp_rw [upper]
  unfold pairedAdj
  change signedStrip (2 * bound) (size + 1) =
    ((Matrix.of fun start target => ∑ block : Bool × Bool,
      if (pairedTransition bound start block).1 = target then
        (pairedTransition bound start block).2 else 0) ^ size) zero zero
  rw [← weighted_walks_eq_pow
    (fun state block => (pairedTransition bound state block).1)
    (fun state block => (pairedTransition bound state block).2) size zero zero]
  simp_rw [contribution]
  change signedStrip (2 * bound) (size + 1) =
    ∑ word : Fin size → Bool × Bool,
      if valid 0 0 (List.ofFn word) then (motzkinWeight true 0 (List.ofFn word)).eval 1 else 0
  simp_rw [zero_valid]
  obtain ⟨correspondence, forward, backward⟩ := pairing_bijection bound size positive
  let lists (Alphabet : Type) (length : ℕ) :
      (Fin length → Alphabet) ≃ {word : List Alphabet // word.length = length} :=
    { toFun := fun word => ⟨List.ofFn word, List.length_ofFn⟩
      invFun := fun word index => word.val.get ⟨index.val, by rw [word.property]; omega⟩
      left_inv := by intro word; funext index; simp
      right_inv := by
        rintro ⟨word, length_eq⟩
        subst length
        apply Subtype.ext
        exact List.ofFn_get word }
  let dyckWords := {word : Fin (2 * (size + 1)) → Bool //
    IsStripDyck (2 * bound) (List.ofFn word)}
  let motzkinWords := {word : Fin size → Bool × Bool //
    IsMotzkinStrip (bound - 1) (List.ofFn word)}
  let dyckEquiv : dyckWords ≃
      {path : List Bool // path.length = 2 * (size + 1) ∧ IsStripDyck (2 * bound) path} :=
    { toFun := fun word => ⟨List.ofFn word.val, List.length_ofFn, word.property⟩
      invFun := fun path =>
        ⟨(lists Bool (2 * (size + 1))).symm ⟨path.val, path.property.1⟩, by
          change IsStripDyck (2 * bound)
            ((lists Bool (2 * (size + 1)))
              ((lists Bool (2 * (size + 1))).symm ⟨path.val, path.property.1⟩)).val
          rw [Equiv.apply_symm_apply]
          exact path.property.2⟩
      left_inv := by
        intro word
        apply Subtype.ext
        exact (lists Bool (2 * (size + 1))).symm_apply_apply word.val
      right_inv := by
        intro path
        apply Subtype.ext
        exact congrArg (fun word : {word : List Bool //
            word.length = 2 * (size + 1)} => word.val)
          ((lists Bool (2 * (size + 1))).apply_symm_apply ⟨path.val, path.property.1⟩) }
  let motzkinEquiv : motzkinWords ≃
      {blocks : List (Bool × Bool) //
        blocks.length = size ∧ IsMotzkinStrip (bound - 1) blocks} :=
    { toFun := fun word => ⟨List.ofFn word.val, List.length_ofFn, word.property⟩
      invFun := fun blocks =>
        ⟨(lists (Bool × Bool) size).symm ⟨blocks.val, blocks.property.1⟩, by
          change IsMotzkinStrip (bound - 1)
            ((lists (Bool × Bool) size)
              ((lists (Bool × Bool) size).symm ⟨blocks.val, blocks.property.1⟩)).val
          rw [Equiv.apply_symm_apply]
          exact blocks.property.2⟩
      left_inv := by
        intro word
        apply Subtype.ext
        exact (lists (Bool × Bool) size).symm_apply_apply word.val
      right_inv := by
        intro blocks
        apply Subtype.ext
        exact congrArg (fun word : {word : List (Bool × Bool) //
            word.length = size} => word.val)
          ((lists (Bool × Bool) size).apply_symm_apply ⟨blocks.val, blocks.property.1⟩) }
  let wordsEquiv := dyckEquiv.trans (correspondence.trans motzkinEquiv.symm)
  unfold signedStrip stripSum
  rw [Polynomial.eval_finsetSum]
  simp only [apply_ite, Polynomial.eval_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun word => IsStripDyck (2 * bound) (List.ofFn word)) (F := inferInstance) _
    (by intro word; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  rw [Finset.sum_subtype
    (p := fun word => IsMotzkinStrip (bound - 1) (List.ofFn word)) (F := inferInstance) _
    (by intro word; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  apply Fintype.sum_equiv wordsEquiv
  intro word
  have expanded := forward (dyckEquiv word)
  have weighted := (pairing_weights (bound - 1)
    (correspondence (dyckEquiv word)).val (correspondence (dyckEquiv word)).property.2).2
  rw [expanded] at weighted
  change weight tauMinus (List.ofFn word.val) =
    motzkinWeight true 0 (correspondence (dyckEquiv word)).val at weighted
  rw [weighted]
  apply congrArg (fun blocks : List (Bool × Bool) => (motzkinWeight true 0 blocks).eval 1)
  exact (congrArg Subtype.val
    (motzkinEquiv.apply_symm_apply (correspondence (dyckEquiv word)))).symm

noncomputable def foldedAdj (vertices : ℕ) : Matrix (Fin vertices) (Fin vertices) ℤ :=
  Matrix.of fun start target =>
    if start.val + 1 = target.val ∨ target.val + 1 = start.val then 1
    else if start = target ∧ (start.val = 0 ∨ start.val + 1 = vertices) then 1 else 0

theorem strip_eq_folded (bound size : ℕ) (positive : 1 ≤ bound)
    (odd : bound % 2 = 1) :
    signedStrip (2 * bound) (size + 1) =
      (foldedAdj (bound + 1) ^ (size + 1)) ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  classical
  let sign (height : ℕ) : ℤ := (-1) ^ height
  let incidence : Matrix (Fin (bound + 1)) (Fin bound) ℤ := Matrix.of fun row index =>
    (if row.val = index.val then 1 else 0) +
      (if row.val = index.val + 1 then sign index.val else 0)
  let cofactor : Matrix (Fin bound) (Fin (bound + 1)) ℤ := Matrix.of fun index column =>
    (if column.val = index.val then sign index.val else 0) +
      (if column.val = index.val + 1 then 1 else 0)
  have sign_succ (height : ℕ) : sign (height + 1) = -sign height := by
    simp [sign, pow_succ]
  have sign_square (height : ℕ) : sign height * sign height = 1 := by
    rw [← pow_add]
    have twice : height + height = 2 * height := by omega
    simp [twice, pow_mul]
  have last_sign : sign (bound - 1) = 1 := by
    have even : bound - 1 = 2 * ((bound - 1) / 2) := by omega
    change (-1 : ℤ) ^ (bound - 1) = 1
    rw [even]
    simp [pow_mul]
  have two_terms {Index : Type} [Fintype Index] [DecidableEq Index]
      (first second : Index) (distinct : first ≠ second) (function : Index → ℤ)
      (support : ∀ index, index ≠ first → index ≠ second → function index = 0) :
      ∑ index, function index = function first + function second := by
    rw [← Finset.sum_pair distinct]
    symm
    apply Finset.sum_subset (by simp)
    intro index _ outside
    exact support index (by simp_all) (by simp_all)
  have cofactor_incidence : cofactor * incidence = pairedAdj bound := by
    ext start target
    rw [Matrix.mul_apply]
    have distinct : start.castSucc ≠ start.succ := by
      intro equal
      have values := congrArg Fin.val equal
      simp at values
    rw [two_terms start.castSucc start.succ distinct]
    · have signs : sign (target.val + 1) * sign target.val = -1 := by
        rw [sign_succ, neg_mul, sign_square]
      have self_next : start.val ≠ start.val + 1 := by omega
      have next_self : start.val + 1 ≠ start.val := by omega
      simp only [cofactor, incidence, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ,
        if_neg self_next, if_neg next_self, add_zero, zero_add]
      unfold pairedAdj
      simp only [Matrix.of_apply]
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      by_cases upper : start.val + 1 < bound <;> by_cases lower : 0 < start.val
      all_goals
        simp only [pairedTransition, upper, lower, dite_true, dite_false]
        simp only [Fin.ext_iff]
        by_cases equal : start.val = target.val
        · have equalFin : start = target := Fin.ext equal
          subst target
          have previous_ne : 0 < start.val → start.val - 1 ≠ start.val := by omega
          simp only [ite_true, ite_false, self_next, next_self, previous_ne, lower, sign,
            zero_add, add_zero, mul_one, one_mul]
        · by_cases above : start.val + 1 = target.val
          · have upper_true : start.val + 1 < bound := by omega
            have backward : start.val ≠ target.val + 1 := by omega
            have previous : start.val - 1 ≠ target.val := by omega
            have next_ne : start.val + 1 ≠ target.val + 1 := by omega
            simp only [if_neg equal, if_pos above, if_neg backward, if_neg previous,
              if_neg next_ne, ite_true, mul_zero, mul_one, add_zero, zero_add]
            all_goals omega
          · by_cases below : start.val = target.val + 1
            · have lower_true : 0 < start.val := by omega
              have previous : start.val - 1 = target.val := by omega
              have next_ne : start.val + 1 ≠ target.val + 1 := by omega
              simp only [if_neg equal, if_neg above, if_pos below, if_pos previous,
                if_neg next_ne, ite_true, mul_zero, add_zero, zero_add]
              all_goals first | omega | simpa only [below] using signs
            · have previous_ne : start.val - 1 ≠ target.val := by omega
              have next_ne : start.val + 1 ≠ target.val + 1 := by omega
              simp only [if_neg equal, if_neg above, if_neg below, if_neg previous_ne,
                if_neg next_ne, ite_true, mul_zero, add_zero]
    · intro index not_first not_second
      have first_ne : index.val ≠ start.val := fun values =>
        not_first (Fin.ext (by simpa using values))
      have second_ne : index.val ≠ start.val + 1 := fun values =>
        not_second (Fin.ext (by simpa using values))
      simp [cofactor, first_ne, second_ne]
  have incidence_cofactor : incidence * cofactor = foldedAdj (bound + 1) := by
    ext start target
    rw [Matrix.mul_apply]
    by_cases bottom : start.val = 0
    · let zero : Fin bound := ⟨0, positive⟩
      rw [Finset.sum_eq_single zero]
      · simp only [incidence, cofactor, foldedAdj, Matrix.of_apply, zero, bottom, Fin.ext_iff]
        split_ifs <;> norm_num [sign] <;>
          simp only [not_true_eq_false, not_false_eq_true, true_or, or_false, and_true,
            zero_add] at * <;> omega
      · intro index _ different
        have nonzero : index.val ≠ 0 := fun values => different (Fin.ext values)
        have not_succ : start.val ≠ index.val + 1 := by omega
        simp [incidence, bottom, nonzero, Ne.symm nonzero]
      · simp
    · by_cases top : start.val = bound
      · let last : Fin bound := ⟨bound - 1, by omega⟩
        rw [Finset.sum_eq_single last]
        · have last_succ : bound - 1 + 1 = bound := by omega
          have bound_ne : bound ≠ bound - 1 := by omega
          simp only [incidence, cofactor, foldedAdj, Matrix.of_apply, last, top, last_sign,
            last_succ, Fin.ext_iff]
          split_ifs <;> norm_num <;>
            (try simp only [or_true, and_true] at *) <;> omega
        · intro index _ different
          have not_equal : start.val ≠ index.val := by omega
          have not_succ : start.val ≠ index.val + 1 := by
            intro equal
            apply different
            apply Fin.ext
            simp only [last]
            omega
          simp [incidence, not_equal, not_succ]
        · simp
      · let upper : Fin bound := ⟨start.val, by omega⟩
        let lower : Fin bound := ⟨start.val - 1, by omega⟩
        have distinct : upper ≠ lower := by
          intro equal
          have values := congrArg Fin.val equal
          simp only [upper, lower] at values
          omega
        rw [two_terms upper lower distinct]
        · have previous_succ : start.val - 1 + 1 = start.val := by omega
          have sign_cancel : sign (start.val - 1) + sign start.val = 0 := by
            have sign_step := sign_succ (start.val - 1)
            rw [previous_succ] at sign_step
            rw [sign_step, add_neg_cancel]
          have ne_previous : start.val ≠ start.val - 1 := by omega
          have ne_next : start.val ≠ start.val + 1 := by omega
          simp only [incidence, cofactor, Matrix.of_apply, upper, lower, previous_succ,
            if_neg ne_previous, if_neg ne_next, add_zero, zero_add]
          by_cases equal : start = target
          · subst target
            simp only [foldedAdj, Matrix.of_apply, Fin.ext_iff]
            have next_self : start.val + 1 ≠ start.val := by omega
            simp only [ne_next, next_self, ne_previous, ite_false, ite_true, bottom, top,
              Nat.add_right_cancel_iff, false_or, true_and, add_zero, zero_add, mul_one,
              one_mul]
            exact (add_comm _ _).trans sign_cancel
          · have values_ne : target.val ≠ start.val := by
              intro values
              exact equal (Fin.ext values.symm)
            by_cases above : start.val + 1 = target.val
            · have ne_lower : target.val ≠ start.val - 1 := by omega
              simp only [foldedAdj, Matrix.of_apply, Fin.ext_iff]
              have not_equal : start.val ≠ target.val := by omega
              have next_eq : target.val = start.val + 1 := above.symm
              simp only [if_neg values_ne, if_neg ne_lower, if_pos next_eq,
                if_pos (Or.inl above), ite_true, mul_zero, one_mul, add_zero, zero_add]
            · by_cases below : target.val + 1 = start.val
              · have lower_eq : target.val = start.val - 1 := by omega
                simp only [foldedAdj, Matrix.of_apply, Fin.ext_iff]
                have next_ne : target.val ≠ start.val + 1 := by omega
                have not_equal : start.val ≠ target.val := by omega
                simp only [if_neg values_ne, if_neg next_ne, if_pos lower_eq,
                  if_pos (Or.inr below), ite_true, mul_zero, add_zero, zero_add, sign_square]
              · have ne_lower : target.val ≠ start.val - 1 := by omega
                simp only [foldedAdj, Matrix.of_apply, Fin.ext_iff]
                have next_ne : target.val ≠ start.val + 1 := by omega
                have below_ne : start.val ≠ target.val + 1 := by omega
                have not_equal : start.val ≠ target.val := by omega
                simp only [if_neg values_ne, if_neg ne_lower, if_neg next_ne, above, below,
                  not_equal, ite_true, ite_false, false_or, mul_zero, add_zero, false_and]
        · intro index not_upper not_lower
          have not_equal : start.val ≠ index.val := by
            intro equal
            exact not_upper (Fin.ext equal.symm)
          have not_succ : start.val ≠ index.val + 1 := by
            intro equal
            apply not_lower
            apply Fin.ext
            simp only [lower]
            omega
          simp [incidence, not_equal, not_succ]
  have powers (length : ℕ) :
      foldedAdj (bound + 1) ^ (length + 1) =
        incidence * pairedAdj bound ^ length * cofactor := by
    induction length with
    | zero => simpa using incidence_cofactor.symm
    | succ length induction_hyp =>
      rw [pow_succ, induction_hyp, ← incidence_cofactor, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Matrix.mul_assoc cofactor, cofactor_incidence,
        ← Matrix.mul_assoc (pairedAdj bound ^ length), ← pow_succ,
        ← Matrix.mul_assoc]
  rw [paired_strip_eq_pow bound size positive, powers]
  let zero : Fin bound := ⟨0, positive⟩
  simp only [Matrix.mul_apply]
  have first_row (index : Fin bound) : incidence ⟨0, by omega⟩ index =
      if index = zero then 1 else 0 := by
    simp only [incidence, Matrix.of_apply, zero, Fin.ext_iff]
    simp [eq_comm]
  have first_column (index : Fin bound) : cofactor index ⟨0, by omega⟩ =
      if index = zero then 1 else 0 := by
    by_cases equal : index = zero
    · subst index
      simp [cofactor, zero, sign]
    · have nonzero : index.val ≠ 0 := fun values => equal (Fin.ext values)
      simp [cofactor, zero, equal, nonzero, Ne.symm nonzero]
  simp_rw [first_row, first_column]
  simp [zero]

end D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer
