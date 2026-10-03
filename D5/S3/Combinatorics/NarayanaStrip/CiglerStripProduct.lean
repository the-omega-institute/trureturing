/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripProduct
   mirror-E: none(waiver:external-named-strip-product-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Proves Cigler's strip product at heights 4m and 4m+1 coefficientwise. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductSeries
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripProduct

open CiglerStripExpansionDefs CiglerStripProductAlgebra CiglerStripProductSeries

theorem result : CiglerStripProductDefs.claim := by
  classical
  have first_return (bound : ℕ) (weights : ℕ → Polynomial ℤ) :
      (∀ inside outside : List Bool,
        IsStripDyck bound inside → IsStripDyck (bound + 1) outside →
        IsStripDyck (bound + 1) (true :: inside ++ false :: outside) ∧
          weight weights (true :: inside ++ false :: outside) =
            weights 0 * weight (fun height => weights (height + 1)) inside *
              weight weights outside) ∧
      (∀ path : List Bool, IsStripDyck (bound + 1) path → path ≠ [] →
        ∃! parts : List Bool × List Bool,
          IsStripDyck bound parts.1 ∧ IsStripDyck (bound + 1) parts.2 ∧
            path = true :: parts.1 ++ false :: parts.2) := by
    classical
    have append_height (left right : List Bool) (index : ℕ) :
        heightAfter (left ++ right) index = heightAfter left index +
          heightAfter right (index - left.length) := by
      simp [heightAfter, List.take_append, List.map_append, List.sum_append]
    have saturated_height (path : List Bool) (index : ℕ) (large : path.length ≤ index) :
        heightAfter path index = heightAfter path path.length := by
      simp [heightAfter, List.take_of_length_le large]
    have cons_height (step : Bool) (path : List Bool) (index : ℕ) :
        heightAfter (step :: path) (index + 1) =
          (if step then (1 : ℤ) else -1) + heightAfter path index := by
      simp [heightAfter]
    let from_height (start : ℤ) (path : List Bool) : Polynomial ℤ :=
      ((List.range path.length).map fun index =>
        if path.getD index true then 1
        else weights (start + heightAfter path (index + 1)).toNat).prod
    have from_cons (start : ℤ) (step : Bool) (path : List Bool) :
        from_height start (step :: path) =
          (if step then 1 else weights (start + (if step then 1 else -1)).toNat) *
            from_height (start + (if step then 1 else -1)) path := by
      simp only [from_height, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, List.prod_cons, List.getD_cons_zero, Function.comp_def,
        Nat.succ_eq_add_one, List.getD_cons_succ, heightAfter, List.take_succ_cons,
        List.take_zero, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
    have from_append (start : ℤ) (left right : List Bool) :
        from_height start (left ++ right) = from_height start left *
          from_height (start + heightAfter left left.length) right := by
      induction left generalizing start with
      | nil => simp [from_height, heightAfter]
      | cons step left recurse =>
        simp only [List.cons_append, from_cons, List.length_cons, cons_height]
        rw [recurse]
        simp only [add_assoc, mul_assoc]
    have from_zero (path : List Bool) : from_height 0 path = weight weights path := by
      simp [from_height, weight]
    have shifted_weight (path : List Bool) (valid : IsStripDyck bound path) :
        from_height 1 path = weight (fun height => weights (height + 1)) path := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro index member
      have index_lt := List.mem_range.mp member
      have nonnegative := (valid.1 (index + 1) (by omega)).1
      have landing : (1 + heightAfter path (index + 1)).toNat =
          (heightAfter path (index + 1)).toNat + 1 := by omega
      simp only [landing]
    let up : Bool → DyckStep := fun step => if step then DyckStep.U else DyckStep.D
    let down : DyckStep → Bool := fun step => match step with
      | .U => true
      | .D => false
    have decode_encode (path : List Bool) : (path.map up).map down = path := by
      induction path with
      | nil => rfl
      | cons step path recurse => cases step <;> simp [up, down, recurse]
    have encode_decode (path : List DyckStep) : (path.map down).map up = path := by
      induction path with
      | nil => rfl
      | cons step path recurse => cases step <;> simp [up, down, recurse]
    have count_height (path : List Bool) :
        heightAfter path path.length =
          ((path.map up).count DyckStep.U : ℤ) - (path.map up).count DyckStep.D := by
      induction path with
      | nil => simp [heightAfter]
      | cons step path recurse =>
        rw [List.length_cons, show path.length + 1 = Nat.succ path.length from rfl,
          cons_height]
        simp only [List.map_cons, List.count_cons, Nat.cast_add]
        rw [recurse]
        cases step <;> simp [up] <;> omega
    have prefix_count (path : List Bool) (index : ℕ) :
        heightAfter path index =
          (((path.map up).take index).count DyckStep.U : ℤ) -
            ((path.map up).take index).count DyckStep.D := by
      calc
        heightAfter path index = heightAfter (path.take index) (path.take index).length :=
          by simp only [heightAfter, List.take_length]
        _ = _ := by simpa only [List.map_take] using count_height (path.take index)
    let encode (path : List Bool) (valid : IsStripDyck (bound + 1) path) : DyckWord :=
      ⟨path.map up, by
        have balanced := valid.2
        rw [count_height] at balanced
        omega, fun index => by
        by_cases small : index ≤ path.length
        · have nonnegative := (valid.1 index small).1
          rw [prefix_count] at nonnegative
          omega
        · have balanced : heightAfter path index = 0 := by
            rw [saturated_height path index (by omega), valid.2]
          rw [prefix_count] at balanced
          omega⟩
    have decoded_nonnegative (word : DyckWord) (index : ℕ) :
        0 ≤ heightAfter (word.toList.map down) index := by
      rw [prefix_count, encode_decode]
      exact sub_nonneg.mpr (by exact_mod_cast word.count_D_le_count_U index)
    have decoded_balanced (word : DyckWord) :
        heightAfter (word.toList.map down) (word.toList.map down).length = 0 := by
      rw [count_height, encode_decode, word.count_U_eq_count_D, sub_self]
    have assemble (inside outside : List Bool) (inside_valid : IsStripDyck bound inside)
        (outside_valid : IsStripDyck (bound + 1) outside) :
        IsStripDyck (bound + 1) (true :: inside ++ false :: outside) := by
      constructor
      · intro index index_le
        cases index with
        | zero => simp [heightAfter]; omega
        | succ index =>
          simp only [List.cons_append] at index_le ⊢
          rw [cons_height, if_pos rfl, append_height]
          by_cases before : index ≤ inside.length
          · rw [Nat.sub_eq_zero_of_le before]
            change 0 ≤ 1 + (heightAfter inside index + 0) ∧
              1 + (heightAfter inside index + 0) ≤ (bound + 1 : ℕ)
            have limits := inside_valid.1 index before
            constructor <;> omega
          · have after : inside.length ≤ index := by omega
            rw [saturated_height inside index after, inside_valid.2]
            obtain ⟨remaining, remaining_eq⟩ : ∃ remaining, index - inside.length =
                remaining + 1 := ⟨index - inside.length - 1, by omega⟩
            rw [remaining_eq, cons_height]
            simp only [Bool.false_eq_true, if_false]
            have limits := outside_valid.1 remaining (by
              simp only [List.length_cons, List.length_append] at index_le
              omega)
            constructor <;> omega
      · simp only [List.cons_append, List.length_cons, List.length_append]
        rw [cons_height, if_pos rfl, append_height,
          saturated_height inside _ (by omega), inside_valid.2]
        have remaining : inside.length + (outside.length + 1) - inside.length =
            outside.length + 1 := by omega
        rw [remaining, cons_height]
        simp only [Bool.false_eq_true, if_false, outside_valid.2]
        omega
    constructor
    · intro inside outside inside_valid outside_valid
      refine ⟨assemble inside outside inside_valid outside_valid, ?_⟩
      simp only [List.cons_append]
      rw [← from_zero, from_cons, if_pos rfl, one_mul]
      norm_num only [ite_true]
      rw [from_append, inside_valid.2, add_zero, from_cons]
      simp only [Bool.false_eq_true, if_false]
      norm_num only [ite_true]
      rw [from_zero, shifted_weight inside inside_valid]
      simp only [Int.toNat_zero]
      ring
    · intro path valid nonempty
      let word := encode path valid
      have word_ne : word ≠ 0 := by
        intro empty
        have lists := congrArg (fun value : DyckWord => value.toList.map down) empty
        apply nonempty
        change (path.map up).map down = [].map down at lists
        simpa only [decode_encode, List.map_nil] using lists
      let inside := word.insidePart.toList.map down
      let outside := word.outsidePart.toList.map down
      have split : path = true :: inside ++ false :: outside := by
        have lists := congrArg (fun value : DyckWord => value.toList.map down)
          (DyckWord.nest_insidePart_add_outsidePart word_ne)
        change (([DyckStep.U] ++ word.insidePart.toList ++ [DyckStep.D]) ++
          word.outsidePart.toList).map down = (path.map up).map down at lists
        simpa only [decode_encode, List.map_append, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.append_assoc, down, inside, outside]
          using lists.symm
      have inside_valid : IsStripDyck bound inside := by
        refine ⟨?_, decoded_balanced word.insidePart⟩
        intro index index_le
        refine ⟨decoded_nonnegative word.insidePart index, ?_⟩
        have limit := (valid.1 (index + 1) (by rw [split]; simp; omega)).2
        rw [split] at limit
        simp only [List.cons_append] at limit
        rw [cons_height, if_pos rfl, append_height] at limit
        rw [Nat.sub_eq_zero_of_le index_le] at limit
        change 1 + (heightAfter inside index + 0) ≤ (bound + 1 : ℕ) at limit
        exact_mod_cast (by omega : heightAfter inside index ≤ (bound : ℤ))
      have outside_valid : IsStripDyck (bound + 1) outside := by
        refine ⟨?_, decoded_balanced word.outsidePart⟩
        intro index index_le
        refine ⟨decoded_nonnegative word.outsidePart index, ?_⟩
        have limit := (valid.1 (inside.length + (index + 1) + 1) (by
          rw [split]; simp only [List.length_cons, List.length_append]; omega)).2
        rw [split] at limit
        simp only [List.cons_append] at limit
        rw [cons_height, if_pos rfl, append_height,
          saturated_height inside _ (by omega), inside_valid.2] at limit
        have remaining : inside.length + (index + 1) - inside.length = index + 1 := by
          omega
        rw [remaining, cons_height] at limit
        simp only [Bool.false_eq_true, if_false] at limit
        omega
      refine ⟨(inside, outside), ⟨inside_valid, outside_valid, split⟩, ?_⟩
      intro parts parts_valid
      let inner : DyckWord :=
        ⟨parts.1.map up, by
          have balanced := parts_valid.1.2
          rw [count_height] at balanced
          omega, fun index => by
          by_cases small : index ≤ parts.1.length
          · have nonnegative := (parts_valid.1.1 index small).1
            rw [prefix_count] at nonnegative
            omega
          · have balanced : heightAfter parts.1 index = 0 := by
              rw [saturated_height _ _ (by omega), parts_valid.1.2]
            rw [prefix_count] at balanced
            omega⟩
      let outer := encode parts.2 parts_valid.2.1
      have encoded_split : word = inner.nest + outer := by
        apply DyckWord.ext
        simp only [word, encode, inner, outer, DyckWord.nest]
        change path.map up = ([DyckStep.U] ++ parts.1.map up ++ [DyckStep.D]) ++
          parts.2.map up
        rw [parts_valid.2.2]
        simp [List.map_append, up]
      have same_inner : inner = word.insidePart := by simp [encoded_split]
      have same_outer : outer = word.outsidePart := by simp [encoded_split]
      apply Prod.ext
      · have lists := congrArg (fun value : DyckWord => value.toList.map down) same_inner
        simpa [inner, decode_encode, inside] using lists
      · have lists := congrArg (fun value : DyckWord => value.toList.map down) same_outer
        simpa [outer, encode, decode_encode, outside] using lists
  
  have first_return_recursion (weights : ℕ → Polynomial ℤ) (bound size : ℕ) :
      stripSum weights (bound + 1) (size + 1) =
        weights 0 * ∑ index ∈ Finset.range (size + 1),
          stripSum (fun height => weights (height + 1)) bound index *
            stripSum weights (bound + 1) (size - index) := by
    classical
    let Paths (height length : ℕ) :=
      {steps : Fin (2 * length) → Bool // IsStripDyck height (List.ofFn steps)}
    let Splits := Σ index : Fin (size + 1), Paths bound index.val ×
      Paths (bound + 1) (size - index.val)
    have as_sum (sequence : ℕ → Polynomial ℤ) (height length : ℕ) :
        stripSum sequence height length =
          ∑ path : Paths height length, weight sequence (List.ofFn path.val) := by
      rw [stripSum, ← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    let tuple (path : List Bool) {length : ℕ} (length_eq : path.length = 2 * length) :
        Fin (2 * length) → Bool := fun index => path.get (Fin.cast length_eq.symm index)
    have tuple_list (path : List Bool) {length : ℕ}
        (length_eq : path.length = 2 * length) : List.ofFn (tuple path length_eq) = path := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using length_eq.symm
      · intro index first_lt second_lt
        simp [tuple]
    have even_length (path : List Bool) {height : ℕ} (valid : IsStripDyck height path) :
        path.length = 2 * (path.length / 2) := by
      have count_formula (word : List Bool) :
          heightAfter word word.length = (word.count true : ℤ) - word.count false ∧
            word.length = word.count true + word.count false := by
        induction word with
        | nil => simp [heightAfter]
        | cons step word recurse =>
          have height_step : heightAfter (step :: word) (step :: word).length =
              (if step then (1 : ℤ) else -1) + heightAfter word word.length := by
            simp [heightAfter]
          rw [height_step]
          cases step
          · simp only [List.count_cons, List.length_cons]
            change -1 + heightAfter word word.length =
              (word.count true : ℤ) - (word.count false + 1 : ℕ) ∧
                word.length + 1 = word.count true + (word.count false + 1)
            omega
          · simp only [List.count_cons, List.length_cons]
            change 1 + heightAfter word word.length =
              (word.count true + 1 : ℕ) - (word.count false : ℤ) ∧
                word.length + 1 = word.count true + 1 + word.count false
            omega
      have counts := count_formula path
      have balanced := valid.2
      omega
    let join : Splits → Paths (bound + 1) (size + 1) := fun split => by
      let path := true :: List.ofFn split.2.1.val ++ false :: List.ofFn split.2.2.val
      have length_eq : path.length = 2 * (size + 1) := by
        simp only [path, List.length_append, List.length_cons, List.length_ofFn]
        have index_lt := split.1.isLt
        omega
      refine ⟨tuple path length_eq, ?_⟩
      rw [tuple_list _ length_eq]
      exact ((first_return bound weights).1 _ _ split.2.1.property
        split.2.2.property).1
    have join_list (split : Splits) : List.ofFn (join split).val =
        true :: List.ofFn split.2.1.val ++ false :: List.ofFn split.2.2.val := by
      dsimp only [join]
      apply tuple_list
      simp only [List.length_append, List.length_cons, List.length_ofFn]
      have index_lt := split.1.isLt
      omega
    have injective : Function.Injective join := by
      intro left right joined
      have nonempty : true :: List.ofFn left.2.1.val ++
          false :: List.ofFn left.2.2.val ≠ [] := by simp
      obtain ⟨parts, valid, unique⟩ := (first_return bound weights).2 _
        (join left).property (by rw [join_list]; exact nonempty)
      have left_parts : (List.ofFn left.2.1.val, List.ofFn left.2.2.val) = parts :=
        unique _ ⟨left.2.1.property, left.2.2.property, join_list left⟩
      have right_parts : (List.ofFn right.2.1.val, List.ofFn right.2.2.val) = parts :=
        unique _ ⟨right.2.1.property, right.2.2.property, by rw [joined, join_list]⟩
      have same_parts := left_parts.trans right_parts.symm
      have inner_eq := congrArg Prod.fst same_parts
      have outer_eq := congrArg Prod.snd same_parts
      have lengths := congrArg List.length inner_eq
      simp only [List.length_ofFn] at lengths
      have indices : left.1 = right.1 := Fin.ext (by omega)
      rcases left with ⟨left_index, left_inner, left_outer⟩
      rcases right with ⟨right_index, right_inner, right_outer⟩
      dsimp only at indices
      subst right_index
      congr 1
      apply Prod.ext
      · exact Subtype.ext (List.ofFn_injective inner_eq)
      · exact Subtype.ext (List.ofFn_injective outer_eq)
    have surjective : Function.Surjective join := by
      intro path
      have nonempty : List.ofFn path.val ≠ [] := by
        intro empty
        have lengths := congrArg List.length empty
        simp only [List.length_ofFn, List.length_nil] at lengths
        omega
      obtain ⟨parts, parts_valid, _⟩ :=
        (first_return bound weights).2 _ path.property nonempty
      have inside_even := even_length parts.1 parts_valid.1
      have outside_even := even_length parts.2 parts_valid.2.1
      have lengths := congrArg List.length parts_valid.2.2
      simp only [List.length_ofFn, List.length_cons, List.length_append] at lengths
      have index_lt : parts.1.length / 2 < size + 1 := by omega
      let index : Fin (size + 1) := ⟨parts.1.length / 2, index_lt⟩
      have outside_length : parts.2.length = 2 * (size - index.val) := by
        dsimp only [index]
        omega
      let inside : Paths bound index.val :=
        ⟨tuple parts.1 inside_even, by rw [tuple_list _ inside_even]; exact parts_valid.1⟩
      let outside : Paths (bound + 1) (size - index.val) :=
        ⟨tuple parts.2 outside_length,
          by rw [tuple_list _ outside_length]; exact parts_valid.2.1⟩
      refine ⟨⟨index, inside, outside⟩, ?_⟩
      apply Subtype.ext
      apply List.ofFn_injective
      rw [join_list]
      change true :: List.ofFn (tuple parts.1 inside_even) ++
        false :: List.ofFn (tuple parts.2 outside_length) = List.ofFn path.val
      rw [tuple_list _ inside_even, tuple_list _ outside_length]
      exact parts_valid.2.2.symm
    let correspondence : Splits ≃ Paths (bound + 1) (size + 1) :=
      Equiv.ofBijective join ⟨injective, surjective⟩
    rw [as_sum, ← correspondence.sum_comp]
    change (∑ split : Splits, weight weights (List.ofFn (join split).val)) = _
    simp_rw [join_list]
    have products (split : Splits) :
        weight weights (true :: List.ofFn split.2.1.val ++ false ::
          List.ofFn split.2.2.val) = weights 0 *
          weight (fun height => weights (height + 1)) (List.ofFn split.2.1.val) *
            weight weights (List.ofFn split.2.2.val) :=
      ((first_return bound weights).1 _ _ split.2.1.property split.2.2.property).2
    simp_rw [products]
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← as_sum, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun index =>
      stripSum (fun height => weights (height + 1)) bound index *
        stripSum weights (bound + 1) (size - index)) (size + 1)
  
  let : Algebra (Polynomial ℤ) (PowerSeries (Polynomial ℤ)) :=
    MvPowerSeries.instAlgebra
  let t : PowerSeries (Polynomial ℤ) := PowerSeries.C Polynomial.X
  let z : PowerSeries (Polynomial ℤ) := PowerSeries.X
  let series (weights : ℕ → Polynomial ℤ) (height : ℕ) :=
    PowerSeries.mk (stripSum weights height)
  let a (weights : ℕ → Polynomial ℤ) (index : ℕ) : PowerSeries (Polynomial ℤ) :=
    PowerSeries.C (weights index) * z
  let star : PowerSeries (Polynomial ℤ) →+* PowerSeries (Polynomial ℤ) :=
    (PowerSeries.rescale (-1)).comp
      (PowerSeries.map (Polynomial.compRingHom (-Polynomial.X)))
  let square : PowerSeries (Polynomial ℤ) →+* PowerSeries (Polynomial ℤ) :=
    (PowerSeries.expand 2 (by decide)).toRingHom.comp
      (PowerSeries.map (Polynomial.compRingHom (Polynomial.X ^ 2)))
  have rescale_constant (polynomial : Polynomial ℤ) :
      PowerSeries.rescale (-1) (PowerSeries.C polynomial) =
        PowerSeries.C polynomial := by
    apply PowerSeries.ext
    intro degree
    cases degree <;> simp [PowerSeries.coeff_C]
  have star_t : star t = -t := by
    simp [star, t, rescale_constant]
  have star_z : star z = -z := by
    simp [star, z, PowerSeries.rescale_X]
  have square_t : square t = t ^ 2 := by
    simp [square, t, PowerSeries.expand_C]
  have square_z : square z = z ^ 2 := by
    simp [square, z]
  have map_cont (hom : PowerSeries (Polynomial ℤ) →+* PowerSeries (Polynomial ℤ))
      (coefficients : ℕ → PowerSeries (Polynomial ℤ))
      (initial previous : PowerSeries (Polynomial ℤ)) (index : ℕ) :
      hom (cont coefficients initial previous index) =
        cont (fun index => hom (coefficients index)) (hom initial) (hom previous) index :=
    by
      induction index using Nat.twoStepInduction with
      | zero => rfl
      | one => rfl
      | more index before after => simp only [cont, map_sub, map_mul, before, after]
  let minus (left right : PowerSeries (Polynomial ℤ)) (index : ℕ) :=
    (if index % 4 = 0 then 1 else if index % 4 = 1 then left
      else if index % 4 = 2 then -1 else -left) * right
  let plus (left right : PowerSeries (Polynomial ℤ)) (index : ℕ) :=
    (if index % 2 = 0 then 1 else left) * right
  have minus_weights : a tauMinus = minus t z := by
    funext index
    dsimp only [a, tauMinus, minus]
    split_ifs <;> simp [t]
  have plus_weights : a tauPlus = plus t z := by
    funext index
    dsimp only [a, tauPlus, plus]
    split_ifs <;> simp [t]
  have star_weights : (fun index => star (a tauMinus index)) = minus (-t) (-z) := by
    rw [minus_weights]
    funext index
    dsimp only [minus]
    split_ifs <;> simp [star_t, star_z]
  have square_weights : (fun index => square (a tauPlus index)) = plus (t ^ 2) (z ^ 2) :=
    by
      rw [plus_weights]
      funext index
      dsimp only [plus]
      split_ifs <;> simp [square_t, square_z]
  have represent (weights : ℕ → Polynomial ℤ) (height : ℕ) :
      IsUnit (cont (a weights) 1 1 (height + 1)) ∧
        cont (a weights) 1 1 (height + 1) * series weights height =
          cont (a weights) 0 1 (height + 1) :=
    continuant_representation weights height first_return_recursion
  have assemble (height : ℕ)
      (numerator : cont (plus (t ^ 2) (z ^ 2)) 0 1 (height + 1) =
        cont (minus t z) 0 1 (height + 1) *
          cont (minus (-t) (-z)) 0 1 (height + 1))
      (denominator : cont (plus (t ^ 2) (z ^ 2)) 1 1 (height + 1) =
        cont (minus t z) 1 1 (height + 1) *
          cont (minus (-t) (-z)) 1 1 (height + 1)) :
      square (series tauPlus height) =
        series tauMinus height * star (series tauMinus height) := by
    obtain ⟨minus_unit, minus_eq⟩ := represent tauMinus height
    obtain ⟨_, plus_eq⟩ := represent tauPlus height
    have flipped_eq := congrArg star minus_eq
    have squared_eq := congrArg square plus_eq
    simp only [map_mul, map_cont, map_zero, map_one, star_weights] at flipped_eq
    simp only [map_mul, map_cont, map_zero, map_one, square_weights] at squared_eq
    rw [minus_weights] at minus_unit minus_eq
    have flipped_unit : IsUnit (cont (minus (-t) (-z)) 1 1 (height + 1)) := by
      have mapped := (represent tauMinus height).1.map star
      simpa only [map_cont, map_one, star_weights] using mapped
    apply (minus_unit.mul flipped_unit).mul_left_cancel
    rw [← denominator, squared_eq, numerator]
    rw [denominator]
    calc
      cont (minus t z) 0 1 (height + 1) *
          cont (minus (-t) (-z)) 0 1 (height + 1) =
        (cont (minus t z) 1 1 (height + 1) * series tauMinus height) *
          (cont (minus (-t) (-z)) 1 1 (height + 1) *
            star (series tauMinus height)) := by rw [minus_eq, flipped_eq]
      _ = _ := by ring
  have coefficient_left (height degree : ℕ) :
      PowerSeries.coeff degree (square (series tauPlus height)) =
        CiglerStripProductDefs.lhsCoeff height degree := by
    change PowerSeries.coeff degree (PowerSeries.expand 2 (by decide)
      (PowerSeries.map (Polynomial.compRingHom (Polynomial.X ^ 2))
        (series tauPlus height))) = _
    rw [PowerSeries.coeff_expand]
    simp only [PowerSeries.coeff_map, series, PowerSeries.coeff_mk,
      Polynomial.coe_compRingHom_apply, CiglerStripProductDefs.lhsCoeff,
      Nat.dvd_iff_mod_eq_zero]
  have coefficient_right (height degree : ℕ) :
      PowerSeries.coeff degree (series tauMinus height * star (series tauMinus height)) =
        CiglerStripProductDefs.rhsCoeff height degree := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [series, star, RingHom.comp_apply, PowerSeries.coeff_rescale,
      PowerSeries.coeff_map, PowerSeries.coeff_mk, Polynomial.coe_compRingHom_apply,
      CiglerStripProductDefs.rhsCoeff, Nat.succ_eq_add_one]
  intro blocks positive degree
  obtain ⟨numerator, denominator, numerator_next, denominator_next⟩ :=
    product_factorization t z blocks
  constructor
  · have identity := assemble (4 * blocks) numerator denominator
    exact (coefficient_left _ _).symm.trans
      ((congrArg (PowerSeries.coeff degree) identity).trans (coefficient_right _ _))
  · have identity := assemble (4 * blocks + 1) numerator_next denominator_next
    exact (coefficient_left _ _).symm.trans
      ((congrArg (PowerSeries.coeff degree) identity).trans (coefficient_right _ _))

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProduct
