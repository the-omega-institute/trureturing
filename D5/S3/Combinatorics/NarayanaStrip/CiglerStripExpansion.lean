/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cigler's two strip expansions by pairing, colored insertions, and cancellation. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansion

open CiglerStripExpansionDefs CiglerStripExpansionPairing
open CiglerStripExpansionSkeleton CiglerStripExpansionCounting Polynomial

theorem result : CiglerStripExpansionDefs.claim := by
  classical
  have colored_gap_bijection (bars size : ℕ) :
      ∃ correspondence :
        {gaps : List (List Bool) // gaps.length = bars + 1 ∧ gaps.flatten.length = size} ≃
          (Finset.Nat.antidiagonalTuple (bars + 1) size) × (Fin size → Bool),
        (∀ gaps, List.ofFn (correspondence gaps).1.val = gaps.val.map List.length) ∧
        (∀ gaps, List.ofFn (correspondence gaps).2 = gaps.val.flatten) ∧
        (∀ data, (correspondence.symm data).val =
          List.splitLengths (List.ofFn data.1.val) (List.ofFn data.2)) ∧
        (∑ gaps ∈ ((Finset.Nat.antidiagonalTuple (bars + 1) size) ×ˢ
            (Finset.univ : Finset (Fin size → Bool))).image
            (fun data => List.splitLengths (List.ofFn data.1) (List.ofFn data.2)),
          Polynomial.X ^ gaps.flatten.count true) =
            Polynomial.C (((size + bars).choose bars : ℕ) : ℤ) *
              (1 + Polynomial.X) ^ size ∧
        (∀ pairs, bars = 2 * pairs →
          (∑ gaps ∈ ((Finset.Nat.antidiagonalTuple (bars + 1) size) ×ˢ
              (Finset.univ : Finset (Fin size → Bool))).image
              (fun data => List.splitLengths (List.ofFn data.1) (List.ofFn data.2)),
            Polynomial.C ((-1 : ℤ) ^ gapCharge true gaps) *
              Polynomial.X ^ gaps.flatten.count true) =
            Polynomial.C (((size / 2 + pairs).choose pairs : ℕ) : ℤ) *
              (1 + Polynomial.X) ^ size) := by
    classical
    have gap_composition_count (bars colors : ℕ) :
        (Finset.Nat.antidiagonalTuple (bars + 1) colors).card =
          (colors + bars).choose bars := by
      have transport : (Finset.Nat.antidiagonalTuple (bars + 1) colors).card =
          ((Finset.univ : Finset (Fin (bars + 1))).finsuppAntidiag colors).card := by
        apply Finset.card_bij (fun data _ => Finsupp.equivFunOnFinite.symm data)
        · intro data inside
          simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
          exact Finset.Nat.mem_antidiagonalTuple.mp inside
        · intro first _ second _ equal
          exact Finsupp.equivFunOnFinite.symm.injective equal
        · intro data inside
          refine ⟨Finsupp.equivFunOnFinite data, ?_, ?_⟩
          · exact Finset.Nat.mem_antidiagonalTuple.mpr
              (Finset.mem_finsuppAntidiag.mp inside).1
          · exact Finsupp.equivFunOnFinite.symm_apply_apply data
      rw [transport, Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin]
      have top : bars + 1 + colors - 1 = colors + bars := by omega
      rw [top]
      exact Nat.choose_symm_add
    have of_list {α : Type} (word : List α) (length : ℕ)
        (agrees : word.length = length) :
        List.ofFn (fun index : Fin length => word.get (Fin.cast agrees.symm index)) =
          word := by
      rw [← List.ofFn_congr agrees word.get, List.ofFn_get]
    let encode (gaps : {gaps : List (List Bool) //
        gaps.length = bars + 1 ∧ gaps.flatten.length = size}) :
        (Finset.Nat.antidiagonalTuple (bars + 1) size) × (Fin size → Bool) :=
      (⟨fun index => (gaps.val.get (Fin.cast gaps.property.1.symm index)).length, by
        rw [Finset.Nat.mem_antidiagonalTuple, ← List.sum_ofFn]
        rw [List.ofFn_comp', of_list gaps.val (bars + 1) gaps.property.1]
        simpa using gaps.property.2⟩,
        fun index => gaps.val.flatten.get (Fin.cast gaps.property.2.symm index))
    have encode_lengths (gaps : {gaps : List (List Bool) //
        gaps.length = bars + 1 ∧ gaps.flatten.length = size}) :
        List.ofFn (encode gaps).1.val = gaps.val.map List.length := by
      change List.ofFn (fun index : Fin (bars + 1) =>
        (gaps.val.get (Fin.cast gaps.property.1.symm index)).length) = _
      rw [List.ofFn_comp', of_list gaps.val (bars + 1) gaps.property.1]
    have encode_colors (gaps : {gaps : List (List Bool) //
        gaps.length = bars + 1 ∧ gaps.flatten.length = size}) :
        List.ofFn (encode gaps).2 = gaps.val.flatten := by
      exact of_list gaps.val.flatten size gaps.property.2
    let decode (data :
        (Finset.Nat.antidiagonalTuple (bars + 1) size) × (Fin size → Bool)) :
        {gaps : List (List Bool) //
          gaps.length = bars + 1 ∧ gaps.flatten.length = size} :=
      ⟨List.splitLengths (List.ofFn data.1.val) (List.ofFn data.2), by
        have total : (List.ofFn data.1.val).sum = (List.ofFn data.2).length := by
          simpa only [List.sum_ofFn, List.length_ofFn] using
            Finset.Nat.mem_antidiagonalTuple.mp data.1.property
        have allocated := And.intro (List.map_splitLengths_length _ _ total.le)
          (List.flatten_splitLengths _ _ total.ge)
        constructor
        · have lengths := congrArg List.length allocated.1
          simpa using lengths
        · rw [allocated.2, List.length_ofFn]⟩
    have decode_encode (gaps : {gaps : List (List Bool) //
        gaps.length = bars + 1 ∧ gaps.flatten.length = size}) :
        decode (encode gaps) = gaps := by
      apply Subtype.ext
      change List.splitLengths (List.ofFn (encode gaps).1.val) (List.ofFn (encode gaps).2) = _
      rw [encode_lengths, encode_colors]
      exact ArrowWilfTwelveSurject.splitLengths_map_length_flatten gaps.val
    have encode_decode (data :
        (Finset.Nat.antidiagonalTuple (bars + 1) size) × (Fin size → Bool)) :
        encode (decode data) = data := by
      have total : (List.ofFn data.1.val).sum = (List.ofFn data.2).length := by
        simpa only [List.sum_ofFn, List.length_ofFn] using
          Finset.Nat.mem_antidiagonalTuple.mp data.1.property
      have allocated := And.intro (List.map_splitLengths_length _ _ total.le)
        (List.flatten_splitLengths _ _ total.ge)
      apply Prod.ext
      · apply Subtype.ext
        apply List.ofFn_injective
        rw [encode_lengths]
        exact allocated.1
      · apply List.ofFn_injective
        rw [encode_colors]
        exact allocated.2
    have allocated (data : (Fin (bars + 1) → ℕ) × (Fin size → Bool))
        (inside : data ∈ Finset.Nat.antidiagonalTuple (bars + 1) size ×ˢ Finset.univ) :
        (List.splitLengths (List.ofFn data.1) (List.ofFn data.2)).map List.length =
            List.ofFn data.1 ∧
          (List.splitLengths (List.ofFn data.1) (List.ofFn data.2)).flatten =
            List.ofFn data.2 := by
      have total : (List.ofFn data.1).sum = (List.ofFn data.2).length := by
        simpa only [List.sum_ofFn, List.length_ofFn] using
          Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_product.mp inside).1
      exact ⟨List.map_splitLengths_length _ _ total.le,
        List.flatten_splitLengths _ _ total.ge⟩
    have color_sum (size : ℕ) :
        (∑ colors : Fin size → Bool,
          (Polynomial.X : Polynomial ℤ) ^ (List.ofFn colors).count true) =
            (1 + Polynomial.X) ^ size := by
      induction size with
      | zero => simp
      | succ size induction_hyp =>
        rw [← (Fin.consEquiv (fun _ : Fin (size + 1) => Bool)).sum_comp]
        rw [Fintype.sum_prod_type]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ,
          Fin.cons_zero, Fin.cons_succ]
        rw [Fintype.univ_bool]
        simp only [Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
          Finset.sum_insert, List.count_cons_self, Finset.sum_singleton, ne_eq,
          Bool.false_eq_true, List.count_cons_of_ne, pow_succ]
        rw [← Finset.sum_mul]
        change (∑ colors : Fin size → Bool,
          Polynomial.X ^ (List.ofFn colors).count true) * Polynomial.X +
          (∑ colors : Fin size → Bool, Polynomial.X ^ (List.ofFn colors).count true) = _
        rw [induction_hyp]
        ring
    refine ⟨⟨encode, decode, decode_encode, encode_decode⟩,
      encode_lengths, encode_colors, fun _ => rfl, ?_, ?_⟩
    · rw [Finset.sum_image]
      · calc
          _ = ∑ data ∈ Finset.Nat.antidiagonalTuple (bars + 1) size ×ˢ
                (Finset.univ : Finset (Fin size → Bool)),
              Polynomial.X ^ (List.ofFn data.2).count true := by
            apply Finset.sum_congr rfl
            intro data inside
            rw [(allocated data inside).2]
          _ = _ := by
            rw [Finset.sum_product]
            simp only [color_sum, Finset.sum_const, nsmul_eq_mul, gap_composition_count]
            simp
      · intro first first_mem second second_mem same
        dsimp only at same
        have first_shape := allocated first first_mem
        have second_shape := allocated second second_mem
        apply Prod.ext
        · apply List.ofFn_injective
          rw [← first_shape.1, ← second_shape.1, same]
        · apply List.ofFn_injective
          rw [← first_shape.2, ← second_shape.2, same]
    · intro pairs bars_eq
      let domain := ((Finset.Nat.antidiagonalTuple (bars + 1) size) ×ˢ
        (Finset.univ : Finset (Fin size → Bool))).image
          (fun data => List.splitLengths (List.ofFn data.1) (List.ofFn data.2))
      have complete (gaps : List (List Bool)) : gaps ∈ domain ↔
          gaps.length = bars + 1 ∧ gaps.flatten.length = size := by
        constructor
        · intro membership
          obtain ⟨data, inside, rfl⟩ := Finset.mem_image.mp membership
          have shape := allocated data inside
          constructor
          · have lengths := congrArg List.length shape.1
            simpa only [List.length_map, List.length_ofFn] using lengths
          · rw [shape.2, List.length_ofFn]
        · intro shape
          let gaps_data : {gaps : List (List Bool) //
            gaps.length = bars + 1 ∧ gaps.flatten.length = size} := ⟨gaps, shape⟩
          refine Finset.mem_image.mpr
            ⟨((encode gaps_data).1.val, (encode gaps_data).2), ?_, ?_⟩
          · exact Finset.mem_product.mpr
              ⟨(encode gaps_data).1.property, Finset.mem_univ _⟩
          · exact congrArg Subtype.val (decode_encode gaps_data)
      have fiber (colors : Fin size → Bool) :
          (∑ gaps ∈ domain.filter (fun gaps => gaps.flatten = List.ofFn colors),
            Polynomial.C ((-1 : ℤ) ^ gapCharge true gaps) *
              Polynomial.X ^ gaps.flatten.count true) =
            Polynomial.C (((size / 2 + pairs).choose pairs : ℕ) : ℤ) *
              Polynomial.X ^ (List.ofFn colors).count true := by
        obtain ⟨_, _, _, signed_count⟩ := fixed_gap_bijection pairs (List.ofFn colors)
        have signed := signed_count
          (domain.filter (fun gaps => gaps.flatten = List.ofFn colors)) (by
            intro gaps
            rw [Finset.mem_filter, complete, bars_eq]
            constructor
            · exact fun shape => ⟨shape.1.1, shape.2⟩
            · intro shape
              refine ⟨⟨shape.1, ?_⟩, shape.2⟩
              rw [shape.2, List.length_ofFn])
        simp only [List.length_ofFn] at signed
        calc
          _ = (∑ gaps ∈ domain.filter (fun gaps => gaps.flatten = List.ofFn colors),
              Polynomial.C ((-1 : ℤ) ^ gapCharge true gaps)) *
                Polynomial.X ^ (List.ofFn colors).count true := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro gaps inside
            rw [(Finset.mem_filter.mp inside).2]
          _ = _ := by rw [← map_sum Polynomial.C, signed]
      have colors_inside (gaps : List (List Bool)) (inside : gaps ∈ domain) :
          gaps.flatten ∈ (Finset.univ : Finset (Fin size → Bool)).image List.ofFn := by
        have length := (complete gaps).mp inside |>.2
        refine Finset.mem_image.mpr ⟨fun index =>
          gaps.flatten.get (Fin.cast length.symm index), Finset.mem_univ _, ?_⟩
        exact of_list gaps.flatten size length
      change (∑ gaps ∈ domain, _) = _
      rw [← Finset.sum_fiberwise_of_maps_to colors_inside,
        Finset.sum_image List.ofFn_injective.injOn]
      simp only [fiber, ← Finset.mul_sum, color_sum]

  intro bound size positive
  let words (α : Type) [Fintype α] [DecidableEq α] (length : ℕ) : Finset (List α) :=
    (Finset.univ : Finset (Fin length → α)).image List.ofFn
  have words_complete {α : Type} [Fintype α] [DecidableEq α]
      (length : ℕ) (word : List α) : word ∈ words α length ↔ word.length = length := by
    constructor
    · intro inside
      obtain ⟨letters, _, rfl⟩ := Finset.mem_image.mp inside
      exact List.length_ofFn
    · intro length_eq
      refine Finset.mem_image.mpr
        ⟨fun index => word.get (Fin.cast length_eq.symm index), Finset.mem_univ _, ?_⟩
      rw [← List.ofFn_congr length_eq word.get, List.ofFn_get]
  let dyckWords (height length : ℕ) := (words Bool length).filter (IsStripDyck height)
  have dyck_complete (height length : ℕ) (path : List Bool) :
      path ∈ dyckWords height length ↔ path.length = length ∧ IsStripDyck height path := by
    simp only [dyckWords, Finset.mem_filter, words_complete]
  have path_sum (weights : ℕ → ℤ[X]) (height semilength : ℕ) :
      stripSum weights height semilength =
        ∑ path ∈ dyckWords height (2 * semilength), weight weights path := by
    change _ = ∑ path ∈ (words Bool (2 * semilength)).filter (IsStripDyck height), _
    dsimp only [words]
    rw [Finset.filter_image, Finset.sum_image List.ofFn_injective.injOn]
    rw [Finset.sum_filter]
    rfl
  have path_count (height semilength : ℕ) :
      (dyckWords height (2 * semilength)).card = stripCount height semilength := by
    change ((words Bool (2 * semilength)).filter (IsStripDyck height)).card = _
    dsimp only [words]
    rw [Finset.filter_image, Finset.card_image_of_injective _ List.ofFn_injective]
    rfl
  let motzWords := (words (Bool × Bool) size).filter (IsMotzkinStrip (bound - 1))
  have motz_complete (blocks : List (Bool × Bool)) : blocks ∈ motzWords ↔
      blocks.length = size ∧ IsMotzkinStrip (bound - 1) blocks := by
    simp only [motzWords, Finset.mem_filter, words_complete]
  obtain ⟨pairing, expand_agrees, inverse_agrees⟩ := pairing_bijection bound size positive
  have pairing_sum (signed : Bool) :
      stripSum (if signed then tauMinus else tauPlus) (2 * bound) (size + 1) =
        ∑ blocks ∈ motzWords, motzkinWeight signed 0 blocks := by
    rw [path_sum]
    let transform (path : List Bool)
        (inside : path ∈ dyckWords (2 * bound) (2 * (size + 1))) :=
      pairing ⟨path, (dyck_complete _ _ _).mp inside⟩
    apply Finset.sum_bij (fun path inside => (transform path inside).val)
    · intro path inside
      exact (motz_complete _).mpr (transform path inside).property
    · intro first first_mem second second_mem same
      have eq_blocks : transform first first_mem = transform second second_mem :=
        Subtype.ext same
      exact congrArg Subtype.val (pairing.injective eq_blocks)
    · intro blocks inside
      let original := pairing.symm ⟨blocks, (motz_complete _).mp inside⟩
      have membership := (dyck_complete _ _ _).mpr original.property
      refine ⟨original.val, membership, ?_⟩
      have recovered : transform original.val membership =
          ⟨blocks, (motz_complete _).mp inside⟩ := by
        change pairing _ = _
        convert pairing.apply_symm_apply ⟨blocks, (motz_complete _).mp inside⟩
      exact congrArg Subtype.val recovered
    · intro path inside
      have expands := expand_agrees ⟨path, (dyck_complete _ _ _).mp inside⟩
      have weights := pairing_weights (bound - 1) (transform path inside).val
        (transform path inside).property.2
      cases signed <;> simp only [Bool.false_eq_true, if_false, if_true]
      · rw [← weights.1, expands]
      · rw [← weights.2, expands]
  obtain ⟨decomposition, encode_agrees, decode_agrees, lengths_agree, strips_agree⟩ :=
    skeleton_decomposition
  have balanced (path : List Bool) (valid : IsStripDyck (bound - 1) path) :
      path.length = 2 * path.count false := by
    have endpoint (word : List Bool) : heightAfter word word.length =
        (word.length : ℤ) - 2 * (word.count false : ℤ) := by
      induction word with
      | nil => simp [heightAfter]
      | cons first rest induction_hyp =>
        cases first <;>
          simp [heightAfter] at induction_hyp ⊢ <;> omega
    have final := endpoint path
    rw [valid.2] at final
    omega
  let gapsWords (bars colors : ℕ) :=
    ((Finset.Nat.antidiagonalTuple (bars + 1) colors) ×ˢ
      (Finset.univ : Finset (Fin colors → Bool))).image
        (fun data => List.splitLengths (List.ofFn data.1) (List.ofFn data.2))
  have gaps_complete (bars colors : ℕ) (gaps : List (List Bool)) :
      gaps ∈ gapsWords bars colors ↔
        gaps.length = bars + 1 ∧ gaps.flatten.length = colors := by
    obtain ⟨correspondence, lengths, colors_eq, inserted, _, _⟩ :=
      colored_gap_bijection bars colors
    constructor
    · intro inside
      obtain ⟨data, membership, rfl⟩ := Finset.mem_image.mp inside
      have total : (List.ofFn data.1).sum = (List.ofFn data.2).length := by
        simpa only [List.sum_ofFn, List.length_ofFn] using
          Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_product.mp membership).1
      have allocated := And.intro (List.map_splitLengths_length _ _ total.le)
        (List.flatten_splitLengths _ _ total.ge)
      constructor
      · have shape := congrArg List.length allocated.1
        simpa only [List.length_map, List.length_ofFn] using shape
      · rw [allocated.2, List.length_ofFn]
    · intro shape
      let data := correspondence ⟨gaps, shape⟩
      refine Finset.mem_image.mpr
        ⟨(data.1.val, data.2), Finset.mem_product.mpr ⟨data.1.property,
          Finset.mem_univ _⟩, ?_⟩
      have reconstructed := inserted data
      rw [correspondence.symm_apply_apply] at reconstructed
      exact reconstructed.symm
  let families := (Finset.range (size / 2 + 1)).sigma (fun index =>
    dyckWords (bound - 1) (2 * index) ×ˢ gapsWords (2 * index) (size - 2 * index))
  have family_complete (index : ℕ) (data : List Bool × List (List Bool)) :
      Sigma.mk index data ∈ families ↔ index ≤ size / 2 ∧
        data.1.length = 2 * index ∧ IsStripDyck (bound - 1) data.1 ∧
          data.2.length = 2 * index + 1 ∧ data.2.flatten.length = size - 2 * index := by
    simp only [families, Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      dyck_complete, gaps_complete]
    have range_eq : index < size / 2 + 1 ↔ index ≤ size / 2 := by omega
    rw [range_eq]
    tauto
  let term (signed : Bool) (data : Σ _index : ℕ, List Bool × List (List Bool)) : ℤ[X] :=
    (if signed then C ((-1 : ℤ) ^ data.1) * C ((-1 : ℤ) ^ gapCharge true data.2.2)
      else 1) * X ^ data.1 * X ^ data.2.2.flatten.count true
  have skeleton_sum (signed : Bool) :
      (∑ blocks ∈ motzWords, motzkinWeight signed 0 blocks) =
        ∑ data ∈ families, term signed data := by
    let encode (blocks : List (Bool × Bool)) :
        Σ _index : ℕ, List Bool × List (List Bool) :=
      Sigma.mk ((extractData blocks).1.count false) (extractData blocks)
    apply Finset.sum_bij (fun blocks _ => encode blocks)
    · intro blocks inside
      have valid := (motz_complete _).mp inside
      have skeleton_valid := (strips_agree _ _).mp valid.2
      have skeleton_length := balanced _ skeleton_valid
      have size_eq := lengths_agree blocks
      rw [valid.1] at size_eq
      have shape := (decomposition blocks).property
      rw [encode_agrees] at shape
      rw [family_complete]
      exact ⟨by omega, skeleton_length, skeleton_valid, by omega, by omega⟩
    · intro first first_mem second second_mem same
      have eq_data := congrArg (fun data : Σ _index : ℕ,
        List Bool × List (List Bool) => data.2) same
      have eq_encoded : decomposition first = decomposition second := by
        apply Subtype.ext
        simpa only [encode_agrees] using eq_data
      exact decomposition.injective eq_encoded
    · intro data inside
      rcases data with ⟨index, skeleton, gaps⟩
      rcases (family_complete index (skeleton, gaps)).mp inside with
        ⟨index_bound, skeleton_length, skeleton_valid, gap_length, gap_colors⟩
      let original := decomposition.symm ⟨(skeleton, gaps), by
        simpa [skeleton_length] using gap_length⟩
      have extracted : extractData original = (skeleton, gaps) := by
        rw [← encode_agrees, decomposition.apply_symm_apply]
      have membership : original ∈ motzWords := by
        rw [motz_complete]
        constructor
        · rw [lengths_agree, extracted]
          omega
        · rw [strips_agree, extracted]
          exact skeleton_valid
      refine ⟨original, membership, ?_⟩
      dsimp only [encode]
      rw [extracted]
      have count := balanced skeleton skeleton_valid
      rw [skeleton_length] at count
      have counted : skeleton.count false = index := by omega
      rw [counted]
    · intro blocks inside
      have factored := skeleton_weights (bound - 1) blocks
        ((motz_complete _).mp inside).2
      cases signed <;> simp only [term, encode, Bool.false_eq_true, if_false, if_true]
      · rw [factored.1, pow_add]
        simp
      · rw [factored.2, pow_add, C_mul, pow_add]
        simp only [mul_assoc]
  have family_sum (signed : Bool) :
      (∑ data ∈ families, term signed data) =
        ∑ index ∈ Finset.range (size / 2 + 1),
          C (if signed then (-1 : ℤ) ^ index *
            ((stripCount (bound - 1) index * (size / 2).choose index : ℕ) : ℤ)
            else ((stripCount (bound - 1) index * size.choose (2 * index) : ℕ) : ℤ)) *
              X ^ index * (1 + X) ^ (size - 2 * index) := by
    change (∑ data ∈ (Finset.range (size / 2 + 1)).sigma _, term signed data) = _
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro index inside
    have index_bound : index ≤ size / 2 := by simpa using inside
    obtain ⟨_, _, _, _, unsigned, signed_count⟩ :=
      colored_gap_bijection (2 * index) (size - 2 * index)
    have total : size - 2 * index + 2 * index = size := by omega
    have half : (size - 2 * index) / 2 + index = size / 2 := by omega
    rw [total] at unsigned
    have signed_gaps := signed_count index rfl
    rw [half] at signed_gaps
    rw [Finset.sum_product]
    cases signed
    · simp only [term, Bool.false_eq_true, if_false, one_mul]
      simp_rw [← Finset.mul_sum]
      rw [unsigned]
      simp only [Finset.sum_const, nsmul_eq_mul, path_count, Nat.cast_mul]
      simp [mul_comm, mul_left_comm, mul_assoc]
    · simp only [term, if_true]
      have rearrange (gaps : List (List Bool)) :
          C ((-1 : ℤ) ^ index) * C ((-1 : ℤ) ^ gapCharge true gaps) *
              X ^ index * X ^ gaps.flatten.count true =
            (C ((-1 : ℤ) ^ index) * X ^ index) *
              (C ((-1 : ℤ) ^ gapCharge true gaps) * X ^ gaps.flatten.count true) := by
        ring
      simp_rw [rearrange, ← Finset.mul_sum]
      rw [signed_gaps]
      simp only [Finset.sum_const, nsmul_eq_mul, path_count, Nat.cast_mul]
      simp [mul_comm, mul_left_comm, mul_assoc]
  constructor
  · simpa using (pairing_sum false).trans ((skeleton_sum false).trans (family_sum false))
  · simpa using (pairing_sum true).trans ((skeleton_sum true).trans (family_sum true))

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansion
