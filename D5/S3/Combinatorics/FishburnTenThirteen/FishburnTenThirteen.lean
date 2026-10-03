/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen
   mirror-E: none(waiver:egge-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution]
   utility: none
   digest: Reversible labelled constructors give both binomial-Catalan Fishburn counts. -/

import D5.S3.Combinatorics.Fishburn.FishburnCatalanBinomialDefs
import D5.S1.Words.Patterns.A398542Polynomial
import Mathlib.RingTheory.PowerSeries.Substitution
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenAConstruction
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteen

open D5.S3.Combinatorics Fishburn FishburnDefs Nonnesting
open NonnestingBasicSum FishburnBasicComponents PowerSeries Finset
open scoped PowerSeries.WithPiTopology

set_option maxHeartbeats 4000000 in
theorem result : FishburnCatalanBinomialDefs.claim1013 := by
  classical
  have componentSeries (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
        (∀ value ∈ pattern, 1 ≤ value) ∧
        ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern) :
      let components (size : ℕ) := {parts : List (List ℕ) |
        (∀ block ∈ parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
        assemble parts ∈ avoiders size patterns}
      let indecs : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else
          ({word : List ℕ | word ∈ avoiders size patterns ∧ sumIndecomposable word}.ncard :
            Polynomial ℚ)
      let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
        ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
      (∀ size, ∃ serialization : components size ≃ avoiders size patterns,
        ∀ parts, (serialization parts).val = assemble parts.val) ∧
      (1 - C Polynomial.X * indecs) * sequences = 1 ∧
      ∀ weight : ℕ → List ℕ → Polynomial ℚ,
        let marked : PowerSeries (Polynomial ℚ) := mk fun size =>
          if size = 0 then 0 else ∑ᶠ block : {word : List ℕ |
            word ∈ avoiders size patterns ∧ sumIndecomposable word}, weight size block.val
        let heads : PowerSeries (Polynomial ℚ) := mk fun size =>
          if size = 0 then 0 else ∑ᶠ parts : components size,
            (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
              weight (parts.val.headD []).length (parts.val.headD [])
        let lasts : PowerSeries (Polynomial ℚ) := mk fun size =>
          if size = 0 then 0 else ∑ᶠ parts : components size,
            (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
              weight (parts.val.reverse.headD []).length (parts.val.reverse.headD [])
        let tails : PowerSeries (Polynomial ℚ) := mk fun size =>
          if size = 0 then 0 else ∑ᶠ parts : components size,
            (Polynomial.X : Polynomial ℚ) ^
              (if parts.val.tail = [] then 1 else parts.val.tail.length) *
                weight (parts.val.headD []).length (parts.val.headD [])
        heads = marked * sequences ∧ lasts = heads ∧
          tails = C Polynomial.X * marked + marked * (sequences - 1) := by
    classical
    let components (size : ℕ) := {parts : List (List ℕ) |
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      assemble parts ∈ avoiders size patterns}
    let indecs : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else
        ({word : List ℕ | word ∈ avoiders size patterns ∧ sumIndecomposable word}.ncard :
          Polynomial ℚ)
    let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
      ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
    change (∀ size, ∃ serialization : components size ≃ avoiders size patterns,
      ∀ parts, (serialization parts).val = assemble parts.val) ∧
      (1 - C Polynomial.X * indecs) * sequences = 1 ∧ _
    have hbase := unique_sum_components 0 [] (by simp) patterns hpatterns
    have hclosure := hbase.2.1
    have hlength (parts : List (List ℕ)) :
        (assemble parts).length = (parts.map List.length).sum := by
      induction parts with
      | nil => rfl
      | cons first rest ih =>
        simp only [assemble, directSum, shift, List.length_append, List.length_map,
          List.map_cons, List.sum_cons, ih]
    have hsize (size : ℕ) (parts : components size) :
        (assemble parts.val).length = size := by
      simpa using parts.property.2.1.length_eq
    have hblock (size : ℕ) (parts : components size) :
        ∀ block ∈ parts.val, block ∈ avoiders block.length patterns :=
      (hclosure parts.val parts.property.1).mp (by
        simpa only [hsize size parts] using parts.property.2)
    have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw; exact List.mem_permutations.mpr hw.1
    let serialize (size : ℕ) (parts : components size) : avoiders size patterns :=
      ⟨assemble parts.val, parts.property.2⟩
    have hinjective (size : ℕ) : Function.Injective (serialize size) := by
      intro left right heq
      have hv : assemble left.val = assemble right.val := congrArg Subtype.val heq
      obtain ⟨canonical, _, hu⟩ :=
        (unique_sum_components size (assemble left.val) left.property.2.1 patterns
          hpatterns).1
      have hl : left.val = canonical := hu _ ⟨rfl, left.property.1, by
        simpa only [hsize size left] using hclosure left.val left.property.1⟩
      have hr : right.val = canonical := hu _ ⟨hv.symm, right.property.1, by
        have hh := hclosure right.val right.property.1
        rw [hsize size right, ← hv] at hh; exact hh⟩
      exact Subtype.ext (hl.trans hr.symm)
    have hsurjective (size : ℕ) : Function.Surjective (serialize size) := by
      intro word
      obtain ⟨parts, hp, _⟩ :=
        (unique_sum_components size word.val word.property.1 patterns hpatterns).1
      exact ⟨⟨parts, hp.2.1, by simpa only [hp.1] using word.property⟩,
        Subtype.ext hp.1⟩
    let serialization (size : ℕ) :=
      Equiv.ofBijective (serialize size) ⟨hinjective size, hsurjective size⟩
    let (size : ℕ) : Finite (avoiders size patterns) := (hfinite size).to_subtype
    let (size : ℕ) : Finite (components size) :=
      Finite.of_injective (serialize size) (hinjective size)
    let (size : ℕ) : Fintype (components size) := Fintype.ofFinite _
    let blocks (size : ℕ) := {word : List ℕ |
      word ∈ avoiders size patterns ∧ sumIndecomposable word}
    let (size : ℕ) : Finite (blocks size) :=
      ((hfinite size).subset (fun _ hw => hw.1)).to_subtype
    let (size : ℕ) : Fintype (blocks size) := Fintype.ofFinite _
    have hempty : ∀ parts : components 0, parts.val = [] := by
      intro parts
      cases heq : parts.val with
      | nil => rfl
      | cons first rest =>
        have hf := parts.property.1 first (by simp [heq])
        have hpos := List.length_pos_iff_ne_nil.mpr hf.1
        have hs := hsize 0 parts
        simp only [heq, assemble, directSum, shift, List.length_append,
          List.length_map] at hs
        omega
    have hnil : [] ∈ components 0 := by
      refine ⟨by simp, ?_⟩
      exact (hclosure [] (by simp)).mpr (by simp)
    have hzero : coeff 0 sequences = 1 := by
      have hsingleton : components 0 = {[]} := by
        ext parts; exact ⟨fun hp => hempty ⟨parts, hp⟩,
          fun hp => by simpa only [Set.mem_singleton_iff.mp hp] using hnil⟩
      simp only [sequences, coeff_mk]; have hterm : ∀ parts : components 0,
          (Polynomial.X : Polynomial ℚ) ^ parts.val.length = 1 := by
        intro parts; simp [hempty parts]
      rw [finsum_congr hterm, finsum_eq_sum_of_fintype]
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsingleton, Set.ncard_singleton]
      rfl
    have hcons (size : ℕ) : ∃ decomposition :
        (Σ cut : Fin (size + 1), blocks (cut.val + 1) × components (size - cut.val)) ≃
          components (size + 1),
        ∀ entry, (decomposition entry).val = entry.2.1.val :: entry.2.2.val := by
      let source := Σ cut : Fin (size + 1),
        blocks (cut.val + 1) × components (size - cut.val)
      have hjoin (entry : source) :
          entry.2.1.val :: entry.2.2.val ∈ components (size + 1) := by
        have hfirst := entry.2.1.property
        have hfLen : entry.2.1.val.length = entry.1.val + 1 := by
          simpa using hfirst.1.1.length_eq
        have hv : ∀ block ∈ entry.2.1.val :: entry.2.2.val, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
          intro block hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨List.length_pos_iff_ne_nil.mp (by omega),
              by simpa only [hfLen] using hfirst.1.1, hfirst.2⟩
          · exact entry.2.2.property.1 block hb
        have hc := (hclosure _ hv).mpr (by
          intro block hb
          rcases List.mem_cons.mp hb with rfl | hb
          · simpa only [hfLen] using hfirst.1
          · exact hblock _ entry.2.2 block hb)
        have hl : (assemble (entry.2.1.val :: entry.2.2.val)).length = size + 1 := by
          simp only [assemble, directSum, shift, List.length_append, List.length_map,
            hfLen, hsize _ entry.2.2]
          omega
        exact ⟨hv, by simpa only [hl] using hc⟩
      obtain ⟨splitter, hsplitter⟩ := (hbase.2.2.2.1 size).2
      let tailTransport : source ≃
          (Σ cut : Fin (size + 1), blocks (cut.val + 1) × avoiders (size - cut.val) patterns) :=
        Equiv.sigmaCongrRight fun cut =>
          Equiv.prodCongr (Equiv.refl _) (serialization (size - cut.val))
      let transported := tailTransport.trans (splitter.trans (serialization (size + 1)).symm)
      refine ⟨transported, ?_⟩
      intro entry
      let target : components (size + 1) :=
        ⟨entry.2.1.val :: entry.2.2.val, hjoin entry⟩
      have heq : transported entry = target := by
        apply (serialization (size + 1)).injective
        apply Subtype.ext
        change ((serialization (size + 1)) (transported entry)).val =
          assemble (entry.2.1.val :: entry.2.2.val)
        simp only [transported, Equiv.trans_apply, Equiv.apply_symm_apply]; rw [hsplitter]
        have hlength : entry.2.1.val.length = entry.1.val + 1 := by
          simpa using entry.2.1.property.1.1.length_eq
        change directSum (entry.1.val + 1) entry.2.1.val (assemble entry.2.2.val) =
          directSum entry.2.1.val.length entry.2.1.val (assemble entry.2.2.val)
        rw [hlength]
      exact congrArg Subtype.val heq
    have hsum (size : ℕ) (weight : List (List ℕ) → Polynomial ℚ) :
        (∑ᶠ parts : components (size + 1), weight parts.val) =
          ∑ cut : Fin (size + 1), ∑ᶠ block : blocks (cut.val + 1),
            ∑ᶠ rest : components (size - cut.val), weight (block.val :: rest.val) := by
      obtain ⟨decomposition, heq⟩ := hcons size
      rw [← finsum_comp_equiv decomposition]
      simp only [finsum_eq_sum_of_fintype, Fintype.sum_sigma, Fintype.sum_prod_type, heq]
    have hrecurrence : sequences = 1 + C Polynomial.X * indecs * sequences := by
      apply PowerSeries.ext; intro degree
      cases degree with
      | zero => simp [hzero, indecs, coeff_zero_eq_constantCoeff_apply]
      | succ degree =>
        rw [map_add, coeff_one, if_neg (by omega), zero_add, mul_assoc, coeff_C_mul,
          coeff_mul, Finset.Nat.sum_antidiagonal_succ]
        simp only [indecs, coeff_mk, ↓reduceIte, zero_mul, zero_add]
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [Nat.add_one_ne_zero, ↓reduceIte]; rw [show coeff (degree + 1) sequences =
          ∑ᶠ parts : components (degree + 1),
            (Polynomial.X : Polynomial ℚ) ^ parts.val.length by
              simp only [sequences, coeff_mk]]
        rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^ parts.length)]
        rw [← Fin.sum_univ_eq_sum_range]; rw [mul_sum]
        apply Finset.sum_congr rfl
        intro cut _; simp only [List.length_cons, pow_succ, finsum_eq_sum_of_fintype]
        rw [sum_comm]; simp only [sum_const, card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card (blocks (cut.val + 1)) : Polynomial ℚ) =
            ({word : List ℕ | word ∈ avoiders (cut.val + 1) patterns ∧
              sumIndecomposable word}.ncard : Polynomial ℚ) := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        simp only [hcard, sequences, coeff_mk, finsum_eq_sum_of_fintype]
        conv_rhs => rw [mul_left_comm Polynomial.X, mul_sum, mul_sum]
        apply Finset.sum_congr rfl
        intro rest _
        ring
    refine ⟨fun size => ⟨serialization size, fun _ => rfl⟩, ?_, ?_⟩
    · linear_combination hrecurrence
    intro weight
    let marked : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ block : blocks size, weight size block.val
    let heads : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ parts : components size,
        (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
          weight (parts.val.headD []).length (parts.val.headD [])
    let lasts : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ parts : components size,
        (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
          weight (parts.val.reverse.headD []).length (parts.val.reverse.headD [])
    let tails : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ parts : components size,
        (Polynomial.X : Polynomial ℚ) ^
          (if parts.val.tail = [] then 1 else parts.val.tail.length) *
            weight (parts.val.headD []).length (parts.val.headD [])
    change heads = marked * sequences ∧ lasts = heads ∧
      tails = C Polynomial.X * marked + marked * (sequences - 1)
    have hheads : heads = marked * sequences := by
      apply PowerSeries.ext; intro degree
      cases degree with
      | zero => simp [heads, marked, coeff_zero_eq_constantCoeff_apply]
      | succ degree =>
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
        simp only [marked, coeff_mk, ↓reduceIte, zero_mul, zero_add]
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [heads, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
        rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
          (parts.length - 1) * weight (parts.headD []).length (parts.headD [])),
          ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro cut _; have hl (block : blocks (cut.val + 1)) : block.val.length = cut.val + 1 := by
          simpa using block.property.1.1.length_eq
        simp only [List.length_cons, Nat.add_sub_cancel, List.headD_cons, hl,
          finsum_eq_sum_of_fintype, sequences, coeff_mk]
        rw [sum_mul]; apply Finset.sum_congr rfl
        intro block _; rw [mul_sum]
        apply Finset.sum_congr rfl
        intro rest _; exact mul_comm _ _
    refine ⟨hheads, ?_, ?_⟩
    · have hreverse (size : ℕ) (parts : components size) :
          parts.val.reverse ∈ components size := by
        have hv : ∀ block ∈ parts.val.reverse, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
          intro block hb; exact parts.property.1 block (List.mem_reverse.mp hb)
        have hc := (hclosure _ hv).mpr (fun block hb =>
          hblock _ parts block (List.mem_reverse.mp hb))
        have hl : (assemble parts.val.reverse).length = size := by
          rw [hlength, List.map_reverse, List.sum_reverse, ← hlength, hsize]
        exact ⟨hv, by simpa only [hl] using hc⟩
      let reversal (size : ℕ) : components size ≃ components size :=
        { toFun := fun parts => ⟨parts.val.reverse, hreverse size parts⟩
          invFun := fun parts => ⟨parts.val.reverse, hreverse size parts⟩
          left_inv := fun parts => Subtype.ext (List.reverse_reverse parts.val)
          right_inv := fun parts => Subtype.ext (List.reverse_reverse parts.val) }
      apply PowerSeries.ext; intro degree
      by_cases hz : degree = 0
      · simp [lasts, heads, hz]
      simp only [lasts, heads, coeff_mk, if_neg hz]; rw [← finsum_comp_equiv (reversal degree)]
      apply finsum_congr
      intro parts; simp [reversal]
    · have htailDifference : tails - heads = (C Polynomial.X - 1) * marked := by
        apply PowerSeries.ext; intro degree
        cases degree with
        | zero => simp [tails, heads, marked, coeff_zero_eq_constantCoeff_apply]
        | succ degree =>
          rw [map_sub, sub_mul, one_mul, map_sub, coeff_C_mul]
          simp only [tails, heads, marked, coeff_mk, Nat.add_one_ne_zero, ↓reduceIte]
          rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
            (if parts.tail = [] then 1 else parts.tail.length) *
              weight (parts.headD []).length (parts.headD [])),
            hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
              (parts.length - 1) * weight (parts.headD []).length (parts.headD []))]
          simp only [List.headD_cons, List.length_cons, Nat.add_sub_cancel,
            finsum_eq_sum_of_fintype]
          change (∑ cut : Fin (degree + 1), ∑ block : blocks (cut.val + 1),
            ∑ rest : components (degree - cut.val),
              Polynomial.X ^ (if rest.val = [] then 1 else rest.val.length) *
                weight block.val.length block.val) -
            (∑ cut : Fin (degree + 1), ∑ block : blocks (cut.val + 1),
              ∑ rest : components (degree - cut.val),
                Polynomial.X ^ rest.val.length * weight block.val.length block.val) = _
          rw [← sum_sub_distrib]
          let lastCut : Fin (degree + 1) := ⟨degree, by omega⟩
          rw [Finset.sum_eq_single lastCut]
          · dsimp +instances only [lastCut]
            have he (parts : components (degree - degree)) : parts.val = [] :=
              hempty ⟨parts.val, by simpa only [Nat.sub_self] using parts.property⟩
            let : Unique (components (degree - degree)) :=
              { default := ⟨[], by simpa only [Nat.sub_self] using hnil⟩
                uniq := fun parts => Subtype.ext (he parts) }
            have hl (block : blocks (degree + 1)) : block.val.length = degree + 1 := by
              simpa using block.property.1.1.length_eq
            simp only [he, ↓reduceIte, List.length_nil, pow_zero, pow_one, one_mul, hl,
              sum_const, card_univ, Fintype.card_unique, one_smul, ← mul_sum]
          · intro cut _ hne
            have hindex : cut.val ≠ degree := by
              intro heq; exact hne (Fin.ext heq)
            have hpositive : 0 < degree - cut.val := by omega
            have hl (rest : components (degree - cut.val)) : rest.val ≠ [] := by
              intro heq; have hs := hsize _ rest
              simp only [heq, assemble, List.length_nil] at hs
              omega
            simp only [hl, ↓reduceIte, sub_self]
          · simp
      linear_combination htailDifference + hheads
  have counts (second : Bool) :
      let patterns := match second with
        | true => [[2, 4, 3, 1], [3, 2, 4, 1]]
        | false => [[2, 4, 1, 3], [2, 4, 3, 1]]
      ∀ size, 1 ≤ size → (avoiders size patterns).ncard =
        FishburnCatalanBinomialDefs.binomialCatalan size := by
    let patterns : List (List ℕ) := match second with
      | true => [[2, 4, 3, 1], [3, 2, 4, 1]]
      | false => [[2, 4, 1, 3], [2, 4, 3, 1]]
    change ∀ size, 1 ≤ size → (avoiders size patterns).ncard =
      FishburnCatalanBinomialDefs.binomialCatalan size
    have hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
        (∀ value ∈ pattern, 1 ≤ value) ∧
        ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern := by
      intro pattern hp
      cases second <;>
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
      all_goals rcases hp with rfl | rfl
      all_goals
        refine ⟨by decide, by unfold sumIndecomposable; decide, by simp, ?_⟩
        intro rank hr hb
        norm_num [NonnestingDefs.letters] at hb
        simp only [List.mem_cons, List.not_mem_nil]
        omega
    let blocks (size : ℕ) := {word : List ℕ |
      word ∈ avoiders size patterns ∧ sumIndecomposable word}
    let components (size : ℕ) := {parts : List (List ℕ) |
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      assemble parts ∈ avoiders size patterns}
    let active (size : ℕ) (word : List ℕ) := (range (word.length + 1)).filter
      fun gap => word.insertIdx gap (size + 1) ∈ avoiders (size + 1) patterns
    let indecs : PowerSeries ℚ := mk fun size =>
      if size = 0 then 0 else ((blocks size).ncard : ℚ)
    let all : PowerSeries ℚ := mk fun size => ((avoiders size patterns).ncard : ℚ)
    let labelled : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ word : blocks size,
        (Polynomial.X : Polynomial ℚ) ^ ((active size word.val).card - 2)
    let quotient : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else ∑ᶠ word : blocks size,
        ∑ exponent ∈ range ((active size word.val).card - 2),
          (Polynomial.X : Polynomial ℚ) ^ exponent
    let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
      ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
    let lifted := indecs.map Polynomial.C
    let marker : PowerSeries (Polynomial ℚ) := C Polynomial.X
    let fronts := if second then (lifted + quotient) * (sequences - 1)
      else labelled * sequences
    have hcomponent :=
      componentSeries patterns hpatterns
    have hclosure := (unique_sum_components 0 [] (by simp) patterns hpatterns).2.1
    have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw; exact List.mem_permutations.mpr hw.1
    let (size : ℕ) : Finite (avoiders size patterns) := (hfinite size).to_subtype
    let (size : ℕ) : Fintype (avoiders size patterns) := Fintype.ofFinite _
    let (size : ℕ) : Finite (blocks size) :=
      ((hfinite size).subset (fun _ hw => hw.1)).to_subtype
    let (size : ℕ) : Fintype (blocks size) := Fintype.ofFinite _
    let (size : ℕ) : Finite (components size) :=
      Finite.of_equiv _ (Classical.choose (hcomponent.1 size)).symm
    let (size : ℕ) : Fintype (components size) := Fintype.ofFinite _
    have hshort (word : List ℕ) (hperm : word.Perm (List.range' 1 word.length))
        (hlen : word.length ≤ 2) : word ∈ avoiders word.length patterns := by
      refine ⟨hperm, ?_, ?_⟩
      · intro before later hgap hlater
        omega
      · intro pattern hp ⟨selection, _, _, hsub, _⟩
        have hl := hsub.length_le
        cases second <;>
          simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
        all_goals rcases hp with rfl | rfl
        all_goals simp only [List.length_map, List.length_cons, List.length_nil] at hl
        all_goals omega
    have honeMember : [1] ∈ blocks 1 :=
      ⟨hshort [1] (by decide) (by decide), by unfold sumIndecomposable; decide⟩
    have honeWord (word : blocks 1) : word.val = [1] := by
      exact List.perm_singleton.mp (by simpa using word.property.1.1)
    let : Unique (blocks 1) :=
      { default := ⟨[1], honeMember⟩
        uniq := fun word => Subtype.ext (honeWord word) }
    have honeCuts : active 1 [1] = range 2 := by
      ext gap; simp only [active, List.length_cons, List.length_nil, mem_filter]
      constructor
      · exact And.left
      · intro hg
        refine ⟨hg, ?_⟩
        have hb : gap < 2 := mem_range.mp hg
        interval_cases gap
        all_goals exact hshort _ (by decide) (by decide)
    have hone : coeff 1 labelled = 1 := by
      have hterm (word : blocks 1) :
          (Polynomial.X : Polynomial ℚ) ^ ((active 1 word.val).card - 2) = 1 := by
        rw [honeWord word, honeCuts, card_range]
        simp
      simp only [labelled, coeff_mk, Nat.one_ne_zero, ↓reduceIte]
      rw [finsum_congr hterm, finsum_eq_sum_of_fintype]
      simp
    have hconstant : constantCoeff labelled = 0 := by simp [labelled]
    have hquotientZero : constantCoeff quotient = 0 := by simp [quotient]
    have hliftZero : constantCoeff lifted = 0 := by
      dsimp only [lifted]; rw [← coeff_zero_eq_constantCoeff_apply, coeff_map]
      simp [indecs]
    have hseqZero : constantCoeff sequences = 1 := by
      have hh := congrArg constantCoeff hcomponent.2.1
      simpa [sequences] using hh
    have hfrontZero : constantCoeff fronts = 0 := by
      cases second <;> simp [fronts, hconstant, hquotientZero, hliftZero, hseqZero]
    have hlabelled : labelled = if second then
        X + X * lifted + X * marker * quotient + X * fronts
      else X + X * fronts + X * marker * quotient := by
      cases second with
      | false =>
        change labelled = X + X * fronts + X * marker * quotient
        have hlast := (hcomponent.2.2 (fun size word =>
          (Polynomial.X : Polynomial ℚ) ^ ((active size word).card - 2))).2.1
        have hhead := (hcomponent.2.2 (fun size word =>
          (Polynomial.X : Polynomial ℚ) ^ ((active size word).card - 2))).1
        have hlastSeries :
            (mk fun size => if size = 0 then 0 else ∑ᶠ parts : components size,
              (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
                (Polynomial.X : Polynomial ℚ) ^
                  ((active (parts.val.reverse.headD []).length
                    (parts.val.reverse.headD [])).card - 2)) = labelled * sequences :=
          hlast.trans hhead
        have hweight (size : ℕ) (hs : 0 < size) (parts : components size) :
            (Polynomial.X : Polynomial ℚ) ^ ((active size (assemble parts.val)).card - 2) =
              Polynomial.X ^ (parts.val.length - 1) * Polynomial.X ^
                ((active (parts.val.reverse.headD []).length
                  (parts.val.reverse.headD [])).card - 2) := by
          have hsize : (assemble parts.val).length = size := by
            simpa using parts.property.2.1.length_eq
          have hblocks : ∀ block ∈ parts.val, block ∈ avoiders block.length patterns :=
            (hclosure parts.val parts.property.1).mp (by
              simpa only [hsize] using parts.property.2)
          have hcalc : ∀ pieces : List (List ℕ),
              (∀ block ∈ pieces, block ≠ [] ∧
                block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
              (∀ block ∈ pieces, block ∈ avoiders block.length patterns) →
              pieces ≠ [] →
              (active (assemble pieces).length (assemble pieces)).card =
                pieces.length - 1 +
                  (active (pieces.reverse.headD []).length (pieces.reverse.headD [])).card ∧
              2 ≤ (active (pieces.reverse.headD []).length
                (pieces.reverse.headD [])).card := by
            intro pieces
            induction pieces using List.reverseRecOn with
            | nil => simp
            | append_singleton earlier last _ =>
              intro hv hc _; have hl := hv last (by simp)
              have hm := hc last (by simp)
              have hprefix : ∀ block ∈ earlier, block ≠ [] ∧
                  block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block :=
                fun block hb => hv block (List.mem_append_left _ hb)
              have hprefixClass := (hclosure earlier hprefix).mpr
                (fun block hb => hc block (List.mem_append_left _ hb))
              have happend : ∀ chunks : List (List ℕ),
                  assemble (chunks ++ [last]) =
                    directSum (assemble chunks).length (assemble chunks) last := by
                intro chunks
                induction chunks with
                | nil => simp [assemble, directSum, shift]
                | cons first rest ih =>
                  simp only [List.cons_append, assemble, ih, directSum, shift,
                    List.length_append, List.length_map, List.map_append,
                    List.map_map, List.append_assoc]
                  congr 1
                  congr 1
                  apply List.map_congr_left
                  intro value _; dsimp only [Function.comp_apply]
                  omega
              have hwhole := (hclosure (earlier ++ [last]) hv).mpr hc
              rw [happend] at hwhole
              have hlength : (directSum (assemble earlier).length (assemble earlier) last).length =
                  (assemble earlier).length + last.length := by
                simp [directSum, shift]
              rw [hlength] at hwhole; have hsum := (FishburnTenThirteenASums.interval_sum_sites
                (assemble earlier).length last.length (assemble earlier) last
                (List.length_pos_iff_ne_nil.mpr hl.1) hprefixClass.1 hm hwhole).2.2.2
                earlier hprefix rfl
              have hzero : 0 ∈ active last.length last := by
                simp only [active, mem_filter, mem_range]
                refine ⟨by omega, ?_⟩
                apply (FishburnTenThirteenSites.interval_active_sites
                  last.length last hm 0 (Nat.zero_le _)).mpr
                refine ⟨by intro before later hb; omega, ?_⟩
                constructor
                intro low hlo high hhi middle hbetween
                have hb (value : ℕ) (hv : value ∈ last) :
                    1 ≤ value ∧ value ≤ last.length := by
                  have hh := hl.2.1.mem_iff.mp hv
                  simp only [List.mem_range', Nat.one_mul] at hh
                  obtain ⟨index, hi, heq⟩ := hh
                  omega
                have hlow := hb low (by simpa using hlo)
                have hhigh := hb high (by simpa using hhi)
                have hbetween' : low ≤ middle ∧ middle ≤ high := hbetween
                apply hl.2.1.mem_iff.mpr
                simp only [List.mem_range', Nat.one_mul]; exact ⟨middle - 1, by omega, by omega⟩
              have hend : last.length ∈ active last.length last := by
                simp only [active, mem_filter, mem_range]
                refine ⟨by omega, ?_⟩
                apply (FishburnTenThirteenSites.interval_active_sites
                  last.length last hm last.length le_rfl).mpr
                refine ⟨by intro before later hb hs ht; omega, ?_⟩
                simpa using (Set.ordConnected_empty : Set.OrdConnected (∅ : Set ℕ))
              have hbound : 2 ≤ (active last.length last).card := by
                have hsubset : ({0, last.length} : Finset ℕ) ⊆ active last.length last := by
                  intro value hv; simp only [mem_insert, mem_singleton] at hv
                  rcases hv with rfl | rfl <;> assumption
                have hh := card_le_card hsubset
                have hn : last.length ≠ 0 := List.length_pos_iff_ne_nil.mpr hl.1 |>.ne'
                simpa [hn, Ne.symm hn] using hh
              simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
                List.headD_cons, List.length_append, List.length_singleton,
                Nat.add_sub_cancel, happend]
              exact ⟨by simpa only [active, hlength] using hsum, hbound⟩
          have hnonempty : parts.val ≠ [] := by
            intro he; simp only [he, assemble, List.length_nil] at hsize
            omega
          obtain ⟨hcuts, hbound⟩ := hcalc parts.val parts.property.1 hblocks hnonempty
          have hcuts' : (active size (assemble parts.val)).card =
              parts.val.length - 1 +
                (active (parts.val.reverse.headD []).length (parts.val.reverse.headD [])).card := by
            simpa only [hsize] using hcuts
          rw [hcuts', ← pow_add]; congr 1
          omega
        have hparentWeight (size : ℕ) (hs : 0 < size) :
            (∑ᶠ word : avoiders size patterns,
              (Polynomial.X : Polynomial ℚ) ^ ((active size word.val).card - 2)) =
              coeff size (labelled * sequences) := by
          obtain ⟨serialization, hserialize⟩ := hcomponent.1 size
          rw [← hlastSeries]; simp only [coeff_mk, if_neg (by omega : size ≠ 0)]
          rw [← finsum_comp_equiv serialization]; apply finsum_congr
          intro parts; rw [hserialize parts]
          exact hweight size hs parts
        apply PowerSeries.ext; intro degree
        cases degree with
        | zero => simp [coeff_zero_eq_constantCoeff_apply, hconstant]
        | succ degree =>
          simp only [map_add, mul_assoc, coeff_succ_X_mul, marker, coeff_C_mul, coeff_X]
          by_cases hz : degree = 0
          · subst degree
            simp [hone, hfrontZero, hquotientZero]
          · obtain ⟨construction, _, _, _, _, _, hpoly⟩ :=
              (FishburnTenThirteenAConstruction.indecomposable_construction degree).2
                (by omega)
            dsimp only at hpoly
            simp only [labelled, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]; have hchild :
                (∑ᶠ word : blocks (degree + 1),
                  (Polynomial.X : Polynomial ℚ) ^ ((active (degree + 1) word.val).card - 2)) =
                  (∑ᶠ word : avoiders degree patterns,
                    (Polynomial.X : Polynomial ℚ) ^ ((active degree word.val).card - 2)) +
                  Polynomial.X * ∑ᶠ word : blocks degree,
                    ∑ exponent ∈ range ((active degree word.val).card - 2),
                      (Polynomial.X : Polynomial ℚ) ^ exponent := by
              simpa only [blocks, active, patterns, Bool.false_eq_true, ↓reduceIte] using hpoly.2
            rw [hchild, hparentWeight degree (by omega)]; simp [fronts, quotient, hz, coeff_mk]
      | true =>
        change labelled = X + X * lifted + X * marker * quotient + X * fronts
        have hheads := (hcomponent.2.2 (fun _ _ => (1 : Polynomial ℚ))).1
        have hmarked :
            (mk fun size => if size = 0 then 0 else
              ∑ᶠ word : blocks size, (1 : Polynomial ℚ)) = lifted := by
          ext degree
          by_cases hz : degree = 0
          · simp [lifted, indecs, hz]
          · simp only [coeff_mk, if_neg hz, coeff_map, lifted, indecs,
              finsum_eq_sum_of_fintype, sum_const, card_univ, nsmul_eq_mul, mul_one]
            rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, map_natCast]
        rw [hmarked] at hheads; have htails := (hcomponent.2.2 (fun size word =>
          ∑ exponent ∈ range ((active size word).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ exponent)).2.2
        have hcombine : lifted * sequences +
            (marker * quotient + quotient * (sequences - 1)) =
              lifted + marker * quotient + (lifted + quotient) * (sequences - 1) := by
          ring
        apply PowerSeries.ext; intro degree
        cases degree with
        | zero => simp [coeff_zero_eq_constantCoeff_apply, hconstant]
        | succ degree =>
          simp only [map_add, mul_assoc, coeff_succ_X_mul, marker, coeff_C_mul, coeff_X]
          by_cases hz : degree = 0
          · subst degree
            simp [hone, hliftZero, hquotientZero, hfrontZero]
          · have hpoly := FishburnTenThirteenBIndecomposable.inductive_counting degree
              (by omega)
            dsimp only at hpoly
            have hformula := congrArg (coeff degree) hcombine
            rw [← hheads, ← htails] at hformula
            simp only [map_add, coeff_mk, if_neg hz] at hformula
            simp only [labelled, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]; have hchild :
                (∑ᶠ word : blocks (degree + 1),
                  (Polynomial.X : Polynomial ℚ) ^ ((active (degree + 1) word.val).card - 2)) =
                  (∑ᶠ parts : components degree,
                    (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1)) +
                  ∑ᶠ parts : components degree,
                    (Polynomial.X : Polynomial ℚ) ^
                      (if parts.val.tail = [] then 1 else parts.val.tail.length) *
                    ∑ exponent ∈ range
                      ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
                      (Polynomial.X : Polynomial ℚ) ^ exponent := by
              simpa only [blocks, components, active, patterns, ↓reduceIte] using hpoly
            rw [hchild]
            simpa [fronts, marker, coeff_C_mul, coeff_X, hz] using hformula
    have hsolution : ∀ size : ℕ, 1 ≤ size →
        coeff size all =
          (FishburnCatalanBinomialDefs.binomialCatalan size : ℚ) := by
      have hsequence := hcomponent.2.1
      change (1 - C Polynomial.X * mk (fun size => if size = 0 then 0 else
        ({word : List ℕ | word ∈ FishburnDefs.avoiders size patterns ∧
          sumIndecomposable word}.ncard : Polynomial ℚ))) * sequences = 1 at hsequence
      have hlift : mk (fun size => if size = 0 then 0 else
          ({word : List ℕ | word ∈ FishburnDefs.avoiders size patterns ∧
            sumIndecomposable word}.ncard : Polynomial ℚ)) = indecs.map Polynomial.C := by
        apply PowerSeries.ext; intro degree
        by_cases hz : degree = 0
        · simp [indecs, blocks, hz]
        · simp [indecs, blocks, hz]
      rw [hlift] at hsequence
      have hfronts : (1 - C Polynomial.X * indecs.map Polynomial.C) * fronts =
          if second then C Polynomial.X * indecs.map Polynomial.C *
            (indecs.map Polynomial.C + quotient) else labelled := by
        cases second <;> simp only [fronts, Bool.false_eq_true, ↓reduceIte]
        · linear_combination labelled * hsequence
        · linear_combination (indecs.map Polynomial.C + quotient) * hsequence
      have hquotient : (1 - C Polynomial.X) * quotient =
          indecs.map Polynomial.C - labelled := by
        apply PowerSeries.ext; intro degree
        have hfinite : ({word : List ℕ |
            word ∈ FishburnDefs.avoiders degree patterns ∧ sumIndecomposable word}).Finite := by
          apply (List.finite_toSet (List.range' 1 degree).permutations).subset
          intro word hw; exact List.mem_permutations.mpr hw.1.1
        let : Fintype {word : List ℕ |
          word ∈ FishburnDefs.avoiders degree patterns ∧ sumIndecomposable word} :=
          hfinite.fintype
        rw [sub_mul, one_mul]; simp only [map_sub, coeff_C_mul, coeff_map]
        by_cases hdegree : degree = 0
        · simp [hdegree, labelled, quotient, indecs]
        · simp only [labelled, quotient, indecs, coeff_mk, if_neg hdegree,
            finsum_eq_sum_of_fintype]
          have hfactor (value : Polynomial ℚ) : value - Polynomial.X * value =
              (1 - Polynomial.X) * value := by ring
          rw [hfactor, mul_sum]; simp only [mul_neg_geom_sum, sum_sub_distrib, sum_const, card_univ,
            nsmul_eq_mul, mul_one]
          congr 1
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, map_natCast]
      have hindecs : constantCoeff indecs = 0 := by
        simp [indecs]
      have hdecomp := FishburnBasicComponents.unique_sum_components 0 [] (by simp) patterns
        hpatterns
      have hallzero : constantCoeff all = 1 := by
        simp only [all, constantCoeff_mk, hdecomp.2.2.1, Nat.cast_one]
      have hproductEquation : indecs * all = all - 1 := by
        ext degree
        cases degree with
        | zero => simp [coeff_zero_eq_constantCoeff_apply, hindecs, hallzero]
        | succ degree =>
          rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
          simp only [coeff_zero_eq_constantCoeff_apply, hindecs, zero_mul, zero_add]
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          simp only [indecs, coeff_mk, Nat.add_one_ne_zero, ↓reduceIte, all]
          change (∑ cut ∈ range (degree + 1),
            (({word : List ℕ | word ∈ FishburnDefs.avoiders (cut + 1) patterns ∧
              sumIndecomposable word}.ncard : ℚ) *
              (FishburnDefs.avoiders (degree - cut) patterns).ncard)) = _
          rw [← Fin.sum_univ_eq_sum_range]
          have hcount := congrArg (Nat.cast : ℕ → ℚ) ((hdecomp.2.2.2.1 degree).1)
          push_cast at hcount
          simpa only [map_sub, coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero,
            all, coeff_mk] using hcount.symm
      have hcomponents : all * (1 - indecs) = 1 := by
        linear_combination -hproductEquation
      have hequation :
          let lifted := indecs.map Polynomial.C
          let marker : PowerSeries (Polynomial ℚ) := C Polynomial.X
          let base := if second then 1 else 1 - X
          let linear := if second then -(1 - X) * (1 + lifted) else 2 * X - 1 - lifted
          (base + linear * marker + (1 - X) * lifted * marker ^ 2) * labelled =
            if second then X * (1 - (1 - lifted) * marker) * (1 + lifted - lifted * marker)
            else X * (1 - lifted * marker) * (1 - (1 - lifted) * marker) := by
        cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlabelled hfronts ⊢
        · linear_combination
            (1 - C Polynomial.X) * (1 - C Polynomial.X * indecs.map Polynomial.C) * hlabelled +
            X * (1 - C Polynomial.X) * hfronts +
            X * C Polynomial.X * (1 - C Polynomial.X * indecs.map Polynomial.C) * hquotient
        · linear_combination
            (1 - C Polynomial.X) * (1 - C Polynomial.X * indecs.map Polynomial.C) * hlabelled +
            X * (1 - C Polynomial.X) * hfronts +
            X * C Polynomial.X *
              (1 + indecs.map Polynomial.C - C Polynomial.X * indecs.map Polynomial.C) * hquotient
      let base : PowerSeries ℚ := if second then 1 else 1 - X
      let linear : PowerSeries ℚ :=
        if second then -(1 - X) * (1 + indecs) else 2 * X - 1 - indecs
      let quadratic : PowerSeries ℚ := (1 - X) * indecs
      let step (root : PowerSeries ℚ) :=
        base + (linear + 1) * root + quadratic * root ^ 2
      have hbase : constantCoeff base = 1 := by cases second <;> simp [base]
      have hlinear : constantCoeff (linear + 1) = 0 := by
        cases second <;> simp [linear, hindecs]
      have hquadratic : constantCoeff quadratic = 0 := by simp [quadratic, hindecs]
      obtain ⟨linearTail, hlinearTail⟩ := X_dvd_iff.mpr hlinear
      obtain ⟨quadraticTail, hquadraticTail⟩ := X_dvd_iff.mpr hquadratic
      have hstepzero (root : PowerSeries ℚ) : constantCoeff (step root) = 1 := by
        simp [step, hbase, hlinear, hquadratic]
      have hcontract (degree : ℕ) (left right : PowerSeries ℚ)
          (hprefix : ∀ index < degree, coeff index left = coeff index right) :
          ∀ index < degree + 1, coeff index (step left) = coeff index (step right) := by
        have hdivide : X ^ degree ∣ left - right := by
          apply X_pow_dvd_iff.mpr
          intro index hindex; simp only [map_sub, hprefix index hindex, sub_self]
        obtain ⟨tail, htail⟩ := hdivide
        have hdifference : step left - step right =
            X * (linearTail + quadraticTail * (left + right)) * (left - right) := by
          dsimp only [step]; rw [hlinearTail, hquadraticTail]
          ring
        have hnext : X ^ (degree + 1) ∣ step left - step right := by
          refine ⟨(linearTail + quadraticTail * (left + right)) * tail, ?_⟩
          rw [hdifference, htail, pow_succ]
          ring
        intro index hindex; have hvalue := X_pow_dvd_iff.mp hnext index hindex
        simpa only [map_sub, sub_eq_zero] using hvalue
      let approximation (depth : ℕ) : PowerSeries ℚ := (step^[depth]) 1
      have hsuccessor (depth : ℕ) : approximation (depth + 1) = step (approximation depth) :=
        Function.iterate_succ_apply' step depth 1
      have happroxzero (depth : ℕ) : constantCoeff (approximation depth) = 1 := by
        cases depth with
        | zero => simp [approximation]
        | succ depth => rw [hsuccessor]; exact hstepzero _
      have hstable (depth stage : ℕ) (hbound : depth ≤ stage) :
          ∀ index < depth + 1, coeff index (approximation depth) =
            coeff index (approximation stage) := by
        induction depth generalizing stage with
        | zero =>
          intro index hindex; have hi : index = 0 := by omega
          subst index
          simp only [coeff_zero_eq_constantCoeff_apply, happroxzero]
        | succ depth induction =>
          cases stage with
          | zero => omega
          | succ stage =>
            rw [hsuccessor, hsuccessor]
            exact hcontract (depth + 1) _ _ (induction stage (by omega))
      let root : PowerSeries ℚ := mk fun index => coeff index (approximation index)
      have hrootprefix (depth : ℕ) : ∀ index < depth + 1,
          coeff index root = coeff index (approximation depth) := by
        intro index hindex
        simpa only [root, coeff_mk] using hstable index depth (by omega) index (by omega)
      have hfixed : root = step root := by
        apply PowerSeries.ext; intro index
        have hp := hrootprefix (index + 1) index (by omega)
        rw [hsuccessor] at hp
        exact hp.trans (hcontract (index + 1) _ _ (hrootprefix index) index (by omega)).symm
      have hkernel : base + linear * root + quadratic * root ^ 2 = 0 := by
        dsimp only [step] at hfixed
        linear_combination -hfixed
      let : UniformSpace ℚ := ⊥
      let : UniformSpace (Polynomial ℚ) := ⊥
      let coefficientEvaluation := Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) root
      have hcontinuous : Continuous coefficientEvaluation := continuous_of_discreteTopology
      let evaluation := eval₂Hom hcontinuous (HasEval.X (R := ℚ))
      have hevalX : evaluation X = X := by simp [evaluation, coe_eval₂Hom]
      have hevalMarker : evaluation (C Polynomial.X) = root := by
        simp [evaluation, coe_eval₂Hom, coefficientEvaluation, Polynomial.coe_eval₂RingHom]
      have hevalLift (source : PowerSeries ℚ) :
          evaluation (source.map Polynomial.C) = source := by
        have hevaluated := hasSum_eval₂ hcontinuous (HasEval.X (R := ℚ))
          (source.map Polynomial.C)
        have hord := PowerSeries.hasSum_of_monomials_self source
        have hterms : (fun index => coefficientEvaluation
            (coeff index (source.map Polynomial.C)) * X ^ index) =
            (fun index => monomial index (coeff index source)) := by
          funext index
          simp [coefficientEvaluation, coeff_map, Polynomial.coe_eval₂RingHom,
            monomial_eq_C_mul_X_pow]
        rw [hterms] at hevaluated
        simpa only [evaluation, coe_eval₂Hom] using hevaluated.unique hord
      have hright : 1 - (1 - indecs) * root = 0 := by
        have hevaluated := congrArg evaluation hequation
        cases second with
        | false =>
          change evaluation (((1 - X) + (2 * X - 1 - indecs.map Polynomial.C) *
            C Polynomial.X + (1 - X) * indecs.map Polynomial.C * (C Polynomial.X) ^ 2) *
            labelled) = evaluation (X * (1 - indecs.map Polynomial.C * C Polynomial.X) *
            (1 - (1 - indecs.map Polynomial.C) * C Polynomial.X)) at hevaluated
          simp only [map_mul, map_add, map_sub, map_one, map_pow, map_ofNat, hevalX,
            hevalMarker, hevalLift] at hevaluated
          have hk : (1 - X) + (2 * X - 1 - indecs) * root +
              (1 - X) * indecs * root ^ 2 = 0 := hkernel
          rw [hk, zero_mul] at hevaluated; have hfactor : 1 - indecs * root ≠ 0 := by
            intro hz; have hvalue := congrArg constantCoeff hz
            simp [hindecs] at hvalue
          exact (mul_eq_zero.mp hevaluated.symm).resolve_left (mul_ne_zero X_ne_zero hfactor)
        | true =>
          change evaluation ((1 + (-(1 - X) * (1 + indecs.map Polynomial.C)) *
            C Polynomial.X + (1 - X) * indecs.map Polynomial.C * (C Polynomial.X) ^ 2) *
            labelled) = evaluation (X * (1 - (1 - indecs.map Polynomial.C) * C Polynomial.X) *
            (1 + indecs.map Polynomial.C - indecs.map Polynomial.C * C Polynomial.X)) at hevaluated
          simp only [map_mul, map_add, map_sub, map_neg, map_one, map_pow, hevalX,
            hevalMarker, hevalLift] at hevaluated
          have hk : 1 + (-(1 - X) * (1 + indecs)) * root +
              (1 - X) * indecs * root ^ 2 = 0 := hkernel
          rw [hk, zero_mul] at hevaluated; have hfactor : 1 + indecs - indecs * root ≠ 0 := by
            intro hz; have hvalue := congrArg constantCoeff hz
            simp [hindecs] at hvalue
          have hproduct := (mul_eq_zero.mp hevaluated.symm).resolve_right hfactor
          exact (mul_eq_zero.mp hproduct).resolve_left X_ne_zero
      have hrootinverse : (1 - indecs) * root = 1 := by linear_combination -hright
      have hscaled : base * (1 - indecs) ^ 2 + linear * (1 - indecs) + quadratic = 0 := by
        calc
          base * (1 - indecs) ^ 2 + linear * (1 - indecs) + quadratic =
              base * (1 - indecs) ^ 2 + linear * (1 - indecs) * ((1 - indecs) * root) +
                quadratic * ((1 - indecs) * root) ^ 2 := by rw [hrootinverse]; ring
          _ = (1 - indecs) ^ 2 * (base + linear * root + quadratic * root ^ 2) := by ring
          _ = 0 := by rw [hkernel, mul_zero]
      have hquadraticEquation : (2 - X) * indecs ^ 2 - (1 + X) * indecs + X = 0 := by
        cases second <;> dsimp [base, linear, quadratic] at hscaled <;>
          linear_combination hscaled
      have hproduct : indecs * all = all - 1 := by linear_combination -hcomponents
      have hcounting : (2 - X) * (all - 1) ^ 2 - (1 + X) * (all - 1) * all + X * all ^ 2 = 0 := by
        calc
          (2 - X) * (all - 1) ^ 2 - (1 + X) * (all - 1) * all + X * all ^ 2 =
              (2 - X) * (indecs * all) ^ 2 - (1 + X) * (indecs * all) * all + X * all ^ 2 := by
                rw [hproduct]
          _ = ((2 - X) * indecs ^ 2 - (1 + X) * indecs + X) * all ^ 2 := by ring
          _ = 0 := by rw [hquadraticEquation, zero_mul]
      have hcountingScaled : (1 - X) * ((all - 1) - (all - 1) ^ 2) = X := by
        linear_combination -hcounting
      have hcountingEquation : all - 1 = X * mk (fun _ => (1 : ℚ)) + (all - 1) ^ 2 := by
        have hvalue := congrArg (fun value => (mk 1 : PowerSeries ℚ) * value) hcountingScaled
        rw [← mul_assoc, mk_one_mul_one_sub_eq_one, one_mul] at hvalue
        linear_combination hvalue
      have hcountingZero : constantCoeff (all - 1) = 0 := by simp [hallzero]
      have coefficientFormula (series : PowerSeries ℚ)
          (hzero : constantCoeff series = 0)
          (hequation : series = X * mk (fun _ => (1 : ℚ)) + series ^ 2) :
          ∀ size : ℕ, 1 ≤ size →
            coeff size (1 + series) =
              (FishburnCatalanBinomialDefs.binomialCatalan size : ℚ) := by
        classical
        let time : PowerSeries ℚ := X * mk (fun _ => (1 : ℚ))
        let cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries
        let candidate : PowerSeries ℚ := time * cat.subst time
        have htime : constantCoeff time = 0 := by simp [time]
        have hsubst : HasSubst time := HasSubst.of_constantCoeff_zero' htime
        have hcat : cat ^ 2 * X + 1 = cat := by
          simpa [cat] using congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
        have hcandidate : candidate = time + candidate ^ 2 := by
          have equation := congrArg (subst time) hcat
          rw [subst_add hsubst, subst_mul hsubst, subst_pow hsubst, subst_X hsubst] at equation
          have hone : (1 : PowerSeries ℚ).subst time = 1 := by
            simpa using (subst_C (a := time) (1 : ℚ))
          rw [hone] at equation; dsimp [candidate]
          calc
            time * cat.subst time = time * ((cat.subst time) ^ 2 * time + 1) :=
              congrArg (time * ·) equation.symm
            _ = time + (time * cat.subst time) ^ 2 := by ring
        have hcandzero : constantCoeff candidate = 0 := by simp [candidate, htime]
        have hunique : series = candidate := by
          have hunit : IsUnit (1 - series - candidate) :=
            PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hzero, hcandzero])
          apply sub_eq_zero.mp
          apply hunit.mul_right_cancel
          simp only [zero_mul]; have hseries : series = time + series ^ 2 := hequation
          linear_combination hseries - hcandidate
        have hpower (degree exponent : ℕ) : coeff degree (time ^ (exponent + 1)) =
            if exponent + 1 ≤ degree then ((degree - 1).choose exponent : ℚ) else 0 := by
          dsimp only [time]; rw [mul_pow, coeff_X_pow_mul']
          have hp := mk_one_pow_eq_mk_choose_add ℚ exponent
          change (mk (fun _ => (1 : ℚ))) ^ (exponent + 1) = _ at hp
          rw [hp]
          split_ifs with hbound
          · rw [coeff_mk]
            congr 2
            omega
          · rfl
        have hpositive : candidate = (X * cat).subst time := by
          rw [subst_mul hsubst, subst_X hsubst]
        intro size hsize; rw [hunique, map_add, coeff_one, if_neg (by omega), zero_add, hpositive,
          coeff_subst' hsubst]
        have hcoeff (exponent : ℕ) : coeff exponent (X * cat) =
            if exponent = 0 then 0 else (catalan (exponent - 1) : ℚ) := by
          cases exponent with
          | zero => simp
          | succ exponent => simp [cat, coeff_map, coeff_succ_X_mul]
        have hfinite : Function.support (fun exponent : ℕ =>
            coeff exponent (X * cat) • coeff size (time ^ exponent)) ⊆
            (Icc 1 size : Set ℕ) := by
          intro exponent hexponent; simp only [Function.mem_support, smul_eq_mul] at hexponent
          have hpos : 0 < exponent := by
            by_contra h
            have he : exponent = 0 := by omega
            simp [he, hcoeff] at hexponent
          have hbound : exponent ≤ size := by
            by_contra h
            obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
            rw [hpower, if_neg (by omega), mul_zero] at hexponent
            contradiction
          exact mem_Icc.mpr ⟨hpos, hbound⟩
        rw [finsum_eq_sum_of_support_subset _ hfinite]; have hsum : (∑ exponent ∈ Icc 1 size,
            coeff exponent (X * cat) • coeff size (time ^ exponent)) =
            ∑ exponent ∈ Icc 1 size,
              (((size - 1).choose (exponent - 1) * catalan (exponent - 1) : ℕ) : ℚ) := by
          apply sum_congr rfl
          intro exponent hexponent; have hb := mem_Icc.mp hexponent
          obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
          rw [hcoeff, if_neg (by omega), hpower, if_pos hb.2]
          simp only [Nat.succ_sub_one, smul_eq_mul, Nat.cast_mul]
          ring
        rw [hsum]; unfold FishburnCatalanBinomialDefs.binomialCatalan
        push_cast; apply sum_bij (fun exponent _ => size + 1 - exponent)
        · intro exponent hexponent
          have hb := mem_Icc.mp hexponent
          exact mem_Icc.mpr ⟨by omega, by omega⟩
        · intro left hleft right hright heq
          have hl := mem_Icc.mp hleft
          have hr := mem_Icc.mp hright
          omega
        · intro exponent hexponent
          have hb := mem_Icc.mp hexponent
          refine ⟨size + 1 - exponent, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          omega
        · intro exponent hexponent
          have hb := mem_Icc.mp hexponent
          have hindex : size + 1 - exponent - 1 = size - exponent := by omega
          have hcatindex : size - (size + 1 - exponent) = exponent - 1 := by omega
          rw [hindex, hcatindex]
          have hchoose := Nat.choose_symm (by omega : exponent - 1 ≤ size - 1)
          rw [show size - 1 - (exponent - 1) = size - exponent by omega] at hchoose; rw [hchoose]


      have hcoefficients := coefficientFormula
        (all - 1) hcountingZero hcountingEquation
      simpa only [add_sub_cancel] using hcoefficients
    intro size hs; have hh := hsolution size hs
    simp only [all, coeff_mk] at hh
    exact_mod_cast hh
  intro size hs; exact ⟨counts false size hs, counts true size hs⟩

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteen
