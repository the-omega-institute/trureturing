/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen
   mirror-E: none(waiver:egge-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reversible labelled constructors give both binomial-Catalan Fishburn counts. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenCoefficients
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenAConstruction
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteen

open D5.S3.Combinatorics Fishburn FishburnDefs Nonnesting
open NonnestingBasicSum FishburnBasicComponents PowerSeries Finset
open scoped PowerSeries.WithPiTopology

set_option maxHeartbeats 4000000 in
theorem result : FishburnCatalanBinomialDefs.claim1013 := by
  classical
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
      FishburnTenThirteenComponentSeries.weighted_component_series patterns hpatterns
    have hclosure := (unique_sum_components 0 [] (by simp) patterns hpatterns).2.1
    have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw
      exact List.mem_permutations.mpr hw.1
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
      ext gap
      simp only [active, List.length_cons, List.length_nil, mem_filter]
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
      dsimp only [lifted]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map]
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
              intro hv hc _
              have hl := hv last (by simp)
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
                  intro value _
                  dsimp only [Function.comp_apply]
                  omega
              have hwhole := (hclosure (earlier ++ [last]) hv).mpr hc
              rw [happend] at hwhole
              have hlength : (directSum (assemble earlier).length (assemble earlier) last).length =
                  (assemble earlier).length + last.length := by
                simp [directSum, shift]
              rw [hlength] at hwhole
              have hsum := (FishburnTenThirteenASums.interval_sum_sites
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
                simp only [List.mem_range', Nat.one_mul]
                exact ⟨middle - 1, by omega, by omega⟩
              have hend : last.length ∈ active last.length last := by
                simp only [active, mem_filter, mem_range]
                refine ⟨by omega, ?_⟩
                apply (FishburnTenThirteenSites.interval_active_sites
                  last.length last hm last.length le_rfl).mpr
                refine ⟨by intro before later hb hs ht; omega, ?_⟩
                simpa using (Set.ordConnected_empty : Set.OrdConnected (∅ : Set ℕ))
              have hbound : 2 ≤ (active last.length last).card := by
                have hsubset : ({0, last.length} : Finset ℕ) ⊆ active last.length last := by
                  intro value hv
                  simp only [mem_insert, mem_singleton] at hv
                  rcases hv with rfl | rfl <;> assumption
                have hh := card_le_card hsubset
                have hn : last.length ≠ 0 := List.length_pos_iff_ne_nil.mpr hl.1 |>.ne'
                simpa [hn, Ne.symm hn] using hh
              simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
                List.headD_cons, List.length_append, List.length_singleton,
                Nat.add_sub_cancel, happend]
              exact ⟨by simpa only [active, hlength] using hsum, hbound⟩
          have hnonempty : parts.val ≠ [] := by
            intro he
            simp only [he, assemble, List.length_nil] at hsize
            omega
          obtain ⟨hcuts, hbound⟩ := hcalc parts.val parts.property.1 hblocks hnonempty
          have hcuts' : (active size (assemble parts.val)).card =
              parts.val.length - 1 +
                (active (parts.val.reverse.headD []).length (parts.val.reverse.headD [])).card := by
            simpa only [hsize] using hcuts
          rw [hcuts', ← pow_add]
          congr 1
          omega
        have hparentWeight (size : ℕ) (hs : 0 < size) :
            (∑ᶠ word : avoiders size patterns,
              (Polynomial.X : Polynomial ℚ) ^ ((active size word.val).card - 2)) =
              coeff size (labelled * sequences) := by
          obtain ⟨serialization, hserialize⟩ := hcomponent.1 size
          rw [← hlastSeries]
          simp only [coeff_mk, if_neg (by omega : size ≠ 0)]
          rw [← finsum_comp_equiv serialization]
          apply finsum_congr
          intro parts
          rw [hserialize parts]
          exact hweight size hs parts
        apply PowerSeries.ext
        intro degree
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
            simp only [labelled, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
            have hchild :
                (∑ᶠ word : blocks (degree + 1),
                  (Polynomial.X : Polynomial ℚ) ^ ((active (degree + 1) word.val).card - 2)) =
                  (∑ᶠ word : avoiders degree patterns,
                    (Polynomial.X : Polynomial ℚ) ^ ((active degree word.val).card - 2)) +
                  Polynomial.X * ∑ᶠ word : blocks degree,
                    ∑ exponent ∈ range ((active degree word.val).card - 2),
                      (Polynomial.X : Polynomial ℚ) ^ exponent := by
              simpa only [blocks, active, patterns, Bool.false_eq_true, ↓reduceIte] using hpoly.2
            rw [hchild, hparentWeight degree (by omega)]
            simp [fronts, quotient, hz, coeff_mk]
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
        rw [hmarked] at hheads
        have htails := (hcomponent.2.2 (fun size word =>
          ∑ exponent ∈ range ((active size word).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ exponent)).2.2
        have hcombine : lifted * sequences +
            (marker * quotient + quotient * (sequences - 1)) =
              lifted + marker * quotient + (lifted + quotient) * (sequences - 1) := by
          ring
        apply PowerSeries.ext
        intro degree
        cases degree with
        | zero => simp [coeff_zero_eq_constantCoeff_apply, hconstant]
        | succ degree =>
          simp only [map_add, mul_assoc, coeff_succ_X_mul, marker, coeff_C_mul, coeff_X]
          by_cases hz : degree = 0
          · subst degree
            simp [hone, hliftZero, hquotientZero, hfrontZero]
          · obtain ⟨construction, _, _, _, _, hpoly⟩ :=
              (FishburnTenThirteenBReconstruction.indecomposable_construction degree).2
                (by omega)
            dsimp only at hpoly
            have hformula := congrArg (coeff degree) hcombine
            rw [← hheads, ← htails] at hformula
            simp only [map_add, coeff_mk, if_neg hz] at hformula
            simp only [labelled, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
            have hchild :
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
      classical
      let all : PowerSeries ℚ := mk fun size => (FishburnDefs.avoiders size patterns).ncard
      let indecs : PowerSeries ℚ := mk fun size =>
        if size = 0 then 0 else ({word : List ℕ | word ∈ FishburnDefs.avoiders size patterns ∧
          sumIndecomposable word}.ncard : ℚ)
      let active (size : ℕ) (word : List ℕ) := (Finset.range (word.length + 1)).filter
        fun gap => word.insertIdx gap (size + 1) ∈ FishburnDefs.avoiders (size + 1) patterns
      let labelled : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ word : {word : List ℕ |
          word ∈ FishburnDefs.avoiders size patterns ∧ sumIndecomposable word},
          (Polynomial.X : Polynomial ℚ) ^ ((active size word.val).card - 2)
      let quotient : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ word : {word : List ℕ |
          word ∈ FishburnDefs.avoiders size patterns ∧ sumIndecomposable word},
          ∑ exponent ∈ range ((active size word.val).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ exponent
      let components (size : ℕ) := {parts : List (List ℕ) |
        (∀ block ∈ parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
        FishburnBasicComponents.assemble parts ∈ FishburnDefs.avoiders size patterns}
      let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
        ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
      let fronts := if second then (indecs.map Polynomial.C + quotient) * (sequences - 1)
        else labelled * sequences
      change labelled = if second then X + X * indecs.map Polynomial.C +
        X * C Polynomial.X * quotient + X * fronts else
          X + X * fronts + X * C Polynomial.X * quotient at hlabelled
      change ∀ size : ℕ, 1 ≤ size →
        coeff size all = (FishburnCatalanBinomialDefs.binomialCatalan size : ℚ)
      have hsequence :=
        (FishburnTenThirteenComponentSeries.weighted_component_series patterns hpatterns).2.1
      change (1 - C Polynomial.X * mk (fun size => if size = 0 then 0 else
        ({word : List ℕ | word ∈ FishburnDefs.avoiders size patterns ∧
          sumIndecomposable word}.ncard : Polynomial ℚ))) * sequences = 1 at hsequence
      have hlift : mk (fun size => if size = 0 then 0 else
          ({word : List ℕ | word ∈ FishburnDefs.avoiders size patterns ∧
            sumIndecomposable word}.ncard : Polynomial ℚ)) = indecs.map Polynomial.C := by
        apply PowerSeries.ext
        intro degree
        by_cases hz : degree = 0
        · simp [indecs, hz]
        · simp [indecs, hz]
      rw [hlift] at hsequence
      have hfronts : (1 - C Polynomial.X * indecs.map Polynomial.C) * fronts =
          if second then C Polynomial.X * indecs.map Polynomial.C *
            (indecs.map Polynomial.C + quotient) else labelled := by
        cases second <;> simp only [fronts, Bool.false_eq_true, ↓reduceIte]
        · linear_combination labelled * hsequence
        · linear_combination (indecs.map Polynomial.C + quotient) * hsequence
      have hquotient : (1 - C Polynomial.X) * quotient =
          indecs.map Polynomial.C - labelled := by
        apply PowerSeries.ext
        intro degree
        have hfinite : ({word : List ℕ |
            word ∈ FishburnDefs.avoiders degree patterns ∧ sumIndecomposable word}).Finite := by
          apply (List.finite_toSet (List.range' 1 degree).permutations).subset
          intro word hw
          exact List.mem_permutations.mpr hw.1.1
        let : Fintype {word : List ℕ |
          word ∈ FishburnDefs.avoiders degree patterns ∧ sumIndecomposable word} :=
          hfinite.fintype
        rw [sub_mul, one_mul]
        simp only [map_sub, coeff_C_mul, coeff_map]
        by_cases hdegree : degree = 0
        · simp [hdegree, labelled, quotient, indecs]
        · simp only [labelled, quotient, indecs, coeff_mk, if_neg hdegree,
            finsum_eq_sum_of_fintype]
          have hfactor (value : Polynomial ℚ) : value - Polynomial.X * value =
              (1 - Polynomial.X) * value := by ring
          rw [hfactor, mul_sum]
          simp only [mul_neg_geom_sum, sum_sub_distrib, sum_const, card_univ,
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
          intro index hindex
          simp only [map_sub, hprefix index hindex, sub_self]
        obtain ⟨tail, htail⟩ := hdivide
        have hdifference : step left - step right =
            X * (linearTail + quadraticTail * (left + right)) * (left - right) := by
          dsimp only [step]
          rw [hlinearTail, hquadraticTail]
          ring
        have hnext : X ^ (degree + 1) ∣ step left - step right := by
          refine ⟨(linearTail + quadraticTail * (left + right)) * tail, ?_⟩
          rw [hdifference, htail, pow_succ]
          ring
        intro index hindex
        have hvalue := X_pow_dvd_iff.mp hnext index hindex
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
          intro index hindex
          have hi : index = 0 := by omega
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
        apply PowerSeries.ext
        intro index
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
          rw [hk, zero_mul] at hevaluated
          have hfactor : 1 - indecs * root ≠ 0 := by
            intro hz
            have hvalue := congrArg constantCoeff hz
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
          rw [hk, zero_mul] at hevaluated
          have hfactor : 1 + indecs - indecs * root ≠ 0 := by
            intro hz
            have hvalue := congrArg constantCoeff hz
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
      have hcoefficients := FishburnTenThirteenCoefficients.counting_solution
        (all - 1) hcountingZero hcountingEquation
      simpa only [add_sub_cancel] using hcoefficients
    intro size hs
    have hh := hsolution size hs
    simp only [all, coeff_mk] at hh
    exact_mod_cast hh
  intro size hs
  exact ⟨counts false size hs, counts true size hs⟩

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteen
