/- GID: D5/S3/Combinatorics/Circle/ForcedMixedDyadic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ForcedMixedDyadic
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Every two-fresh strict competitor in an unbounded native family requires a mixed packet. -/
module
public import D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
public import D5.S3.Combinatorics.Circle.DyadicResetDenominations
import Mathlib.Tactic

/-! Necessary physical count and prefix constraints allow arbitrary returns and reorderings. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ForcedMixedDyadic
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open DyadicResetSource DyadicResetBlocks DyadicResetDenominations
open scoped BigOperators

private theorem forced_counts (a b c x y z₁ z₂ A B H₀ Gt Ht Ut : ℕ)
    (hAB : A < B) (ha : a ≤ 1) (budget : a + b + c ≤ 2) (h : ℤ)
    (hend : 0 ≤ h ∧ h ≤ 7)
    (hmass : h = 6 + 4 * ((a : ℤ) - x) - 7 * ((b : ℤ) - y) +
      2 * c - z₁ - 2 * z₂)
    (block : (1 : ℤ) + a + y ≤ b + x + if 4 ≤ h then 1 else 0)
    (gbal : Gt + a + b = 3 + x + y)
    (hbal : Ht + x * A + y * B = H₀ + a * A + b * B)
    (ubal : Ut + a + b + c = 5 + x + y + z₁ + z₂)
    (strict : Gt < 3 ∨ Gt = 3 ∧ (Ht < H₀ ∨ Ht = H₀ ∧ Ut < 5)) :
    a = 0 ∧ b = 1 ∧ c = 1 := by
  rcases strict with hg | ⟨hg, hs⟩
  · split_ifs at block <;> omega
  · have hcounts : a + b = x + y := by omega
    have hax : a ≤ x := by split_ifs at block <;> omega
    obtain ⟨d, hd, hBd⟩ : ∃ d : ℕ, 0 < d ∧ B = A + d :=
      ⟨B - A, by omega, by omega⟩
    obtain ⟨v, hxv⟩ : ∃ v : ℕ, x = a + v := ⟨x - a, by omega⟩
    have hbv : b = y + v := by omega
    subst B; subst x; subst b
    have hbal' : Ht = H₀ + v * d := by nlinarith [hbal]
    rcases hs with hh | ⟨hh, hu⟩
    · omega
    · have hv : v = 0 := by nlinarith
      subst v
      omega


private def count (r : ℕ) (W : List (Fin (4 * r))) (a : ℕ) : ℕ :=
  W.countP (fun i => exponent 4 r i = a)

private theorem count_card (r : ℕ) (L : List (Fin (4 * r))) (hn : L.Nodup)
    (a : ℕ) : (L.toFinset.filter (fun i => exponent 4 r i = a)).card = count r L a := by
  classical
  have he : L.toFinset.filter (fun i => exponent 4 r i = a) =
      (L.filter (fun i => exponent 4 r i = a)).toFinset := by
    ext i
    simp
  rw [he, List.toFinset_card_of_nodup (hn.filter _)]
  rfl

private theorem four_sums (r : ℕ) (W : List (Fin (4 * r))) :
    mass (scaled 4 r) W =
      (count r W 0 : ℤ) + 2 * count r W 1 + 4 * count r W 2 - 7 * count r W 3 ∧
    W.length = count r W 0 + count r W 1 + count r W 2 + count r W 3 := by
  induction W with
  | nil => simp [count, mass]
  | cons a W ih =>
    have ha : exponent 4 r a < 4 := Nat.mod_lt _ (by decide)
    have hv : scaled 4 r a =
        if exponent 4 r a = 0 then 1 else
        if exponent 4 r a = 1 then 2 else
        if exponent 4 r a = 2 then 4 else -7 := by
      change (if exponent 4 r a = 3 then -(7 : ℤ) else (2 : ℤ) ^ exponent 4 r a) = _
      interval_cases h : exponent 4 r a <;> norm_num [h]
    simp only [count, mass, List.map_cons, List.sum_cons,
      List.length_cons, List.countP_cons] at ih ⊢
    rw [hv]
    interval_cases h : exponent 4 r a <;> simp [h] at * <;> omega

private theorem four_energy (r : ℕ) (hr : 1 ≤ r) (W : List (Fin (4 * r))) :
    H (4 * r) (unit 4 r) W =
      count r W 2 * 3 ^ (4 * unit 4 r) + count r W 3 * 3 ^ (7 * unit 4 r) := by
  have hv (a : Fin (4 * r)) : energyWeight (4 * r) (unit 4 r) a =
      if exponent 4 r a = 2 then 3 ^ (4 * unit 4 r) else
      if exponent 4 r a = 3 then 3 ^ (7 * unit 4 r) else 0 := by
    have ha : exponent 4 r a < 4 := Nat.mod_lt _ (by decide)
    have hs := source_values 4 r (by decide) hr a
    have hl := large_iff 4 r (by decide) hr a
    change Large _ _ a ↔ 2 ≤ exponent 4 r a at hl
    change actualSource (4 * r) (unit 4 r) a =
      (unit 4 r : ℤ) * (if exponent 4 r a = 3 then -(7 : ℤ)
        else (2 : ℤ) ^ exponent 4 r a) at hs
    unfold energyWeight
    interval_cases h : exponent 4 r a <;>
      norm_num [h] at hs hl ⊢ <;>
      simp [hs, hl, Int.natAbs_mul, mul_comm]
  induction W with
  | nil => simp [H, mass, count]
  | cons a W ih =>
    have ha : exponent 4 r a < 4 := Nat.mod_lt _ (by decide)
    simp only [H, mass, List.map_cons, List.sum_cons, count, List.countP_cons] at ih ⊢
    rw [hv]
    interval_cases h : exponent 4 r a <;> simp [h, Nat.add_mul] at * <;> omega

private theorem permutation_of_differences {α : Type*} [DecidableEq α]
    (W V : List α) (hW : W.Nodup) (hV : V.Nodup) :
    (V ++ (W.toFinset \ V.toFinset).toList).Perm
      (W ++ (V.toFinset \ W.toFinset).toList) := by
  classical
  have hn₁ : (V ++ (W.toFinset \ V.toFinset).toList).Nodup := by
    apply hV.append (Finset.nodup_toList _)
    apply List.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (List.mem_toFinset.mpr ha)
  have hn₂ : (W ++ (V.toFinset \ W.toFinset).toList).Nodup := by
    apply hW.append (Finset.nodup_toList _)
    apply List.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (List.mem_toFinset.mpr ha)
  apply (List.perm_ext_iff_of_nodup hn₁ hn₂).mpr
  intro a
  simp only [List.mem_append, Finset.mem_toList, Finset.mem_sdiff, List.mem_toFinset]
  tauto

/-- The necessity argument quantifies over every physical ordering and every
choice of returned old labels. The old inventory is specified by its four
native residue multiplicities, not by a proposed competitor or arrival gate. -/
theorem forced_mixed_of_counts (r : ℕ) (hr : 3 ≤ r)
    (W V : List (Fin (4 * r)))
    (hW : TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) W)
    (hV : TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) V)
    (hc0 : W.countP (fun i => exponent 4 r i = 0) = r)
    (hc1 : W.countP (fun i => exponent 4 r i = 1) = r - 2)
    (hc2 : W.countP (fun i => exponent 4 r i = 2) = r - 1)
    (hc3 : W.countP (fun i => exponent 4 r i = 3) = r - 2)
    (fresh : (V.toFinset \ W.toFinset).card ≤ 2)
    (strict : J (4 * r) (unit 4 r) V < J (4 * r) (unit 4 r) W) :
    ∃ e z : Fin (4 * r), e ≠ z ∧
      V.toFinset \ W.toFinset = {e, z} ∧
      actualSource (4 * r) (unit 4 r) e = 2 * (unit 4 r : ℤ) ∧
      actualSource (4 * r) (unit 4 r) z = -7 * (unit 4 r : ℤ) := by
  classical
  let I := (V.toFinset \ W.toFinset).toList
  let R := (W.toFinset \ V.toFinset).toList
  have hperm : (V ++ R).Perm (W ++ I) := permutation_of_differences W V hW.1 hV.1
  have hcount (a : ℕ) : count r V a + count r R a = count r W a + count r I a := by
    simpa [count] using hperm.countP_eq (fun i => exponent 4 r i = a)
  have hIc0 : count r I 0 = 0 := by
    have hfull : W.toFinset.filter (fun i => exponent 4 r i = 0) =
        Finset.univ.filter (fun i : Fin (4 * r) => exponent 4 r i = 0) := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have hwc : (W.toFinset.filter (fun i => exponent 4 r i = 0)).card = r := by
        rw [count_card r W hW.1]
        exact hc0
      have hrc : (Finset.univ.filter (fun i : Fin (4 * r) => exponent 4 r i = 0)).card = r :=
        residue_card 4 r 0 (by decide) (by decide)
      rw [hrc, hwc]
    apply List.countP_eq_zero.mpr
    intro a ha
    have hi := Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro hz
    have hmem : a ∈ W.toFinset.filter (fun i => exponent 4 r i = 0) := by
      rw [hfull]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hz⟩
    exact hi.2 (Finset.mem_filter.mp hmem).1
  have hIc2 : count r I 2 ≤ 1 := by
    have htot : count r W 2 + count r I 2 ≤ r := by
      have hn : (W ++ I).Nodup := hW.1.append (Finset.nodup_toList _)
        (List.disjoint_left.mpr (by
          intro a ha hi; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2
            (List.mem_toFinset.mpr ha)))
      have hsub : ((W ++ I).toFinset.filter (fun i => exponent 4 r i = 2)) ⊆
          Finset.univ.filter (fun i : Fin (4 * r) => exponent 4 r i = 2) :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      have hle := Finset.card_le_card hsub
      rw [count_card r (W ++ I) hn] at hle
      have hrc : (Finset.univ.filter (fun i : Fin (4 * r) => exponent 4 r i = 2)).card = r :=
        residue_card 4 r 2 (by decide) (by decide)
      rw [hrc] at hle
      simpa only [List.countP_append, count] using hle
    change count r W 2 = r - 1 at hc2
    omega
  have hbudget : count r I 2 + count r I 3 + count r I 1 ≤ 2 := by
    have hlen : I.length ≤ 2 := by simpa [I] using fresh
    have hl := (four_sums r I).2
    omega
  have hws : count r W 0 = r ∧ count r W 1 = r - 2 ∧
      count r W 2 = r - 1 ∧ count r W 3 = r - 2 := ⟨hc0, hc1, hc2, hc3⟩
  have hWmass : mass (scaled 4 r) W = 6 := by
    have hs := (four_sums r W).1
    obtain ⟨h0, h1, h2, h3⟩ := hws
    rw [h0, h1, h2, h3] at hs
    omega
  have hWlen : W.length = 4 * r - 5 := by
    have hs := (four_sums r W).2
    omega
  have hWG : G (4 * r) (unit 4 r) W = 3 := by
    have hb := physical_balance (largeWeight (4 * r) (unit 4 r)) W hW.1
    change G (4 * r) (unit 4 r) W + largeUsed (4 * r) (unit 4 r) W = _ at hb
    rw [large_total 4 r (by decide) (by omega), large_used_counts 4 r (by decide) (by omega)] at hb
    change G (4 * r) (unit 4 r) W + (count r W 2 + count r W 3) = 2 * r at hb
    rw [show count r W 2 = r - 1 from hc2, show count r W 3 = r - 2 from hc3] at hb
    omega
  have hWU : U W = 5 := by
    have hb := physical_balance (fun _ : Fin (4 * r) => (1 : ℕ)) W hW.1
    have hb' : U W + W.length = 4 * r := by simpa [U, mass, List.map_const'] using hb
    omega
  have hVG := physical_balance (largeWeight (4 * r) (unit 4 r)) V hV.1
  change G (4 * r) (unit 4 r) V + largeUsed (4 * r) (unit 4 r) V = _ at hVG
  rw [large_total 4 r (by decide) (by omega), large_used_counts 4 r (by decide) (by omega)] at hVG
  have hgbal : G (4 * r) (unit 4 r) V + count r I 2 + count r I 3 =
      3 + count r R 2 + count r R 3 := by
    have h2 := hcount 2; have h3 := hcount 3
    change G (4 * r) (unit 4 r) V + (count r V 2 + count r V 3) = 2 * r at hVG
    omega
  have hVm := (four_sums r V).1
  have hmass : mass (scaled 4 r) V = 6 +
      4 * ((count r I 2 : ℤ) - count r R 2) -
      7 * ((count r I 3 : ℤ) - count r R 3) +
      2 * count r I 1 - count r R 0 - 2 * count r R 1 := by
    have h0 := hcount 0; have h1 := hcount 1
    have h2 := hcount 2; have h3 := hcount 3
    have hw := (four_sums r W).1
    omega
  have hstrip := ((legal_iff 4 r (by decide) (by omega) V).mp hV).2
  have hend : 0 ≤ mass (scaled 4 r) V ∧ mass (scaled 4 r) V ≤ 7 := by
    simpa [height, top, List.take_length, mass] using inStrip_prefix hstrip V.length
  have hsteps (a : Fin (4 * r)) : 0 < scaled 4 r a ∨ scaled 4 r a = -(7 : ℤ) := by
    by_cases h : exponent 4 r a = 3
    · right; simpa [height, top] using (scaled_reset_iff 4 r (by decide) a).mpr h
    · left; exact (scaled_positive_iff 4 r (by decide) a).mpr
        (by have he : exponent 4 r a < 4 := Nat.mod_lt a.val (by decide : 0 < 4); omega)
  have hblock := reset_top_bound (scaled 4 r) 4 7 (by norm_num) (by norm_num) hsteps V
    (by simpa [height, top] using hstrip)
  have htop : (fun a : Fin (4 * r) => decide (scaled 4 r a = 4)) =
      (fun a => decide (exponent 4 r a = 2)) := by
    funext a
    have he : scaled 4 r a = 4 ↔ exponent 4 r a = 2 := by
      simpa [top] using scaled_top_iff 4 r (by decide) a
    simp only [he]
  have hreset : (fun a : Fin (4 * r) => decide (scaled 4 r a = -7)) =
      (fun a => decide (exponent 4 r a = 3)) := by
    funext a
    have he : scaled 4 r a = -7 ↔ exponent 4 r a = 3 := by
      simpa [height, top] using scaled_reset_iff 4 r (by decide) a
    simp only [he]
  rw [htop, hreset] at hblock
  have hblock' : (1 : ℤ) + count r I 2 + count r R 3 ≤
      count r I 3 + count r R 2 + if 4 ≤ mass (scaled 4 r) V then 1 else 0 := by
    have h2 := hcount 2; have h3 := hcount 3
    change (count r V 2 : ℤ) ≤ count r V 3 + _ at hblock
    omega
  have hbal : H (4 * r) (unit 4 r) V + count r R 2 * 3 ^ (4 * unit 4 r) +
      count r R 3 * 3 ^ (7 * unit 4 r) = H (4 * r) (unit 4 r) W +
      count r I 2 * 3 ^ (4 * unit 4 r) + count r I 3 * 3 ^ (7 * unit 4 r) := by
    have he := (hperm.map (energyWeight (4 * r) (unit 4 r))).sum_eq
    change H (4 * r) (unit 4 r) V + H (4 * r) (unit 4 r) R =
      H (4 * r) (unit 4 r) W + H (4 * r) (unit 4 r) I at he
    simpa [four_energy r (by omega), add_assoc] using he
  have hubal : U V + count r I 2 + count r I 3 + count r I 1 =
      5 + count r R 2 + count r R 3 + count r R 0 + count r R 1 := by
    have hb := physical_balance (fun _ : Fin (4 * r) => (1 : ℕ)) V hV.1
    have hc : U V + V.length = 4 * r := by simpa [U, mass, List.map_const'] using hb
    have hi := (four_sums r I).2; have hr' := (four_sums r R).2
    have hl := hperm.length_eq
    simp only [List.length_append] at hl
    omega
  have hstrict : G (4 * r) (unit 4 r) V < 3 ∨
      G (4 * r) (unit 4 r) V = 3 ∧
        (H (4 * r) (unit 4 r) V < H (4 * r) (unit 4 r) W ∨
         H (4 * r) (unit 4 r) V = H (4 * r) (unit 4 r) W ∧ U V < 5) := by
    have hs := Prod.Lex.toLex_lt_toLex.mp strict
    rcases hs with h | ⟨h, h'⟩
    · exact Or.inl (by simpa [hWG] using h)
    · exact Or.inr ⟨by simpa [hWG] using h,
        by simpa [hWU] using Prod.Lex.toLex_lt_toLex.mp h'⟩
  have hAB : 3 ^ (4 * unit 4 r) < 3 ^ (7 * unit 4 r) := by
    have hd := (capacity_bounds 4 r (by decide) (by omega)).1
    exact pow_lt_pow_right₀ (by decide) (by omega)
  obtain ⟨ha, hb, hc⟩ := forced_counts (count r I 2) (count r I 3) (count r I 1)
    (count r R 2) (count r R 3) (count r R 0) (count r R 1)
    (3 ^ (4 * unit 4 r)) (3 ^ (7 * unit 4 r)) (H (4 * r) (unit 4 r) W)
    (G (4 * r) (unit 4 r) V) (H (4 * r) (unit 4 r) V) (U V)
    hAB hIc2 hbudget (mass (scaled 4 r) V) hend hmass hblock' hgbal hbal hubal hstrict
  obtain ⟨e, heI, he⟩ : ∃ e ∈ I, exponent 4 r e = 1 := by
    have hn : count r I 1 ≠ 0 := by omega
    simpa [count] using (List.countP_pos_iff.mp (by omega : 0 < count r I 1))
  obtain ⟨z, hzI, hz⟩ : ∃ z ∈ I, exponent 4 r z = 3 := by
    have hn : count r I 3 ≠ 0 := by omega
    simpa [count] using (List.countP_pos_iff.mp (by omega : 0 < count r I 3))
  have hne : e ≠ z := by intro h; subst z; omega
  refine ⟨e, z, hne, ?_, ?_, ?_⟩
  · have hsub : {e, z} ⊆ V.toFinset \ W.toFinset := by
      apply Finset.pair_subset.mpr
      exact ⟨Finset.mem_toList.mp heI, Finset.mem_toList.mp hzI⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa [hne] using fresh)).symm
  · rw [source_values 4 r (by decide) (by omega)]
    change (unit 4 r : ℤ) * value 4 (exponent 4 r e) = _
    norm_num [he, value]; ring
  · rw [source_values 4 r (by decide) (by omega)]
    change (unit 4 r : ℤ) * value 4 (exponent 4 r z) = _
    norm_num [hz, value, height, top]; ring


private def label (r : ℕ) (j : Fin r) (a : Fin 4) : Fin (4 * r) :=
  ⟨4 * j.val + a.val, by have := j.isLt; have := a.isLt; omega⟩

private theorem label_exp (r : ℕ) (j : Fin r) (a : Fin 4) :
    exponent 4 r (label r j a) = a.val := by
  dsimp [exponent, label]
  omega

private theorem label_value (r : ℕ) (j : Fin r) (a : Fin 4) :
    scaled 4 r (label r j a) = value 4 a.val := by
  change value 4 (exponent 4 r (label r j a)) = _
  rw [label_exp]

private def row (r : ℕ) (j : Fin r) : List (Fin (4 * r)) :=
  [label r j 2, label r j 1, label r j 0, label r j 3]

private def prior (r : ℕ) : List (Fin (4 * r)) :=
  (List.finRange (r - 2)).flatMap (fun j => row r (j.castLE (Nat.sub_le r 2)))

private theorem rows_mass (r : ℕ) (L : List (Fin r)) :
    mass (scaled 4 r) (L.flatMap (row r)) = 0 := by
  induction L with
  | nil => simp [mass]
  | cons j L ih =>
    simp only [List.flatMap_cons, mass, List.map_append, List.sum_append]
    change mass (scaled 4 r) (row r j) + mass (scaled 4 r) (L.flatMap (row r)) = 0
    have hj : mass (scaled 4 r) (row r j) = 0 := by
      norm_num [row, mass, label_value, value, height, top]
    rw [hj, ih, add_zero]

private theorem rows_strip (r : ℕ) (L : List (Fin r)) :
    InStrip (scaled 4 r) 7 0 (L.flatMap (row r)) := by
  induction L with
  | nil => norm_num [InStrip]
  | cons j L ih =>
    have hj : InStrip (scaled 4 r) 7 0 (row r j) := by
      norm_num [row, InStrip, label_value, value, height, top]
    apply inStrip_append hj
    have hz : mass (scaled 4 r) (row r j) = 0 := by
      norm_num [row, mass, label_value, value, height, top]
    change InStrip (scaled 4 r) 7 (0 + mass (scaled 4 r) (row r j)) (L.flatMap (row r))
    rw [hz, add_zero]
    exact ih

private theorem prior_mass (r : ℕ) : mass (scaled 4 r) (prior r) = 0 := by
  simpa [prior, List.flatMap_map, Function.comp_def] using
    rows_mass r ((List.finRange (r - 2)).map (fun j => j.castLE (Nat.sub_le r 2)))

private theorem prior_strip (r : ℕ) : InStrip (scaled 4 r) 7 0 (prior r) := by
  simpa [prior, List.flatMap_map, Function.comp_def] using
    rows_strip r ((List.finRange (r - 2)).map (fun j => j.castLE (Nat.sub_le r 2)))

private theorem prior_bound (r : ℕ) (a : Fin (4 * r)) (ha : a ∈ prior r) :
    a.val < 4 * (r - 2) := by
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp ha
  simp only [row, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;>
    simp only [label, Fin.val_castLE] <;> have := j.isLt <;> omega

private theorem prior_nodup (r : ℕ) : (prior r).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro j _
    simp [row, label, Fin.ext_iff]
  · apply (List.nodup_finRange (r - 2)).pairwise_of_forall_ne
    intro j _ k _ hjk
    apply List.disjoint_left.mpr
    intro a ha hb
    simp only [row, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with hb | hb | hb | hb <;>
      have he := congrArg Fin.val hb <;>
      simp only [label, Fin.val_castLE] at he <;>
      exact hjk (Fin.ext (by omega))

private theorem prior_counts (r a : ℕ) (ha : a < 4) :
    count r (prior r) a = r - 2 := by
  have hc (j : Fin (r - 2)) :
      (row r (j.castLE (Nat.sub_le r 2))).countP
        (fun i => exponent 4 r i = a) = 1 := by
    interval_cases a <;> norm_num [row, List.countP_cons, label_exp]
  simp only [count, prior, List.countP_flatMap, Function.comp_def, hc]
  simp

/-- An unbounded native family realizes the obstructing old inventory. -/
theorem obstructing_inventory_exists (r : ℕ) (hr : 3 ≤ r) :
    ∃ W : List (Fin (4 * r)),
      TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) W ∧
      W.countP (fun i => exponent 4 r i = 0) = r ∧
      W.countP (fun i => exponent 4 r i = 1) = r - 2 ∧
      W.countP (fun i => exponent 4 r i = 2) = r - 1 ∧
      W.countP (fun i => exponent 4 r i = 3) = r - 2 := by
  let j : Fin r := ⟨r - 2, by omega⟩
  let k : Fin r := ⟨r - 1, by omega⟩
  let T := [label r j 2, label r j 0, label r k 0]
  have hT : T.Nodup := by simp [T, label, Fin.ext_iff, j, k]; omega
  have hdis : List.Disjoint (prior r) T := by
    apply List.disjoint_left.mpr
    intro a ha hb
    have hbound := prior_bound r a ha
    simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [label, j, k] at hbound <;> omega
  have hstrip : InStrip (scaled 4 r) (height 4) 0 (prior r ++ T) := by
    apply inStrip_append (by simpa [height, top] using prior_strip r)
    change InStrip (scaled 4 r) (height 4) (0 + mass (scaled 4 r) (prior r)) T
    rw [prior_mass, add_zero]
    norm_num [T, InStrip, label_value, value, height, top]
  refine ⟨prior r ++ T, (legal_iff 4 r (by decide) (by omega) _).mpr
    ⟨(prior_nodup r).append hT hdis, hstrip⟩, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [List.countP_append]
    change count r (prior r) _ + _ = _
    rw [prior_counts r _ (by decide)]
    norm_num [T, List.countP_cons, label_exp] <;> omega


/-- The two-label bound is attained on an unbounded family, and every strict
competitor within that bound must use an existential fresh +2d label together
with an existential fresh -7d label. Arbitrary returns and orders remain in
scope; no particular pair of equal-valued physical outsiders is singled out. -/
theorem forced_mixed_obstruction (r : ℕ) (hr : 3 ≤ r) :
    ∃ W : List (Fin (4 * r)),
      TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) W ∧
      G (4 * r) (unit 4 r) W = 3 ∧
      (∃ V : List (Fin (4 * r)),
        TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) V ∧
        J (4 * r) (unit 4 r) V < J (4 * r) (unit 4 r) W ∧
        (V.toFinset \ W.toFinset).card ≤ 2) ∧
      (∀ V : List (Fin (4 * r)),
        TwoOppositeLargeExchange.Legal (4 * r) (unit 4 r) V →
        J (4 * r) (unit 4 r) V < J (4 * r) (unit 4 r) W →
        (V.toFinset \ W.toFinset).card ≤ 2 →
        ∃ e z : Fin (4 * r), e ≠ z ∧
          V.toFinset \ W.toFinset = {e, z} ∧
          actualSource (4 * r) (unit 4 r) e = 2 * (unit 4 r : ℤ) ∧
          actualSource (4 * r) (unit 4 r) z = -7 * (unit 4 r : ℤ)) := by
  classical
  obtain ⟨W, hW, h0, h1, h2, h3⟩ := obstructing_inventory_exists r hr
  have hGW : G (4 * r) (unit 4 r) W = 3 := by
    have hb := physical_balance (largeWeight (4 * r) (unit 4 r)) W hW.1
    change G (4 * r) (unit 4 r) W + largeUsed (4 * r) (unit 4 r) W = _ at hb
    rw [large_total 4 r (by decide) (by omega),
      large_used_counts 4 r (by decide) (by omega), h2, h3] at hb
    omega
  obtain ⟨V, hVL, hVJ, hVI, _⟩ := MixedDyadicAugmentation.native_two_fresh_augmentation
    4 r (by decide) (by omega) W hW (by omega)
  refine ⟨W, hW, hGW, ⟨V, hVL, hVJ, hVI⟩, ?_⟩
  intro T hT hJ hI
  exact forced_mixed_of_counts r hr W T hW hT h0 h1 h2 h3 hI hJ

end D5.S3.Combinatorics.Circle.ForcedMixedDyadic
