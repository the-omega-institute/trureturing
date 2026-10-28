/- GID: D5/S3/Combinatorics/Circle/MixedDyadicAugmentation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/MixedDyadicAugmentation
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: At most two fresh physical labels strictly augment arbitrary legal dyadic reset words. -/
module
public import D5.S3.Combinatorics.Circle.DyadicResetSource
public import D5.S3.Combinatorics.Circle.DyadicResetBlocks
public import D5.S3.Combinatorics.Circle.DyadicResetAllocation
public import D5.S3.Combinatorics.Circle.DyadicResetWords
public import D5.S3.Combinatorics.Circle.DyadicResetDenominations

/-! Mixed insertion uses physical permutation balances and the original lexicographic objective. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open DyadicResetSource DyadicResetBlocks DyadicResetAllocation DyadicResetWords DyadicResetDenominations
open scoped BigOperators

private theorem descent_of_perm {k t : ℕ} (W V I R : List (Fin k))
    (hW : W.Nodup) (hI : I.Nodup) (hIW : ∀ a ∈ I, a ∉ W)
    (hR : ∀ a ∈ R, a ∈ W) (hRS : ∀ a ∈ R, ¬ Large k t a)
    (hperm : (V ++ R).Perm (W ++ I))
    (hgain : 0 < largeUsed k t I ∨
      (R.length < I.length ∧ ∀ a ∈ I, ¬ Large k t a)) :
    V.Nodup ∧ J k t V < J k t W ∧
      I.toFinset = V.toFinset \ W.toFinset ∧
      R.toFinset = W.toFinset \ V.toFinset := by
  classical
  have hWI : (W ++ I).Nodup := hW.append hI (List.disjoint_left.mpr (by
    intro a ha hi; exact hIW a hi ha))
  obtain ⟨hV, hRn, hVR⟩ := List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)
  have hvR : ∀ a ∈ V, a ∉ R := fun a ha => List.disjoint_left.mp hVR ha
  have hm (a : Fin k) : (a ∈ V ∨ a ∈ R) ↔ (a ∈ W ∨ a ∈ I) := by
    simpa only [List.mem_append] using hperm.mem_iff (a := a)
  have hsets : I.toFinset = V.toFinset \ W.toFinset ∧
      R.toFinset = W.toFinset \ V.toFinset := by
    constructor <;> ext a
    all_goals
      have h1 := hm a
      have h2 := hvR a
      have h3 := hIW a
      have h4 := hR a
      simp only [List.mem_toFinset, Finset.mem_sdiff]
      tauto
  have hmass {β : Type} [AddCommMonoid β] (w : Fin k → β) :
      mass w V + mass w R = mass w W + mass w I := by
    simpa [mass] using (hperm.map w).sum_eq
  have hRzero : largeUsed k t R = 0 := by
    simp only [largeUsed, mass]
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    simp [largeWeight, hRS a ha]
  have hwg := physical_balance (largeWeight k t) W hW
  have hvg := physical_balance (largeWeight k t) V hV
  have hlg := hmass (largeWeight k t)
  change G k t W + largeUsed k t W = _ at hwg
  change G k t V + largeUsed k t V = _ at hvg
  change largeUsed k t V + largeUsed k t R = largeUsed k t W + largeUsed k t I at hlg
  have hG : G k t V + largeUsed k t I = G k t W := by omega
  have hwc : U W + W.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) W hW
  have hvc : U V + V.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) V hV
  have hlen := hperm.length_eq
  simp only [List.length_append] at hlen
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases hgain with hg | ⟨hu, hIS⟩
    · exact Or.inl (by omega)
    · have hIZ : largeUsed k t I = 0 := by
        simp only [largeUsed, mass]
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        simp [largeWeight, hIS a ha]
      have hezero (L : List (Fin k)) (hL : ∀ a ∈ L, ¬ Large k t a) : H k t L = 0 := by
        simp only [H, mass]
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        simp [energyWeight, hL a ha]
      have he := hmass (energyWeight k t)
      change H k t V + H k t R = H k t W + H k t I at he
      rw [hezero R hRS, hezero I hIS] at he
      refine Or.inr ⟨by omega, ?_⟩
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inr ⟨by omega, by omega⟩
  exact ⟨hV, hJ, hsets⟩


/-- A retained list of distinct top labels supplies one physical head per
complete small-coin bin. The tail receives no head. -/
private theorem heads_allocation {α : Type*} [DecidableEq α]
    (S : Finset α) (e : α → ℕ) (b h p : ℕ) (A : Fin p → α)
    (hA : Function.Injective A) (hAS : ∀ i, A i ∉ S)
    (hAe : ∀ i, e (A i) = b)
    (hal : D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation S e
      (fun i : Fin p ⊕ Unit => Sum.elim (fun _ => 2 ^ b - 1) (fun _ => h) i)) :
    D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation
      (S ∪ Finset.univ.image A) e
      (fun i : Fin p ⊕ Unit => Sum.elim (fun _ => 2 * 2 ^ b - 1) (fun _ => h) i) := by
  classical
  obtain ⟨K, hKS, hKD, hKC, hKb⟩ := hal
  let K' : Fin p ⊕ Unit → Finset α :=
    Sum.elim (fun i => insert (A i) (K (Sum.inl i))) (fun u => K (Sum.inr u))
  have hnot (i : Fin p) (j : Fin p ⊕ Unit) : A i ∉ K j :=
    fun h => hAS i (hKS j h)
  refine ⟨K', ?_, ?_, ?_, ?_⟩
  · intro i x hx
    cases i with
    | inl i =>
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      · exact Finset.mem_union_left _ (hKS _ hx)
    | inr u => exact Finset.mem_union_left _ (hKS _ hx)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rcases Finset.mem_insert.mp hx with rfl | hx <;>
          rcases Finset.mem_insert.mp hy with hy | hy
        · exact hij (congrArg Sum.inl (hA hy))
        · exact hnot i _ hy
        · exact hnot j _ (hy ▸ hx)
        · exact Finset.disjoint_left.mp (hKD _ _ hij) hx hy
      | inr u =>
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hnot i _ hy
        · exact Finset.disjoint_left.mp (hKD _ _ hij) hx hy
    | inr u =>
      cases j with
      | inl j =>
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hnot j _ hx
        · exact Finset.disjoint_left.mp (hKD _ _ hij) hx hy
      | inr v => exact False.elim (hij (congrArg Sum.inr (Subsingleton.elim u v)))
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := hKC x hx
      refine ⟨i, ?_⟩
      cases i with
      | inl i => exact Finset.mem_insert_of_mem hi
      | inr u => exact hi
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨Sum.inl i, Finset.mem_insert_self _ _⟩
  · intro i
    cases i with
    | inl i =>
      change (∑ x ∈ insert (A i) (K (Sum.inl i)), 2 ^ e x) = _
      rw [Finset.sum_insert (hnot i _), hAe, hKb]
      have hp : 0 < (2 : ℕ) ^ b := by positivity
      simp only [Sum.elim_inl]
      omega
    | inr u => exact hKb (Sum.inr u)


/-- The coupled allocation is realized with the original physical top and reset
labels. Its hypotheses are the arithmetic residue budgets used by the all-word
reduction; no intermediate append is required to be legal. -/
set_option maxHeartbeats 800000 in
private theorem coupled_exchange (m r p j g : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) (hW : Legal (m * r) (unit m r) W)
    (S : Finset (Fin (m * r))) (A : Fin p → Fin (m * r))
    (Z : List (Fin (m * r))) (a z : Fin (m * r))
    (hA : Function.Injective A) (hp : 1 ≤ p) (hpr : p + 1 ≤ r)
    (hAZ : Z.length + 1 = p)
    (hperm : W.Perm (S.toList ++ List.ofFn A ++ Z))
    (he : ∀ x ∈ S, exponent m r x < m - 2)
    (hAe : ∀ i, exponent m r (A i) = m - 2)
    (hZe : ∀ x ∈ Z, exponent m r x = m - 1)
    (haW : a ∉ W) (hzW : z ∉ W)
    (haj : exponent m r a = j) (hj : j < m - 2)
    (hz : exponent m r z = m - 1)
    (hg : 0 < g) (hgs : g < 2 ^ j)
    (hmass : (∑ x ∈ S, 2 ^ exponent m r x) + g = p * (2 ^ (m - 2) - 1))
    (owned : ∀ q ≤ j, (∑ x ∈ S.filter (fun x => exponent m r x < q),
      2 ^ exponent m r x) = r * (2 ^ q - 1))
    (oldBins : ∀ q, j < q → q ≤ m - 2 →
      p * (2 ^ q - 1) - g ≤
        ∑ x ∈ S.filter (fun x => exponent m r x < q), 2 ^ exponent m r x) :
    ∃ V : List (Fin (m * r)), Legal (m * r) (unit m r) V ∧
      J (m * r) (unit m r) V < J (m * r) (unit m r) W ∧
      V.toFinset \ W.toFinset = {a, z} ∧ W.toFinset \ V.toFinset = ∅ := by
  classical
  have hmem (x : Fin (m * r)) : x ∈ W ↔ x ∈ S ∨ (∃ i, A i = x) ∨ x ∈ Z := by
    simpa only [List.mem_append, Finset.mem_toList, List.mem_ofFn, or_assoc] using hperm.mem_iff (a := x)
  have haS : a ∉ S := fun h => haW ((hmem a).mpr (Or.inl h))
  have hne : a ≠ z := by intro h; subst z; omega
  have hAS (i : Fin p) : A i ∉ insert a S := by
    intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · have := hAe i; rw [hi, haj] at this; omega
    · have := he (A i) hi; have := hAe i; omega
  have hsmall := coupled_allocation S (exponent m r) a (m - 2) j p r g
    haS haj hj hp hpr hg hgs he hmass owned oldBins
  have hfull := heads_allocation (insert a S) (exponent m r) (m - 2) (2 ^ j - g) p
    A hA hAS hAe hsmall
  let P := insert a S ∪ Finset.univ.image A
  let Z' := Z ++ [z]
  have hlen : Z'.length = p := by simp only [Z', List.length_append, List.length_singleton]; exact hAZ
  have hal : D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation P (exponent m r)
      (fun i : Fin Z'.length ⊕ Unit => Sum.elim (fun _ => height m) (fun _ => 2 ^ j - g) i) := by
    exact hlen.symm ▸ hfull
  have hpos (x : Fin (m * r)) (hx : x ∈ P) :
      scaled m r x = (2 : ℤ) ^ exponent m r x := by
    have hlt : exponent m r x < m - 1 := by
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · have := he x hx; omega
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [hAe]; omega
    change (if exponent m r x = m - 1 then -(height m : ℤ) else (2 : ℤ) ^ exponent m r x) = _
    exact if_neg (by omega)
  have hneg (x : Fin (m * r)) (hx : x ∈ Z') : scaled m r x = -(height m : ℤ) := by
    apply (scaled_reset_iff m r hm x).mpr
    rcases List.mem_append.mp hx with hx | hx
    · exact hZe x hx
    · have hx' := List.mem_singleton.mp hx
      simpa only [hx'] using hz
  have hcap : 2 ^ j - g ≤ height m := by
    have hpw := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega : j ≤ m - 2)
    have hB : 0 < (2 : ℕ) ^ (m - 2) := by positivity
    dsimp [height, top]; omega
  obtain ⟨V, hVP, hVs⟩ := word_of_allocation (scaled m r) P (exponent m r) Z' (height m)
    (2 ^ j - g) hcap hpos hneg hal
  have hZN : Z.Nodup := (List.nodup_append'.mp (hperm.nodup_iff.mp hW.1)).2.1
  have hzZ : z ∉ Z := fun h => hzW ((hmem z).mpr (Or.inr (Or.inr h)))
  have hZ'N : Z'.Nodup := hZN.append (by simp) (List.disjoint_left.mpr (by
    intro x hx hi; have h := List.mem_singleton.mp hi; subst x; exact hzZ hx))
  have hPN : (P.toList ++ Z').Nodup := by
    apply (Finset.nodup_toList _).append hZ'N
    apply List.disjoint_left.mpr
    intro x hx hz'
    have hp' := hpos x (Finset.mem_toList.mp hx)
    have hn' := hneg x hz'
    have hpow : 0 < (2 : ℤ) ^ exponent m r x := by positivity
    have hM : (0 : ℤ) ≤ height m := by positivity
    omega
  have hWI : (W ++ [a, z]).Nodup := hW.1.append (by simp [hne])
    (List.disjoint_left.mpr (by
      intro x hx hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact haW hx
      · exact hzW hx))
  have hPP : (P.toList ++ Z').Perm (W ++ [a, z]) := by
    apply (List.perm_ext_iff_of_nodup hPN hWI).mpr
    intro x
    have hw := hmem x
    simp only [P, Z', List.mem_append, Finset.mem_toList, Finset.mem_union,
      Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hVI : (V ++ []).Perm (W ++ [a, z]) := by simpa using hVP.trans hPP
  have hgain : 0 < largeUsed (m * r) (unit m r) [a, z] := by
    have hL : Large (m * r) (unit m r) z :=
      (large_iff m r hm hr z).mpr (by change m - 2 ≤ exponent m r z; omega)
    simp [largeUsed, mass, largeWeight, hL]
  obtain ⟨hVN, hJ, hI, hR⟩ := descent_of_perm W V [a, z] [] hW.1 (by simp [hne])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl; exact haW; exact hzW)
    (by simp) (by simp) hVI (Or.inl hgain)
  exact ⟨V, (legal_iff m r hm hr V).mpr ⟨hVN, hVs⟩, hJ,
    by simpa using hI.symm, by simpa using hR.symm⟩


private theorem partition_counts (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) (hW : W.Nodup)
    (S : Finset (Fin (m * r))) (Z : List (Fin (m * r)))
    (hperm : W.Perm (S.toList ++ Z))
    (he : ∀ x ∈ S, exponent m r x ≤ m - 2)
    (hz : ∀ x ∈ Z, exponent m r x = m - 1) :
    (S.filter (fun x => exponent m r x = m - 2)).card ≤ r ∧
    Z.length ≤ r ∧
    G (m * r) (unit m r) W +
      (S.filter (fun x => exponent m r x = m - 2)).card + Z.length = 2 * r := by
  classical
  have hZN := (List.nodup_append'.mp (hperm.nodup_iff.mp hW)).2.1
  have htopsub : S.filter (fun x => exponent m r x = m - 2) ⊆
      Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 2) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hZsub : Z.toFinset ⊆
      Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 1) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hz x (List.mem_toFinset.mp hx)⟩
  have hcTop : (Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 2)).card = r :=
    residue_card m r (m - 2) (by omega) (by omega)
  have hcReset : (Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 1)).card = r :=
    residue_card m r (m - 1) (by omega) (by omega)
  have hpt := Finset.card_le_card htopsub
  rw [hcTop] at hpt
  have hn := Finset.card_le_card hZsub
  rw [hcReset, List.toFinset_card_of_nodup hZN] at hn
  refine ⟨hpt, hn, ?_⟩
  have hSsum : mass (largeWeight (m * r) (unit m r)) S.toList =
      (S.filter (fun x => exponent m r x = m - 2)).card := by
    unfold mass
    rw [← List.sum_toFinset _ (Finset.nodup_toList S)]
    simp only [Finset.toList_toFinset, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    have hle := he x hx
    unfold largeWeight
    simp only [large_iff m r hm hr]
    change (if m - 2 ≤ exponent m r x then 1 else 0) = _
    split_ifs <;> omega
  have hZsum : mass (largeWeight (m * r) (unit m r)) Z = Z.length := by
    have hweights : ∀ x ∈ Z, largeWeight (m * r) (unit m r) x = 1 := by
      intro x hx
      have hl : Large (m * r) (unit m r) x :=
        (large_iff m r hm hr x).mpr (by change m - 2 ≤ exponent m r x; rw [hz x hx]; omega)
      simp [largeWeight, hl]
    unfold mass
    rw [List.map_congr_left hweights]
    simp
  have hs : mass (largeWeight (m * r) (unit m r)) W =
      mass (largeWeight (m * r) (unit m r)) S.toList +
      mass (largeWeight (m * r) (unit m r)) Z := by
    simpa [mass] using (hperm.map (largeWeight (m * r) (unit m r))).sum_eq
  have hb := physical_balance (largeWeight (m * r) (unit m r)) W hW
  rw [large_total m r hm hr] at hb
  change G (m * r) (unit m r) W + mass (largeWeight (m * r) (unit m r)) W = _ at hb
  change mass (largeWeight (m * r) (unit m r)) W =
    mass (largeWeight (m * r) (unit m r)) S.toList +
      mass (largeWeight (m * r) (unit m r)) Z at hs
  rw [hSsum, hZsum] at hs
  omega

private theorem fresh_top (m r : ℕ) (hm : 3 ≤ m)
    (W : List (Fin (m * r))) (S : Finset (Fin (m * r)))
    (Z : List (Fin (m * r))) (hperm : W.Perm (S.toList ++ Z))
    (hz : ∀ x ∈ Z, exponent m r x = m - 1)
    (hc : (S.filter (fun x => exponent m r x = m - 2)).card < r) :
    ∃ a : Fin (m * r), a ∉ W ∧ exponent m r a = m - 2 := by
  classical
  have hrc := residue_card m r (m - 2) (by omega) (by omega)
  obtain ⟨a, ha, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (S.filter (fun x => exponent m r x = m - 2)).card <
      (Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 2)).card by
        simpa only [exponent, hrc] using hc)
  have he := (Finset.mem_filter.mp ha).2
  refine ⟨a, ?_, he⟩
  intro haW
  have hmem := hperm.mem_iff.mp haW
  rcases List.mem_append.mp hmem with hS | hZ
  · exact hn (Finset.mem_filter.mpr ⟨Finset.mem_toList.mp hS, he⟩)
  · have := hz a hZ; omega


private theorem fresh_reset (m r : ℕ) (hm : 3 ≤ m)
    (W : List (Fin (m * r))) (S : Finset (Fin (m * r)))
    (Z : List (Fin (m * r))) (hZN : Z.Nodup) (hperm : W.Perm (S.toList ++ Z))
    (he : ∀ x ∈ S, exponent m r x ≤ m - 2)
    (hc : Z.length < r) :
    ∃ a : Fin (m * r), a ∉ W ∧ exponent m r a = m - 1 := by
  classical
  have hrc := residue_card m r (m - 1) (by omega) (by omega)
  obtain ⟨a, ha, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show Z.toFinset.card <
      (Finset.univ.filter (fun x : Fin (m * r) => exponent m r x = m - 1)).card by
        simpa only [exponent, hrc, List.toFinset_card_of_nodup hZN] using hc)
  have he' := (Finset.mem_filter.mp ha).2
  refine ⟨a, ?_, he'⟩
  intro haW
  have hmem := hperm.mem_iff.mp haW
  rcases List.mem_append.mp hmem with hS | hZ
  · have := he a (Finset.mem_toList.mp hS); omega
  · exact hn (List.mem_toFinset.mpr hZ)


private theorem append_exchange (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) (hW : Legal (m * r) (unit m r) W)
    (a : Fin (m * r)) (ha : a ∉ W)
    (hfit : 0 ≤ mass (scaled m r) W + scaled m r a ∧
      mass (scaled m r) W + scaled m r a ≤ height m) :
    ∃ V, Legal (m * r) (unit m r) V ∧ J (m * r) (unit m r) V < J (m * r) (unit m r) W ∧
      (V.toFinset \ W.toFinset).card ≤ 2 ∧
      (∀ x ∈ W.toFinset \ V.toFinset, ¬ Large (m * r) (unit m r) x) := by
  classical
  have hs := ((legal_iff m r hm hr W).mp hW).2
  have hend := inStrip_prefix hs W.length
  simp only [List.take_length, zero_add] at hend
  have hsingle : InStrip (scaled m r) (height m) (mass (scaled m r) W) [a] := by
    simpa [InStrip] using (show 0 ≤ mass (scaled m r) W ∧
      mass (scaled m r) W ≤ height m ∧
      0 ≤ mass (scaled m r) W + scaled m r a ∧
      mass (scaled m r) W + scaled m r a ≤ height m from
      ⟨hend.1, hend.2, hfit⟩)
  have hVstrip : InStrip (scaled m r) (height m) 0 (W ++ [a]) :=
    inStrip_append hs (by simpa using hsingle)
  have hperm : ((W ++ [a]) ++ []).Perm (W ++ [a]) := by simp
  have hgain : 0 < largeUsed (m * r) (unit m r) [a] ∨
      ([].length < [a].length ∧ ∀ x ∈ [a], ¬ Large (m * r) (unit m r) x) := by
    by_cases hL : Large (m * r) (unit m r) a
    · left; simp [largeUsed, mass, largeWeight, hL]
    · right; simp [hL]
  obtain ⟨hVN, hJ, hI, hR⟩ := descent_of_perm W (W ++ [a]) [a] [] hW.1 (by simp)
    (by simpa) (by simp) (by simp) hperm hgain
  refine ⟨W ++ [a], (legal_iff m r hm hr _).mpr ⟨hVN, hVstrip⟩, hJ, ?_, ?_⟩
  · rw [← hI]; simp
  · rw [← hR]; simp

private theorem replace_exchange (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) (hW : Legal (m * r) (unit m r) W)
    (S : Finset (Fin (m * r))) (Z : List (Fin (m * r))) (h : ℕ) (hcap : h ≤ height m)
    (hperm : W.Perm (S.toList ++ Z))
    (he : ∀ x ∈ S, exponent m r x ≤ m - 2)
    (hz : ∀ x ∈ Z, exponent m r x = m - 1)
    (K : Fin Z.length ⊕ Unit → Finset (Fin (m * r)))
    (hKS : ∀ i, K i ⊆ S) (hKD : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hKC : ∀ a ∈ S, ∃ i, a ∈ K i)
    (hKb : ∀ i, ∑ a ∈ K i, 2 ^ exponent m r a =
      Sum.elim (fun _ : Fin Z.length => height m) (fun _ : Unit => h) i)
    (i : Fin Z.length ⊕ Unit) (hmissing : ∀ x ∈ K i, exponent m r x ≠ m - 2)
    (hbig : 2 ^ (m - 2) ≤ ∑ x ∈ K i, 2 ^ exponent m r x)
    (a : Fin (m * r)) (ha : a ∉ W) (hae : exponent m r a = m - 2) :
    ∃ V, Legal (m * r) (unit m r) V ∧ J (m * r) (unit m r) V < J (m * r) (unit m r) W ∧
      (V.toFinset \ W.toFinset).card ≤ 2 ∧
      (∀ x ∈ W.toFinset \ V.toFinset, ¬ Large (m * r) (unit m r) x) := by
  classical
  have hmem (x : Fin (m * r)) : x ∈ W ↔ x ∈ S ∨ x ∈ Z := by
    simpa only [List.mem_append, Finset.mem_toList] using hperm.mem_iff (a := x)
  have haS : a ∉ S := fun h => ha ((hmem a).mpr (Or.inl h))
  obtain ⟨R, hR, hRm⟩ := select_power (K i) (exponent m r) (m - 2)
    (fun x hx => he x (hKS i hx)) hbig
  have hal := replace_bin S (exponent m r) _ K hKS hKD hKC hKb i a R haS hR
    (by simpa [hae] using hRm)
  let S' := insert a (S \ R)
  have hpower (x : Fin (m * r)) (hx : x ∈ S') :
      scaled m r x = (2 : ℤ) ^ exponent m r x := by
    have hle : exponent m r x ≤ m - 2 := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact he x (Finset.mem_sdiff.mp hx).1
    change (if exponent m r x = m - 1 then -(height m : ℤ) else (2 : ℤ) ^ exponent m r x) = _
    exact if_neg (by omega)
  have hreset (x : Fin (m * r)) (hx : x ∈ Z) : scaled m r x = -(height m : ℤ) :=
    (scaled_reset_iff m r hm x).mpr (hz x hx)
  obtain ⟨V, hVP, hVs⟩ := word_of_allocation (scaled m r) S' (exponent m r) Z (height m) h
    hcap hpower hreset hal
  have hRS : R ⊆ S := hR.trans (hKS i)
  have hp : ((V ++ R.toList)).Perm (W ++ [a]) := by
    calc
      V ++ R.toList ~ (S'.toList ++ Z) ++ R.toList := hVP.append_right _
      _ ~ (S'.toList ++ R.toList) ++ Z := by
        simpa only [List.append_assoc] using
          (List.Perm.refl S'.toList).append (List.perm_append_comm : (Z ++ R.toList).Perm (R.toList ++ Z))
      _ ~ (S.toList ++ [a]) ++ Z := (replacement_perm S R a hRS haS).append_right Z
      _ ~ (S.toList ++ Z) ++ [a] := by
        simpa only [List.append_assoc] using
          (List.Perm.refl S.toList).append (List.perm_append_comm : ([a] ++ Z).Perm (Z ++ [a]))
      _ ~ W ++ [a] := hperm.symm.append_right [a]
  have hret : ∀ x ∈ R.toList, ¬ Large (m * r) (unit m r) x := by
    intro x hx
    have hxi := hR (Finset.mem_toList.mp hx)
    have hle := he x (hKS i hxi)
    have hne := hmissing x hxi
    rw [large_iff m r hm hr]
    change ¬ m - 2 ≤ exponent m r x
    omega
  have hL : Large (m * r) (unit m r) a :=
    (large_iff m r hm hr a).mpr (by change m - 2 ≤ exponent m r a; omega)
  obtain ⟨hVN, hJ, hI, hR'⟩ := descent_of_perm W V [a] R.toList hW.1 (by simp)
    (by simpa) (fun x hx => (hmem x).mpr (Or.inl (hRS (Finset.mem_toList.mp hx))))
    hret hp (Or.inl (by simp [largeUsed, mass, largeWeight, hL]))
  refine ⟨V, (legal_iff m r hm hr V).mpr ⟨hVN, hVs⟩, hJ, ?_, ?_⟩
  · rw [← hI]; simp
  · rw [← hR']; simpa only [List.mem_toFinset] using hret


/-- Arbitrary actual legal words in every one-bit repeated source admit a
strict original-J augmentation with at most two originally fresh labels. All
returned labels are SMALL. The source hypothesis remains a genuine restriction. -/
set_option maxHeartbeats 1600000 in
theorem native_two_fresh_augmentation (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) (hW : Legal (m * r) (unit m r) W)
    (hG : 0 < G (m * r) (unit m r) W) :
    ∃ V, Legal (m * r) (unit m r) V ∧ J (m * r) (unit m r) V < J (m * r) (unit m r) W ∧
      (V.toFinset \ W.toFinset).card ≤ 2 ∧
      (∀ x ∈ W.toFinset \ V.toFinset, ¬ Large (m * r) (unit m r) x) := by
  classical
  let b := m - 2
  let B := 2 ^ b
  let M := height m
  have hB : 0 < B := by dsimp [B]; positivity
  have hMB : M = 2 * B - 1 := rfl
  have hBM : B ≤ M := by omega
  have hM2 : M < 2 * B := by omega
  have hsteps (a : Fin (m * r)) : 0 < scaled m r a ∨ scaled m r a = -(M : ℤ) := by
    by_cases h : exponent m r a = m - 1
    · right; exact (scaled_reset_iff m r hm a).mpr h
    · left; apply (scaled_positive_iff m r hm a).mpr
      have he : exponent m r a < m := Nat.mod_lt _ (by omega)
      omega
  have hpowers (a : Fin (m * r)) (h : 0 < scaled m r a) :
      scaled m r a = (2 : ℤ) ^ exponent m r a := by
    have he := (scaled_positive_iff m r hm a).mp h
    change (if exponent m r a = m - 1 then -(height m : ℤ)
      else (2 : ℤ) ^ exponent m r a) = _
    exact if_neg (by omega)
  obtain ⟨S, Z, h, hcap, hperm, hpos, hneg, hend, hal⟩ :=
    allocation_of_strip (scaled m r) (exponent m r) M W hsteps hpowers hW.1
      ((legal_iff m r hm hr W).mp hW).2
  have he (a : Fin (m * r)) (ha : a ∈ S) : exponent m r a ≤ m - 2 := by
    have := (scaled_positive_iff m r hm a).mp (hpos a ha); omega
  have hz (a : Fin (m * r)) (ha : a ∈ Z) : exponent m r a = m - 1 :=
    (scaled_reset_iff m r hm a).mp (hneg a ha)
  let T := S.filter (fun x => exponent m r x = b)
  let p := T.card
  have hZN := (List.nodup_append'.mp (hperm.nodup_iff.mp hW.1)).2.1
  obtain ⟨hpr, hnr, hbal⟩ := partition_counts m r hm hr W hW.1 S Z hperm he hz
  change p ≤ r at hpr
  change G (m * r) (unit m r) W + p + Z.length = 2 * r at hbal
  obtain ⟨K, hKS, hKD, hKC, hKb⟩ := hal
  have hKcap (i : Fin Z.length ⊕ Unit) :
      Sum.elim (fun _ : Fin Z.length => M) (fun _ : Unit => h) i < 2 * 2 ^ b := by
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega
  obtain ⟨htotal, hcounts⟩ := top_occupancy S (exponent m r) b _ K hKS hKD hKC hKb hKcap
  change p = ∑ i, ((K i).filter (fun a => exponent m r a = b)).card at htotal
  have missing (i : Fin Z.length ⊕ Unit)
      (hi : ((K i).filter (fun a => exponent m r a = b)).card = 0) : p ≤ Z.length := by
    rw [htotal]
    exact missing_top_bound Z.length _ hcounts i hi
  by_cases hlow : h < B
  · have hzero : ((K (Sum.inr ())).filter (fun a => exponent m r a = b)).card = 0 := by
      by_contra hn
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < ((K (Sum.inr ())).filter
        (fun a => exponent m r a = b)).card)
      obtain ⟨haK, hae⟩ := Finset.mem_filter.mp ha
      have hle := Finset.single_le_sum (fun x _ => Nat.zero_le ((2 : ℕ) ^ exponent m r x)) haK
      rw [hae, hKb] at hle
      change B ≤ h at hle
      omega
    have hpN := missing (Sum.inr ()) hzero
    obtain ⟨a, ha, hae⟩ := fresh_top m r hm W S Z hperm hz (by change p < r; omega)
    apply append_exchange m r hm hr W hW a ha
    have hval : scaled m r a = (B : ℤ) := by
      change value m (exponent m r a) = _
      rw [hae]
      simp [value, B, b, show m - 2 ≠ m - 1 by omega]
    rw [hend, hval]
    exact ⟨by positivity, by exact_mod_cast (show h + B ≤ M by omega)⟩
  by_cases hmissing : ∃ i : Fin Z.length ⊕ Unit,
      ((K i).filter (fun a => exponent m r a = b)).card = 0
  · obtain ⟨i, hi⟩ := hmissing
    have hpN := missing i hi
    obtain ⟨a, ha, hae⟩ := fresh_top m r hm W S Z hperm hz (by change p < r; omega)
    apply replace_exchange m r hm hr W hW S Z h hcap hperm he hz K hKS hKD hKC hKb i
    · intro x hx hxe
      have hm' : x ∈ (K i).filter (fun a => exponent m r a = b) :=
        Finset.mem_filter.mpr ⟨hx, hxe⟩
      have hempty := Finset.card_eq_zero.mp hi
      simpa only [hempty, Finset.notMem_empty] using hm'
    · rw [hKb]
      cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega
    · exact a
    · exact ha
    · exact hae
  have hpn : p = Z.length + 1 := by
    have hone : ∀ i : Fin Z.length ⊕ Unit,
        ((K i).filter (fun a => exponent m r a = b)).card = 1 := by
      intro i
      have hn : ((K i).filter (fun a => exponent m r a = b)).card ≠ 0 :=
        fun h => hmissing ⟨i, h⟩
      have hl := hcounts i
      omega
    rw [htotal]
    simp [hone, Fintype.sum_sum_type]
  have hfreshReset : ∃ z : Fin (m * r), z ∉ W ∧ exponent m r z = m - 1 :=
    fresh_reset m r hm W S Z hZN hperm he (by omega)
  by_cases hfull : h = M
  · obtain ⟨z, hzW, hze⟩ := hfreshReset
    apply append_exchange m r hm hr W hW z hzW
    have hzv := (scaled_reset_iff m r hm z).mpr hze
    rw [hend, hfull, hzv]
    constructor <;> omega
  let g := M - h
  have hg : 0 < g := by dsimp [g]; omega
  have hgap : h + g = M := by dsimp [g]; omega
  let SM := S.filter (fun x => exponent m r x < b)
  have hSMsub : SM ⊆ low m r b := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
  have htot : (∑ x ∈ S, 2 ^ exponent m r x) = Z.length * M + h := by
    have h' := allocation_total S (exponent m r)
      (fun i : Fin Z.length ⊕ Unit => Sum.elim (fun _ => M) (fun _ => h) i)
      ⟨K, hKS, hKD, hKC, hKb⟩
    simpa [Fintype.sum_sum_type] using h'
  have hTmass : (∑ x ∈ T, 2 ^ exponent m r x) = p * B := by
    calc
      _ = ∑ _x ∈ T, B := Finset.sum_congr rfl (by
        intro x hx; rw [(Finset.mem_filter.mp hx).2])
      _ = _ := by simp [p]
  have hcom : S.filter (fun x => ¬ exponent m r x < b) = T := by
    ext x
    simp only [T, Finset.mem_filter]
    have hle : x ∈ S → exponent m r x ≤ b := fun hx => he x hx
    omega
  have hsplit : (∑ x ∈ SM, 2 ^ exponent m r x) + p * B = Z.length * M + h := by
    have hs := Finset.sum_filter_add_sum_filter_not S (fun x => exponent m r x < b)
      (fun x => (2 : ℕ) ^ exponent m r x)
    rw [hcom, hTmass] at hs
    exact hs.trans htot
  have hmass : (∑ x ∈ SM, 2 ^ exponent m r x) + g = p * (B - 1) := by
    rw [hpn] at hsplit ⊢
    nlinarith
  have hfullmass : (∑ x ∈ low m r b, 2 ^ exponent m r x) = r * (B - 1) :=
    low_mass m r b (by omega) (by dsimp [b]; omega)
  let F := low m r b \ SM
  have hF : F.Nonempty := by
    by_contra hn
    have hnone : low m r b ⊆ SM := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hn)
    have heq : SM = low m r b := Finset.Subset.antisymm hSMsub hnone
    rw [heq, hfullmass] at hmass
    have hmul := Nat.mul_le_mul_right (B - 1) hpr
    omega
  obtain ⟨a, haF, hmin⟩ := F.exists_min_image (exponent m r) hF
  have haL := (Finset.mem_sdiff.mp haF).1
  have haSM := (Finset.mem_sdiff.mp haF).2
  have haj : exponent m r a < b := (Finset.mem_filter.mp haL).2
  have haW : a ∉ W := by
    intro haw
    rcases List.mem_append.mp (hperm.mem_iff.mp haw) with has | haz
    · exact haSM (Finset.mem_filter.mpr ⟨Finset.mem_toList.mp has, haj⟩)
    · have := hz a haz; omega
  have hav : scaled m r a = (2 : ℤ) ^ exponent m r a := by
    change (if exponent m r a = m - 1 then -(height m : ℤ) else (2 : ℤ) ^ exponent m r a) = _
    exact if_neg (by dsimp [b] at haj; omega)
  by_cases hfits : 2 ^ exponent m r a ≤ g
  · apply append_exchange m r hm hr W hW a haW
    rw [hend, hav]
    exact ⟨by positivity, by exact_mod_cast (show h + 2 ^ exponent m r a ≤ M by omega)⟩
  have hgs : g < 2 ^ exponent m r a := by omega
  have hpr' : p + 1 ≤ r := by
    have hsub : insert a SM ⊆ low m r b := Finset.insert_subset haL hSMsub
    have hle := Finset.sum_le_sum_of_subset (f := fun x => (2 : ℕ) ^ exponent m r x) hsub
    rw [Finset.sum_insert haSM, hfullmass] at hle
    by_contra hn
    have hpe : p = r := by omega
    rw [hpe] at hmass
    omega
  have howned : ∀ q ≤ exponent m r a,
      (∑ x ∈ SM.filter (fun x => exponent m r x < q), 2 ^ exponent m r x) =
        r * (2 ^ q - 1) := by
    intro q hq
    have heq : SM.filter (fun x => exponent m r x < q) = low m r q := by
      ext x
      simp only [Finset.mem_filter, low, Finset.mem_univ, true_and]
      constructor
      · exact And.right
      · intro hx
        refine ⟨?_, hx⟩
        by_contra hn
        have hxF : x ∈ F := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, by omega⟩, hn⟩
        have := hmin x hxF
        omega
    rw [heq]
    exact low_mass m r q (by omega) (by omega)
  have hgap' : h + g = 2 ^ (b + 1) - 1 := by
    rw [hgap, hMB]
    simp [B, pow_succ, Nat.mul_comm]
  have hOld := old_bins_residues S (exponent m r) b (exponent m r a) Z.length h g hgap' hgs
    (show D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation S (exponent m r)
      (fun i : Fin Z.length ⊕ Unit => Sum.elim (fun _ => 2 ^ (b + 1) - 1) (fun _ => h) i) from
      by simpa only [← hgap', hgap] using
        (show D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation S (exponent m r)
          (fun i : Fin Z.length ⊕ Unit => Sum.elim (fun _ => M) (fun _ => h) i) from
          ⟨K, hKS, hKD, hKC, hKb⟩))
  have hparts : S.toList.Perm (SM.toList ++ T.toList) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList S) ?_).mpr
    · intro x
      have hx : x ∈ S → exponent m r x ≤ b := fun hx => he x hx
      simp only [List.mem_append, Finset.mem_toList, SM, T, Finset.mem_filter]
      omega
    · apply (Finset.nodup_toList SM).append (Finset.nodup_toList T)
      apply List.disjoint_left.mpr
      intro x hx hy
      have h1 := (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hy)).2
      omega
  obtain ⟨z, hzW, hze⟩ := hfreshReset
  have hA : Function.Injective T.toList.get := (Finset.nodup_toList T).injective_get
  have hAe (i : Fin T.toList.length) : exponent m r (T.toList.get i) = m - 2 :=
    (Finset.mem_filter.mp (Finset.mem_toList.mp (List.get_mem T.toList i))).2
  have hperm' : W.Perm (SM.toList ++ List.ofFn T.toList.get ++ Z) := by
    simpa only [List.ofFn_get] using hperm.trans (hparts.append_right Z)
  obtain ⟨V, hVL, hVJ, hVI, hVR⟩ := coupled_exchange m r T.toList.length (exponent m r a) g hm hr
    W hW SM T.toList.get Z a z hA (by simpa [p] using (show 1 ≤ p by omega))
    (by simpa [p] using hpr') (by simpa [p] using hpn.symm) hperm'
    (fun x hx => (Finset.mem_filter.mp hx).2) hAe hz haW hzW rfl haj hze hg hgs
    (by simpa [p, B, b] using hmass) howned
    (by intro q hjq hqb; simpa only [← hpn, SM] using hOld q hjq hqb)
  refine ⟨V, hVL, hVJ, ?_, ?_⟩
  · rw [hVI]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  · rw [hVR]; simp

end D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
