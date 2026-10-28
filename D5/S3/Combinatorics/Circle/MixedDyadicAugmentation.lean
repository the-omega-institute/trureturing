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
      | inr v => exact False.elim (hij (by congr; exact Subsingleton.elim u v))
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
    simpa only [List.mem_append, Finset.mem_toList, List.mem_ofFn] using hperm.mem_iff (a := x)
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
    simpa [D5.S3.Combinatorics.Transportation.DyadicAllocation.Allocation, P, height, top, hlen] using hfull
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
    · simpa only [List.mem_singleton] using hx ▸ hz
  have hcap : 2 ^ j - g ≤ height m := by
    have hpw := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega : j ≤ m - 2)
    have hB : 0 < (2 : ℕ) ^ (m - 2) := by positivity
    dsimp [height, top]; omega
  obtain ⟨V, hVP, hVs⟩ := word_of_allocation (scaled m r) P (exponent m r) Z' (height m)
    (2 ^ j - g) hcap hpos hneg hal
  have hZN : Z.Nodup := (List.nodup_append.mp (hperm.nodup_iff.mp hW.1)).2
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
      intro x hx hi; simp only [List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact haW hx
      · exact hzW hx))
  have hPP : (P.toList ++ Z').Perm (W ++ [a, z]) := by
    apply (List.perm_ext_iff_of_nodup hPN hWI).mpr
    intro x
    have hw := hmem x
    simp only [P, Z', List.mem_append, Finset.mem_toList, Finset.mem_union,
      Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
      List.mem_cons, List.mem_singleton]
    tauto
  have hVI : (V ++ []).Perm (W ++ [a, z]) := by simpa using hVP.trans hPP
  have hgain : 0 < largeUsed (m * r) (unit m r) [a, z] := by
    have hL : Large (m * r) (unit m r) z :=
      (large_iff m r hm hr z).mpr (by change m - 2 ≤ exponent m r z; omega)
    simp [largeUsed, mass, largeWeight, hL]
  obtain ⟨hVN, hJ, hI, hR⟩ := descent_of_perm W V [a, z] [] hW.1 (by simp [hne])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton] at hx
        rcases hx with rfl | rfl; exact haW; exact hzW)
    (by simp) (by simp) hVI (Or.inl hgain)
  exact ⟨V, (legal_iff m r hm hr V).mpr ⟨hVN, hVs⟩, hJ,
    by simpa using hI.symm, by simpa using hR.symm⟩

end D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
