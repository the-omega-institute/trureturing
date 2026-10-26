/- GID: D5/S3/Combinatorics/Circle/M5RetainedTail
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5RetainedTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual T depletion, retained tail, individual gates and terminal completion. -/
module
import all D5.S3.Combinatorics.Circle.M5PhysicalInventory
/-! # M5RetainedTail -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth SourcePrefixInventory
open Fin.NatCast
open scoped BigOperators

private def retainedTail {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw) : Finset (Occ R.len) :=
  K.keep ∪ rowMask R.len 6 K.payᶜ ∪ fullRow R.toRowData 7

private theorem bank_row7_disjoint {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) :
    Disjoint (bank R.toRowData Sn Sw) (fullRow R.toRowData 7) := by
  simp only [bank, fullRow, Finset.disjoint_union_left]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide

private theorem row7_wj_disjoint {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) :
    Disjoint (fullRow R.toRowData 7) (wjUsed R.toRowData Sn Sw) := by
  classical
  simp only [wjUsed, firstParents, initialSmall, fullRow,
    Finset.disjoint_union_right, Finset.disjoint_insert_right,
    Finset.disjoint_singleton_right, inl_not_rowMask, not_false_eq_true, true_and, and_true]
  repeat' apply And.intro
  all_goals apply rowMask_disjoint <;> decide

private theorem tail_disjoint {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw) : Disjoint (tUsed R.toRowData K) (retainedTail R K) := by
  classical
  apply Finset.disjoint_left.mpr
  intro o ht hs
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_union.mp hs with hs | hs
    · have hb := K.available hs
      simp only [tUsed, tSmall, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at ht
      rcases ht with rfl | hw | ⟨_, hn⟩ | hr
      · simpa [bank, fullRow] using hb
      · exact Finset.disjoint_left.mp (bank_wj_disjoint R.toRowData Sn Sw) hb hw
      · exact hn hs
      · exact Finset.disjoint_left.mp (bank_row6_disjoint R.toRowData Sn Sw K.pay) hb hr
    · simp only [tUsed, tSmall, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at ht
      rcases ht with rfl | hw | ⟨hb, _⟩ | hr
      · exact inl_not_rowMask R.len 6 6 K.payᶜ hs
      · exact Finset.disjoint_left.mp (row6_wj_disjoint R.toRowData Sn Sw K.payᶜ) hs hw
      · exact Finset.disjoint_left.mp (bank_row6_disjoint R.toRowData Sn Sw K.payᶜ) hb hs
      · have hd : Disjoint (rowMask R.len 6 K.pay) (rowMask R.len 6 K.payᶜ) :=
          (Finset.disjoint_map _).mpr disjoint_compl_right
        exact Finset.disjoint_left.mp hd hr hs
  · simp only [tUsed, tSmall, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff] at ht
    rcases ht with rfl | hw | ⟨hb, _⟩ | hr
    · exact inl_not_rowMask R.len 7 6 Finset.univ hs
    · exact Finset.disjoint_left.mp (row7_wj_disjoint R Sn Sw) hs hw
    · exact Finset.disjoint_left.mp (bank_row7_disjoint R Sn Sw) hb hs
    · exact Finset.disjoint_left.mp (rowMask_disjoint R.len 6 7 K.pay Finset.univ (by decide)) hr hs

private theorem retained_sum {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw) :
    ∑ o ∈ retainedTail R K, R.f o = (∑ o ∈ K.keep, R.f o) -
      ((2 : ℤ) ^ R.len 6 - 1 - weight K.pay) * D.u +
      ((2 : ℤ) ^ R.len 7 - 1) * D.y := by
  have hd6 := (bank_row6_disjoint R.toRowData Sn Sw K.payᶜ).mono_left K.available
  change Disjoint K.keep (rowMask R.len 6 K.payᶜ) at hd6
  have hd7 : Disjoint (K.keep ∪ rowMask R.len 6 K.payᶜ) (fullRow R.toRowData 7) :=
    Finset.disjoint_union_left.mpr ⟨(bank_row7_disjoint R Sn Sw).mono_left K.available,
      rowMask_disjoint R.len 6 7 K.payᶜ Finset.univ (by decide)⟩
  rw [retainedTail, Finset.sum_union hd7, Finset.sum_union hd6,
    row_sum, fullRow_sum, weight_compl, (show R.base 6 = -D.u from R.base6), R.base7]
  ring

private def uvUsed {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw) : Finset (Occ R.len) :=
  insert (Sum.inl 8) (insert (Sum.inl 7) (tUsed R.toRowData K ∪ retainedTail R K))

private theorem uv_extension {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw)
    (pre : Prefix R.f D.C (Sum.inl 0) (tUsed R.toRowData K) (tHeight R.toRowData K)) :
    Nonempty (Prefix R.f D.C (Sum.inl 0) (uvUsed R K)
      ((D.z - D.a0) / 2 + R.f (Sum.inl 8))) := by
  classical
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D.toPrefixArithmetic
  obtain ⟨hell0, hW0, hell, hhi, hW, hwidth⟩ := gate_limits D.toPrefixArithmetic
  have h2C : 2 * D.C = D.N - 1 := by have hN := D.N_quarter; have hC := D.C_quarter; omega
  have hhalf : 2 * ((D.z - D.a0) / 2) = D.z - D.a0 := by
    have hz := D.odd_z; have ha := D.odd_a0; omega
  have hend : tHeight R.toRowData K + ∑ o ∈ retainedTail R K, R.f o =
      -R.f (Sum.inl 7) + (D.z - D.a0) / 2 := by
    rw [retained_sum]
    dsimp only [tHeight]
    have hpu := congrArg (fun v : ℤ => v * D.u) (show 2 * (2 : ℤ) ^ R.len 6 = D.F from R.pow6)
    nlinarith only [R.next7, hpu, R.large6, R.large7, D.y_source, hell, hhalf]
  have hpostU : tHeight R.toRowData K + (∑ o ∈ retainedTail R K, R.f o) +
      R.f (Sum.inl 7) = (D.z - D.a0) / 2 := by omega
  have hUneg : R.f (Sum.inl 7) < 0 := by
    nlinarith only [R.large7, mul_pos (show 0 < D.F by have hh := D.F_two; omega) hu0]
  have hbefore : 0 ≤ -R.f (Sum.inl 7) + (D.z - D.a0) / 2 ∧
      -R.f (Sum.inl 7) + (D.z - D.a0) / 2 ≤ D.C := by
    constructor
    · have hh := D.a0_bounds.2; omega
    · nlinarith only [R.large7, D.y_source, D.y_minimum, D.nzb.2,
        D.a0_bounds.1, D.a_positive, hhalf, h2C]
  have hsmall : ∀ o ∈ retainedTail R K, |R.f o| ≤ D.Q - 1 := by
    intro o ho
    rcases Finset.mem_union.mp ho with ho | ho
    · rcases Finset.mem_union.mp ho with ho | ho
      · exact bank_small R.toRowData Sn Sw o (K.available ho)
      · exact row_small R.toRowData 6 K.payᶜ o ho
    · exact row_small R.toRowData 7 Finset.univ o ho
  obtain ⟨preS⟩ := prefix_batch pre (retainedTail R K) (D.Q - 1)
    (by have hh := D.Q_positive; omega) (by have hh := D.C_quarter; omega)
    (tail_disjoint R K) hsmall (by simpa only [hend] using hbefore)
  have hUg : 0 ≤ (D.z - D.a0) / 2 ∧ (D.z - D.a0) / 2 ≤ D.C := by
    have ha := D.a0_bounds; have hz := D.u_above; have hu := D.u_bound
    constructor <;> nlinarith only [hhalf, ha.1, ha.2, hz, hu, D.a_positive]
  have hkeep (i : Fin 10) : Sum.inl i ∉ K.keep := by
    intro hi; have hb := K.available hi; simpa (disch := decide) [bank, fullRow] using hb
  obtain ⟨preU⟩ := prefix_large preS (Sum.inl 7)
    (by simp (disch := decide) [tUsed, tSmall, retainedTail, wjUsed, firstParents,
      initialSmall, fullRow, bank, hkeep])
    (by simpa only [hpostU] using hUg)
  have hVpos : 0 ≤ R.f (Sum.inl 8) := by
    nlinarith only [R.large8, D.a0_bounds.2, D.u_above, D.u_bound, h2C, hz0]
  have hVg : 0 ≤ (D.z - D.a0) / 2 + R.f (Sum.inl 8) ∧
      (D.z - D.a0) / 2 + R.f (Sum.inl 8) ≤ D.C := by
    constructor
    · omega
    · nlinarith only [hhalf, R.large8, h2C, hzmax, D.a0_bounds.1]
  obtain ⟨preV⟩ := prefix_large preU (Sum.inl 8)
    (by simp (disch := decide) [tUsed, tSmall, retainedTail, wjUsed, firstParents,
      initialSmall, fullRow, bank, hkeep])
    (by simpa only [hpostU] using hVg)
  simpa only [uvUsed, hpostU] using
    (show Nonempty (Prefix R.f D.C (Sum.inl 0) _ _) from ⟨preV⟩)

private def terminal {D : Arithmetic} (R : RowData D) : Finset (Occ R.len) :=
  {Sum.inl 9} ∪ fullRow R.toRowData 8 ∪ fullRow R.toRowData 9

private theorem terminal_complement {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw) : (uvUsed R K)ᶜ = terminal R := by
  classical
  have hkeep (i : Fin 10) : Sum.inl i ∉ K.keep := by
    intro hi; have hb := K.available hi; simpa (disch := decide) [bank, fullRow] using hb
  ext o
  rcases o with i | ⟨i, j⟩
  · fin_cases i <;> simp (disch := decide) [uvUsed, tUsed, tSmall, retainedTail, wjUsed,
      firstParents, initialSmall, bank, fullRow, terminal, hkeep]
  · have hkb := K.available (x := Sum.inr ⟨i, j⟩)
    fin_cases i <;> by_cases hk : Sum.inr ⟨_, j⟩ ∈ K.keep <;>
      simp (disch := decide) [uvUsed, tUsed, tSmall, retainedTail, wjUsed,
        firstParents, initialSmall, bank, fullRow, terminal, hk] at * <;> tauto

private theorem complete_occurrences {D : Arithmetic} (R : RowData D)
    {Sn : Finset (Fin (R.len 2))} {Sw : Finset (Fin (R.len 4))}
    (K : TSelection R.toRowData Sn Sw)
    (pre : Prefix R.f D.C (Sum.inl 0) (uvUsed R K)
      ((D.z - D.a0) / 2 + R.f (Sum.inl 8))) :
    Nonempty (Prefix R.f D.C (Sum.inl 0) Finset.univ 0) := by
  classical
  let e := Fintype.equivFin (Occ R.len)
  let rem := (terminal R).toList.map e
  let s := fun j => R.f (e.symm j)
  let H := (D.z - D.a0) / 2 + R.f (Sum.inl 8)
  have hmem (j : Fin (Fintype.card (Occ R.len))) : j ∈ rem ↔ e.symm j ∈ terminal R := by
    constructor
    · intro hj
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hj
      have he' := congrArg e.symm he
      simp only [Equiv.symm_apply_apply] at he'
      rw [← he']
      exact Finset.mem_toList.mp ho
    · intro hj
      exact List.mem_map.mpr ⟨e.symm j, Finset.mem_toList.mpr hj, e.apply_symm_apply j⟩
  have hnd : rem.Nodup := (terminal R).nodup_toList.map e.injective
  have hhs : 0 ≤ H ∧ H ≤ D.C := by
    have hh := inStrip_prefix pre.legal pre.word.length
    simpa only [List.take_length, zero_add, pre.height] using hh
  have hsumRem : (rem.map s).sum = ∑ o ∈ terminal R, R.f o := by
    simp only [rem, s, List.map_map, Function.comp_def, Equiv.symm_apply_apply]
    rw [← List.sum_toFinset _ (terminal R).nodup_toList, Finset.toList_toFinset]
  have hsumPre : (∑ o ∈ uvUsed R K, R.f o) = H := by
    rw [← Finset.sum_map_toList, ← (pre.perm.map R.f).sum_eq]
    exact pre.height
  have htotal : H + (rem.map s).sum = 0 := by
    have hd : Disjoint (uvUsed R K) (uvUsed R K)ᶜ := disjoint_compl_right
    have hh := Finset.sum_union (f := R.f) hd
    rw [Finset.union_compl, terminal_complement R K] at hh
    rw [hsumRem]
    linarith only [hh, R.total, hsumPre]
  have hb : ∀ j ∈ rem, |s j| ≤ D.C := by
    intro j hj
    have hm := (hmem j).mp hj
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · have heq := Finset.mem_singleton.mp hm
        simp only [s, heq]
        exact R.bound 9
      · exact (row_small R.toRowData 8 Finset.univ _ hm).trans (by have hh := D.C_quarter; have hq := D.Q_positive; omega)
    · exact (row_small R.toRowData 9 Finset.univ _ hm).trans (by have hh := D.C_quarter; have hq := D.Q_positive; omega)
  have hs : ∀ j ∈ rem, 2 * s j ≤ D.C := by
    intro j hj
    have hm := (hmem j).mp hj
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · have heq := Finset.mem_singleton.mp hm
        have hn := R.last_negative
        dsimp only [s]
        rw [heq]
        have hq := D.Q_positive; have hc := D.C_quarter
        omega
      · have hh := abs_le.mp (row_small R.toRowData 8 Finset.univ _ hm)
        have hc := D.C_quarter
        dsimp only [s]; omega
    · have hh := abs_le.mp (row_small R.toRowData 9 Finset.univ _ hm)
      have hc := D.C_quarter
      dsimp only [s]; omega
  have hn : ∀ j ∈ rem, ∀ l ∈ rem,
      D.C < -2 * s j → D.C < -2 * s l → j = l := by
    have hlarge : ∀ j ∈ rem, D.C < -2 * s j → e.symm j = Sum.inl 9 := by
      intro j hj hjl
      have hm := (hmem j).mp hj
      rcases Finset.mem_union.mp hm with hm | hm
      · rcases Finset.mem_union.mp hm with hm | hm
        · exact Finset.mem_singleton.mp hm
        · have hh := abs_le.mp (row_small R.toRowData 8 Finset.univ _ hm)
          have hc := D.C_quarter
          dsimp only [s] at hjl
          omega
      · have hh := abs_le.mp (row_small R.toRowData 9 Finset.univ _ hm)
        have hc := D.C_quarter
        dsimp only [s] at hjl
        omega
    intro j hj l hl hjl hll
    exact e.symm.injective ((hlarge j hj hjl).trans (hlarge l hl hll).symm)
  obtain ⟨post, hp, hlegal⟩ := TwoLargeOrdering.complete_small_positives s D.C
    rem.length rem H (le_refl _) hnd hhs htotal hb hs hn
  let tail := post.map e.symm
  have hpt : tail.Perm (terminal R).toList := by
    have hid : (e.symm : _ → _) ∘ e = id := by
      funext o
      exact e.symm_apply_apply o
    simpa only [tail, rem, List.map_map, hid, List.map_id] using hp.map e.symm
  have htlegal : InStrip R.f D.C H tail := (inStrip_map e.symm R.f D.C H post).mpr hlegal
  have htSum : (tail.map R.f).sum = ∑ o ∈ terminal R, R.f o := by
    rw [(hpt.map R.f).sum_eq, ← List.sum_toFinset _ (terminal R).nodup_toList,
      Finset.toList_toFinset]
  have hdis : List.Disjoint pre.word tail := by
    rw [List.disjoint_left]
    intro o ho ht
    have hu := Finset.mem_toList.mp (pre.perm.mem_iff.mp ho)
    have hr := Finset.mem_toList.mp (hpt.mem_iff.mp ht)
    rw [← terminal_complement R K] at hr
    exact (Finset.mem_compl.mp hr) hu
  have hndfull := (pre.perm.nodup_iff.mpr (uvUsed R K).nodup_toList).append
    (hpt.nodup_iff.mpr (terminal R).nodup_toList) hdis
  have hpfull : (pre.word ++ tail).Perm (Finset.univ : Finset (Occ R.len)).toList := by
    rw [List.perm_ext_iff_of_nodup hndfull Finset.univ.nodup_toList]
    intro o
    simp only [List.mem_append, pre.perm.mem_iff, hpt.mem_iff, Finset.mem_toList,
      ← terminal_complement R K, Finset.mem_compl, Finset.mem_univ, iff_true]
    exact Classical.em _
  refine ⟨⟨pre.word ++ tail, hpfull, ?_, ?_, ?_⟩⟩
  · apply inStrip_append pre.legal
    simpa only [zero_add, pre.height] using htlegal
  · rw [List.map_append, List.sum_append, pre.height, htSum]
    rw [hsumRem] at htotal
    exact htotal
  · have hn : pre.word ≠ [] := by intro he; simpa (disch := decide) [he] using pre.head
    simpa only [List.head?_append_of_ne_nil pre.word hn] using pre.head

end D5.S3.Combinatorics.Circle.M5FullWordConsumer
