/- GID: D5/S3/Combinatorics/Circle/M5PhysicalInventory
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5PhysicalInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical row occurrences and exact legal prefix extensions. -/
module
import all D5.S3.Combinatorics.Circle.M5AttainedMesh
import all D5.S3.Combinatorics.Circle.TwoLargeOrdering
/-! # M5PhysicalInventory -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth
open Fin.NatCast
open scoped BigOperators

private abbrev Occ (len : Fin 10 → ℕ) := Fin 10 ⊕ (Σ i : Fin 10, Fin (len i))

private def rowMask (len : Fin 10 → ℕ) (i : Fin 10) (S : Finset (Fin (len i))) :
    Finset (Occ len) :=
  S.map ⟨fun j => Sum.inr ⟨i, j⟩, by intro j k h; simpa using h⟩

private theorem rowMask_sum (len : Fin 10 → ℕ) (f : Occ len → ℤ) (i : Fin 10)
    (S : Finset (Fin (len i))) (s : ℤ)
    (h : ∀ j, f (Sum.inr ⟨i, j⟩) = (2 : ℤ) ^ j.val * s) :
    ∑ l ∈ rowMask len i S, f l = (∑ j ∈ S, (2 : ℤ) ^ j.val) * s := by
  rw [rowMask, Finset.sum_map]
  change (∑ j ∈ S, f (Sum.inr ⟨i, j⟩)) = _
  simp_rw [h]
  rw [Finset.sum_mul]

private theorem rowMask_disjoint (len : Fin 10 → ℕ) (i j : Fin 10)
    (S : Finset (Fin (len i))) (T : Finset (Fin (len j))) (hij : i ≠ j) :
    Disjoint (rowMask len i S) (rowMask len j T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro l hl hl'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hl
  obtain ⟨b, hb, hab⟩ := Finset.mem_map.mp hl'
  have he := congrArg (fun o : Occ len => match o with
    | .inl i => i
    | .inr p => p.1) hab
  exact hij he.symm

@[simp] private theorem inl_not_rowMask (len : Fin 10 → ℕ) (i j : Fin 10)
    (S : Finset (Fin (len i))) : Sum.inl j ∉ rowMask len i S := by
  simp [rowMask]

@[simp] private theorem inr_mem_rowMask (len : Fin 10 → ℕ) (i : Fin 10)
    (S : Finset (Fin (len i))) (j : Fin (len i)) :
    Sum.inr ⟨i, j⟩ ∈ rowMask len i S ↔ j ∈ S := by
  rw [rowMask, Finset.mem_map]
  change (∃ a ∈ S, (Sum.inr ⟨i, a⟩ : Occ len) = Sum.inr ⟨i, j⟩) ↔ j ∈ S
  simp

private theorem rowMask_mono (len : Fin 10 → ℕ) (i : Fin 10)
    {S T : Finset (Fin (len i))} (h : S ⊆ T) : rowMask len i S ⊆ rowMask len i T :=
  Finset.map_subset_map.mpr h

private def occurrences (len : Fin 10 → ℕ) : List (Occ len) :=
  (List.finRange 10).flatMap (fun i => Sum.inl i :: List.ofFn (fun j => Sum.inr ⟨i, j⟩))

private theorem mem_occurrences (len : Fin 10 → ℕ) (o : Occ len) : o ∈ occurrences len := by
  rcases o with i | ⟨i, j⟩
  · exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp⟩
  · exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩

private def physical {k t : ℕ} (x : Fin k) :
    Occ (fun i : Fin 10 => sourceLength t x i.val) → Fin k
  | .inl i => sourceParent t x i.val
  | .inr ⟨i, j⟩ => advance (sourceParent t x i.val) (j.val + 1)

private theorem physical_inventory {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    ((occurrences (fun i : Fin 10 => sourceLength t x i.val)).map (physical x)).Perm
      (List.finRange k) := by
  have hp := source_partition h
  have he : (occurrences (fun i : Fin 10 => sourceLength t x i.val)).map (physical x) =
      (List.range 10).flatMap (fun i => sourceParent t x i ::
        rowLabels (sourceParent t x i) (sourceLength t x i)) := by
    simp only [occurrences, List.map_flatMap, List.map_cons, List.map_ofFn, physical,
      rowLabels, Function.comp_apply]
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    rfl
  rw [he]
  exact hp

private theorem physical_injective {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : Function.Injective (physical (t := t) x) := by
  have hnd := (physical_inventory h).nodup_iff.mpr (List.nodup_finRange k)
  exact fun o o' he => List.inj_on_of_nodup_map hnd
    (mem_occurrences _ o) (mem_occurrences _ o') he

private structure Prefix {α : Type*} [DecidableEq α] (s : α → ℤ) (C : ℤ)
    (first : α) (A : Finset α) (h : ℤ) where
  word : List α
  perm : word.Perm A.toList
  legal : InStrip s C 0 word
  height : (word.map s).sum = h
  head : word.head? = some first

private theorem prefix_batch {α : Type*} [DecidableEq α]
    {s : α → ℤ} {C : ℤ} {first : α} {A : Finset α} {h : ℤ}
    (pre : Prefix s C first A h) (S : Finset α) (Q : ℤ)
    (hQ : 0 ≤ Q) (hQC : 2 * Q ≤ C) (hdis : Disjoint A S)
    (hsmall : ∀ i ∈ S, |s i| ≤ Q)
    (hend : 0 ≤ h + ∑ i ∈ S, s i ∧ h + ∑ i ∈ S, s i ≤ C) :
    Nonempty (Prefix s C first (A ∪ S) (h + ∑ i ∈ S, s i)) := by
  have hnd := pre.perm.nodup_iff.mpr A.nodup_toList
  have hh := inStrip_prefix pre.legal pre.word.length
  simp only [List.take_length, zero_add, pre.height] at hh
  have hsumS : (S.toList.map s).sum = ∑ i ∈ S, s i := by
    rw [← List.sum_toFinset _ S.nodup_toList, Finset.toList_toFinset]
  obtain ⟨post, hp, hs⟩ := ThreeRowSource.small_batch s C Q hQ hQC
    S.toList.length S.toList h (le_refl _) S.nodup_toList hh
    (by simpa only [hsumS] using hend)
    (fun i hi => hsmall i (Finset.mem_toList.mp hi))
  have hsumPost : (post.map s).sum = ∑ i ∈ S, s i := (hp.map s).sum_eq.trans hsumS
  have hdisList : List.Disjoint pre.word post := by
    rw [List.disjoint_left]
    intro i hi hj
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_toList.mp (pre.perm.mem_iff.mp hi))
      (Finset.mem_toList.mp (hp.mem_iff.mp hj))
  have hwordnd : (pre.word ++ post).Nodup :=
    hnd.append (hp.nodup_iff.mpr S.nodup_toList) hdisList
  have hmem : (pre.word ++ post).toFinset = A ∪ S := by
    ext i
    simp only [List.mem_toFinset, List.mem_append, pre.perm.mem_iff, hp.mem_iff,
      Finset.mem_toList, Finset.mem_union]
  have hperm : (pre.word ++ post).Perm (A ∪ S).toList := by
    rw [List.perm_ext_iff_of_nodup hwordnd (A ∪ S).nodup_toList]
    intro i
    rw [← List.mem_toFinset, hmem, Finset.mem_toList]
  refine ⟨⟨pre.word ++ post, hperm, ?_, ?_, ?_⟩⟩
  · apply inStrip_append pre.legal
    simpa only [zero_add, pre.height] using hs
  · simp only [List.map_append, List.sum_append, pre.height, hsumPost]
  · have hn : pre.word ≠ [] := by intro he; simpa [he] using pre.head
    simpa only [List.head?_append_of_ne_nil pre.word hn] using pre.head

private theorem prefix_large {α : Type*} [DecidableEq α]
    {s : α → ℤ} {C : ℤ} {first : α} {A : Finset α} {h : ℤ}
    (pre : Prefix s C first A h) (i : α) (hi : i ∉ A)
    (hend : 0 ≤ h + s i ∧ h + s i ≤ C) :
    Nonempty (Prefix s C first (insert i A) (h + s i)) := by
  have hnd := pre.perm.nodup_iff.mpr A.nodup_toList
  have hin : i ∉ pre.word := by
    intro hh
    exact hi (Finset.mem_toList.mp (pre.perm.mem_iff.mp hh))
  have hwordnd : (pre.word ++ [i]).Nodup := by simpa using List.Nodup.concat hin hnd
  have hperm : (pre.word ++ [i]).Perm (insert i A).toList := by
    rw [List.perm_ext_iff_of_nodup hwordnd (insert i A).nodup_toList]
    intro j
    simp only [List.mem_append, List.mem_singleton, Finset.mem_toList, Finset.mem_insert]
    rw [pre.perm.mem_iff, Finset.mem_toList]
    tauto
  have hh := inStrip_prefix pre.legal pre.word.length
  simp only [List.take_length, zero_add, pre.height] at hh
  refine ⟨⟨pre.word ++ [i], hperm, ?_, ?_, ?_⟩⟩
  · apply inStrip_append pre.legal
    simpa only [zero_add, pre.height, InStrip, List.sum_nil, add_zero] using
      (show 0 ≤ h ∧ h ≤ C ∧ 0 ≤ h + s i ∧ h + s i ≤ C from ⟨hh.1, hh.2, hend⟩)
  · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, pre.height]
  · have hn : pre.word ≠ [] := by intro he; simpa [he] using pre.head
    simpa only [List.head?_append_of_ne_nil pre.word hn] using pre.head

private theorem prefix_single {α : Type*} [DecidableEq α] (s : α → ℤ) (C : ℤ)
    (i : α) (hC : 0 ≤ C) (hi : 0 ≤ s i ∧ s i ≤ C) :
    Nonempty (Prefix s C i {i} (s i)) := by
  refine ⟨⟨[i], by simp, ?_, by simp, rfl⟩⟩
  simpa only [InStrip, List.sum_nil, zero_add] using (show 0 ≤ (0 : ℤ) ∧ 0 ≤ C ∧
    0 ≤ s i ∧ s i ≤ C from ⟨le_refl _, hC, hi⟩)

private structure RowData (D : Arithmetic) where
  len : Fin 10 → ℕ
  f : Occ len → ℤ
  base : Fin 10 → ℤ
  values : ∀ (i : Fin 10) (j : Fin (len i)),
    f (Sum.inr ⟨i, j⟩) = (2 : ℤ) ^ j.val * base i
  small : ∀ (i : Fin 10) (j : Fin (len i)), |f (Sum.inr ⟨i, j⟩)| ≤ D.Q - 1
  bound : ∀ i : Fin 10, |f (Sum.inl i)| ≤ D.C
  base0 : base 0 = -D.z
  base1 : base 1 = D.b
  base2 : base 2 = -D.n
  base3 : base 3 = D.b1
  base4 : base 4 = -D.w
  base5 : base 5 = D.v
  base6 : base 6 = -D.u
  base7 : base 7 = D.y
  pow0 : (2 : ℤ) ^ len 0 = D.q
  pow1 : (2 : ℤ) ^ len 1 = D.q
  pow2 : (2 : ℤ) ^ len 2 = D.q
  pow3 : (2 : ℤ) ^ len 3 = D.r
  pow4 : (2 : ℤ) ^ len 4 = D.H / 4
  pow5 : (2 : ℤ) ^ len 5 = D.e
  pow6 : 2 * (2 : ℤ) ^ len 6 = D.F
  large0 : 2 * f (Sum.inl 0) = D.N - D.z
  large1 : f (Sum.inl 1) = -D.q * D.z
  large2 : f (Sum.inl 2) = D.q * D.b
  large3 : f (Sum.inl 3) = -D.q * D.n
  large4 : f (Sum.inl 4) = D.r * D.b1
  large5 : f (Sum.inl 5) = -(D.H / 4) * D.w
  large6 : 2 * f (Sum.inl 6) = D.N - D.u
  large7 : 2 * f (Sum.inl 7) = -D.F * D.u
  large8 : 2 * f (Sum.inl 8) = D.N - D.a0
  last_negative : f (Sum.inl 9) < 0
  next7 : D.a0 = D.N - 2 * (2 : ℤ) ^ len 7 * D.y
  total : ∑ o : Occ len, f o = 0

private def fullRow {D : Arithmetic} (R : RowData D) (i : Fin 10) : Finset (Occ R.len) :=
  rowMask R.len i Finset.univ

private theorem fullRow_sum {D : Arithmetic} (R : RowData D) (i : Fin 10) :
    ∑ o ∈ fullRow R i, R.f o = ((2 : ℤ) ^ R.len i - 1) * R.base i := by
  rw [fullRow, rowMask_sum R.len R.f i Finset.univ (R.base i) (R.values i)]
  rw [← weight, weight_full]

private theorem row_small {D : Arithmetic} (R : RowData D) (i : Fin 10)
    (S : Finset (Fin (R.len i))) :
    ∀ o ∈ rowMask R.len i S, |R.f o| ≤ D.Q - 1 := by
  intro o ho
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ho
  exact R.small i j

private theorem row_sum {D : Arithmetic} (R : RowData D) (i : Fin 10)
    (S : Finset (Fin (R.len i))) :
    ∑ o ∈ rowMask R.len i S, R.f o = weight S * R.base i :=
  rowMask_sum R.len R.f i S (R.base i) (R.values i)

private def bank {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) : Finset (Occ R.len) :=
  rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0 ∪ fullRow R 1 ∪ fullRow R 5

private theorem bank_parts {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) :
    rowMask R.len 2 Sn ⊆ bank R Sn Sw ∧ rowMask R.len 4 Sw ⊆ bank R Sn Sw ∧
      fullRow R 0 ⊆ bank R Sn Sw ∧ fullRow R 1 ⊆ bank R Sn Sw ∧ fullRow R 5 ⊆ bank R Sn Sw := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro o ho <;> simp only [bank, Finset.mem_union] <;> tauto

private theorem two_rows_sum {D : Arithmetic} (R : RowData D) (i j : Fin 10)
    (S : Finset (Fin (R.len i))) (T : Finset (Fin (R.len j))) (hij : i ≠ j) :
    (∑ o ∈ rowMask R.len i S ∪ rowMask R.len j T, R.f o) =
      weight S * R.base i + weight T * R.base j := by
  rw [Finset.sum_union (rowMask_disjoint R.len i j S T hij), row_sum, row_sum]

private theorem three_rows_sum {D : Arithmetic} (R : RowData D) (i j k : Fin 10)
    (S : Finset (Fin (R.len i))) (T : Finset (Fin (R.len j))) (U : Finset (Fin (R.len k)))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ o ∈ rowMask R.len i S ∪ rowMask R.len j T ∪ rowMask R.len k U, R.f o) =
      weight S * R.base i + weight T * R.base j + weight U * R.base k := by
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
    ⟨rowMask_disjoint R.len i k S U hik, rowMask_disjoint R.len j k T U hjk⟩),
    two_rows_sum R i j S T hij, row_sum]

private structure TSelection {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) where
  keep : Finset (Occ R.len)
  available : keep ⊆ bank R Sn Sw
  pay : Finset (Fin (R.len 6))
  gate : (D.u - D.z) / 2 ≤ -(∑ o ∈ keep, R.f o) - weight pay * D.u ∧
    -(∑ o ∈ keep, R.f o) - weight pay * D.u ≤ D.u - (D.z + 1) / 2

private theorem selection_of_coeff {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (M : Finset (Occ R.len)) (hM : M ⊆ bank R Sn Sw) (f : ℤ)
    (hf : 0 ≤ f) (hfu : f < (2 : ℤ) ^ R.len 6)
    (hgate : (D.u - D.z) / 2 ≤ -(∑ o ∈ M, R.f o) - f * D.u ∧
      -(∑ o ∈ M, R.f o) - f * D.u ≤ D.u - (D.z + 1) / 2) :
    Nonempty (TSelection R Sn Sw) := by
  obtain ⟨S, hS⟩ := mask_exists (R.len 6) f hf hfu
  exact ⟨⟨M, hM, S, by simpa only [hS] using hgate⟩⟩

private theorem select_T {D : Arithmetic} (R : RowData D) (A : ℤ)
    (hA : 1 ≤ A) (hAP : A ≤ D.H / 4)
    (hprev : 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1)
    (hnext : D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    Nonempty (TSelection R Sn Sw) := by
  classical
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D
  obtain ⟨hN, hW, hZ, hB, hV⟩ := bank_parts R Sn Sw
  have hmissing : weight Swᶜ = A - 1 := by rw [weight_compl, R.pow4, hSw]; ring
  have hrow0 (S : Finset (Fin (R.len 0))) : rowMask R.len 0 S ⊆ bank R Sn Sw :=
    (rowMask_mono R.len 0 (Finset.subset_univ S)).trans hZ
  have hrow1 (S : Finset (Fin (R.len 1))) : rowMask R.len 1 S ⊆ bank R Sn Sw :=
    (rowMask_mono R.len 1 (Finset.subset_univ S)).trans hB
  have hrow4 (S : Finset (Fin (R.len 4))) (hS : S ⊆ Sw) : rowMask R.len 4 S ⊆ bank R Sn Sw :=
    (rowMask_mono R.len 4 hS).trans hW
  rcases D.branch with ⟨hF, hF4⟩ | hF
  · have hpow6 : (2 : ℤ) ^ R.len 6 = D.H / 4 := by
      have hh := R.pow6
      have hH := D.H_four
      omega
    have halfbounds := half_source_bounds D hF
    obtain ⟨hell0, hW0, hell, hhi, hWeq, hwidth⟩ := gate_limits D
    by_cases he : D.e = 1
    · obtain ⟨hBsource, hKsource, hB2n⟩ := half_one_geometry D hF he
      obtain ⟨hAsmall, hAr, hD0⟩ := half_one_canonical_bounds D hF he A hA hprev hnext
      have hBpos : 0 < D.w - D.b := by omega
      have hAB : A * (D.w - D.b) ≤ (D.u - 1) / 2 := by
        have hm := mul_nonneg (show 0 ≤ D.H / 4 - A by omega) (le_of_lt hBpos)
        have hH4B := congrArg (fun H : ℤ => H * (D.w - D.b)) D.H_four
        have hnU : D.n < D.u := by have hnz := D.nzb.1; have hzu := D.u_above; omega
        nlinarith only [hm, hBsource, hH4B, hnU, hWeq]
      by_cases hspan : (D.u - D.z) / 2 ≤ (D.H / 4 - A) * (D.w - D.b)
      · obtain ⟨J, hJS, hlo, hhi'⟩ := supported_multiple_crossing (R.len 4) Sw
          ((D.u - D.z) / 2) (D.u - (D.z + 1) / 2) ((D.u - 1) / 2) (D.w - D.b) A
          hell0 hBpos hA hwidth (by rw [← weight_nat, hSw]; exact hspan)
          (by rw [← weight_nat, hmissing]) hAB
        have hc0 := weight_nonneg J
        have hcmax : weight J < (2 : ℤ) ^ R.len 1 := by
          have hm := weight_mono hJS
          rw [R.pow1]
          omega
        obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (weight J) hc0 hcmax
        apply selection_of_coeff R Sn Sw (rowMask R.len 4 J ∪ rowMask R.len 1 Bmask)
          (Finset.union_subset (hrow4 J hJS) (hrow1 Bmask)) 0 (le_refl _)
          (by positivity)
        rw [two_rows_sum R 4 1 J Bmask (by decide), R.base4, R.base1, hBM]
        rw [← weight_nat] at hlo hhi'
        constructor <;> nlinarith only [hlo, hhi']
      · have hend := half_one_borrow_endpoint D hF he A hA hAP hprev hnext (lt_of_not_ge hspan)
        let fm := min A (D.H / 4 - 1)
        have hfm : 0 ≤ fm := by dsimp only [fm]; omega
        have hfmcast : ((fm.toNat : ℕ) : ℤ) = fm := Int.toNat_of_nonneg hfm
        have hlo0 : (D.u - D.z) / 2 ≤ D.z - A * D.H * D.Δ := by
          have hu2z := halfbounds.1
          omega
        obtain ⟨f, hfm', hlo, hhi'⟩ := one_step_crossing (D.z - A * D.H * D.Δ)
          ((D.u - D.z) / 2) (D.u - (D.z + 1) / 2) ((D.u - 1) / 2) (D.u - D.b)
          fm.toNat hlo0 hwidth ⟨by omega, by omega⟩ (by simpa only [hfmcast] using hend)
        have hf : (f : ℤ) ≤ fm := by
          have hh : (f : ℤ) ≤ (fm.toNat : ℤ) := by exact_mod_cast hfm'
          omega
        have hfA : (f : ℤ) ≤ A := by dsimp only [fm] at hf; omega
        have hfP : (f : ℤ) ≤ D.H / 4 - 1 := by dsimp only [fm] at hf; omega
        obtain ⟨Zmask, hZM⟩ := mask_exists (R.len 0) 1 (by omega) (by rw [R.pow0]; omega)
        obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (A - (f : ℤ)) (by omega)
          (by rw [R.pow1]; omega)
        apply selection_of_coeff R Sn Sw
          (rowMask R.len 2 Sn ∪ rowMask R.len 0 Zmask ∪ rowMask R.len 1 Bmask)
          (Finset.union_subset (Finset.union_subset hN (hrow0 Zmask)) (hrow1 Bmask))
          (f : ℤ) (by omega) (by rw [hpow6]; omega)
        rw [three_rows_sum R 2 0 1 Sn Zmask Bmask (by decide) (by decide) (by decide),
          hSn, hZM, hBM, R.base2, R.base0, R.base1]
        have hbA := congrArg (fun b : ℤ => A * b) D.b_n
        constructor <;> nlinarith only [hlo, hhi', hbA]
    · have he2 : 2 ≤ D.e := by have hh := D.e_one; omega
      obtain ⟨hA1, c, f, hcP, hfc, hcf, hlo, hhi'⟩ := half_many_T_coefficients D hF he2 A hA hprev
      have hzero : weight Swᶜ = 0 := by omega
      obtain ⟨Wmask, hWMsub, hWM⟩ := supported_mask_exists Sw hzero (c : ℤ) (by omega)
        (by rw [hSw]; omega)
      obtain ⟨Bmask, hBM⟩ := mask_exists (R.len 1) (2 * (c : ℤ) - (f : ℤ)) (by omega)
        (by rw [R.pow1]; omega)
      apply selection_of_coeff R Sn Sw
        (rowMask R.len 2 Sn ∪ rowMask R.len 4 Wmask ∪ rowMask R.len 1 Bmask)
        (Finset.union_subset (Finset.union_subset hN (hrow4 Wmask hWMsub)) (hrow1 Bmask))
        (f : ℤ) (by omega) (by rw [hpow6]; omega)
      rw [three_rows_sum R 2 4 1 Sn Wmask Bmask (by decide) (by decide) (by decide),
        hSn, hWM, hBM, R.base2, R.base4, R.base1, hA1]
      constructor <;> nlinarith only [hlo, hhi']
  · obtain ⟨hu2z, c, hcmax, hlo, hhi⟩ := lower_T_coefficient D hF
    obtain ⟨Zmask, hZM⟩ := mask_exists (R.len 0) (c : ℤ) (by omega)
      (by rw [R.pow0]; omega)
    apply selection_of_coeff R Sn Sw (rowMask R.len 0 Zmask) (hrow0 Zmask) 0 (le_refl _)
      (by positivity)
    rw [row_sum, hZM, R.base0]
    constructor <;> nlinarith only [hlo, hhi]

private def firstParents (len : Fin 10 → ℕ) : Finset (Occ len) :=
  {Sum.inl 2, Sum.inl 1, Sum.inl 0}

private def initialSmall {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) : Finset (Occ R.len) :=
  fullRow R 3 ∪ rowMask R.len 2 Snᶜ ∪ rowMask R.len 4 Swᶜ

private def wjUsed {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) : Finset (Occ R.len) :=
  insert (Sum.inl 5) (insert (Sum.inl 4) (insert (Sum.inl 3)
    (firstParents R.len ∪ initialSmall R Sn Sw)))

private def wjHeight {D : Arithmetic} (R : RowData D) (f : ℤ) : ℤ :=
  f + R.f (Sum.inl 4) + R.f (Sum.inl 5)

private theorem wj_prefix {D : Arithmetic} (R : RowData D) (A f : ℤ)
    (hA : 1 ≤ A) (hAP : A ≤ D.H / 4) (hf : 0 ≤ f) (hfg : f ≤ (D.w - 1) / 2)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    Nonempty (Prefix R.f D.C (Sum.inl 0) (wjUsed R Sn Sw) (wjHeight R f)) ∧
      0 < wjHeight R f ∧ 2 * wjHeight R f ≤ D.v - 1 := by
  classical
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D
  obtain ⟨h2C, hNb1, hbz, hwB1, hNw, hnf0, hnfC, hfPC, hZ0, hZv⟩ := wj_geometry D f hf hfg
  have hH := D.H_eight
  have hHq := D.H_q
  have hq0 : 0 < D.q := by omega
  have hC0 : 0 ≤ D.C := by have hh := D.C_quarter; have hh' := D.Q_positive; omega
  have hp0 : 0 ≤ R.f (Sum.inl 0) ∧ R.f (Sum.inl 0) ≤ D.C := by
    have hm := mul_nonneg (show 0 ≤ D.H - 1 by omega) (le_of_lt hz0)
    have hb := abs_le.mp (R.bound 0)
    constructor
    · nlinarith only [R.large0, D.N_z, hm, hz0, hb0]
    · exact hb.2
  have hfirst : 2 * (R.f (Sum.inl 0) + R.f (Sum.inl 1)) = D.Δ := by
    have hHZ := congrArg (fun H : ℤ => H * D.z) hHq
    nlinarith only [R.large0, R.large1, D.N_z, hbz, hHZ]
  have hfirstbounds : 0 ≤ R.f (Sum.inl 0) + R.f (Sum.inl 1) ∧
      R.f (Sum.inl 0) + R.f (Sum.inl 1) ≤ D.C := by
    have hneg : R.f (Sum.inl 1) < 0 := by rw [R.large1]; nlinarith only [mul_pos hq0 hz0]
    have hd := D.delta_two
    omega
  have hsecondbounds : 0 ≤ R.f (Sum.inl 0) + R.f (Sum.inl 1) + R.f (Sum.inl 2) ∧
      R.f (Sum.inl 0) + R.f (Sum.inl 1) + R.f (Sum.inl 2) ≤ D.C := by
    have hpos : 0 < D.q * D.b := mul_pos hq0 hb0
    have hΔn : D.Δ < D.n := by
      have hm := mul_nonneg (show 0 ≤ D.H - 1 by omega) (show 0 ≤ D.Δ by have hh := D.delta_two; omega)
      nlinarith only [hm, D.delta_n]
    have hHb := congrArg (fun H : ℤ => H * D.b) hHq
    constructor
    · nlinarith only [hfirstbounds.1, R.large2, hpos]
    · nlinarith only [hfirst, R.large2, D.N_b, hHb, h2C, hΔn]
  obtain ⟨pre0⟩ := prefix_single R.f D.C (Sum.inl 0) hC0 hp0
  obtain ⟨pre1⟩ := prefix_large pre0 (Sum.inl 1) (by simp) hfirstbounds
  obtain ⟨pre2⟩ := prefix_large pre1 (Sum.inl 2) (by simp) hsecondbounds
  have hSnc : weight Snᶜ = D.q - 1 - A := by rw [weight_compl, R.pow2, hSn]
  have hSwc : weight Swᶜ = A - 1 := by rw [weight_compl, R.pow4, hSw]; ring
  have hI : (∑ o ∈ initialSmall R Sn Sw, R.f o) =
      (D.r - 1) * D.b1 - (D.q - 1 - A) * D.n - (A - 1) * D.w := by
    change (∑ o ∈ rowMask R.len 3 Finset.univ ∪ rowMask R.len 2 Snᶜ ∪ rowMask R.len 4 Swᶜ,
      R.f o) = _
    rw [three_rows_sum R 3 2 4 Finset.univ Snᶜ Swᶜ (by decide) (by decide) (by decide),
      weight_full, R.pow3, hSnc, hSwc, R.base3, R.base2, R.base4]
    ring
  have hIend : R.f (Sum.inl 0) + R.f (Sum.inl 1) + R.f (Sum.inl 2) +
      (∑ o ∈ initialSmall R Sn Sw, R.f o) = D.q * D.n + f := by
    have hqN := congrArg (fun H : ℤ => H * D.n) hHq
    have hqB := congrArg (fun H : ℤ => H * D.b) hHq
    nlinarith only [hI, hfirst, R.large2, D.N_b, hNb1, D.w_source, heq, hqN, hqB]
  have hdis : Disjoint (firstParents R.len) (initialSmall R Sn Sw) := by
    apply Finset.disjoint_left.mpr
    intro o ho hi
    simp only [firstParents, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl <;> simpa only [initialSmall, fullRow,
      Finset.mem_union, inl_not_rowMask, or_self] using hi
  obtain ⟨preI⟩ := prefix_batch pre2 (initialSmall R Sn Sw) (D.Q - 1)
    (by have hh := D.Q_positive; omega)
    (by have hh := D.C_quarter; omega) hdis
    (by
      intro o ho
      simp only [initialSmall, Finset.mem_union] at ho
      rcases ho with (ho | ho) | ho
      · exact row_small R 3 Finset.univ o ho
      · exact row_small R 2 Snᶜ o ho
      · exact row_small R 4 Swᶜ o ho)
    (by simpa only [hIend] using And.intro hnf0 hnfC)
  have hgamma : R.f (Sum.inl 0) + R.f (Sum.inl 1) + R.f (Sum.inl 2) +
      (∑ o ∈ initialSmall R Sn Sw, R.f o) + R.f (Sum.inl 3) = f := by
    rw [hIend, R.large3]; ring
  have hfC : f ≤ D.C := by have hqn := mul_nonneg (le_of_lt hq0) (le_of_lt hn0); omega
  obtain ⟨preG⟩ := prefix_large preI (Sum.inl 3)
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma] using And.intro hf hfC)
  have hPdouble : 2 * R.f (Sum.inl 4) = D.N - D.w := by
    nlinarith only [R.large4, D.w_source]
  have hPbounds : 0 ≤ f + R.f (Sum.inl 4) ∧ f + R.f (Sum.inl 4) ≤ D.C := by
    have hm := mul_nonneg (show 0 ≤ D.q by omega) (le_of_lt hw0)
    constructor <;> nlinarith only [hPdouble, hfPC, hf, hNw, hm]
  obtain ⟨preP⟩ := prefix_large preG (Sum.inl 4)
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma] using hPbounds)
  have hZeq : 2 * wjHeight R f = 2 * f + D.N - (D.q + 1) * D.w := by
    have hh := congrArg (fun q : ℤ => q * D.w) hq
    dsimp only [wjHeight]
    nlinarith only [hPdouble, R.large5, hh]
  have hZpos : 0 < wjHeight R f := by omega
  have hZbounds : 0 ≤ wjHeight R f ∧ wjHeight R f ≤ D.C := by
    have hJneg : R.f (Sum.inl 5) ≤ 0 := by rw [R.large5]; nlinarith only [mul_nonneg (show 0 ≤ D.H / 4 by omega) (le_of_lt hw0)]
    dsimp only [wjHeight] at *
    omega
  obtain ⟨preJ⟩ := prefix_large preP (Sum.inl 5)
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma, wjHeight] using hZbounds)
  refine ⟨?_, hZpos, by omega⟩
  simpa only [hgamma, wjUsed, wjHeight, firstParents] using (show Nonempty (Prefix R.f D.C (Sum.inl 0) _ _) from ⟨preJ⟩)

@[simp] private theorem inr_not_rowMask_of_ne (len : Fin 10 → ℕ) (i j : Fin 10)
    (S : Finset (Fin (len i))) (a : Fin (len j)) (hij : i ≠ j) :
    Sum.inr ⟨j, a⟩ ∉ rowMask len i S := by
  intro h
  have ha : Sum.inr ⟨j, a⟩ ∈ rowMask len j Finset.univ :=
    (inr_mem_rowMask len j Finset.univ a).mpr (Finset.mem_univ _)
  exact Finset.disjoint_left.mp (rowMask_disjoint len i j S Finset.univ hij) h ha

private theorem bank_wj_disjoint {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) :
    Disjoint (bank R Sn Sw) (wjUsed R Sn Sw) := by
  classical
  simp only [bank, wjUsed, firstParents, initialSmall, fullRow,
    Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_insert_right, Finset.disjoint_singleton_right,
    Finset.mem_union, not_or, inl_not_rowMask, not_false_eq_true, true_and, and_true]
  repeat' apply And.intro
  all_goals first
    | exact (Finset.disjoint_map _).mpr disjoint_compl_right
    | exact (Finset.disjoint_map _).mpr disjoint_compl_left
    | apply rowMask_disjoint; decide


private theorem bank_row6_disjoint {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (S : Finset (Fin (R.len 6))) : Disjoint (bank R Sn Sw) (rowMask R.len 6 S) := by
  simp only [bank, fullRow, Finset.disjoint_union_left]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide

private theorem row6_wj_disjoint {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (S : Finset (Fin (R.len 6))) : Disjoint (rowMask R.len 6 S) (wjUsed R Sn Sw) := by
  classical
  simp only [wjUsed, firstParents, initialSmall, fullRow,
    Finset.disjoint_union_right, Finset.disjoint_insert_right,
    Finset.disjoint_singleton_right, inl_not_rowMask, not_false_eq_true, true_and, and_true]
  repeat' apply And.intro
  all_goals apply rowMask_disjoint <;> decide


private theorem bank_small {D : Arithmetic} (R : RowData D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4))) :
    ∀ o ∈ bank R Sn Sw, |R.f o| ≤ D.Q - 1 := by
  intro o ho
  simp only [bank, Finset.mem_union] at ho
  rcases ho with (((ho | ho) | ho) | ho) | ho
  · exact row_small R 2 Sn o ho
  · exact row_small R 4 Sw o ho
  · exact row_small R 0 Finset.univ o ho
  · exact row_small R 1 Finset.univ o ho
  · exact row_small R 5 Finset.univ o ho

private theorem bank_charge {D : Arithmetic} (R : RowData D) (A f : ℤ)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    2 * (wjHeight R f + ∑ o ∈ bank R Sn Sw, R.f o) = D.z - D.u := by
  classical
  have hdis0 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw) (fullRow R 0) := by
    simp only [fullRow, Finset.disjoint_union_left]
    constructor <;> apply rowMask_disjoint <;> decide
  have hdis1 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0) (fullRow R 1) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
  have hdis5 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0 ∪ fullRow R 1)
      (fullRow R 5) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
  have hsum : (∑ o ∈ bank R Sn Sw, R.f o) =
      -A * D.n - (D.H / 4 - A) * D.w - (D.q - 1) * D.z +
      (D.q - 1) * D.b + (D.e - 1) * D.v := by
    rw [bank, Finset.sum_union hdis5, Finset.sum_union hdis1, Finset.sum_union hdis0,
      two_rows_sum R 2 4 Sn Sw (by decide), fullRow_sum, fullRow_sum, fullRow_sum,
      hSn, hSw, R.pow0, R.pow1, R.pow5, R.base0, R.base1, R.base2, R.base4, R.base5]
    ring
  have hbz : D.b - D.z = D.Δ := by nlinarith only [D.b_n, D.z_n]
  have hδq := congrArg (fun H : ℤ => H * D.Δ) D.H_q
  have hwq := congrArg (fun q : ℤ => q * D.w) (arithmetic_geometry D).2.2.2.2.2.2.2.1
  have hd := congrArg (fun d : ℤ => 2 * (D.q - 1) * d) hbz
  have hp : 2 * R.f (Sum.inl 4) = D.N - D.w := by nlinarith only [R.large4, D.w_source]
  dsimp only [wjHeight]
  nlinarith only [hsum, heq, hp, R.large5, D.u_source, D.v_source, D.z_n, hδq, hwq, hd]


end D5.S3.Combinatorics.Circle.M5FullWordConsumer
