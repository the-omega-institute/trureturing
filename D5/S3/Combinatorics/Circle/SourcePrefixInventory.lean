/- GID: D5/S3/Combinatorics/Circle/SourcePrefixInventory
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SourcePrefixInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Shared physical seven-row prefix and exact T depletion. -/
module
public import D5.S3.Combinatorics.Circle.M5AttainedMesh
public import D5.S3.Combinatorics.Circle.M5SourceArithmetic
public import D5.S3.Combinatorics.Circle.SourceWidth
import all D5.S3.Combinatorics.Circle.M5AttainedMesh
import all D5.S3.Combinatorics.Circle.TwoLargeOrdering
/-! # Shared seven-row prefix and exact T depletion -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.SourcePrefixInventory
open SourceWidth M5FullWordConsumer
open scoped BigOperators
variable {ι : Type} [DecidableEq ι]

abbrev naturalRows : Fin 7 ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
abbrev fivePairRows : Fin 7 ↪ Fin 10 := ⟨Fin.castLE (by decide), Fin.castLE_injective _⟩

abbrev Occ (len : ι → ℕ) := ι ⊕ (Σ i : ι, Fin (len i))

def rowMask (len : ι → ℕ) (i : ι) (S : Finset (Fin (len i))) :
    Finset (Occ len) :=
  S.map ⟨fun j => Sum.inr ⟨i, j⟩, by intro j k h; simpa using h⟩

theorem rowMask_sum (len : ι → ℕ) (f : Occ len → ℤ) (i : ι)
    (S : Finset (Fin (len i))) (s : ℤ)
    (h : ∀ j, f (Sum.inr ⟨i, j⟩) = (2 : ℤ) ^ j.val * s) :
    ∑ l ∈ rowMask len i S, f l = (∑ j ∈ S, (2 : ℤ) ^ j.val) * s := by
  rw [rowMask, Finset.sum_map]
  change (∑ j ∈ S, f (Sum.inr ⟨i, j⟩)) = _
  simp_rw [h]
  rw [Finset.sum_mul]

theorem rowMask_disjoint (len : ι → ℕ) (i j : ι)
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

@[simp] theorem inl_not_rowMask (len : ι → ℕ) (i j : ι)
    (S : Finset (Fin (len i))) : Sum.inl j ∉ rowMask len i S := by
  simp [rowMask]

@[simp] theorem inr_mem_rowMask (len : ι → ℕ) (i : ι)
    (S : Finset (Fin (len i))) (j : Fin (len i)) :
    Sum.inr ⟨i, j⟩ ∈ rowMask len i S ↔ j ∈ S := by
  rw [rowMask, Finset.mem_map]
  change (∃ a ∈ S, (Sum.inr ⟨i, a⟩ : Occ len) = Sum.inr ⟨i, j⟩) ↔ j ∈ S
  simp

theorem rowMask_mono (len : ι → ℕ) (i : ι)
    {S T : Finset (Fin (len i))} (h : S ⊆ T) : rowMask len i S ⊆ rowMask len i T :=
  Finset.map_subset_map.mpr h

structure Prefix {α : Type*} [DecidableEq α] (s : α → ℤ) (C : ℤ)
    (first : α) (A : Finset α) (h : ℤ) where
  word : List α
  perm : word.Perm A.toList
  legal : InStrip s C 0 word
  height : (word.map s).sum = h
  head : word.head? = some first

theorem prefix_batch {α : Type*} [DecidableEq α]
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

theorem prefix_large {α : Type*} [DecidableEq α]
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

theorem prefix_single {α : Type*} [DecidableEq α] (s : α → ℤ) (C : ℤ)
    (i : α) (hC : 0 ≤ C) (hi : 0 ≤ s i ∧ s i ≤ C) :
    Nonempty (Prefix s C i {i} (s i)) := by
  refine ⟨⟨[i], by simp, ?_, by simp, rfl⟩⟩
  simpa only [InStrip, List.sum_nil, zero_add] using (show 0 ≤ (0 : ℤ) ∧ 0 ≤ C ∧
    0 ≤ s i ∧ s i ≤ C from ⟨le_refl _, hC, hi⟩)

theorem inStrip_map {α β : Type*} (g : α → β) (s : β → ℤ)
    (C h : ℤ) (word : List α) :
    InStrip s C h (word.map g) ↔ InStrip (fun a => s (g a)) C h word := by
  induction word generalizing h with
  | nil => rfl
  | cons a word ih => simpa only [List.map_cons, InStrip] using
      (and_congr_right (fun _ => and_congr_right (fun _ => ih (h + s (g a)))))

structure RowData (row : Fin 7 ↪ ι) (D : PrefixArithmetic) where
  len : ι → ℕ
  f : Occ len → ℤ
  base : ι → ℤ
  values : ∀ (i : ι) (j : Fin (len i)),
    f (Sum.inr ⟨i, j⟩) = (2 : ℤ) ^ j.val * base i
  small : ∀ (i : ι) (j : Fin (len i)), |f (Sum.inr ⟨i, j⟩)| ≤ D.Q - 1
  bound : ∀ i : ι, |f (Sum.inl i)| ≤ D.C
  base0 : base (row 0) = -D.z
  base1 : base (row 1) = D.b
  base2 : base (row 2) = -D.n
  base3 : base (row 3) = D.b1
  base4 : base (row 4) = -D.w
  base5 : base (row 5) = D.v
  base6 : base (row 6) = -D.u
  pow0 : (2 : ℤ) ^ len (row 0) = D.q
  pow1 : (2 : ℤ) ^ len (row 1) = D.q
  pow2 : (2 : ℤ) ^ len (row 2) = D.q
  pow3 : (2 : ℤ) ^ len (row 3) = D.r
  pow4 : (2 : ℤ) ^ len (row 4) = D.H / 4
  pow5 : (2 : ℤ) ^ len (row 5) = D.e
  pow6 : 2 * (2 : ℤ) ^ len (row 6) = D.F
  large0 : 2 * f (Sum.inl (row 0)) = D.N - D.z
  large1 : f (Sum.inl (row 1)) = -D.q * D.z
  large2 : f (Sum.inl (row 2)) = D.q * D.b
  large3 : f (Sum.inl (row 3)) = -D.q * D.n
  large4 : f (Sum.inl (row 4)) = D.r * D.b1
  large5 : f (Sum.inl (row 5)) = -(D.H / 4) * D.w
  large6 : 2 * f (Sum.inl (row 6)) = D.N - D.u

variable {row : Fin 7 ↪ ι}

def fullRow {D : PrefixArithmetic} (R : RowData row D) (i : ι) : Finset (Occ R.len) :=
  rowMask R.len i Finset.univ

theorem fullRow_sum {D : PrefixArithmetic} (R : RowData row D) (i : ι) :
    ∑ o ∈ fullRow R i, R.f o = ((2 : ℤ) ^ R.len i - 1) * R.base i := by
  rw [fullRow, rowMask_sum R.len R.f i Finset.univ (R.base i) (R.values i)]
  rw [← weight, weight_full]

theorem row_small {D : PrefixArithmetic} (R : RowData row D) (i : ι)
    (S : Finset (Fin (R.len i))) :
    ∀ o ∈ rowMask R.len i S, |R.f o| ≤ D.Q - 1 := by
  intro o ho
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ho
  exact R.small i j

theorem row_sum {D : PrefixArithmetic} (R : RowData row D) (i : ι)
    (S : Finset (Fin (R.len i))) :
    ∑ o ∈ rowMask R.len i S, R.f o = weight S * R.base i :=
  rowMask_sum R.len R.f i S (R.base i) (R.values i)

def bank {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) : Finset (Occ R.len) :=
  rowMask R.len (row 2) Sn ∪ rowMask R.len (row 4) Sw ∪ fullRow R (row 0) ∪ fullRow R (row 1) ∪ fullRow R (row 5)

theorem bank_parts {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) :
    rowMask R.len (row 2) Sn ⊆ bank R Sn Sw ∧ rowMask R.len (row 4) Sw ⊆ bank R Sn Sw ∧
      fullRow R (row 0) ⊆ bank R Sn Sw ∧ fullRow R (row 1) ⊆ bank R Sn Sw ∧ fullRow R (row 5) ⊆ bank R Sn Sw := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro o ho <;> simp only [bank, Finset.mem_union] <;> tauto

theorem two_rows_sum {D : PrefixArithmetic} (R : RowData row D) (i j : ι)
    (S : Finset (Fin (R.len i))) (T : Finset (Fin (R.len j))) (hij : i ≠ j) :
    (∑ o ∈ rowMask R.len i S ∪ rowMask R.len j T, R.f o) =
      weight S * R.base i + weight T * R.base j := by
  rw [Finset.sum_union (rowMask_disjoint R.len i j S T hij), row_sum, row_sum]

theorem three_rows_sum {D : PrefixArithmetic} (R : RowData row D) (i j k : ι)
    (S : Finset (Fin (R.len i))) (T : Finset (Fin (R.len j))) (U : Finset (Fin (R.len k)))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ o ∈ rowMask R.len i S ∪ rowMask R.len j T ∪ rowMask R.len k U, R.f o) =
      weight S * R.base i + weight T * R.base j + weight U * R.base k := by
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
    ⟨rowMask_disjoint R.len i k S U hik, rowMask_disjoint R.len j k T U hjk⟩),
    two_rows_sum R i j S T hij, row_sum]

structure TSelection {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) where
  keep : Finset (Occ R.len)
  available : keep ⊆ bank R Sn Sw
  pay : Finset (Fin (R.len (row 6)))
  gate : (D.u - D.z) / 2 ≤ -(∑ o ∈ keep, R.f o) - weight pay * D.u ∧
    -(∑ o ∈ keep, R.f o) - weight pay * D.u ≤ D.u - (D.z + 1) / 2

def firstParents (row : Fin 7 ↪ ι) (len : ι → ℕ) : Finset (Occ len) :=
  {Sum.inl (row 2), Sum.inl (row 1), Sum.inl (row 0)}

def initialSmall {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) : Finset (Occ R.len) :=
  fullRow R (row 3) ∪ rowMask R.len (row 2) Snᶜ ∪ rowMask R.len (row 4) Swᶜ

def wjUsed {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) : Finset (Occ R.len) :=
  insert (Sum.inl (row 5)) (insert (Sum.inl (row 4)) (insert (Sum.inl (row 3))
    (firstParents row R.len ∪ initialSmall R Sn Sw)))

def wjHeight {D : PrefixArithmetic} (R : RowData row D) (f : ℤ) : ℤ :=
  f + R.f (Sum.inl (row 4)) + R.f (Sum.inl (row 5))

theorem wj_prefix {D : PrefixArithmetic} (R : RowData row D) (A f : ℤ)
    (hA : 1 ≤ A) (hAP : A ≤ D.H / 4) (hf : 0 ≤ f) (hfg : f ≤ (D.w - 1) / 2)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4))))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    Nonempty (Prefix R.f D.C (Sum.inl (row 0)) (wjUsed R Sn Sw) (wjHeight R f)) ∧
      0 < wjHeight R f ∧ 2 * wjHeight R f ≤ D.v - 1 := by
  classical
  obtain ⟨hn0, hz0, hb0, hw0, hv0, hu0, hP, hq, hHw, hwb, hzmax⟩ := arithmetic_geometry D
  obtain ⟨h2C, hNb1, hbz, hwB1, hNw, hnf0, hnfC, hfPC, hZ0, hZv⟩ := wj_geometry D f hf hfg
  have hH := D.H_eight
  have hHq := D.H_q
  have hq0 : 0 < D.q := by omega
  have hC0 : 0 ≤ D.C := by have hh := D.C_quarter; have hh' := D.Q_positive; omega
  have hp0 : 0 ≤ R.f (Sum.inl (row 0)) ∧ R.f (Sum.inl (row 0)) ≤ D.C := by
    have hm := mul_nonneg (show 0 ≤ D.H - 1 by omega) (le_of_lt hz0)
    have hb := abs_le.mp (R.bound (row 0))
    constructor
    · nlinarith only [R.large0, D.N_z, hm, hz0, hb0]
    · exact hb.2
  have hfirst : 2 * (R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1))) = D.Δ := by
    have hHZ := congrArg (fun H : ℤ => H * D.z) hHq
    nlinarith only [R.large0, R.large1, D.N_z, hbz, hHZ]
  have hfirstbounds : 0 ≤ R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) ∧
      R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) ≤ D.C := by
    have hneg : R.f (Sum.inl (row 1)) < 0 := by rw [R.large1]; nlinarith only [mul_pos hq0 hz0]
    have hd := D.delta_two
    omega
  have hsecondbounds : 0 ≤ R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) + R.f (Sum.inl (row 2)) ∧
      R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) + R.f (Sum.inl (row 2)) ≤ D.C := by
    have hpos : 0 < D.q * D.b := mul_pos hq0 hb0
    have hΔn : D.Δ < D.n := by
      have hm := mul_nonneg (show 0 ≤ D.H - 1 by omega) (show 0 ≤ D.Δ by have hh := D.delta_two; omega)
      nlinarith only [hm, D.delta_n]
    have hHb := congrArg (fun H : ℤ => H * D.b) hHq
    constructor
    · nlinarith only [hfirstbounds.1, R.large2, hpos]
    · nlinarith only [hfirst, R.large2, D.N_b, hHb, h2C, hΔn]
  obtain ⟨pre0⟩ := prefix_single R.f D.C (Sum.inl (row 0)) hC0 hp0
  obtain ⟨pre1⟩ := prefix_large pre0 (Sum.inl (row 1)) (by simp) hfirstbounds
  obtain ⟨pre2⟩ := prefix_large pre1 (Sum.inl (row 2)) (by simp) hsecondbounds
  have hSnc : weight Snᶜ = D.q - 1 - A := by rw [weight_compl, R.pow2, hSn]
  have hSwc : weight Swᶜ = A - 1 := by rw [weight_compl, R.pow4, hSw]; ring
  have hI : (∑ o ∈ initialSmall R Sn Sw, R.f o) =
      (D.r - 1) * D.b1 - (D.q - 1 - A) * D.n - (A - 1) * D.w := by
    change (∑ o ∈ rowMask R.len (row 3) Finset.univ ∪ rowMask R.len (row 2) Snᶜ ∪ rowMask R.len (row 4) Swᶜ,
      R.f o) = _
    rw [three_rows_sum R (row 3) (row 2) (row 4) Finset.univ Snᶜ Swᶜ (by simp) (by simp) (by simp),
      weight_full, R.pow3, hSnc, hSwc, R.base3, R.base2, R.base4]
    ring
  have hIend : R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) + R.f (Sum.inl (row 2)) +
      (∑ o ∈ initialSmall R Sn Sw, R.f o) = D.q * D.n + f := by
    have hqN := congrArg (fun H : ℤ => H * D.n) hHq
    have hqB := congrArg (fun H : ℤ => H * D.b) hHq
    nlinarith only [hI, hfirst, R.large2, D.N_b, hNb1, D.w_source, heq, hqN, hqB]
  have hdis : Disjoint (firstParents row R.len) (initialSmall R Sn Sw) := by
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
      · exact row_small R (row 3) Finset.univ o ho
      · exact row_small R (row 2) Snᶜ o ho
      · exact row_small R (row 4) Swᶜ o ho)
    (by simpa only [hIend] using And.intro hnf0 hnfC)
  have hgamma : R.f (Sum.inl (row 0)) + R.f (Sum.inl (row 1)) + R.f (Sum.inl (row 2)) +
      (∑ o ∈ initialSmall R Sn Sw, R.f o) + R.f (Sum.inl (row 3)) = f := by
    rw [hIend, R.large3]; ring
  have hfC : f ≤ D.C := by have hqn := mul_nonneg (le_of_lt hq0) (le_of_lt hn0); omega
  obtain ⟨preG⟩ := prefix_large preI (Sum.inl (row 3))
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma] using And.intro hf hfC)
  have hPdouble : 2 * R.f (Sum.inl (row 4)) = D.N - D.w := by
    nlinarith only [R.large4, D.w_source]
  have hPbounds : 0 ≤ f + R.f (Sum.inl (row 4)) ∧ f + R.f (Sum.inl (row 4)) ≤ D.C := by
    have hm := mul_nonneg (show 0 ≤ D.q by omega) (le_of_lt hw0)
    constructor <;> nlinarith only [hPdouble, hfPC, hf, hNw, hm]
  obtain ⟨preP⟩ := prefix_large preG (Sum.inl (row 4))
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma] using hPbounds)
  have hZeq : 2 * wjHeight R f = 2 * f + D.N - (D.q + 1) * D.w := by
    have hh := congrArg (fun q : ℤ => q * D.w) hq
    dsimp only [wjHeight]
    nlinarith only [hPdouble, R.large5, hh]
  have hZpos : 0 < wjHeight R f := by omega
  have hZbounds : 0 ≤ wjHeight R f ∧ wjHeight R f ≤ D.C := by
    have hJneg : R.f (Sum.inl (row 5)) ≤ 0 := by rw [R.large5]; nlinarith only [mul_nonneg (show 0 ≤ D.H / 4 by omega) (le_of_lt hw0)]
    dsimp only [wjHeight] at *
    omega
  obtain ⟨preJ⟩ := prefix_large preP (Sum.inl (row 5))
    (by simp [firstParents, initialSmall, fullRow])
    (by simpa only [hgamma, wjHeight] using hZbounds)
  refine ⟨?_, hZpos, by omega⟩
  simpa only [hgamma, wjUsed, wjHeight, firstParents] using (show Nonempty (Prefix R.f D.C (Sum.inl (row 0)) _ _) from ⟨preJ⟩)

@[simp] theorem inr_not_rowMask_of_ne (len : ι → ℕ) (i j : ι)
    (S : Finset (Fin (len i))) (a : Fin (len j)) (hij : i ≠ j) :
    Sum.inr ⟨j, a⟩ ∉ rowMask len i S := by
  intro h
  have ha : Sum.inr ⟨j, a⟩ ∈ rowMask len j Finset.univ :=
    (inr_mem_rowMask len j Finset.univ a).mpr (Finset.mem_univ _)
  exact Finset.disjoint_left.mp (rowMask_disjoint len i j S Finset.univ hij) h ha

theorem bank_wj_disjoint {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) :
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
    | apply rowMask_disjoint; simp

theorem bank_row6_disjoint {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4))))
    (S : Finset (Fin (R.len (row 6)))) : Disjoint (bank R Sn Sw) (rowMask R.len (row 6) S) := by
  simp only [bank, fullRow, Finset.disjoint_union_left]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> simp

theorem row6_wj_disjoint {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4))))
    (S : Finset (Fin (R.len (row 6)))) : Disjoint (rowMask R.len (row 6) S) (wjUsed R Sn Sw) := by
  classical
  simp only [wjUsed, firstParents, initialSmall, fullRow,
    Finset.disjoint_union_right, Finset.disjoint_insert_right,
    Finset.disjoint_singleton_right, inl_not_rowMask, not_false_eq_true, true_and, and_true]
  repeat' apply And.intro
  all_goals apply rowMask_disjoint <;> simp

theorem bank_small {D : PrefixArithmetic} (R : RowData row D)
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4)))) :
    ∀ o ∈ bank R Sn Sw, |R.f o| ≤ D.Q - 1 := by
  intro o ho
  simp only [bank, Finset.mem_union] at ho
  rcases ho with (((ho | ho) | ho) | ho) | ho
  · exact row_small R (row 2) Sn o ho
  · exact row_small R (row 4) Sw o ho
  · exact row_small R (row 0) Finset.univ o ho
  · exact row_small R (row 1) Finset.univ o ho
  · exact row_small R (row 5) Finset.univ o ho

theorem bank_charge {D : PrefixArithmetic} (R : RowData row D) (A f : ℤ)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4))))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A) :
    2 * (wjHeight R f + ∑ o ∈ bank R Sn Sw, R.f o) = D.z - D.u := by
  classical
  have hdis0 : Disjoint (rowMask R.len (row 2) Sn ∪ rowMask R.len (row 4) Sw) (fullRow R (row 0)) := by
    simp only [fullRow, Finset.disjoint_union_left]
    constructor <;> apply rowMask_disjoint <;> simp
  have hdis1 : Disjoint (rowMask R.len (row 2) Sn ∪ rowMask R.len (row 4) Sw ∪ fullRow R (row 0)) (fullRow R (row 1)) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> simp
  have hdis5 : Disjoint (rowMask R.len (row 2) Sn ∪ rowMask R.len (row 4) Sw ∪ fullRow R (row 0) ∪ fullRow R (row 1))
      (fullRow R (row 5)) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> simp
  have hsum : (∑ o ∈ bank R Sn Sw, R.f o) =
      -A * D.n - (D.H / 4 - A) * D.w - (D.q - 1) * D.z +
      (D.q - 1) * D.b + (D.e - 1) * D.v := by
    rw [bank, Finset.sum_union hdis5, Finset.sum_union hdis1, Finset.sum_union hdis0,
      two_rows_sum R (row 2) (row 4) Sn Sw (by simp), fullRow_sum, fullRow_sum, fullRow_sum,
      hSn, hSw, R.pow0, R.pow1, R.pow5, R.base0, R.base1, R.base2, R.base4, R.base5]
    ring
  have hbz : D.b - D.z = D.Δ := by nlinarith only [D.b_n, D.z_n]
  have hδq := congrArg (fun H : ℤ => H * D.Δ) D.H_q
  have hwq := congrArg (fun q : ℤ => q * D.w) (arithmetic_geometry D).2.2.2.2.2.2.2.1
  have hd := congrArg (fun d : ℤ => 2 * (D.q - 1) * d) hbz
  have hp : 2 * R.f (Sum.inl (row 4)) = D.N - D.w := by nlinarith only [R.large4, D.w_source]
  dsimp only [wjHeight]
  nlinarith only [hsum, heq, hp, R.large5, D.u_source, D.v_source, D.z_n, hδq, hwq, hd]

def tSmall {D : PrefixArithmetic} (R : RowData row D)
    {Sn : Finset (Fin (R.len (row 2)))} {Sw : Finset (Fin (R.len (row 4)))}
    (K : TSelection R Sn Sw) : Finset (Occ R.len) :=
  (bank R Sn Sw \ K.keep) ∪ rowMask R.len (row 6) K.pay

def tUsed {D : PrefixArithmetic} (R : RowData row D)
    {Sn : Finset (Fin (R.len (row 2)))} {Sw : Finset (Fin (R.len (row 4)))}
    (K : TSelection R Sn Sw) : Finset (Occ R.len) :=
  insert (Sum.inl (row 6)) (wjUsed R Sn Sw ∪ tSmall R K)

def tHeight {D : PrefixArithmetic} (R : RowData row D)
    {Sn : Finset (Fin (R.len (row 2)))} {Sw : Finset (Fin (R.len (row 4)))}
    (K : TSelection R Sn Sw) : ℤ :=
  -(∑ o ∈ K.keep, R.f o) - weight K.pay * D.u - (D.u - D.z) / 2 + R.f (Sum.inl (row 6))

theorem t_extension {D : PrefixArithmetic} (R : RowData row D) (A f : ℤ)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len (row 2)))) (Sw : Finset (Fin (R.len (row 4))))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A)
    (pre : Prefix R.f D.C (Sum.inl (row 0)) (wjUsed R Sn Sw) (wjHeight R f))
    (K : TSelection R Sn Sw) :
    Nonempty (Prefix R.f D.C (Sum.inl (row 0)) (tUsed R K) (tHeight R K)) := by
  classical
  obtain ⟨hell0, hW0, hell, hhi, hW, hwidth⟩ := gate_limits D
  have h2C : 2 * D.C = D.N - 1 := by have hN := D.N_quarter; have hC := D.C_quarter; omega
  have hWle : (D.u - 1) / 2 ≤ D.C := by have hu := D.u_bound; omega
  have hdis : Disjoint (wjUsed R Sn Sw) (tSmall R K) := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨(bank_wj_disjoint R Sn Sw).symm.mono_right Finset.sdiff_subset,
      (row6_wj_disjoint R Sn Sw K.pay).symm⟩
  have hsmall : ∀ o ∈ tSmall R K, |R.f o| ≤ D.Q - 1 := by
    intro o ho
    rcases Finset.mem_union.mp ho with ho | ho
    · exact bank_small R Sn Sw o (Finset.mem_sdiff.mp ho).1
    · exact row_small R (row 6) K.pay o ho
  have hsum : (∑ o ∈ tSmall R K, R.f o) =
      (∑ o ∈ bank R Sn Sw, R.f o) - (∑ o ∈ K.keep, R.f o) - weight K.pay * D.u := by
    rw [tSmall, Finset.sum_union ((bank_row6_disjoint R Sn Sw K.pay).mono_left Finset.sdiff_subset),
      row_sum, R.base6]
    have hh := Finset.sum_sdiff K.available (f := R.f)
    linarith only [hh]
  have hend : wjHeight R f + ∑ o ∈ tSmall R K, R.f o =
      -(∑ o ∈ K.keep, R.f o) - weight K.pay * D.u - (D.u - D.z) / 2 := by
    have hh := bank_charge R A f heq Sn Sw hSn hSw
    linarith only [hh, hsum, hell]
  have hbefore : 0 ≤ wjHeight R f + ∑ o ∈ tSmall R K, R.f o ∧
      wjHeight R f + ∑ o ∈ tSmall R K, R.f o ≤ (D.u - 1) / 2 := by
    rw [hend]
    constructor <;> linarith only [K.gate.1, K.gate.2, hwidth]
  obtain ⟨preS⟩ := prefix_batch pre (tSmall R K) (D.Q - 1)
    (by have hh := D.Q_positive; omega) (by have hh := D.C_quarter; omega)
    hdis hsmall ⟨hbefore.1, hbefore.2.trans hWle⟩
  have hpos : 0 ≤ R.f (Sum.inl (row 6)) := by
    have hu := D.u_bound
    nlinarith only [R.large6, h2C, hu, D.Q_positive, D.C_quarter]
  obtain ⟨preT⟩ := prefix_large preS (Sum.inl (row 6))
    (by simp (disch := decide) [wjUsed, firstParents, initialSmall, tSmall, bank, fullRow])
    (by constructor <;> nlinarith only [hbefore.1, hbefore.2, hpos, R.large6, h2C, hW])
  simpa only [tUsed, tHeight, hend] using
    (show Nonempty (Prefix R.f D.C (Sum.inl (row 0)) _ _) from ⟨preT⟩)

end D5.S3.Combinatorics.Circle.SourcePrefixInventory
