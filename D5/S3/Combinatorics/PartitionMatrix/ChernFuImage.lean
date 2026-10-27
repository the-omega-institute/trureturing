/- GID: D5/S3/Combinatorics/PartitionMatrix/ChernFuImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartitionMatrix/ChernFuImage
   mirror-E: none(waiver:general-native-partition-matrix-characterization)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Fintype.Order]
   utility: none
   digest: Improper partition matrices have exactly the whole-alphabet gap image. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

/-! Chern--Fu, arXiv:2508.21318v2, Definition 1.1, Definition 2.1 and
Question 5.5. Labels are `t.val + 1` for `t : Fin n`; rows and columns are
zero based. The fixed map counts columns strictly before the label's row.
The reconstruction is the finite ordered-partition construction of
Claesson--Dukes--Kubitzke, arXiv:1006.1312v2, Section 2 and Theorem 3.
No literature theorem is assumed as a formal premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartitionMatrix.ChernFuImage

open Finset
open scoped BigOperators



/-- Literal square set-entry partition matrices on the native labels `[n]`.
A `Fin n` element `t` represents the source label `t.val + 1`. -/
structure NativePM (n k : ℕ) where
  cell : Fin k → Fin k → Finset (Fin n)
  upper : ∀ r c, c < r → cell r c = ∅
  partition : ∀ t, ∃! p : Fin k × Fin k, t ∈ cell p.1 p.2
  row_nonempty : ∀ r, ∃ c t, t ∈ cell r c
  column_nonempty : ∀ c, ∃ r t, t ∈ cell r c
  label_order : ∀ a b r c s d, a < b → a ∈ cell r c → b ∈ cell s d → c ≤ d

/-- Coordinates of labels in a partition matrix. Surjectivity says that every
row and every column is nonempty; upper triangularity and native label order
are separate axioms, with no improperness or sequence condition included. -/
structure Coordinates (n k : ℕ) where
  row : Fin n → Fin k
  col : Fin n → Fin k
  upper : ∀ t, row t ≤ col t
  row_surjective : Function.Surjective row
  col_surjective : Function.Surjective col
  col_monotone : Monotone col

variable {n k : ℕ}

private noncomputable def location (P : NativePM n k) (t : Fin n) : Fin k × Fin k :=
  (P.partition t).exists.choose

private theorem location_mem (P : NativePM n k) (t : Fin n) :
    t ∈ P.cell (location P t).1 (location P t).2 :=
  (P.partition t).exists.choose_spec

private theorem location_eq (P : NativePM n k) (t : Fin n) (r c : Fin k)
    (h : t ∈ P.cell r c) : location P t = (r,c) :=
  (P.partition t).unique (location_mem P t) h

private noncomputable def fromNative (P : NativePM n k) : Coordinates n k where
  row t := (location P t).1
  col t := (location P t).2
  upper t := by
    by_contra h
    have := P.upper _ _ (lt_of_not_ge h)
    have hm := location_mem P t
    rw [this] at hm
    exact (Finset.notMem_empty t) hm
  row_surjective r := by
    obtain ⟨c,t,ht⟩ := P.row_nonempty r
    exact ⟨t, congrArg Prod.fst (location_eq P t r c ht)⟩
  col_surjective c := by
    obtain ⟨r,t,ht⟩ := P.column_nonempty c
    exact ⟨t, congrArg Prod.snd (location_eq P t r c ht)⟩
  col_monotone := by
    intro a b hab
    rcases hab.eq_or_lt with h | h
    · exact le_of_eq (congrArg (fun t => (location P t).2) h)
    · exact P.label_order a b _ _ _ _ h (location_mem P a) (location_mem P b)

private def toNative (P : Coordinates n k) : NativePM n k where
  cell r c := univ.filter (fun t => P.row t = r ∧ P.col t = c)
  upper r c h := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have ht := (mem_filter.mp ht).2
    have := P.upper t
    rw [ht.1,ht.2] at this
    exact (not_le_of_gt h) this
  partition t := by
    refine ⟨(P.row t,P.col t), by simp, ?_⟩
    intro p hp
    have hp := (mem_filter.mp hp).2
    exact Prod.ext hp.1.symm hp.2.symm
  row_nonempty r := by
    obtain ⟨t,ht⟩ := P.row_surjective r
    exact ⟨P.col t,t,by simp [ht]⟩
  column_nonempty c := by
    obtain ⟨t,ht⟩ := P.col_surjective c
    exact ⟨P.row t,t,by simp [ht]⟩
  label_order a b r c s d hab ha hb := by
    have ha := (mem_filter.mp ha).2
    have hb := (mem_filter.mp hb).2
    simpa [ha.2,hb.2] using P.col_monotone hab.le

private theorem native_ext (P Q : NativePM n k) (h : P.cell = Q.cell) : P = Q := by
  cases P
  cases Q
  congr

private theorem coordinates_ext (P Q : Coordinates n k)
    (hr : P.row = Q.row) (hc : P.col = Q.col) : P = Q := by
  cases P
  cases Q
  congr

private theorem from_to (P : Coordinates n k) : fromNative (toNative P) = P := by
  apply coordinates_ext
  · funext t
    exact congrArg Prod.fst (location_eq (toNative P) t (P.row t) (P.col t) (by simp [toNative]))
  · funext t
    exact congrArg Prod.snd (location_eq (toNative P) t (P.row t) (P.col t) (by simp [toNative]))

private theorem to_from (P : NativePM n k) : toNative (fromNative P) = P := by
  apply native_ext
  funext r c
  ext t
  change t ∈ univ.filter (fun t => (location P t).1 = r ∧ (location P t).2 = c) ↔
    t ∈ P.cell r c
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hr,hc⟩
    have := location_mem P t
    simpa [hr,hc] using this
  · intro ht
    have h := location_eq P t r c ht
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Exact faithful correspondence between the literal native set-entry
matrices and label coordinates, at each `n` and each permitted dimension `k`.
Both composites are identities, including every cell of the native matrix. -/
noncomputable def nativeEquiv : NativePM n k ≃ Coordinates n k where
  toFun := fromNative
  invFun := toNative
  left_inv := to_from
  right_inv := from_to

/-- The labels of a native column, represented at zero-based label indices. -/
def column (P : NativePM n k) (c : Fin k) : Finset (Fin n) :=
  univ.filter (fun t => ∃ r, t ∈ P.cell r c)

/-- The fixed source map: sum COLUMN cardinalities strictly before the
label's row. An empty sum is zero. -/
noncomputable def fixedPi (P : NativePM n k) (t : Fin n) : ℕ :=
  ∑ c ∈ univ.filter (fun c => c < (nativeEquiv P).row t), (column P c).card

private theorem column_eq (P : NativePM n k) (c : Fin k) :
    column P c = univ.filter (fun t => (nativeEquiv P).col t = c) := by
  ext t
  simp only [column, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨r,ht⟩
    exact congrArg Prod.snd (location_eq P t r c ht)
  · intro hc
    change (location P t).2 = c at hc
    exact ⟨(location P t).1, by rw [← hc]; exact location_mem P t⟩

private def fiber (P : Coordinates n k) (c : Fin k) : Finset (Fin n) :=
  univ.filter (fun t => P.col t = c)

private theorem fiber_nonempty (P : Coordinates n k) (c : Fin k) :
    (fiber P c).Nonempty := by
  obtain ⟨t,ht⟩ := P.col_surjective c
  exact ⟨t, by simp [fiber,ht]⟩

private noncomputable def first (P : Coordinates n k) (c : Fin k) : Fin n :=
  (fiber P c).min' (fiber_nonempty P c)

private theorem col_first (P : Coordinates n k) (c : Fin k) :
    P.col (first P c) = c :=
  by
    have h : first P c ∈ fiber P c := min'_mem _ _
    exact (mem_filter.mp h).2

private theorem first_le (P : Coordinates n k) (c : Fin k) (t : Fin n)
    (ht : P.col t = c) : first P c ≤ t :=
  min'_le _ _ (by simp [fiber,ht])

private theorem col_lt_iff (P : Coordinates n k) (t : Fin n) (c : Fin k) :
    P.col t < c ↔ t < first P c := by
  constructor
  · intro h
    by_contra hn
    have hm := P.col_monotone (le_of_not_gt hn)
    rw [col_first] at hm
    exact (not_le_of_gt h) hm
  · intro h
    have hm := P.col_monotone h.le
    rw [col_first] at hm
    apply lt_of_le_of_ne hm
    intro heq
    exact (not_le_of_gt h) (first_le P c t heq)

private theorem first_strictMono (P : Coordinates n k) : StrictMono (first P) := by
  intro c d h
  exact (col_lt_iff P (first P c) d).mp (by simpa [col_first] using h)

private noncomputable def cut (P : Coordinates n k) (c : Fin k) : ℕ := (first P c).val

private theorem cut_strictMono (P : Coordinates n k) : StrictMono (cut P) :=
  fun _ _ h => first_strictMono P h

private noncomputable def pi (P : Coordinates n k) (t : Fin n) : ℕ :=
  ∑ c ∈ univ.filter (fun c => c < P.row t), (fiber P c).card

private theorem pi_eq_cut (P : Coordinates n k) (t : Fin n) :
    pi P t = cut P (P.row t) := by
  unfold pi fiber
  rw [sum_card_fiberwise_eq_card_filter]
  have hs : (univ.filter (fun i : Fin n =>
      P.col i ∈ univ.filter (fun c => c < P.row t))) =
      Iio (first P (P.row t)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_Iio]
    exact col_lt_iff P i (P.row t)
  rw [hs, Fin.card_Iio]
  rfl

private theorem fixedPi_eq_pi (P : NativePM n k) : fixedPi P = pi (nativeEquiv P) := by
  funext t
  unfold fixedPi pi
  apply sum_congr rfl
  intro c _
  rw [column_eq]
  rfl

/-- The whole alphabet of a sequence; it is not restricted to a prefix. -/
def alphabet (e : Fin n → ℕ) : Finset ℕ := univ.image e

/-- Maximum of zero and all occurring values strictly below the native label
`i`. The bottom value in `Finset.sup` includes zero even for an empty filter. -/
def previous (e : Fin n → ℕ) (i : ℕ) : ℕ :=
  ((alphabet e).filter (fun a => a < i)).sup id

/-- The sequence-only gap criterion. The native adjacent labels are
`j.val + 1` and `j.val + 2`, at zero-based indices `j` and `j.val + 1`.
Both occurrence tests use the alphabet of the entire sequence. -/
def Phi (e : Fin n → ℕ) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n),
    j.val + 1 ∉ alphabet e →
    (j.val + 1 - previous e (j.val + 1)) % 2 = 1 →
    e j = e ⟨j.val + 1,h⟩

private theorem mem_alphabet_iff (e : Fin n → ℕ) (a : ℕ) :
    a ∈ alphabet e ↔ ∃ t, e t = a := by
  simp [alphabet]

private theorem alphabet_pi_iff (P : Coordinates n k) (a : ℕ) :
    a ∈ alphabet (pi P) ↔ ∃ c, cut P c = a := by
  rw [mem_alphabet_iff]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨P.row t, (pi_eq_cut P t).symm.trans ht⟩
  · rintro ⟨c,hc⟩
    obtain ⟨t,ht⟩ := P.row_surjective c
    exact ⟨t, by rw [pi_eq_cut,ht,hc]⟩

private theorem previous_pi (P : Coordinates n k) (j : Fin n) :
    previous (pi P) (j.val + 1) = cut P (P.col j) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    have ha := mem_filter.mp ha
    obtain ⟨c,hc⟩ := (alphabet_pi_iff P a).mp ha.1
    have hfirst : first P c ≤ j := by
      change (first P c).val ≤ j.val
      change (first P c).val = a at hc
      omega
    have hm := P.col_monotone hfirst
    rw [col_first] at hm
    simpa [hc] using (cut_strictMono P).monotone hm
  · apply Finset.le_sup (f := id)
    apply mem_filter.mpr
    refine ⟨(alphabet_pi_iff P _).mpr ⟨P.col j,rfl⟩, ?_⟩
    have h := first_le P (P.col j) j rfl
    change (first P (P.col j)).val < j.val + 1
    exact Nat.lt_succ_of_le h

private theorem same_column_iff (P : Coordinates n k) (j : Fin n)
    (h : j.val + 1 < n) :
    P.col j = P.col ⟨j.val + 1,h⟩ ↔ j.val + 1 ∉ alphabet (pi P) := by
  let t : Fin n := ⟨j.val + 1,h⟩
  constructor
  · intro hs ha
    obtain ⟨c,hc⟩ := (alphabet_pi_iff P _).mp ha
    have hf : first P c = t := Fin.ext hc
    have hct : P.col t = c := by rw [← hf]; exact col_first P c
    have hm := first_le P c j (hs.trans hct)
    rw [hf] at hm
    have : j.val + 1 ≤ j.val := hm
    omega
  · intro hn
    by_contra hne
    have hjt : j ≤ t := by change j.val ≤ j.val + 1; omega
    have hlt : P.col j < P.col t :=
      lt_of_le_of_ne (P.col_monotone hjt) hne
    have hle := first_le P (P.col t) t rfl
    have hgt : j < first P (P.col t) := by
      by_contra hh
      have hm := P.col_monotone (le_of_not_gt hh)
      rw [col_first] at hm
      exact (not_le_of_gt hlt) hm
    have hv : cut P (P.col t) = j.val + 1 := by
      have hle' : (first P (P.col t)).val ≤ j.val + 1 := hle
      have hgt' : j.val < (first P (P.col t)).val := hgt
      unfold cut
      omega
    exact hn ((alphabet_pi_iff P _).mpr ⟨P.col t,hv⟩)

private theorem column_nonempty (P : NativePM n k) (c : Fin k) :
    (column P c).Nonempty := by
  obtain ⟨r,t,ht⟩ := P.column_nonempty c
  exact ⟨t,by simp only [column,mem_filter,mem_univ,true_and]; exact ⟨r,ht⟩⟩

/-- Least native LABEL in a column. In particular, its parity uses labels
starting at one, not zero-based list indices. -/
noncomputable def columnLeast (P : NativePM n k) (c : Fin k) : ℕ :=
  ((column P c).min' (column_nonempty P c)).val + 1

private theorem columnLeast_eq (P : NativePM n k) (c : Fin k) :
    columnLeast P c = cut (nativeEquiv P) c + 1 := by
  have hc : column P c = fiber (nativeEquiv P) c := column_eq P c
  unfold columnLeast cut first
  simp only [hc]

/-- Improperness as in Chern--Fu: neither row order of a same-column
adjacent pair can be proper. Equal rows define neither an ascent nor a
descent. Proper parity compares the lower label to its column's least label. -/
noncomputable def Improper (P : NativePM n k) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n),
    ¬ ((nativeEquiv P).col j = (nativeEquiv P).col ⟨j.val + 1,h⟩ ∧
      (nativeEquiv P).row j < (nativeEquiv P).row ⟨j.val + 1,h⟩ ∧
      (j.val + 1) % 2 = columnLeast P ((nativeEquiv P).col j) % 2) ∧
    ¬ ((nativeEquiv P).col j = (nativeEquiv P).col ⟨j.val + 1,h⟩ ∧
      (nativeEquiv P).row ⟨j.val + 1,h⟩ < (nativeEquiv P).row j ∧
      (j.val + 1) % 2 = columnLeast P ((nativeEquiv P).col j) % 2)

private theorem improper_iff_rows (P : NativePM n k) :
    Improper P ↔ ∀ (j : Fin n) (h : j.val + 1 < n),
      (nativeEquiv P).col j = (nativeEquiv P).col ⟨j.val + 1,h⟩ →
      (j.val + 1) % 2 = (cut (nativeEquiv P) ((nativeEquiv P).col j) + 1) % 2 →
      (nativeEquiv P).row j = (nativeEquiv P).row ⟨j.val + 1,h⟩ := by
  unfold Improper
  simp only [columnLeast_eq]
  constructor
  · intro hp j h hc he
    rcases lt_trichotomy ((nativeEquiv P).row j) ((nativeEquiv P).row ⟨j.val + 1,h⟩)
      with hr | hr | hr
    · exact False.elim ((hp j h).1 ⟨hc,hr,he⟩)
    · exact hr
    · exact False.elim ((hp j h).2 ⟨hc,hr,he⟩)
  · intro hp j h
    constructor
    · rintro ⟨hc,hr,he⟩
      exact (ne_of_lt hr) (hp j h hc he)
    · rintro ⟨hc,hr,he⟩
      exact (ne_of_gt hr) (hp j h hc he)

private theorem improper_iff_phi (P : NativePM n k) : Improper P ↔ Phi (fixedPi P) := by
  rw [improper_iff_rows,fixedPi_eq_pi]
  constructor
  · intro hp j h ha ho
    have hc := (same_column_iff (nativeEquiv P) j h).mpr ha
    have hb := first_le (nativeEquiv P) ((nativeEquiv P).col j) j rfl
    have hb' : cut (nativeEquiv P) ((nativeEquiv P).col j) ≤ j.val := hb
    rw [previous_pi] at ho
    have he : (j.val + 1) % 2 =
        (cut (nativeEquiv P) ((nativeEquiv P).col j) + 1) % 2 := by omega
    rw [pi_eq_cut,pi_eq_cut,hp j h hc he]
  · intro hp j h hc he
    have ha := (same_column_iff (nativeEquiv P) j h).mp hc
    have hb := first_le (nativeEquiv P) ((nativeEquiv P).col j) j rfl
    have hb' : cut (nativeEquiv P) ((nativeEquiv P).col j) ≤ j.val := hb
    have ho : (j.val + 1 - previous (pi (nativeEquiv P)) (j.val + 1)) % 2 = 1 := by
      rw [previous_pi]
      omega
    have hh := hp j h ha ho
    rw [pi_eq_cut,pi_eq_cut] at hh
    exact (cut_strictMono (nativeEquiv P)).injective hh

private theorem zero_mem_alphabet (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) : 0 ∈ alphabet e := by
  apply (mem_alphabet_iff e 0).mpr
  exact ⟨⟨0,hn⟩,Nat.eq_zero_of_le_zero (he ⟨0,hn⟩)⟩

private theorem alphabet_lt (e : Fin n → ℕ) (he : ∀ t, e t ≤ t.val)
    (a : ℕ) (ha : a ∈ alphabet e) : a < n := by
  obtain ⟨t,ht⟩ := (mem_alphabet_iff e a).mp ha
  exact ht ▸ (lt_of_le_of_lt (he t) t.isLt)

private theorem previous_lt (e : Fin n → ℕ) (i : ℕ) (hi : 0 < i) :
    previous e i < i := by
  apply (Finset.sup_lt_iff hi).mpr
  intro a ha
  exact (mem_filter.mp ha).2

private theorem previous_mem (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) (i : ℕ) (hi : 0 < i) :
    previous e i ∈ alphabet e := by
  have hs : ((alphabet e).filter (fun a => a < i)).Nonempty :=
    ⟨0,mem_filter.mpr ⟨zero_mem_alphabet e hn he,hi⟩⟩
  have hm := Finset.sup_mem_of_nonempty (f := id) hs
  have hm' : previous e i ∈ (alphabet e).filter (fun a => a < i) := by
    simpa only [Set.image_id,mem_coe,previous] using hm
  exact (mem_filter.mp hm').1

private theorem entry_le_previous (e : Fin n → ℕ) (he : ∀ t, e t ≤ t.val)
    (t : Fin n) : e t ≤ previous e (t.val + 1) :=
  Finset.le_sup (f := id) (mem_filter.mpr
    ⟨(mem_alphabet_iff e _).mpr ⟨t,rfl⟩,Nat.lt_succ_of_le (he t)⟩)

private theorem previous_mono (e : Fin n → ℕ) : Monotone (previous e) := by
  intro i j hij
  apply Finset.sup_mono
  intro a ha
  have ha := mem_filter.mp ha
  exact mem_filter.mpr ⟨ha.1,lt_of_lt_of_le ha.2 hij⟩

private theorem previous_at_value (e : Fin n → ℕ) (a : ℕ)
    (ha : a ∈ alphabet e) : previous e (a + 1) = a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    exact Nat.le_of_lt_succ (mem_filter.mp hb).2
  · exact Finset.le_sup (f := id) (mem_filter.mpr ⟨ha,Nat.lt_succ_self a⟩)

private def value (e : Fin n → ℕ) (c : Fin (alphabet e).card) : ℕ :=
  ((alphabet e).orderIsoOfFin rfl c).val

private theorem value_injective (e : Fin n → ℕ) : Function.Injective (value e) := by
  intro a b h
  apply ((alphabet e).orderIsoOfFin rfl).injective
  exact Subtype.ext h

/-- The native CDK reconstruction: rows are ranked by occurring values;
the column of native label `t.val + 1` is ranked by the greatest occurring
value at most `t.val`. Its validity uses only the inversion bounds.
No improperness or `Phi` assumption occurs in this construction. -/
noncomputable def reconstruct (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) : Coordinates n (alphabet e).card := by
  let Y := (alphabet e).orderIsoOfFin rfl
  refine {
    row := fun t => Y.symm ⟨e t,(mem_alphabet_iff e _).mpr ⟨t,rfl⟩⟩
    col := fun t => Y.symm ⟨previous e (t.val + 1),
      previous_mem e hn he _ (Nat.zero_lt_succ _)⟩
    upper := ?_
    row_surjective := ?_
    col_surjective := ?_
    col_monotone := ?_ }
  · intro t
    exact Y.symm.monotone (entry_le_previous e he t)
  · intro r
    obtain ⟨t,ht⟩ := (mem_alphabet_iff e _).mp (Y r).property
    refine ⟨t,?_⟩
    apply Y.injective
    simp only [OrderIso.apply_symm_apply]
    exact Subtype.ext ht
  · intro c
    let a := (Y c).val
    have ha : a ∈ alphabet e := (Y c).property
    let t : Fin n := ⟨a,alphabet_lt e he a ha⟩
    refine ⟨t,?_⟩
    apply Y.injective
    simp only [OrderIso.apply_symm_apply]
    apply Subtype.ext
    exact previous_at_value e a ha
  · intro a b hab
    exact Y.symm.monotone (previous_mono e (Nat.add_le_add_right hab 1))

private theorem value_row_reconstruct (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) (t : Fin n) :
    value e ((reconstruct e hn he).row t) = e t := by
  simp [value,reconstruct]

private theorem value_col_reconstruct (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) (t : Fin n) :
    value e ((reconstruct e hn he).col t) = previous e (t.val + 1) := by
  simp [value,reconstruct]

private theorem cut_reconstruct (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) (c : Fin (alphabet e).card) :
    cut (reconstruct e hn he) c = value e c := by
  let R := reconstruct e hn he
  have ha : value e c ∈ alphabet e := ((alphabet e).orderIsoOfFin rfl c).property
  let t : Fin n := ⟨value e c,alphabet_lt e he _ ha⟩
  have hc : R.col t = c := by
    apply value_injective e
    rw [value_col_reconstruct]
    exact previous_at_value e _ ha
  have hle : (first R c).val ≤ value e c := first_le R c t hc
  have hx := value_col_reconstruct e hn he (first R c)
  change value e (R.col (first R c)) = previous e ((first R c).val + 1) at hx
  rw [col_first] at hx
  have hlt := previous_lt e ((first R c).val + 1) (Nat.zero_lt_succ _)
  change (first R c).val = value e c
  omega

private theorem pi_reconstruct (e : Fin n → ℕ) (hn : 0 < n)
    (he : ∀ t, e t ≤ t.val) : pi (reconstruct e hn he) = e := by
  funext t
  rw [pi_eq_cut,cut_reconstruct,value_row_reconstruct]

/-- Chern--Fu v2 Question 5.5, for every positive length and every native
inversion sequence. The existential image includes every matrix dimension;
`Phi` uses the whole sequence. Native label `i` is list index `i-1`.
The map is the fixed sum of COLUMN cardinalities, before the label's row. -/
theorem result (n : ℕ) (hn : 0 < n) (e : List ℕ) (hlen : e.length = n)
    (he : D5.S3.Combinatorics.InversionSeq.InversionSeqDefs.IsInversionSeq e) :
    (∃ (k : ℕ) (P : NativePM n k), Improper P ∧
      fixedPi P = fun t : Fin n => e.getD t.val 0) ↔
    Phi (fun t : Fin n => e.getD t.val 0) := by
  let f : Fin n → ℕ := fun t => e.getD t.val 0
  have hf : ∀ t, f t ≤ t.val := by
    intro t
    exact he t.val (hlen ▸ t.isLt)
  constructor
  · rintro ⟨k,P,hP,hPi⟩
    rw [← hPi]
    exact (improper_iff_phi P).mp hP
  · intro hp
    let R := reconstruct f hn hf
    let P : NativePM n (alphabet f).card := nativeEquiv.symm R
    have hPi : fixedPi P = f := by
      rw [fixedPi_eq_pi]
      change pi (nativeEquiv (nativeEquiv.symm R)) = f
      rw [Equiv.apply_symm_apply]
      exact pi_reconstruct f hn hf
    exact ⟨(alphabet f).card,P,(improper_iff_phi P).mpr (by rw [hPi]; exact hp),hPi⟩

end D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
