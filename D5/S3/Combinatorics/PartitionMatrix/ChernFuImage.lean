/- GID: D5/S3/Combinatorics/PartitionMatrix/ChernFuImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartitionMatrix/ChernFuImage
   mirror-E: none(waiver:general-native-partition-matrix-characterization)
   anchors: [D5/L/Combinatorics/chernfu2026signed, D5/L/Combinatorics/claesson2011partition]
   utility: none
   digest: The fixed CDK image of improper partition matrices is characterized by whole-alphabet gaps. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartitionMatrix.ChernFuImage

open Finset
open scoped BigOperators

/-! Chern--Fu, arXiv:2508.21318v2, Definition 1.1, Definition 2.1 and
Question 5.5. Labels are `t.val + 1` for `t : Fin n`; rows and columns are
zero based. The fixed map counts columns strictly before the label's row.
The reconstruction is the finite ordered-partition construction of
Claesson--Dukes--Kubitzke, arXiv:1006.1312v2, Section 2 and Theorem 3.
No literature theorem is assumed as a formal premise. -/

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

private theorem pi_bound (P : Coordinates n k) (t : Fin n) : pi P t ≤ t.val := by
  rw [pi_eq_cut]
  have hm : first P (P.row t) ≤ t := by
    by_contra h
    have := (col_lt_iff P t (P.row t)).mpr (lt_of_not_ge h)
    exact (not_le_of_gt this) (P.upper t)
  exact hm

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

end D5.S3.Combinatorics.PartitionMatrix.ChernFuImage
