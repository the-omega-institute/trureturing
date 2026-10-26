/- GID: D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCanonicalJoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every joint irreducible reduction has the same actual rectangle and function. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
public import Mathlib.Logic.Relation

/-! Confluence of the actual signed deletions, without identifying different arrays. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreContract MiuraCoreCellExpand
  MiuraCoreJoint MiuraCoreNormal MiuraSlabIncidence MiuraCanonicalColumns
open Relation

private abbrev Rectangle := Σ m : ℕ, Σ n : ℕ, Cell m n → ℤ
private def pack {m n : ℕ} (h : Cell m n → ℤ) : Rectangle := ⟨m, n, h⟩

private inductive Deletion : Rectangle → Rectangle → Prop where
  | column {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
      (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
      (hjk : j.val + 1 = k.val) : Deletion (pack h) (pack (contractAt h hm j hj))
  | row {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h) (hn : 0 < n)
      (i k : Fin m) (hi : frozenColumn (transposeHeight h) i)
      (hk : frozenColumn (transposeHeight h) k) (hik : i.val + 1 = k.val) :
      Deletion (pack h) (pack (contractRow h hn i hi))

private def swap (x : Rectangle) : Rectangle := ⟨x.2.1, x.1, transposeHeight x.2.2⟩

private theorem transpose_deletion {x y : Rectangle} (h : Deletion x y) :
    Deletion (swap x) (swap y) := by
  cases h with
  | column h hh hm j k hj hk hjk =>
    exact .row (transposeHeight h) (transpose_isHeight hh) hm j k hj hk hjk
  | row h hh hn i k hi hk hik =>
    exact .column (transposeHeight h) (transpose_isHeight hh) hn i k hi hk hik

private theorem transpose_refl {x y : Rectangle} (h : ReflGen Deletion x y) :
    ReflGen Deletion (swap x) (swap y) := by
  cases h with
  | refl => exact .refl
  | single h => exact .single (transpose_deletion h)

private theorem column_diamond_lt {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (j k l t : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (hl : frozenColumn h l) (ht : frozenColumn h t)
    (hjk : j.val + 1 = k.val) (hlt : l.val + 1 = t.val) (hjl : j.val < l.val) :
    ∃ w, ReflGen Deletion (pack (contractAt h hm j hj)) w ∧
      ReflGen Deletion (pack (contractAt h hm l hl)) w := by
  by_cases he : j.val + 1 = l.val
  · have hab := adjacent_deletions_equal h hh hm j l hj hl he
    refine ⟨pack (contractAt h hm j hj), .refl, ?_⟩
    rw [hab]
  · have hkl : k.val < l.val := by omega
    let l' : Fin (n - 1) := ⟨l.val - 1, by have := l.isLt; omega⟩
    let t' : Fin (n - 1) := ⟨t.val - 1, by have := t.isLt; omega⟩
    let j' : Fin (n - 1) := ⟨j.val, by have := hl.2.1; omega⟩
    let k' : Fin (n - 1) := ⟨k.val, by have := hl.2.1; omega⟩
    have hl' : frozenColumn (contractAt h hm j hj) l' :=
      frozen_after_left_deletion h hh hm j l hj hl hjl
    have ht' : frozenColumn (contractAt h hm j hj) t' :=
      frozen_after_left_deletion h hh hm j t hj ht (by omega)
    have hj' : frozenColumn (contractAt h hm l hl) j' :=
      frozen_after_right_deletion h hh hm l j hl hj hjl
    have hk' : frozenColumn (contractAt h hm l hl) k' :=
      frozen_after_right_deletion h hh hm l k hl hk hkl
    refine ⟨pack (contractAt (contractAt h hm j hj) hm l' hl'), ?_, ?_⟩
    · exact .single (.column _ (contractAt_isHeight h hh hm j hj) hm l' t' hl' ht'
        (by dsimp [l', t']; have := hl.1; omega))
    · rw [separated_deletions_commute h hh hm j l hj hl hjl]
      exact .single (.column _ (contractAt_isHeight h hh hm l hl) hm j' k' hj' hk'
        (by dsimp [j', k']; omega))

private theorem column_diamond {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (j k l t : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (hl : frozenColumn h l) (ht : frozenColumn h t)
    (hjk : j.val + 1 = k.val) (hlt : l.val + 1 = t.val) :
    ∃ w, ReflGen Deletion (pack (contractAt h hm j hj)) w ∧
      ReflGen Deletion (pack (contractAt h hm l hl)) w := by
  rcases lt_trichotomy j.val l.val with hlt' | he | hgt
  · exact column_diamond_lt h hh hm j k l t hj hk hl ht hjk hlt hlt'
  · have ej : j = l := Fin.ext he
    subst l
    exact ⟨pack (contractAt h hm j hj), .refl, .refl⟩
  · obtain ⟨w, hlw, hjw⟩ := column_diamond_lt h hh hm l t j k hl ht hj hk hlt hjk hgt
    exact ⟨w, hjw, hlw⟩

private theorem mixed_diamond {m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 0 < n)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (hjk : j.val + 1 = k.val) (i l : Fin m)
    (hi : frozenColumn (transposeHeight h) i) (hl : frozenColumn (transposeHeight h) l)
    (hil : i.val + 1 = l.val) :
    ∃ w, ReflGen Deletion (pack (contractAt h hm j hj)) w ∧
      ReflGen Deletion (pack (contractRow h hn i hi)) w := by
  have hn' : 0 < n - 1 := by have := hj.1; have := hj.2.1; omega
  have hm' : 0 < m - 1 := by have := hi.1; have := hi.2.1; omega
  refine ⟨pack (contractRow (contractAt h hm j hj) hn' i
    (frozen_row_after_column h hm j hj i hi)), ?_, ?_⟩
  · exact .single (.row _ (contractAt_isHeight h hh hm j hj) hn' i l
      (frozen_row_after_column h hm j hj i hi)
      (frozen_row_after_column h hm j hj l hl) hil)
  · rw [← contract_row_column_commute h hm hn i hi j hj]
    exact .single (.column _
      (transpose_isHeight (contractAt_isHeight _ (transpose_isHeight hh) hn i hi))
      hm' j k (frozen_column_after_row h hn i hi j hj)
      (frozen_column_after_row h hn i hi k hk) hjk)

private theorem deletion_diamond (x y z : Rectangle) (hxy : Deletion x y)
    (hxz : Deletion x z) :
    ∃ w, ReflGen Deletion y w ∧ ReflGen Deletion z w := by
  cases hxy with
  | column h hh hm j k hj hk hjk =>
    cases hxz with
    | column _ _ _ l t hl ht hlt =>
      exact column_diamond h hh hm j k l t hj hk hl ht hjk hlt
    | row _ _ hn i l hi hl hil =>
      exact mixed_diamond h hh hm hn j k hj hk hjk i l hi hl hil
  | row h hh hn i l hi hl hil =>
    cases hxz with
    | column _ _ hm j k hj hk hjk =>
      obtain ⟨w, hyw, hzw⟩ := mixed_diamond h hh hm hn j k hj hk hjk i l hi hl hil
      exact ⟨w, hzw, hyw⟩
    | row _ _ _ j k hj hk hjk =>
      obtain ⟨w, hyw, hzw⟩ := column_diamond (transposeHeight h) (transpose_isHeight hh)
        hn i l j k hi hl hj hk hil hjk
      exact ⟨swap w, transpose_refl hyw, transpose_refl hzw⟩

private theorem reduction_path {m n M N : ℕ} {h : Cell m n → ℤ} {g : Cell M N → ℤ}
    (hg : JointReduction h g) (hh : IsHeight h) : ReflTransGen Deletion (pack h) (pack g) := by
  induction hg with
  | refl h => exact .refl
  | column h hm j k hj hk hjk tail ih =>
    exact (ih (contractAt_isHeight h hh hm j hj)).head (.column h hh hm j k hj hk hjk)
  | row h hn i k hi hk hik tail ih =>
    exact (ih (transpose_isHeight (contractAt_isHeight _ (transpose_isHeight hh) hn i hi))).head
      (.row h hh hn i k hi hk hik)

private theorem reduced_path_eq {m n : ℕ} {h : Cell m n → ℤ}
    (hc : NoAdjacentFrozen h) (hr : NoAdjacentFrozen (transposeHeight h))
    {y : Rectangle} (hy : ReflTransGen Deletion (pack h) y) : pack h = y := by
  rcases hy.cases_head with he | ⟨z, hz, _⟩
  · exact he
  · cases hz with
    | column _ _ _ j k hj hk hjk => exact (hc ⟨j, k, hjk, hj, hk⟩).elim
    | row _ _ _ i k hi hk hik => exact (hr ⟨i, k, hik, hi, hk⟩).elim

/-- Arbitrary legal choices on the same height array have one actual reduced endpoint. -/
theorem joint_reduced_core_unique {m n M N P Q : ℕ}
    {h : Cell m n → ℤ} (hh : IsHeight h)
    {g : Cell M N → ℤ} {f : Cell P Q → ℤ}
    (hg : JointReduction h g) (hf : JointReduction h f)
    (hgc : NoAdjacentFrozen g) (hgr : NoAdjacentFrozen (transposeHeight g))
    (hfc : NoAdjacentFrozen f) (hfr : NoAdjacentFrozen (transposeHeight f)) :
    (⟨M, N, g⟩ : Σ M : ℕ, Σ N : ℕ, Cell M N → ℤ) = ⟨P, Q, f⟩ := by
  have diamond : ∀ x y z, Deletion x y → Deletion x z →
      ∃ w, ReflGen Deletion y w ∧ ReflTransGen Deletion z w := by
    intro x y z hxy hxz
    obtain ⟨w, hyw, hzw⟩ := deletion_diamond x y z hxy hxz
    refine ⟨w, hyw, ?_⟩
    cases hzw with
    | refl => exact .refl
    | single hz => exact .single hz
  obtain ⟨w, hgw, hfw⟩ := Relation.church_rosser diamond
    (reduction_path hg hh) (reduction_path hf hh)
  exact (reduced_path_eq hgc hgr hgw).trans (reduced_path_eq hfc hfr hfw).symm

end D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
