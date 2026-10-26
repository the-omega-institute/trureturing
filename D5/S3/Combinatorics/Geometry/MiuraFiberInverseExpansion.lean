/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every actual joint reduction reads back supported indexed run lengths. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberInverse
import all D5.S3.Combinatorics.Geometry.MiuraFiberInverse
import all D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
import all D5.S3.Combinatorics.Geometry.MiuraFiberReadback
import all D5.S3.Combinatorics.Geometry.MiuraCoreTranspose

/-! Occupied coordinates are transported along the actual signed reduction path. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreExtremum MiuraCoreResidual MiuraCoreNormal MiuraCoreJoint
  MiuraCoreTranspose MiuraSlabIncidence MiuraFiberIndexed MiuraFiberReadback
  MiuraFiberJoint MiuraPolynomialCoreSum MiuraRunCompositions MiuraCoreRestore
  MiuraCanonicalJoint MiuraCanonicalColumns MiuraCoreFrozenSlope MiuraFiberInverse
  MiuraCoreBoundary
open private contract_active contract_rows_active transpose_reduction
  from D5.S3.Combinatorics.Geometry.MiuraFiberInverse
open private position_lt position_strict increment_position increment_total
  from D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
open private adjacent_position from D5.S3.Combinatorics.Geometry.MiuraFiberReadback
open private transpose_min_iff transpose_max_iff
  from D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
open scoped BigOperators
variable {m n M N A B : ℕ}

private theorem insertion_site (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 2 ≤ n) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j → frozenColumn h j) (f : Cell A B → ℤ)
    (hB : B = n + ∑ j, w j)
    (ha : ∀ k, activeColumn f k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition w j)
    (q : Fin B) (hq : ¬ activeColumn f q) (hq0 : 0 < q.val) :
    ∃ t : Fin n, frozenColumn h t ∧
      ∀ l : Fin n, q.val ≤ columnPosition w l ↔ t ≤ l := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : columnPosition w last = n - 1 + ∑ j, w j := by
    have he : Finset.univ.filter (fun k : Fin n => k ≤ last) = Finset.univ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      change k.val ≤ n - 1
      have := k.isLt
      omega
    simp only [columnPosition, he]
    rfl
  let S := Finset.univ.filter (fun t : Fin n => q.val ≤ columnPosition w t)
  have hS : S.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have := q.isLt
    omega
  let t := S.min' hS
  have ht : q.val ≤ columnPosition w t := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hth : ∀ l : Fin n, q.val ≤ columnPosition w l ↔ t ≤ l := by
    intro l
    constructor
    · intro hl
      exact Finset.min'_le S l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
    · intro hl
      exact ht.trans ((position_strict w).monotone hl)
  refine ⟨t, ?_, hth⟩
  by_cases hwt : 0 < w t
  · exact hw t hwt
  have hzero : w t = 0 := by omega
  have h0 : columnPosition w (⟨0, by omega⟩ : Fin n) = 0 := by
    have hw0 : w ⟨0, by omega⟩ = 0 := by
      by_contra hz
      have H := (hw ⟨0, by omega⟩ (Nat.pos_of_ne_zero hz)).1
      change 0 < 0 at H
      omega
    have he : Finset.univ.filter (fun k : Fin n => k ≤ (⟨0, by omega⟩ : Fin n)) = {⟨0, by omega⟩} := by ext k; simp [Fin.le_iff_val_le_val, Fin.ext_iff]
    change 0 + _ = 0
    rw [he, Finset.sum_singleton, hw0]
  have ht0 : 0 < t.val := by
    by_contra he
    have et : t = (⟨0, by omega⟩ : Fin n) := by
      apply Fin.ext
      change t.val = 0
      omega
    rw [et, h0] at ht
    omega
  let prev : Fin n := ⟨t.val - 1, by have := t.isLt; omega⟩
  have hp : columnPosition w prev < q.val := by
    by_contra he
    have hp := (hth prev).mp (by omega)
    change t.val ≤ t.val - 1 at hp
    omega
  have hstep := adjacent_position w prev t (by dsimp [prev]; omega)
  have heq : q.val = columnPosition w t := by omega
  have hta : ¬ activeColumn h t := by
    intro hta
    exact hq ((ha q).mpr ⟨t, hta, heq⟩)
  have hb := inactive_internal h (by omega) (boundary_columns_active h hh hm hn) t hta
  exact inactive_imp_frozenColumn h hh t hb.1 hb.2 hm hta

private theorem lift_column_weights (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 2 ≤ n) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j → frozenColumn h j)
    (g : Cell A B → ℤ) (hg : IsHeight g) (hA : 0 < A)
    (j k : Fin B) (hj : frozenColumn g j) (hk : frozenColumn g k)
    (hjk : j.val + 1 = k.val) (hB : B - 1 = n + ∑ l, w l)
    (ha : ∀ l, activeColumn (contractAt g hA j hj) l ↔
      ∃ t, activeColumn h t ∧ l.val = columnPosition w t) :
    ∃ v : Fin n → ℕ, (∀ t, 0 < v t → frozenColumn h t) ∧ B = n + ∑ t, v t ∧
      ∀ l, activeColumn g l ↔ ∃ t, activeColumn h t ∧ l.val = columnPosition v t := by
  classical
  let q : Fin (B - 1) := ⟨j.val, by have := hk.2.1; omega⟩
  have hq : frozenColumn (contractAt g hA j hj) q := by
    have H := frozen_after_left_deletion g hg hA j k hj hk (by omega)
    convert H using 1
    apply Fin.ext
    dsimp [q]
    omega
  obtain ⟨t, ht, hth⟩ := insertion_site h hh hm hn w hw (contractAt g hA j hj)
    hB ha q (frozenColumn_not_active _ q hq) hj.1
  let v : Fin n → ℕ := fun l => w l + if l = t then 1 else 0
  have hv : ∀ l, v l = w l + if l = t then 1 else 0 := fun _ => rfl
  have htotal := increment_total v w t hv
  have hpos : ∀ l, columnPosition v l = columnPosition w l + if t ≤ l then 1 else 0 :=
    fun l => increment_position v w t l hv
  have hbound : ∀ l, columnPosition w l < B - 1 := by
    intro l; rw [hB]; exact position_lt w l
  let pos : Fin n → Fin (B - 1) := fun l => ⟨columnPosition w l, hbound l⟩
  have hexpand : ∀ l,
      (cellExpand j (⟨0, hA⟩, pos l) hj.1 hj.2.1).2.val = columnPosition v l := by
    intro l
    rw [hpos]
    by_cases he : j.val ≤ columnPosition w l
    · have ht' := (hth l).mp he
      simp only [cellExpand, pos, Fin.val_mk, show ¬ columnPosition w l < j.val by omega,
        ite_false, ht', ite_true]
    · have ht' : ¬ t ≤ l := fun hl => he ((hth l).mpr hl)
      simp only [cellExpand, pos, Fin.val_mk, show columnPosition w l < j.val by omega,
        ite_true, ht', ite_false, add_zero]
  refine ⟨v, ?_, by have := hj.1; have := j.isLt; omega, ?_⟩
  · intro l hl
    by_cases he : l = t
    · exact he.symm ▸ ht
    · apply hw l
      dsimp [v] at hl
      simpa only [he, ite_false, add_zero] using hl
  · intro l
    constructor
    · intro hl
      have hne : l ≠ j := by
        intro he; exact frozenColumn_not_active g j hj (he ▸ hl)
      obtain ⟨p, hp⟩ := cellExpand_surjOn j hj.1 hj.2.1 (⟨0, hA⟩, l) hne
      have hcol : (cellExpand j (⟨0, hA⟩, p.2) hj.1 hj.2.1).2 = l := by
        have H := congrArg Prod.snd hp
        simpa only [cellExpand, apply_ite, Prod.snd] using H
      have hpactive := (contract_active g hg hA j hj p.2).mpr (hcol.symm ▸ hl)
      obtain ⟨u, hu, heq⟩ := (ha p.2).mp hpactive
      have hep : p.2 = pos u := Fin.ext heq
      refine ⟨u, hu, ?_⟩
      rw [hep] at hcol
      exact (congrArg Fin.val hcol).symm.trans (hexpand u)
    · rintro ⟨u, hu, heq⟩
      have hpa := (ha (pos u)).mpr ⟨u, hu, rfl⟩
      have hga := (contract_active g hg hA j hj (pos u)).mp hpa
      have he : (cellExpand j (⟨0, hA⟩, pos u) hj.1 hj.2.1).2 = l :=
        Fin.ext ((hexpand u).trans heq.symm)
      exact he ▸ hga

/-- Every actual reduction path supplies complete supported row and column weights.
The readout is taken from occupied positions of the actual source array. -/
theorem reduction_indexed_active (a b : ℕ) {m n M N : ℕ}
    (g : Cell m n → ℤ) (h : Cell M N → ℤ) (red : JointReduction g h) :
    2 ≤ m → 2 ≤ n → Residual a b g → 2 ≤ M → 2 ≤ N → IsHeight h →
    ∃ (r : Fin M → ℕ) (c : Fin N → ℕ),
      (∀ i, 0 < r i → frozenColumn (transposeHeight h) i) ∧
      (∀ j, 0 < c j → frozenColumn h j) ∧
      m = M + ∑ i, r i ∧ n = N + ∑ j, c j ∧
      (∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition c j) ∧
      (∀ k, activeColumn (transposeHeight g) k ↔
        ∃ i, activeColumn (transposeHeight h) i ∧ k.val = columnPosition r i) := by
  classical
  induction red with
  | refl h =>
    intro hm hn hh _ _ _
    refine ⟨fun _ => 0, fun _ => 0, (by intro i hi; change 0 < 0 at hi; omega), (by intro j hj; change 0 < 0 at hj; omega),
      by simp, by simp, ?_, ?_⟩
    · intro k
      simp only [columnPosition, Finset.sum_const_zero, add_zero]
      constructor
      · intro hk; exact ⟨k, hk, rfl⟩
      · rintro ⟨j, hj, he⟩; exact (Fin.ext he).symm ▸ hj
    · intro k
      simp only [columnPosition, Finset.sum_const_zero, add_zero]
      constructor
      · intro hk; exact ⟨k, hk, rfl⟩
      · rintro ⟨j, hj, he⟩; exact (Fin.ext he).symm ▸ hj
  | column g hpos j k hj hk hjk tail ih =>
    intro hm hn hg hM hN hh
    obtain ⟨r, c, hrs, hcs, hrm, hcn, hca, hra⟩ := ih hm (by have := hj.1; have := hk.2.1; omega)
      (contractAt_residual a b g hpos j hj hg) hM hN hh
    obtain ⟨v, hvs, hvd, hva⟩ := lift_column_weights _ hh (by omega) hN c hcs
      g hg.1.1 hpos j k hj hk hjk hcn hca
    refine ⟨r, v, hrs, hvs, hrm, hvd, hva, ?_⟩
    intro i
    exact (contract_rows_active g hg.1.1 hpos j hj i).symm.trans (hra i)
  | row g hpos j k hj hk hjk tail ih =>
    intro hm hn hg hM hN hh
    obtain ⟨r, c, hrs, hcs, hrm, hcn, hca, hra⟩ := ih (by have := hj.1; have := hk.2.1; omega) hn
      (contractRow_residual a b g hpos j hj hg) hM hN hh
    obtain ⟨v, hvs, hvd, hva⟩ := lift_column_weights (transposeHeight _) (transpose_isHeight hh)
      (by omega) hM r hrs (transposeHeight g) (transpose_isHeight hg.1.1)
      hpos j k hj hk hjk hrm hra
    refine ⟨v, c, hvs, hcs, hvd, hcn, ?_, hva⟩
    intro i
    exact (contract_rows_active (transposeHeight g) (transpose_isHeight hg.1.1)
      hpos j hj i).symm.trans (hca i)

end D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion
