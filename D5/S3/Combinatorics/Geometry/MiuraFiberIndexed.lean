/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberIndexed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberIndexed
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Simultaneous indexed frozen-line insertions transport every individual extremum. -/

module
public import D5.S3.Combinatorics.Geometry.MiuraCoreStretch
import all D5.S3.Combinatorics.Geometry.MiuraCoreStretch
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Indexed insertions into the actual array, with exact extremum positions. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreExtremum MiuraCoreResidual MiuraCoreReduction
  MiuraCoreRestore MiuraCoreStretch MiuraCoreFrozenSlope MiuraSlabIncidence
open private column_trans from D5.S3.Combinatorics.Geometry.MiuraCoreStretch
open scoped BigOperators
variable {m n : ℕ}

/-- Extra copies at and before an original line shift its last surviving copy. -/
def columnPosition (w : Fin n → ℕ) (j : Fin n) : ℕ :=
  j.val + ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k

private theorem position_lt (w : Fin n → ℕ) (j : Fin n) :
    columnPosition w j < n + ∑ k, w k := by
  have hs : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k) ≤ ∑ k, w k :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have := j.isLt
  unfold columnPosition
  omega

private theorem position_strict (w : Fin n → ℕ) : StrictMono (columnPosition w) := by
  intro j k hjk
  have hs : (∑ l ∈ Finset.univ.filter (fun l : Fin n => l ≤ j), w l) ≤
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => l ≤ k), w l := by
    apply Finset.sum_le_sum_of_subset
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_trans (Finset.mem_filter.mp hl).2 (le_of_lt hjk)⟩
  have hv : j.val < k.val := hjk
  unfold columnPosition
  omega

private theorem increment_position (w v : Fin n → ℕ) (j k : Fin n)
    (hw : ∀ l, w l = v l + if l = j then 1 else 0) :
    columnPosition w k = columnPosition v k + if j ≤ k then 1 else 0 := by
  classical
  simp only [columnPosition, hw, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private theorem increment_total (w v : Fin n → ℕ) (j : Fin n)
    (hw : ∀ l, w l = v l + if l = j then 1 else 0) :
    (∑ l, w l) = (∑ l, v l) + 1 := by
  classical
  simp only [hw, Finset.sum_add_distrib]
  simp

/-- Every extremum retains its original row and cumulative column coordinate. -/
def ColumnExtremaExpansion {N : ℕ} (h : Cell m n → ℤ) (w : Fin n → ℕ)
    (g : Cell m N → ℤ) : Prop :=
  (∀ q, IsStrictLocalMin g q ↔ ∃ p, IsStrictLocalMin h p ∧
    q.1 = p.1 ∧ q.2.val = columnPosition w p.2) ∧
  (∀ q, IsStrictLocalMax g q ↔ ∃ p, IsStrictLocalMax h p ∧
    q.1 = p.1 ∧ q.2.val = columnPosition w p.2)

private theorem expansion_active {N : ℕ} {h : Cell m n → ℤ} {w : Fin n → ℕ}
    {g : Cell m N → ℤ} (he : ColumnExtremaExpansion h w g) (k : Fin N) :
    activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition w j := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · obtain ⟨p, hp, _, hq⟩ := (he.2 (i,k)).mp hi
      exact ⟨p.2, ⟨p.1, Or.inl hp⟩, hq⟩
    · obtain ⟨p, hp, _, hq⟩ := (he.1 (i,k)).mp hi
      exact ⟨p.2, ⟨p.1, Or.inr hp⟩, hq⟩
  · rintro ⟨j, ⟨i, hi | hi⟩, hpos⟩
    · exact ⟨i, Or.inl ((he.2 _).mpr ⟨(i,j), hi, rfl, hpos⟩)⟩
    · exact ⟨i, Or.inr ((he.1 _).mpr ⟨(i,j), hi, rfl, hpos⟩)⟩

private theorem expansion_frozen {N : ℕ} {h : Cell m n → ℤ} {w : Fin n → ℕ}
    {g : Cell m N → ℤ} (he : ColumnExtremaExpansion h w g)
    (hN : N = n + ∑ k, w k) (hg : IsHeight g) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    ∃ k : Fin N, frozenColumn g k ∧ k.val = columnPosition w j := by
  have hleft : 0 < columnPosition w j := by
    have := hj.1
    dsimp [columnPosition]
    omega
  have hright : columnPosition w j + 1 < N := by
    have hs : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k) ≤ ∑ k, w k :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have := hj.2.1
    dsimp [columnPosition]
    omega
  let k : Fin N := ⟨columnPosition w j, by omega⟩
  refine ⟨k, ?_, rfl⟩
  apply (frozenColumn_iff_inactive g hg k hleft hright hm).mpr
  intro hactive
  obtain ⟨l, hl, heq⟩ := (expansion_active he _).mp hactive
  have hjl : j = l := (position_strict w).injective heq
  exact frozenColumn_not_active h j hj (hjl.symm ▸ hl)

private theorem insertion_extrema (g : Cell m N → ℤ) (hg : IsHeight g)
    (hm : 0 < m) (j : Fin N) (hj : frozenColumn g j) :
    let f := stretchColumn g hm j hj
    let j' : Fin (N+1) := ⟨j.val, by have := j.isLt; omega⟩
    (∀ q, IsStrictLocalMin f q ↔ ∃ p, IsStrictLocalMin g p ∧
      q = cellExpand j' p hj.1 (by change j.val + 1 < N + 1; have := hj.2.1; omega)) ∧
    (∀ q, IsStrictLocalMax f q ↔ ∃ p, IsStrictLocalMax g p ∧
      q = cellExpand j' p hj.1 (by change j.val + 1 < N + 1; have := hj.2.1; omega)) := by
  dsimp only
  let f := stretchColumn g hm j hj
  let j' : Fin (N+1) := ⟨j.val, by have := j.isLt; omega⟩
  have hs : SeamSlope g j' hj.1 (by change j.val + 1 < N + 1; have := hj.2.1; omega) (frozenSlope g hm j hj) := by
    intro i
    exact frozenSlope_eq g hg hm j hj i
  have hf : IsHeight f := restoreColumn_isHeight (n := N + 1) g hg j' hj.1 _ _
    (frozenSlope_pm g hg hm j hj)
  have hfr : frozenColumn f j' := restoreColumn_frozen (n := N + 1) g j' hj.1 _ _ hs
  have hc : contractAt f hm j' hfr = g := contractAt_restoreColumn (n := N + 1) g hm j' hj.1 _ _ hs
  constructor
  · intro q
    constructor
    · intro hq
      have hnq : q.2 ≠ j' := by
        intro e
        exact frozenColumn_no_extremum f j' hfr q.1 (by have hx : q = (q.1, j') := Prod.ext rfl e; exact hx ▸ Or.inr hq)
      obtain ⟨p, hp⟩ := cellExpand_surjOn j' hfr.1 hfr.2.1 q hnq
      refine ⟨p, ?_, hp.symm⟩
      rw [← hc]
      exact contractAt_isSLm_of_h_min f hf hm j' hfr p (hp.symm ▸ hq)
    · rintro ⟨p, hp, rfl⟩
      exact h_min_of_contractAt_isSLm f hf hm j' hfr p (hc.symm ▸ hp)
  · intro q
    constructor
    · intro hq
      have hnq : q.2 ≠ j' := by
        intro e
        exact frozenColumn_no_extremum f j' hfr q.1 (by have hx : q = (q.1, j') := Prod.ext rfl e; exact hx ▸ Or.inl hq)
      obtain ⟨p, hp⟩ := cellExpand_surjOn j' hfr.1 hfr.2.1 q hnq
      refine ⟨p, ?_, hp.symm⟩
      rw [← hc]
      exact contractAt_isSLM_of_h_max f hf hm j' hfr p (hp.symm ▸ hq)
    · rintro ⟨p, hp, rfl⟩
      exact h_max_of_contractAt_isSLM f hf hm j' hfr p (hc.symm ▸ hp)

private theorem increment_cell {N : ℕ} (w v : Fin n → ℕ) (j : Fin n)
    (hw : ∀ l, w l = v l + if l = j then 1 else 0)
    (k : Fin N) (hk0 : 0 < k.val) (hk1 : k.val + 1 < N)
    (hkj : k.val = columnPosition v j) (p : Cell m n) (r : Cell m N)
    (hr : r.1 = p.1 ∧ r.2.val = columnPosition v p.2) :
    let k' : Fin (N+1) := ⟨k.val, by have := k.isLt; omega⟩
    (cellExpand k' r hk0 (by change k.val + 1 < N + 1; omega)).1 = p.1 ∧
      (cellExpand k' r hk0 (by change k.val + 1 < N + 1; omega)).2.val = columnPosition w p.2 := by
  dsimp only
  rw [increment_position w v j p.2 hw]
  by_cases hp : p.2 < j
  · have hpos := position_strict v hp
    have hlt : r.2.val < k.val := by omega
    have hnle : ¬ j ≤ p.2 := not_le.mpr hp
    simp only [cellExpand, Fin.val_mk, hlt, ite_true, hnle, ite_false, add_zero]
    exact hr
  · have hle : j ≤ p.2 := le_of_not_gt hp
    have hpos := (position_strict v).monotone hle
    have hnlt : ¬ r.2.val < k.val := by omega
    simp only [cellExpand, Fin.val_mk, hnlt, ite_false, hle, ite_true]
    exact ⟨hr.1, by omega⟩

/-- Every coordinate of the entire finite extra-length vector is simultaneously realized
by one actual normalized array, with exact individual extremum positions. -/
theorem indexed_column_expansion (a b : ℕ) (h : Cell m n → ℤ)
    (hm : 0 < m) (hr : Residual a b h) (w : Fin n → ℕ)
    (hsupport : ∀ j, 0 < w j → frozenColumn h j) :
    ∃ g : Cell m (n + ∑ j, w j) → ℤ,
      Residual a b g ∧ ColumnReduction g h ∧ ColumnExtremaExpansion h w g := by
  classical
  have go : ∀ (S : ℕ) (w : Fin n → ℕ), (∑ j, w j) = S →
      (∀ j, 0 < w j → frozenColumn h j) →
      ∃ (N : ℕ) (g : Cell m N → ℤ), N = n + (∑ j, w j) ∧
        Residual a b g ∧ ColumnReduction g h ∧ ColumnExtremaExpansion h w g := by
    intro S
    induction S using Nat.strong_induction_on with
    | h S ih =>
      intro w hS hs
      by_cases hz : S = 0
      · have hwzero : ∀ j, w j = 0 := by
          intro j
          have hle : w j ≤ ∑ k, w k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          omega
        have hpzero : ∀ j, columnPosition w j = j.val := by simp [columnPosition, hwzero]
        refine ⟨n, h, by simp [hwzero], hr, .refl h, ?_⟩
        constructor <;> intro q <;> constructor
        · intro hq; exact ⟨q, hq, rfl, (hpzero q.2).symm⟩
        · rintro ⟨p, hp, he1, he2⟩
          have he : q = p := Prod.ext he1 (Fin.ext (he2.trans (hpzero p.2)))
          exact he.symm ▸ hp
        · intro hq; exact ⟨q, hq, rfl, (hpzero q.2).symm⟩
        · rintro ⟨p, hp, he1, he2⟩
          have he : q = p := Prod.ext he1 (Fin.ext (he2.trans (hpzero p.2)))
          exact he.symm ▸ hp
      · have hp : 0 < ∑ j, w j := by omega
        obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hp
        let v := Function.update w j (w j - 1)
        have hw : ∀ l, w l = v l + if l = j then 1 else 0 := by
          intro l
          by_cases hl : l = j
          · subst l; simp only [v, Function.update_self, ite_true]; omega
          · simp [v, Function.update_of_ne hl, hl]
        have ht := increment_total w v j hw
        have hvs : (∑ l, v l) < S := by omega
        have hv : ∀ l, 0 < v l → frozenColumn h l := by
          intro l hl
          have := hw l
          exact hs l (by omega)
        obtain ⟨N, g, hN, hg, hred, he⟩ := ih (∑ l, v l) hvs v rfl hv
        obtain ⟨k, hk, hkj⟩ := expansion_frozen he hN hg.1.1 hm j (hs j hj)
        let f := stretchColumn g hm k hk
        have hN' : N + 1 = n + ∑ l, w l := by omega
        have hi := insertion_extrema g hg.1.1 hm k hk
        have hinc := increment_cell (m := m) w v j hw k hk.1 hk.2.1 hkj
        have hposlt : ∀ p : Cell m n, columnPosition v p.2 < N := by
          intro p; rw [hN]; exact position_lt v p.2
        refine ⟨N+1, f, hN', stretchColumn_residual a b g hm k hk hg,
          column_trans (stretchColumn_reduction g hg.1.1 hm k hk) hred, ?_⟩
        constructor
        · intro q
          constructor
          · intro hq
            obtain ⟨r, hr, hqr⟩ := (hi.1 q).mp hq
            obtain ⟨p, hp, hrp⟩ := (he.1 r).mp hr
            refine ⟨p, hp, ?_⟩
            exact hqr.symm ▸ hinc p r hrp
          · rintro ⟨p, hp, hqp⟩
            let r : Cell m N := (p.1, ⟨columnPosition v p.2, hposlt p⟩)
            have hrp : r.1 = p.1 ∧ r.2.val = columnPosition v p.2 := ⟨rfl,rfl⟩
            have hqr := hinc p r hrp
            apply (hi.1 q).mpr
            refine ⟨r, (he.1 r).mpr ⟨p,hp,hrp⟩, ?_⟩
            exact Prod.ext (hqp.1.trans hqr.1.symm) (Fin.ext (hqp.2.trans hqr.2.symm))
        · intro q
          constructor
          · intro hq
            obtain ⟨r, hr, hqr⟩ := (hi.2 q).mp hq
            obtain ⟨p, hp, hrp⟩ := (he.2 r).mp hr
            refine ⟨p, hp, ?_⟩
            exact hqr.symm ▸ hinc p r hrp
          · rintro ⟨p, hp, hqp⟩
            let r : Cell m N := (p.1, ⟨columnPosition v p.2, hposlt p⟩)
            have hrp : r.1 = p.1 ∧ r.2.val = columnPosition v p.2 := ⟨rfl,rfl⟩
            have hqr := hinc p r hrp
            apply (hi.2 q).mpr
            refine ⟨r, (he.2 r).mpr ⟨p,hp,hrp⟩, ?_⟩
            exact Prod.ext (hqp.1.trans hqr.1.symm) (Fin.ext (hqp.2.trans hqr.2.symm))
  obtain ⟨N,g,hN,hg,hred,he⟩ := go (∑ j,w j) w rfl hsupport
  subst N
  exact ⟨g,hg,hred,he⟩

end D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
