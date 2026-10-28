/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberInverse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual reduced cores and occupied line positions recover the entire height function. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberCore
public import D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
import all D5.S3.Combinatorics.Geometry.MiuraCoreNormal
import all D5.S3.Combinatorics.Geometry.MiuraCoreJoint
import all D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
import all D5.S3.Combinatorics.Geometry.MiuraCoreTranspose

/-! Recovery of every actual cell, including all frozen lines. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberInverse
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreExtremum MiuraCoreResidual MiuraCoreNormal MiuraCoreJoint
  MiuraCoreTranspose MiuraSlabIncidence MiuraFiberIndexed MiuraFiberReadback
  MiuraFiberJoint MiuraPolynomialCoreSum MiuraRunCompositions MiuraCoreRestore
  MiuraCanonicalJoint MiuraCanonicalColumns MiuraCoreFrozenSlope
open private normalize_exists from D5.S3.Combinatorics.Geometry.MiuraCoreNormal
open private joint_trans from D5.S3.Combinatorics.Geometry.MiuraCoreJoint
open private slope_after_left from D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
open private transpose_min_iff transpose_max_iff
  from D5.S3.Combinatorics.Geometry.MiuraCoreTranspose
open scoped BigOperators
variable {m n M N : ℕ}

private theorem contract_active (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (k : Fin (n - 1)) :
    activeColumn (contractAt h hm j hj) k ↔
      activeColumn h (cellExpand j (⟨0, hm⟩, k) hj.1 hj.2.1).2 := by
  unfold activeColumn
  apply exists_congr
  intro i
  rw [contractAt_isSLE_iff h hh hm j hj]
  unfold cellExpand
  split_ifs <;> rfl

private theorem contract_rows_active (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (i : Fin m) :
    activeColumn (transposeHeight (contractAt h hm j hj)) i ↔
      activeColumn (transposeHeight h) i := by
  simp only [activeColumn, IsStrictLocalExtremum, transpose_min_iff, transpose_max_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · have hx := h_max_of_contractAt_isSLM h hh hm j hj (i, k) hk
      refine ⟨(cellExpand j (i, k) hj.1 hj.2.1).2, Or.inl ?_⟩
      by_cases he : k.val < j.val <;> simpa [cellExpand, he] using hx
    · have hx := h_min_of_contractAt_isSLm h hh hm j hj (i, k) hk
      refine ⟨(cellExpand j (i, k) hj.1 hj.2.1).2, Or.inr ?_⟩
      by_cases he : k.val < j.val <;> simpa [cellExpand, he] using hx
  · rintro ⟨k, hk | hk⟩
    · have hne : k ≠ j := fun e => frozenColumn_no_extremum h j hj i
        (Or.inl (e ▸ hk))
      obtain ⟨p, hp⟩ := cellExpand_surjOn j hj.1 hj.2.1 (i, k) hne
      have hx := contractAt_isSLM_of_h_max h hh hm j hj p (hp.symm ▸ hk)
      have hi : p.1 = i := by
        have := congrArg Prod.fst hp
        simpa [cellExpand, apply_ite] using this
      exact ⟨p.2, Or.inl (by simpa only [←hi] using hx)⟩
    · have hne : k ≠ j := fun e => frozenColumn_no_extremum h j hj i
        (Or.inr (e ▸ hk))
      obtain ⟨p, hp⟩ := cellExpand_surjOn j hj.1 hj.2.1 (i, k) hne
      have hx := contractAt_isSLm_of_h_min h hh hm j hj p (hp.symm ▸ hk)
      have hi : p.1 = i := by
        have := congrArg Prod.fst hp
        simpa [cellExpand, apply_ite] using this
      exact ⟨p.2, Or.inr (by simpa only [←hi] using hx)⟩

private theorem same_frozen (h g : Cell m n → ℤ) (hh : IsHeight h) (hg : IsHeight g)
    (hm : 0 < m) (ha : ∀ j, activeColumn h j ↔ activeColumn g j)
    (j : Fin n) (hj : frozenColumn h j) : frozenColumn g j := by
  apply (frozenColumn_iff_inactive g hg j hj.1 hj.2.1 hm).mpr
  exact fun hn => frozenColumn_not_active h j hj ((ha j).mpr hn)

private theorem transpose_reduction {h : Cell m n → ℤ} {g : Cell M N → ℤ}
    (hr : JointReduction h g) : JointReduction (transposeHeight h) (transposeHeight g) := by
  induction hr with
  | refl h => exact .refl _
  | column h hm j k hj hk hjk tail ih => exact .row (transposeHeight h) hm j k hj hk hjk ih
  | row h hn i k hi hk hik tail ih => exact .column (transposeHeight h) hn i k hi hk hik ih

private theorem contracted_reduces {a b : ℕ} (h : Cell m n → ℤ)
    (hr : Residual a b h) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (hjk : j.val + 1 = k.val) (f : Cell M N → ℤ)
    (hf : JointReduction h f) (hfc : NoAdjacentFrozen f)
    (hfr : NoAdjacentFrozen (transposeHeight f)) :
    JointReduction (contractAt h (by omega) j hj) f := by
  have hn' : 2 ≤ n - 1 := by have := hj.1; have := hk.2.1; omega
  obtain ⟨P, Q, g, hP, _, hQ, _, hred, hg, hgc, hgr⟩ := normalize_exists a b
    (m + (n - 1)) m (n - 1) (contractAt h (by omega) j hj) rfl hm hn'
      (contractAt_residual a b h (by omega) j hj hr)
  have he := joint_reduced_core_unique hr.1.1 hf
    (.column h (by omega) j k hj hk hjk hred) hfc hfr hgc hgr
  exact Eq.mp (congrArg (fun x : Σ P : ℕ, Σ Q : ℕ, Cell P Q → ℤ =>
    JointReduction (contractAt h (by omega) j hj) x.2.2) he.symm) hred

private theorem restore_equal (h g : Cell m n → ℤ) (hh : IsHeight h) (hg : IsHeight g)
    (hm : 0 < m) (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (gj : frozenColumn g j) (gk : frozenColumn g k) (hjk : j.val + 1 = k.val)
    (he : contractAt h hm j hj = contractAt g hm j gj) : h = g := by
  have hj0 := hj.1
  have hk0 := hk.1
  have hsH := slope_after_left h hh hm j k hj hk (by omega)
  have hsG := slope_after_left g hg hm j k gj gk (by omega)
  have hs : frozenSlope h hm j hj = frozenSlope g hm j gj := by
    have hH := frozenSlope_eq_right h hh hm j hj ⟨0, hm⟩
    have hG := frozenSlope_eq_right g hg hm j gj ⟨0, hm⟩
    have ek : (⟨j.val + 1, hj.2.1⟩ : Fin n) = k := Fin.ext hjk
    have ej : (⟨k.val - 1, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    have hHK : frozenSlope h hm j hj = frozenSlope h hm k hk := by
      unfold frozenSlope at *
      rw [ek] at hH
      rw [ej]
      omega
    have hGK : frozenSlope g hm j gj = frozenSlope g hm k gk := by
      unfold frozenSlope at *
      rw [ek] at hG
      rw [ej]
      omega
    rw [hHK, hGK, ←hsH, ←hsG]
    unfold frozenSlope
    exact congrArg (fun u : Cell m (n - 1) → ℤ =>
      u (⟨0, hm⟩, ⟨k.val - 1, by have := k.isLt; omega⟩) -
      u (⟨0, hm⟩, ⟨k.val - 1 - 1, by have := k.isLt; omega⟩)) he
  rw [←restoreColumn_contractAt h hh hm j hj,
      ←restoreColumn_contractAt g hg hm j gj, he, hs]

private theorem reduced_reduction {h : Cell m n → ℤ} {f : Cell M N → ℤ}
    (hc : NoAdjacentFrozen h) (hr : NoAdjacentFrozen (transposeHeight h))
    (red : JointReduction h f) :
    (⟨m, n, h⟩ : Σ m : ℕ, Σ n : ℕ, Cell m n → ℤ) = ⟨M, N, f⟩ := by
  cases red with
  | refl => rfl
  | column h hm j k hj hk hjk tail => exact (hc ⟨j, k, hjk, hj, hk⟩).elim
  | row h hn i k hi hk hik tail => exact (hr ⟨i, k, hik, hi, hk⟩).elim

/-- A common actual reduced core and the occupied positions on both physical axes
recover all values of the normalized arrays. -/
theorem same_core_same_active_equal (a b : ℕ) (h g : Cell m n → ℤ)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hh : Residual a b h) (hg : Residual a b g)
    (f : Cell M N → ℤ) (hf : NoAdjacentFrozen f)
    (hft : NoAdjacentFrozen (transposeHeight f))
    (hr : JointReduction h f) (gr : JointReduction g f)
    (ha : ∀ j, activeColumn h j ↔ activeColumn g j)
    (hat : ∀ i, activeColumn (transposeHeight h) i ↔ activeColumn (transposeHeight g) i) :
    h = g := by
  classical
  have go : ∀ s m n M N (h g : Cell m n → ℤ) (f : Cell M N → ℤ), m + n = s →
      2 ≤ m → 2 ≤ n → Residual a b h → Residual a b g →
      NoAdjacentFrozen f → NoAdjacentFrozen (transposeHeight f) →
      JointReduction h f → JointReduction g f →
      (∀ j, activeColumn h j ↔ activeColumn g j) →
      (∀ i, activeColumn (transposeHeight h) i ↔ activeColumn (transposeHeight g) i) →
      h = g := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      have column_case : ∀ m n M N (h g : Cell m n → ℤ) (f : Cell M N → ℤ), m + n = s →
          2 ≤ m → 2 ≤ n → Residual a b h → Residual a b g →
          NoAdjacentFrozen f → NoAdjacentFrozen (transposeHeight f) →
          JointReduction h f → JointReduction g f →
          (∀ j, activeColumn h j ↔ activeColumn g j) →
          (∀ i, activeColumn (transposeHeight h) i ↔ activeColumn (transposeHeight g) i) →
          (∃ j k : Fin n, j.val + 1 = k.val ∧ frozenColumn h j ∧ frozenColumn h k) → h = g := by
        intro m n M N h g f hsum hm hn hh hg hf hft hr gr ha hat hc
        obtain ⟨j, k, hjk, hj, hk⟩ := hc
        have gj := same_frozen h g hh.1.1 hg.1.1 (by omega) ha j hj
        have gk := same_frozen h g hh.1.1 hg.1.1 (by omega) ha k hk
        have hn' : 2 ≤ n - 1 := by have := hj.1; have := hk.2.1; omega
        have he := ih (m + (n - 1)) (by omega) m (n - 1) M N
          (contractAt h (by omega) j hj) (contractAt g (by omega) j gj) f rfl hm hn'
          (contractAt_residual a b h (by omega) j hj hh)
          (contractAt_residual a b g (by omega) j gj hg) hf hft
          (contracted_reduces h hh hm hn j k hj hk hjk f hr hf hft)
          (contracted_reduces g hg hm hn j k gj gk hjk f gr hf hft)
          (fun l => (contract_active h hh.1.1 (by omega) j hj l).trans
            ((ha _).trans (contract_active g hg.1.1 (by omega) j gj l).symm))
          (fun i => (contract_rows_active h hh.1.1 (by omega) j hj i).trans
            ((hat i).trans (contract_rows_active g hg.1.1 (by omega) j gj i).symm))
        exact restore_equal h g hh.1.1 hg.1.1 (by omega) j k hj hk gj gk hjk he
      intro m n M N h g f hsum hm hn hh hg hf hft hr gr ha hat
      by_cases hc : ∃ j k : Fin n, j.val + 1 = k.val ∧ frozenColumn h j ∧ frozenColumn h k
      · exact column_case m n M N h g f hsum hm hn hh hg hf hft hr gr ha hat hc
      by_cases ht : ∃ j k : Fin m, j.val + 1 = k.val ∧
          frozenColumn (transposeHeight h) j ∧ frozenColumn (transposeHeight h) k
      · have he := column_case n m N M (transposeHeight h) (transposeHeight g)
          (transposeHeight f) (by omega) hn hm (transpose_residual a b h hh)
          (transpose_residual a b g hg) hft hf (transpose_reduction hr)
          (transpose_reduction gr) hat ha ht
        exact congrArg transposeHeight he
      have gc : NoAdjacentFrozen g := by
        rintro ⟨j, k, hjk, hj, hk⟩
        exact hc ⟨j, k, hjk, same_frozen g h hg.1.1 hh.1.1 (by omega)
          (fun j => (ha j).symm) j hj, same_frozen g h hg.1.1 hh.1.1 (by omega)
          (fun j => (ha j).symm) k hk⟩
      have gt : NoAdjacentFrozen (transposeHeight g) := by
        rintro ⟨j, k, hjk, hj, hk⟩
        exact ht ⟨j, k, hjk, same_frozen _ _ (transpose_isHeight hg.1.1)
          (transpose_isHeight hh.1.1) (by omega) (fun i => (hat i).symm) j hj,
          same_frozen _ _ (transpose_isHeight hg.1.1) (transpose_isHeight hh.1.1)
          (by omega) (fun i => (hat i).symm) k hk⟩
      have he := (reduced_reduction hc ht hr).trans (reduced_reduction gc gt gr).symm
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  exact go (m + n) m n M N h g f rfl hm hn hh hg hf hft hr gr ha hat

end D5.S3.Combinatorics.Geometry.MiuraFiberInverse
