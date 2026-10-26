/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberReadback
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberReadback
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual occupied positions uniquely read every indexed frozen-core length. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
public import Mathlib.Order.Preorder.Finite
import all D5.S3.Combinatorics.Geometry.MiuraFiberIndexed

/-! Read every insertion coordinate from the same actual expanded function. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberReadback
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreBoundary
  MiuraCoreFrozenSlope MiuraCoreResidual MiuraCoreNormal MiuraFiberIndexed
open private position_lt position_strict expansion_active
  from D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
open scoped BigOperators
variable {m n M N : ℕ}

private theorem adjacent_position (w : Fin n → ℕ) (j k : Fin n)
    (hjk : j.val + 1 = k.val) :
    columnPosition w k = columnPosition w j + 1 + w k := by
  classical
  have hfilter : Finset.univ.filter (fun l : Fin n => l ≤ k) =
      insert k (Finset.univ.filter (fun l : Fin n => l ≤ j)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hl
      by_cases hlj : l ≤ j
      · exact Or.inr hlj
      · left; apply Fin.ext; have hv : j.val < l.val := lt_of_not_ge hlj
        have hlv : l.val ≤ k.val := hl
        omega
    · rintro (rfl | hl)
      · exact le_rfl
      · have hlv : l.val ≤ j.val := hl
        change l.val ≤ k.val
        omega
  have hknot : k ∉ Finset.univ.filter (fun l : Fin n => l ≤ j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    change j.val < k.val
    omega
  simp only [columnPosition, hfilter, Finset.sum_insert hknot]
  omega

private theorem active_position_eq (h : Cell m n → ℤ) (w v : Fin n → ℕ)
    (g : Cell M N → ℤ) (hNw : N = n + ∑ j, w j) (hNv : N = n + ∑ j, v j)
    (hew : ∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition w j)
    (hev : ∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition v j) :
    ∀ j, activeColumn h j → columnPosition w j = columnPosition v j := by
  classical
  let A := {j : Fin n // activeColumn h j}
  let ew : A ↪o ℕ := OrderEmbedding.ofStrictMono (fun j => columnPosition w j.val)
    (fun _ _ hlt => position_strict w hlt)
  let ev : A ↪o ℕ := OrderEmbedding.ofStrictMono (fun j => columnPosition v j.val)
    (fun _ _ hlt => position_strict v hlt)
  have hrange : Set.range ew = Set.range ev := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨j,hj⟩,rfl⟩
      let k : Fin N := ⟨columnPosition w j, by rw [hNw]; exact position_lt w j⟩
      have ha := (hew k).mpr ⟨j,hj,rfl⟩
      obtain ⟨l,hl,he⟩ := (hev k).mp ha
      exact ⟨⟨l,hl⟩,he.symm⟩
    · rintro _ ⟨⟨j,hj⟩,rfl⟩
      let k : Fin N := ⟨columnPosition v j, by rw [hNv]; exact position_lt v j⟩
      have ha := (hev k).mpr ⟨j,hj,rfl⟩
      obtain ⟨l,hl,he⟩ := (hew k).mp ha
      exact ⟨⟨l,hl⟩,he.symm⟩
  have he : ew = ev := OrderEmbedding.range_eq_iff.mp hrange
  intro j hj
  exact congrArg (fun e : A ↪o ℕ => e ⟨j,hj⟩) he

/-- For an actual reduced core, the complete occupied-position readout determines
all extra lengths, including zero extra copies, without any canonical-core assumption. -/
theorem indexed_column_weights_unique (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 2 ≤ n) (hno : NoAdjacentFrozen h)
    (w v : Fin n → ℕ) (hw : ∀ j, 0 < w j → frozenColumn h j)
    (hv : ∀ j, 0 < v j → frozenColumn h j)
    (g : Cell M N → ℤ) (hNw : N = n + ∑ j, w j) (hNv : N = n + ∑ j, v j)
    (hew : ∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition w j)
    (hev : ∀ k, activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition v j) : w = v := by
  classical
  have hends := boundary_columns_active h hh hm hn
  have hif : ∀ j, ¬ activeColumn h j → frozenColumn h j := by
    intro j hj
    have hb := inactive_internal h (by omega) hends j hj
    exact inactive_imp_frozenColumn h hh j hb.1 hb.2 hm hj
  have hzero : ∀ (z : Fin n → ℕ), (∀ j, 0 < z j → frozenColumn h j) →
      ∀ j, activeColumn h j → z j = 0 := by
    intro z hz j hj
    by_contra hne
    exact frozenColumn_not_active h j (hz j (Nat.pos_of_ne_zero hne)) hj
  have hposeq := active_position_eq h w v g hNw hNv hew hev
  funext j
  by_cases hj : activeColumn h j
  · rw [hzero w hw j hj,hzero v hv j hj]
  · have hfr := hif j hj
    let l : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
    let r : Fin n := ⟨j.val+1,hfr.2.1⟩
    have hlj : l.val + 1 = j.val := by dsimp [l]; have := hfr.1; omega
    have hjr : j.val + 1 = r.val := rfl
    have hl : activeColumn h l := by
      by_contra hln
      exact hno ⟨l,j,hlj,hif l hln,hfr⟩
    have hr : activeColumn h r := by
      by_contra hrn
      exact hno ⟨j,r,hjr,hfr,hif r hrn⟩
    have hlpos := hposeq l hl
    have hrpos := hposeq r hr
    have hwl := adjacent_position w l j hlj
    have hwr := adjacent_position w j r hjr
    have hvl := adjacent_position v l j hlj
    have hvr := adjacent_position v j r hjr
    have hwzero := hzero w hw r hr
    have hvzero := hzero v hv r hr
    omega

end D5.S3.Combinatorics.Geometry.MiuraFiberReadback
