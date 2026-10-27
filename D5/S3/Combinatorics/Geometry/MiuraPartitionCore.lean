/- GID: D5/S3/Combinatorics/Geometry/MiuraPartitionCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraPartitionCore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every large actual residual array belongs to one exact positive-run core. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberCore
public import D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
import all D5.S3.Combinatorics.Geometry.MiuraFiberCore

/-! The actual reduced core retains a frozen line on each physical axis. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraPartitionCore
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreResidual
  MiuraCoreBoundary MiuraCoreContract MiuraCoreJoint MiuraCoreNormal MiuraCoreTranspose
  MiuraCanonicalColumns MiuraCanonicalJoint MiuraPolynomialCoreSum
  MiuraCoreFrozenSlope MiuraSlabIncidence
open private inactive_run_card joint_sides from D5.S3.Combinatorics.Geometry.MiuraFiberCore

private theorem large_frozen {m n : ℕ} (a b : ℕ) (h : Cell m n → ℤ)
    (hm : 0 < m) (hn : 2 ≤ n) (hlarge : a + b < n) (hr : Residual a b h) :
    ∃ j, frozenColumn h j := by
  classical
  have hd : numExtrema h ≤ a + b := by
    simpa only [hr.2.1,hr.2.2.1] using numExtrema_le_split h
  have hcard : (Finset.univ.filter (activeColumn h)).card < (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ,Fintype.card_fin,numActiveColumns] using
      lt_of_le_of_lt ((numActiveColumns_le_numExtrema h).trans hd) hlarge
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hja : ¬activeColumn h j := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hj
  have hb := inactive_internal h (by omega) (boundary_columns_active h hr.1.1 hm hn) j hja
  exact ⟨j,inactive_imp_frozenColumn h hr.1.1 j hb.1 hb.2 hm hja⟩

private theorem joint_frozen_exists {m n M N : ℕ} {h : Cell m n → ℤ}
    {g : Cell M N → ℤ} (red : JointReduction h g) :
    IsHeight h → (∃ j, frozenColumn h j) →
      (∃ i, frozenColumn (transposeHeight h) i) →
      (∃ j, frozenColumn g j) ∧ (∃ i, frozenColumn (transposeHeight g) i) := by
  induction red with
  | refl h => intro _ hc hr; exact ⟨hc,hr⟩
  | column h hm j k hj hk hjk tail ih =>
    intro hh _ hr
    apply ih (contractAt_isHeight h hh hm j hj)
      ⟨_, frozen_after_left_deletion h hh hm j k hj hk (by omega)⟩
    obtain ⟨i,hi⟩ := hr
    exact ⟨i,frozen_row_after_column h hm j hj i hi⟩
  | row h hn i k hi hk hik tail ih =>
    intro hh hc _
    apply ih (transpose_isHeight (contractAt_isHeight (transposeHeight h)
      (transpose_isHeight hh) hn i hi))
    · obtain ⟨j,hj⟩ := hc
      exact ⟨j,frozen_column_after_row h hn i hi j hj⟩
    · exact ⟨_, frozen_after_left_deletion (transposeHeight h) (transpose_isHeight hh)
        hn i k hi hk (by omega)⟩

private theorem reduced_runs_positive {m n : ℕ} (h : Cell m n → ℤ)
    (hh : IsHeight h) (hm : 0 < m) (hn : 2 ≤ n) (hno : NoAdjacentFrozen h)
    (hex : ∃ j, frozenColumn h j) : 1 ≤ numFrozenRuns h := by
  classical
  obtain ⟨j,hj⟩ := hex
  let : Nonempty {j : Fin n // ¬activeColumn h j} := ⟨⟨j,frozenColumn_not_active h j hj⟩⟩
  have hp := Fintype.card_pos (α := {j : Fin n // ¬activeColumn h j})
  rw [inactive_run_card h hh hm hn hno] at hp
  omega

/-- Every original large residual array reduces to a member of the same finite
actual Core family; positivity of both run counts is derived from that array. -/
theorem residual_core_exists {m n : ℕ} (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : 5 ≤ a + b) (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n)
    (h : Cell m n → ℤ) (hr : Residual a b h) :
    ∃ K : Core a b, JointReduction h K.2.2.val ∧
      ∀ sd, AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1,(v.2.val : ℤ) + 1))
        (minima h) (m : ℤ) (n : ℤ) sd ↔
      AllOnSide (fun v : Cell K.1.val K.2.1.val => ((v.1.val : ℤ) + 1,(v.2.val : ℤ) + 1))
        (minima K.2.2.val) (K.1.val : ℤ) (K.2.1.val : ℤ) sd := by
  obtain ⟨M,N,g,hM,hMb,hN,hNb,hred,hg,hgc,hgr⟩ :=
    residual_reduced_joint_core_exists a b ha hb h (by omega) (by omega) hr
  have hc := large_frozen a b h (by omega) (by omega) (by omega) hr
  have hrw := large_frozen a b (transposeHeight h) (by omega) (by omega) (by omega)
    (transpose_residual a b h hr)
  obtain ⟨hcf,hrf⟩ := joint_frozen_exists hred hr.1.1 hc hrw
  have hpC := reduced_runs_positive g hg.1.1 (by omega) hN hgc hcf
  have hpR := reduced_runs_positive (transposeHeight g) (transpose_isHeight hg.1.1)
    (by omega) hM hgr hrf
  let K : Core a b := ⟨⟨M,by omega⟩,⟨N,by omega⟩,
    ⟨g,hM,hN,hg,hgc,hgr,hpR,hpC⟩⟩
  exact ⟨K,hred,joint_sides hred hr.1.1⟩

end D5.S3.Combinatorics.Geometry.MiuraPartitionCore
