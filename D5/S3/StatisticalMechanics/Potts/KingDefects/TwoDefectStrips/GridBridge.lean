/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Row-list bond sums for the literal king grid. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers of the settlement on the live path of HardinA229752.result)
defects_rows: proof_shape=content; consumers=literal_bridge
literal_bridge: proof_shape=content; consumers=HardinA229752.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Row-list costs split into horizontal and between-row sums. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

theorem defects_rows {q k : ℕ} (H V : Finset (Fin k × Fin k)) (n : ℕ)
    (f : Fin (n + 1) → Row q k) :
    defects H V (List.ofFn f) =
      (∑ i, bondDefects H (f i) (f i)) +
      ∑ i : Fin n, bondDefects V (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ, defects, tailDefects]
  | succ n ih =>
    have h := ih (Fin.tail f)
    rw [List.ofFn_succ] at h
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [defects, tailDefects] at h ⊢
    simp only [Fin.tail, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
      Fin.castSucc_zero, Fin.succ_castSucc] at h ⊢
    omega

set_option backward.isDefEq.respectTransparency false in
theorem literal_bridge {k : ℕ} (H V : Finset (Fin k × Fin k))
    (hH : ∀ r : Row 4 k, bondDefects H r r =
      ∑ j : Fin (k-1), if r (KingGrid.lo j) = r (KingGrid.hi j) then 1 else 0)
    (hV : ∀ r t : Row 4 k, bondDefects V r t =
      (∑ j, if r j = t j then 1 else 0) +
      (∑ j : Fin (k-1), if r (KingGrid.lo j) = t (KingGrid.hi j) then 1 else 0) +
      ∑ j : Fin (k-1), if r (KingGrid.hi j) = t (KingGrid.lo j) then 1 else 0)
    (n : ℕ) : literalCount (q := 4) H V 2 (n+1) = KingTwoGrid.L (n+1) k := by
  classical
  have hs (g : Fin (n+1) → Fin (n+1) → ℕ) :
      (∑ i : Fin (n+1-1), g (KingGrid.lo i) (KingGrid.hi i)) =
      ∑ i : Fin n, g i.castSucc i.succ := by
    let E : Fin (n+1-1) ≃ Fin n := finCongr (by omega)
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hc (f : KingGrid.Cell (n+1) k → Fin 4) :
      defects H V (List.ofFn fun i j => f (i,j)) =
        (Finset.univ.filter fun e : KingGrid.Edge (n+1) k => KingGrid.mono f e).card := by
    rw [defects_rows]
    simp_rw [hH, hV]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, KingGrid.sum_edges]
    dsimp only [KingGrid.mono, KingGrid.end0, KingGrid.end1]
    simp only [Finset.sum_add_distrib]
    rw [hs (fun x y => ∑ j, if f (x,j) = f (y,j) then 1 else 0),
      hs (fun x y => ∑ j : Fin (k-1),
        if f (x,KingGrid.lo j) = f (y,KingGrid.hi j) then 1 else 0),
      hs (fun x y => ∑ j : Fin (k-1),
        if f (x,KingGrid.hi j) = f (y,KingGrid.lo j) then 1 else 0)]
    simp only [add_assoc]
  unfold literalCount KingTwoGrid.L
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hc]
  rfl

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
