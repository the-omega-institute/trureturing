/- GID: D5/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Chinese remainder coordinates identify the pentagonal-prism square complement with a ten-cycle. -/
import D5.S3.Combinatorics.Graph.Walks.BinaryRungSpectrum
import D5.S3.Combinatorics.Graph.Walks.PowerSpectrumStructure
import Mathlib.Algebra.Group.Units.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CubicCirculant
open SimpleGraph
open WellCoveredPowerCliqueProduct (power)
noncomputable section

/-- The vertex `j` maps to `(2j mod 5, j mod 2)`, with bijectivity supplied by CRT. -/
def pentagonSquareEquiv : Fin 10 ≃ Fin 5 × ZMod 2 :=
  let u : (ZMod 5)ˣ := ZMod.unitOfCoprime 2 (by norm_num)
  ((ZMod.finEquiv 10).toEquiv.trans
      (ZMod.chineseRemainder (show Nat.Coprime 5 2 from by norm_num)).toEquiv).trans
    (((Units.mulLeft u).prodCongr (Equiv.refl (ZMod 2))).trans
      ((ZMod.finEquiv 5).symm.toEquiv.prodCongr (Equiv.refl (ZMod 2))))

private theorem pentagonSquareEquiv_coords (j : Fin 10) :
    (pentagonSquareEquiv j).1.val = (2*j.val)%5 ∧
      (pentagonSquareEquiv j).2.val = j.val%2 := by
  constructor
  · change (((2 : ZMod 5)*(j.val : ZMod 5)).val) = (2*j.val)%5
    rw [ZMod.val_mul,ZMod.val_two_eq_two_mod,ZMod.val_natCast]
    exact (Nat.mul_mod 2 j.val 5).symm
  · change (j.val : ZMod 2).val = j.val%2
    exact ZMod.val_natCast 2 j.val

/-- Actual distance-two nonedges of the prism form the ten-cycle in explicit CRT coordinates. -/
def pentagon_square_complement_iso :
    cycleGraph 10 ≃g (power ((cycleGraph 5) □ (⊤ : SimpleGraph (ZMod 2))) 2)ᶜ where
  toEquiv := pentagonSquareEquiv
  map_rel_iff' := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hci := pentagonSquareEquiv_coords i
    have hcj := pentagonSquareEquiv_coords j
    have hc : (cycleGraph 5).Connected := connected_cycleGraph_add_one
    have hd := WellCoveredPowerCliqueProduct.distance_cliqueProduct hc
      (pentagonSquareEquiv i) (pentagonSquareEquiv j)
    have hlabel : (pentagonSquareEquiv i).2=(pentagonSquareEquiv j).2 ↔ i.val%2=j.val%2 := by
      constructor
      · intro h
        have hh := congrArg ZMod.val h
        simpa only [hci.2,hcj.2] using hh
      · intro h
        apply ZMod.val_injective
        simpa only [hci.2,hcj.2] using h
    have hd' : (((cycleGraph 5) □ (⊤ : SimpleGraph (ZMod 2))).dist
        (pentagonSquareEquiv i) (pentagonSquareEquiv j)) =
        min (Nat.dist ((2*i.val)%5) ((2*j.val)%5))
          (5-Nat.dist ((2*i.val)%5) ((2*j.val)%5)) +
          (if i.val%2=j.val%2 then 0 else 1) := by
      calc
        _ = (cycleGraph 5).dist (pentagonSquareEquiv i).1 (pentagonSquareEquiv j).1 +
            (if (pentagonSquareEquiv i).2=(pentagonSquareEquiv j).2 then 0 else 1) := hd
        _ = _ := by
          rw [MatchingCliqueCycle.cycle_distance 2]
          simp only [WellCoveredPowerCliqueProduct.cycleMetric,hlabel,hci.1,hcj.1]
    change (pentagonSquareEquiv i ≠ pentagonSquareEquiv j ∧
      ¬ (pentagonSquareEquiv i ≠ pentagonSquareEquiv j ∧
        (((cycleGraph 5) □ (⊤ : SimpleGraph (ZMod 2))).dist
          (pentagonSquareEquiv i) (pentagonSquareEquiv j) ≤ 2))) ↔ (cycleGraph 10).Adj i j
    simp only [ne_eq,pentagonSquareEquiv.injective.eq_iff,hd',Nat.dist,
      cycleGraph_adj,sub_eq_iff_eq_add',Fin.ext_iff,Fin.val_add,Fin.val_one]
    clear hd hd' hlabel hci hcj hc
    fin_cases i <;> fin_cases j <;> norm_num

end
end CubicCirculant
