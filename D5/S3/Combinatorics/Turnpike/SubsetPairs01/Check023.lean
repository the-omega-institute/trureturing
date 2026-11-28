/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs01/Check023
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs01.Check016
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow023_01
def τ : Triangle 7 := ⟨(0,2,3),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4}
      [((4,11,3),19)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5}
      [((5,10,3),13)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5}
      [((5,10,3),13), ((4,11,3),6)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6}
      [((6,9,3),12)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6}
      [((6,9,3),12), ((4,11,3),7)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6}
      [((6,9,3),12), ((5,10,3),7)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6}
      [((6,9,3),12), ((5,10,3),7)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7}
      [((7,8,3),2), ((7,11,6),14)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,7}
      [((7,8,3),2), ((4,11,3),17), ((7,11,6),6)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7}
      [((7,8,3),2), ((5,10,3),13), ((7,11,6),14)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,7}
      [((7,8,3),2), ((5,10,3),13), ((4,11,3),4), ((7,11,6),14)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7}
      [((7,8,3),2), ((6,9,3),12), ((7,11,6),14)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,7}
      [((7,8,3),2), ((6,9,3),12), ((4,11,3),5), ((7,11,6),14)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7}
      [((7,8,3),2), ((6,9,3),12), ((5,10,3),5), ((7,11,6),14)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,7}
      [((7,8,3),2), ((6,9,3),12), ((5,10,3),5), ((7,11,6),14)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9}
      [((9,9,6),12), ((9,11,8),14)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,9}
      [((9,9,6),12), ((4,11,3),19), ((9,11,8),4)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,9}
      [((9,9,6),12), ((5,10,3),13), ((9,11,8),14)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,9}
      [((9,9,6),12), ((5,10,3),13), ((4,11,3),6), ((9,11,8),14)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9}
      [((6,9,3),12), ((9,11,8),14)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,9}
      [((6,9,3),10), ((9,9,6),2), ((4,11,3),9), ((9,11,8),14)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,9}
      [((6,9,3),6), ((9,9,6),6), ((5,10,3),13), ((9,11,8),14)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,9}
      [((9,9,6),12), ((5,10,3),13), ((4,11,3),6), ((9,11,8),14)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9}
      [((7,8,3),2), ((9,9,6),12), ((7,11,6),2), ((9,11,8),14)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,7,9}
      [((7,8,3),2), ((9,9,6),12), ((4,11,3),17), ((7,11,6),2), ((9,11,8),4)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7,9}
      [((7,8,3),2), ((9,9,6),12), ((5,10,3),13), ((7,11,6),2), ((9,11,8),14)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,7,9}
      [((7,8,3),2), ((9,9,6),12), ((5,10,3),13), ((4,11,3),4), ((7,11,6),2), ((9,11,8),14)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9}
      [((7,8,3),2), ((6,9,3),12), ((7,11,6),14), ((9,11,8),9)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,7,9}
      [((7,8,3),2), ((6,9,3),12), ((4,11,3),5), ((7,11,6),14), ((9,11,8),4)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7,9}
      [((7,8,3),2), ((6,9,3),7), ((9,9,6),5), ((5,10,3),10), ((7,11,6),9), ((9,11,8),14)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,7,9}
      [((7,8,3),2), ((6,9,3),7), ((9,9,6),5), ((5,10,3),10), ((7,11,6),9), ((9,11,8),14)] := by
  decide +kernel
private theorem case_32 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {10}
      [((10,8,6),2), ((10,10,8),13), ((10,11,9),3)] := by
  decide +kernel
private theorem case_33 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,10}
      [((10,8,6),2), ((10,10,8),13), ((4,11,3),19), ((10,11,9),3)] := by
  decide +kernel
private theorem case_34 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,10}
      [((10,8,6),2), ((5,10,3),13), ((10,11,9),3)] := by
  decide +kernel
private theorem case_35 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,10}
      [((10,8,6),2), ((10,10,8),13), ((4,11,3),19), ((10,11,9),3)] := by
  decide +kernel
private theorem case_36 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,10}
      [((10,8,6),2), ((6,9,3),12), ((10,10,8),13), ((10,11,9),3)] := by
  decide +kernel
private theorem case_37 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,10}
      [((10,8,6),2), ((6,9,3),12), ((10,10,8),13), ((4,11,3),7), ((10,11,9),3)] := by
  decide +kernel
private theorem case_38 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,10}
      [((10,8,6),2), ((6,9,3),12), ((5,10,3),7), ((10,10,8),6), ((10,11,9),3)] := by
  decide +kernel
private theorem case_39 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,10}
      [((10,8,6),2), ((6,9,3),12), ((10,10,8),13), ((4,11,3),7), ((10,11,9),3)] := by
  decide +kernel
private theorem case_40 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,10}
      [((7,8,3),2), ((10,10,8),13), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_41 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,7,10}
      [((7,8,3),2), ((10,10,8),13), ((4,11,3),17), ((7,11,6),6)] := by
  decide +kernel
private theorem case_42 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7,10}
      [((7,8,3),2), ((5,10,3),13), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_43 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,7,10}
      [((7,8,3),2), ((5,10,3),11), ((10,10,8),2), ((4,11,3),6), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_44 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,10}
      [((7,8,3),2), ((6,9,3),12), ((10,10,8),13), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_45 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,7,10}
      [((7,8,3),2), ((6,9,3),12), ((10,10,8),13), ((4,11,3),5), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_46 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7,10}
      [((7,8,3),2), ((6,9,3),12), ((5,10,3),5), ((10,10,8),8), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_47 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,7,10}
      [((7,8,3),2), ((6,9,3),12), ((10,10,8),13), ((4,11,3),5), ((7,11,6),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_48 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9,10}
      [((10,8,6),2), ((9,9,6),12), ((10,10,8),13), ((9,11,8),1), ((10,11,9),3)] := by
  decide +kernel
private theorem case_49 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,9,10}
      [((10,8,6),2),
       ((9,9,6),12),
       ((10,10,8),13),
       ((4,11,3),19),
       ((9,11,8),1),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_50 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,9,10}
      [((10,8,6),2), ((9,9,6),12), ((5,10,3),13), ((9,11,8),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_51 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,9,10}
      [((10,8,6),2), ((9,9,6),12), ((5,10,3),13), ((4,11,3),6), ((9,11,8),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_52 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9,10}
      [((10,8,6),2), ((6,9,3),12), ((10,10,8),13), ((9,11,8),1), ((10,11,9),3)] := by
  decide +kernel
private theorem case_53 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,9,10}
      [((10,8,6),2),
       ((9,9,6),12),
       ((10,10,8),13),
       ((4,11,3),19),
       ((9,11,8),1),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_54 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,9,10}
      [((10,8,6),2), ((6,9,3),6), ((9,9,6),6), ((5,10,3),13), ((9,11,8),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_55 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,9,10}
      [((10,8,6),2),
       ((9,9,6),12),
       ((5,10,3),7),
       ((10,10,8),6),
       ((4,11,3),12),
       ((9,11,8),8),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_56 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9,10}
      [((7,8,3),2), ((9,9,6),12), ((10,10,8),13), ((7,11,6),2), ((9,11,8),1), ((10,11,9),3)] := by
  decide +kernel
private theorem case_57 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,7,9,10}
      [((7,8,3),2),
       ((9,9,6),12),
       ((10,10,8),13),
       ((4,11,3),17),
       ((7,11,6),2),
       ((9,11,8),1),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_58 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7,9,10}
      [((7,8,3),2), ((9,9,6),12), ((5,10,3),13), ((7,11,6),2), ((9,11,8),14), ((10,11,9),3)] := by
  decide +kernel
private theorem case_59 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,7,9,10}
      [((7,8,3),2),
       ((9,9,6),12),
       ((5,10,3),13),
       ((4,11,3),4),
       ((7,11,6),2),
       ((9,11,8),14),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_60 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9,10}
      [((7,8,3),2), ((6,9,3),12), ((10,10,8),13), ((7,11,6),14), ((9,11,8),1), ((10,11,9),3)] := by
  decide +kernel
private theorem case_61 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,6,7,9,10}
      [((7,8,3),2),
       ((6,9,3),12),
       ((10,10,8),13),
       ((4,11,3),5),
       ((7,11,6),14),
       ((9,11,8),1),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_62 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7,9,10}
      [((7,8,3),2),
       ((6,9,3),12),
       ((5,10,3),5),
       ((10,10,8),8),
       ((7,11,6),14),
       ((9,11,8),6),
       ((10,11,9),3)] := by
  decide +kernel
private theorem case_63 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {4,5,6,7,9,10}
      [((7,8,3),2),
       ((6,9,3),12),
       ((5,10,3),5),
       ((10,10,8),8),
       ((7,11,6),14),
       ((9,11,8),6),
       ((10,11,9),3)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 1 2 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {4},
       {5},
       {4,5},
       {6},
       {4,6},
       {5,6},
       {4,5,6},
       {7},
       {4,7},
       {5,7},
       {4,5,7},
       {6,7},
       {4,6,7},
       {5,6,7},
       {4,5,6,7},
       {9},
       {4,9},
       {5,9},
       {4,5,9},
       {6,9},
       {4,6,9},
       {5,6,9},
       {4,5,6,9},
       {7,9},
       {4,7,9},
       {5,7,9},
       {4,5,7,9},
       {6,7,9},
       {4,6,7,9},
       {5,6,7,9},
       {4,5,6,7,9},
       {10},
       {4,10},
       {5,10},
       {4,5,10},
       {6,10},
       {4,6,10},
       {5,6,10},
       {4,5,6,10},
       {7,10},
       {4,7,10},
       {5,7,10},
       {4,5,7,10},
       {6,7,10},
       {4,6,7,10},
       {5,6,7,10},
       {4,5,6,7,10},
       {9,10},
       {4,9,10},
       {5,9,10},
       {4,5,9,10},
       {6,9,10},
       {4,6,9,10},
       {5,6,9,10},
       {4,5,6,9,10},
       {7,9,10},
       {4,7,9,10},
       {5,7,9,10},
       {4,5,7,9,10},
       {6,7,9,10},
       {4,6,7,9,10},
       {5,6,7,9,10},
       {4,5,6,7,9,10}} := by decide +kernel
  rw [cover] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst U; exact ⟨_, case_0⟩
  · subst U; exact ⟨_, case_1⟩
  · subst U; exact ⟨_, case_2⟩
  · subst U; exact ⟨_, case_3⟩
  · subst U; exact ⟨_, case_4⟩
  · subst U; exact ⟨_, case_5⟩
  · subst U; exact ⟨_, case_6⟩
  · subst U; exact ⟨_, case_7⟩
  · subst U; exact ⟨_, case_8⟩
  · subst U; exact ⟨_, case_9⟩
  · subst U; exact ⟨_, case_10⟩
  · subst U; exact ⟨_, case_11⟩
  · subst U; exact ⟨_, case_12⟩
  · subst U; exact ⟨_, case_13⟩
  · subst U; exact ⟨_, case_14⟩
  · subst U; exact ⟨_, case_15⟩
  · subst U; exact ⟨_, case_16⟩
  · subst U; exact ⟨_, case_17⟩
  · subst U; exact ⟨_, case_18⟩
  · subst U; exact ⟨_, case_19⟩
  · subst U; exact ⟨_, case_20⟩
  · subst U; exact ⟨_, case_21⟩
  · subst U; exact ⟨_, case_22⟩
  · subst U; exact ⟨_, case_23⟩
  · subst U; exact ⟨_, case_24⟩
  · subst U; exact ⟨_, case_25⟩
  · subst U; exact ⟨_, case_26⟩
  · subst U; exact ⟨_, case_27⟩
  · subst U; exact ⟨_, case_28⟩
  · subst U; exact ⟨_, case_29⟩
  · subst U; exact ⟨_, case_30⟩
  · subst U; exact ⟨_, case_31⟩
  · subst U; exact ⟨_, case_32⟩
  · subst U; exact ⟨_, case_33⟩
  · subst U; exact ⟨_, case_34⟩
  · subst U; exact ⟨_, case_35⟩
  · subst U; exact ⟨_, case_36⟩
  · subst U; exact ⟨_, case_37⟩
  · subst U; exact ⟨_, case_38⟩
  · subst U; exact ⟨_, case_39⟩
  · subst U; exact ⟨_, case_40⟩
  · subst U; exact ⟨_, case_41⟩
  · subst U; exact ⟨_, case_42⟩
  · subst U; exact ⟨_, case_43⟩
  · subst U; exact ⟨_, case_44⟩
  · subst U; exact ⟨_, case_45⟩
  · subst U; exact ⟨_, case_46⟩
  · subst U; exact ⟨_, case_47⟩
  · subst U; exact ⟨_, case_48⟩
  · subst U; exact ⟨_, case_49⟩
  · subst U; exact ⟨_, case_50⟩
  · subst U; exact ⟨_, case_51⟩
  · subst U; exact ⟨_, case_52⟩
  · subst U; exact ⟨_, case_53⟩
  · subst U; exact ⟨_, case_54⟩
  · subst U; exact ⟨_, case_55⟩
  · subst U; exact ⟨_, case_56⟩
  · subst U; exact ⟨_, case_57⟩
  · subst U; exact ⟨_, case_58⟩
  · subst U; exact ⟨_, case_59⟩
  · subst U; exact ⟨_, case_60⟩
  · subst U; exact ⟨_, case_61⟩
  · subst U; exact ⟨_, case_62⟩
  · subst U; exact ⟨_, case_63⟩
end Flow023_01
end Omega.Turnpike.SubsetCertificate
