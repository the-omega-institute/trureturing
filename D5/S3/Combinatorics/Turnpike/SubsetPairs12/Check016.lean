/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs12/Check016
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs12.Check015
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow016_12
def τ : Triangle 7 := ⟨(0,1,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1}
      [((11,1,0),20)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2}
      [((10,2,0),10)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2}
      [((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3}
      [((9,3,0),6)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3}
      [((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3}
      [((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3}
      [((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {4}
      [((8,4,0),4)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,4}
      [((8,4,0),4), ((11,1,0),20)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,4}
      [((8,4,0),4), ((10,2,0),10)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,4}
      [((8,4,0),4), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,4}
      [((8,4,0),4), ((9,3,0),6)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,4}
      [((8,4,0),4), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,4}
      [((8,4,0),4), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,4}
      [((8,4,0),4), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5}
      [((7,5,0),2)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,5}
      [((7,5,0),2), ((11,1,0),20)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,5}
      [((7,5,0),2), ((10,2,0),10)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,5}
      [((7,5,0),2), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,5}
      [((7,5,0),2), ((9,3,0),6)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,5}
      [((7,5,0),2), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,5}
      [((7,5,0),2), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,5}
      [((7,5,0),2), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {4,5}
      [((7,5,0),2), ((8,4,0),4)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,4,5}
      [((7,5,0),2), ((8,4,0),4), ((11,1,0),20)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,4,5}
      [((7,5,0),2), ((8,4,0),4), ((10,2,0),10)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,4,5}
      [((7,5,0),2), ((8,4,0),4), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,4,5}
      [((7,5,0),2), ((8,4,0),4), ((9,3,0),6)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,4,5}
      [((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,4,5}
      [((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,4,5}
      [((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_32 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {6}
      [((6,6,0),8)] := by
  decide +kernel
private theorem case_33 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,6}
      [((6,6,0),8), ((11,1,0),20)] := by
  decide +kernel
private theorem case_34 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,6}
      [((6,6,0),8), ((10,2,0),10)] := by
  decide +kernel
private theorem case_35 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,6}
      [((6,6,0),8), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_36 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,6}
      [((6,6,0),8), ((9,3,0),6)] := by
  decide +kernel
private theorem case_37 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,6}
      [((6,6,0),8), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_38 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,6}
      [((6,6,0),8), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_39 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,6}
      [((6,6,0),8), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_40 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {4,6}
      [((6,6,0),8), ((8,4,0),4)] := by
  decide +kernel
private theorem case_41 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,4,6}
      [((6,6,0),8), ((8,4,0),4), ((11,1,0),20)] := by
  decide +kernel
private theorem case_42 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,4,6}
      [((6,6,0),8), ((8,4,0),4), ((10,2,0),10)] := by
  decide +kernel
private theorem case_43 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,4,6}
      [((6,6,0),8), ((8,4,0),4), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_44 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,4,6}
      [((6,6,0),8), ((8,4,0),4), ((9,3,0),6)] := by
  decide +kernel
private theorem case_45 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,4,6}
      [((6,6,0),8), ((8,4,0),4), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_46 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,4,6}
      [((6,6,0),8), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_47 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,4,6}
      [((6,6,0),8), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_48 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,6}
      [((6,6,0),8), ((7,5,0),2)] := by
  decide +kernel
private theorem case_49 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,5,6}
      [((6,6,0),8), ((7,5,0),2), ((11,1,0),20)] := by
  decide +kernel
private theorem case_50 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,5,6}
      [((6,6,0),8), ((7,5,0),2), ((10,2,0),10)] := by
  decide +kernel
private theorem case_51 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,5,6}
      [((6,6,0),8), ((7,5,0),2), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_52 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,5,6}
      [((6,6,0),8), ((7,5,0),2), ((9,3,0),6)] := by
  decide +kernel
private theorem case_53 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,5,6}
      [((6,6,0),8), ((7,5,0),2), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_54 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,5,6}
      [((6,6,0),8), ((7,5,0),2), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_55 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,5,6}
      [((6,6,0),8), ((7,5,0),2), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_56 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4)] := by
  decide +kernel
private theorem case_57 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((11,1,0),20)] := by
  decide +kernel
private theorem case_58 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((10,2,0),10)] := by
  decide +kernel
private theorem case_59 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
private theorem case_60 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {3,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((9,3,0),6)] := by
  decide +kernel
private theorem case_61 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,3,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((11,1,0),20)] := by
  decide +kernel
private theorem case_62 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {2,3,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10)] := by
  decide +kernel
private theorem case_63 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {1,2,3,4,5,6}
      [((6,6,0),8), ((7,5,0),2), ((8,4,0),4), ((9,3,0),6), ((10,2,0),10), ((11,1,0),20)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 1)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 1 2 0 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 1)).powerset =
      {∅,
       {1},
       {2},
       {1,2},
       {3},
       {1,3},
       {2,3},
       {1,2,3},
       {4},
       {1,4},
       {2,4},
       {1,2,4},
       {3,4},
       {1,3,4},
       {2,3,4},
       {1,2,3,4},
       {5},
       {1,5},
       {2,5},
       {1,2,5},
       {3,5},
       {1,3,5},
       {2,3,5},
       {1,2,3,5},
       {4,5},
       {1,4,5},
       {2,4,5},
       {1,2,4,5},
       {3,4,5},
       {1,3,4,5},
       {2,3,4,5},
       {1,2,3,4,5},
       {6},
       {1,6},
       {2,6},
       {1,2,6},
       {3,6},
       {1,3,6},
       {2,3,6},
       {1,2,3,6},
       {4,6},
       {1,4,6},
       {2,4,6},
       {1,2,4,6},
       {3,4,6},
       {1,3,4,6},
       {2,3,4,6},
       {1,2,3,4,6},
       {5,6},
       {1,5,6},
       {2,5,6},
       {1,2,5,6},
       {3,5,6},
       {1,3,5,6},
       {2,3,5,6},
       {1,2,3,5,6},
       {4,5,6},
       {1,4,5,6},
       {2,4,5,6},
       {1,2,4,5,6},
       {3,4,5,6},
       {1,3,4,5,6},
       {2,3,4,5,6},
       {1,2,3,4,5,6}} := by decide +kernel
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
end Flow016_12
end Omega.Turnpike.SubsetCertificate
