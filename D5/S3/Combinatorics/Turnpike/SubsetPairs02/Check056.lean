/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check056
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check046
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow056_02
def τ : Triangle 7 := ⟨(0,5,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1}
      [((1,11,0),30)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2}
      [((2,10,0),6)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2}
      [((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {4}
      [((4,8,0),9)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,4}
      [((4,8,0),9), ((1,11,0),30)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,4}
      [((4,8,0),9), ((2,10,0),6)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,4}
      [((4,8,0),9), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5}
      [((5,7,0),2)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,5}
      [((5,7,0),2), ((1,11,0),30)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,5}
      [((5,7,0),2), ((2,10,0),6)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,5}
      [((5,7,0),2), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {4,5}
      [((5,7,0),2), ((4,8,0),9)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,4,5}
      [((5,7,0),2), ((4,8,0),9), ((1,11,0),30)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,4,5}
      [((5,7,0),2), ((4,8,0),9), ((2,10,0),6)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,4,5}
      [((5,7,0),2), ((4,8,0),9), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6}
      [((6,6,0),3)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,6}
      [((6,6,0),3), ((1,11,0),30)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,6}
      [((6,6,0),3), ((2,10,0),6)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,6}
      [((6,6,0),3), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {4,6}
      [((6,6,0),3), ((4,8,0),9)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,4,6}
      [((6,6,0),3), ((4,8,0),9), ((1,11,0),30)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,4,6}
      [((6,6,0),3), ((4,8,0),9), ((2,10,0),6)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,4,6}
      [((6,6,0),3), ((4,8,0),9), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,6}
      [((6,6,0),3), ((5,7,0),2)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,5,6}
      [((6,6,0),3), ((5,7,0),2), ((1,11,0),30)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,5,6}
      [((6,6,0),3), ((5,7,0),2), ((2,10,0),6)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,5,6}
      [((6,6,0),3), ((5,7,0),2), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {4,5,6}
      [((6,6,0),3), ((5,7,0),2), ((4,8,0),9)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,4,5,6}
      [((6,6,0),3), ((5,7,0),2), ((4,8,0),9), ((1,11,0),30)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {2,4,5,6}
      [((6,6,0),3), ((5,7,0),2), ((4,8,0),9), ((2,10,0),6)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {1,2,4,5,6}
      [((6,6,0),3), ((5,7,0),2), ((4,8,0),9), ((2,10,0),6), ((1,11,0),30)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {1},
       {2},
       {1,2},
       {4},
       {1,4},
       {2,4},
       {1,2,4},
       {5},
       {1,5},
       {2,5},
       {1,2,5},
       {4,5},
       {1,4,5},
       {2,4,5},
       {1,2,4,5},
       {6},
       {1,6},
       {2,6},
       {1,2,6},
       {4,6},
       {1,4,6},
       {2,4,6},
       {1,2,4,6},
       {5,6},
       {1,5,6},
       {2,5,6},
       {1,2,5,6},
       {4,5,6},
       {1,4,5,6},
       {2,4,5,6},
       {1,2,4,5,6}} := by decide +kernel
  rw [cover] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
end Flow056_02
end Omega.Turnpike.SubsetCertificate
