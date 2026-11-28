/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check246
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check245
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow246_02
def τ : Triangle 7 := ⟨(2,4,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6}
      [((6,8,2),13)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7}
      [((7,8,3),6), ((7,10,5),11)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7}
      [((6,8,2),13), ((7,10,5),11)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8}
      [((8,6,2),14), ((8,10,6),11)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8}
      [((8,6,2),14), ((8,10,6),11)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,8}
      [((8,6,2),14), ((7,8,3),6), ((7,10,5),11), ((8,10,6),9)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,8}
      [((8,6,2),14), ((7,8,3),6), ((7,10,5),11), ((8,10,6),9)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9}
      [((9,5,2),3), ((9,6,3),6), ((9,8,5),11), ((9,10,7),4)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,9}
      [((9,5,2),3), ((6,8,2),11), ((9,6,3),6), ((9,8,5),2), ((9,10,7),4)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9}
      [((9,5,2),3), ((9,6,3),6), ((9,8,5),11), ((9,10,7),4)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,9}
      [((9,5,2),3), ((6,8,2),11), ((9,6,3),6), ((9,8,5),2), ((7,10,5),9), ((9,10,7),4)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9}
      [((9,5,2),3), ((8,6,2),11), ((9,6,3),3), ((9,8,5),11), ((8,10,6),11), ((9,10,7),4)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8,9}
      [((9,5,2),3),
       ((8,6,2),9),
       ((6,8,2),2),
       ((9,6,3),5),
       ((9,8,5),11),
       ((8,10,6),11),
       ((9,10,7),4)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,8,9}
      [((9,5,2),3),
       ((8,6,2),11),
       ((9,6,3),3),
       ((7,8,3),3),
       ((9,8,5),10),
       ((7,10,5),1),
       ((8,10,6),11),
       ((9,10,7),4)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,8,9}
      [((9,5,2),3),
       ((8,6,2),11),
       ((9,6,3),3),
       ((7,8,3),3),
       ((9,8,5),10),
       ((7,10,5),1),
       ((8,10,6),11),
       ((9,10,7),4)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {10}
      [((10,5,3),3), ((10,8,6),11), ((10,10,8),4)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,10}
      [((6,8,2),13), ((10,5,3),3), ((10,10,8),4)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,10}
      [((10,5,3),3), ((7,8,3),3), ((7,10,5),11), ((10,8,6),10), ((10,10,8),4)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,10}
      [((6,8,2),13), ((10,5,3),3), ((7,10,5),11), ((10,10,8),4)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,10}
      [((8,6,2),14), ((10,5,3),3), ((10,8,6),11), ((10,10,8),4)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8,10}
      [((8,6,2),14), ((10,5,3),3), ((10,8,6),11), ((10,10,8),4)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,8,10}
      [((8,6,2),14),
       ((10,5,3),3),
       ((7,8,3),3),
       ((7,10,5),11),
       ((10,8,6),10),
       ((8,10,6),1),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,8,10}
      [((8,6,2),14),
       ((10,5,3),3),
       ((7,8,3),3),
       ((7,10,5),11),
       ((10,8,6),10),
       ((8,10,6),1),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,10}
      [((9,5,2),3), ((9,6,3),6), ((9,8,5),11), ((10,8,6),2), ((9,10,7),4), ((10,10,8),4)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,9,10}
      [((9,5,2),3), ((6,8,2),11), ((9,6,3),6), ((9,8,5),2), ((9,10,7),4), ((10,10,8),4)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9,10}
      [((9,5,2),3),
       ((9,6,3),6),
       ((9,8,5),2),
       ((7,10,5),9),
       ((10,8,6),11),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,9,10}
      [((9,5,2),3),
       ((6,8,2),11),
       ((9,6,3),6),
       ((7,10,5),11),
       ((10,8,6),2),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9,10}
      [((9,5,2),3),
       ((8,6,2),11),
       ((9,6,3),3),
       ((9,8,5),11),
       ((10,8,6),2),
       ((8,10,6),9),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8,9,10}
      [((9,5,2),1),
       ((8,6,2),11),
       ((6,8,2),2),
       ((10,5,3),2),
       ((9,6,3),3),
       ((9,8,5),11),
       ((8,10,6),11),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,8,9,10}
      [((9,5,2),3),
       ((8,6,2),11),
       ((9,6,3),3),
       ((7,8,3),3),
       ((9,8,5),10),
       ((7,10,5),1),
       ((8,10,6),11),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,8,9,10}
      [((9,5,2),3),
       ((8,6,2),11),
       ((9,6,3),3),
       ((7,8,3),3),
       ((9,8,5),10),
       ((7,10,5),1),
       ((8,10,6),11),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {6},
       {7},
       {6,7},
       {8},
       {6,8},
       {7,8},
       {6,7,8},
       {9},
       {6,9},
       {7,9},
       {6,7,9},
       {8,9},
       {6,8,9},
       {7,8,9},
       {6,7,8,9},
       {10},
       {6,10},
       {7,10},
       {6,7,10},
       {8,10},
       {6,8,10},
       {7,8,10},
       {6,7,8,10},
       {9,10},
       {6,9,10},
       {7,9,10},
       {6,7,9,10},
       {8,9,10},
       {6,8,9,10},
       {7,8,9,10},
       {6,7,8,9,10}} := by decide +kernel
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
end Flow246_02
end Omega.Turnpike.SubsetCertificate
