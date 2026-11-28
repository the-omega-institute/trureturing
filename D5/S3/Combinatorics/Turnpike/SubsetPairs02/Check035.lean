/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check035
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check034
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow035_02
def τ : Triangle 7 := ⟨(0,3,5),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3}
      [((3,10,1),19)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6}
      [((6,7,1),11), ((6,8,2),6), ((6,10,4),9)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,6}
      [((6,7,1),11), ((3,10,1),19), ((6,8,2),6)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8}
      [((8,6,2),3), ((8,8,4),9), ((8,9,5),2), ((8,10,6),3)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,8}
      [((3,10,1),19), ((8,6,2),3), ((8,8,4),9), ((8,9,5),2)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8}
      [((6,7,1),11), ((8,6,2),3), ((6,8,2),3), ((8,8,4),9), ((8,9,5),2), ((8,10,6),3)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,6,8}
      [((6,7,1),11), ((3,10,1),19), ((8,6,2),3), ((6,8,2),3), ((8,8,4),9), ((8,9,5),2)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9}
      [((9,7,4),9), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,9}
      [((3,10,1),19), ((9,7,4),9), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,9}
      [((6,7,1),11), ((6,8,2),6), ((6,10,4),9), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,6,9}
      [((6,7,1),11), ((3,10,1),19), ((6,8,2),6), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9}
      [((8,6,2),3), ((9,7,4),9), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,8,9}
      [((3,10,1),19), ((8,6,2),3), ((9,7,4),9), ((9,8,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8,9}
      [((6,7,1),11), ((8,6,2),3), ((6,8,2),3), ((8,8,4),9), ((8,9,5),2), ((9,9,6),3)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {3,6,8,9}
      [((6,7,1),11),
       ((3,10,1),19),
       ((8,6,2),3),
       ((6,8,2),3),
       ((8,8,4),9),
       ((8,9,5),2),
       ((9,9,6),3)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {3},
       {6},
       {3,6},
       {8},
       {3,8},
       {6,8},
       {3,6,8},
       {9},
       {3,9},
       {6,9},
       {3,6,9},
       {8,9},
       {3,8,9},
       {6,8,9},
       {3,6,8,9}} := by decide +kernel
  rw [cover] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
end Flow035_02
end Omega.Turnpike.SubsetCertificate
