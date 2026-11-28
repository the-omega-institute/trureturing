/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check146
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check145
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow146_02
def τ : Triangle 7 := ⟨(1,4,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5}
      [((5,8,1),13), ((5,10,3),6)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6}
      [((6,8,2),10), ((6,10,4),4)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,6}
      [((5,8,1),13), ((5,10,3),6), ((6,10,4),4)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7}
      [((7,6,1),14), ((7,8,3),6), ((7,10,5),2)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,7}
      [((7,6,1),14), ((5,8,1),6), ((7,8,3),6), ((7,10,5),2)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7}
      [((7,6,1),14), ((6,8,2),10), ((7,8,3),3), ((6,10,4),4), ((7,10,5),2)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,6,7}
      [((7,6,1),14), ((5,8,1),6), ((6,8,2),7), ((5,10,3),6), ((6,10,4),4), ((7,10,5),2)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8}
      [((8,5,1),3), ((8,6,2),10), ((8,8,4),4), ((8,10,6),8)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,8}
      [((8,5,1),3), ((5,8,1),13), ((8,6,2),10), ((5,10,3),6), ((8,10,6),8)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,8}
      [((8,5,1),3), ((8,6,2),10), ((8,8,4),4), ((8,10,6),8)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,6,8}
      [((8,5,1),3), ((5,8,1),13), ((8,6,2),10), ((5,10,3),6), ((6,10,4),4), ((8,10,6),8)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,8}
      [((8,5,1),3), ((7,6,1),14), ((7,8,3),6), ((8,8,4),4), ((7,10,5),2), ((8,10,6),8)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,7,8}
      [((8,5,1),3),
       ((7,6,1),8),
       ((5,8,1),9),
       ((8,6,2),6),
       ((5,10,3),6),
       ((8,8,4),4),
       ((7,10,5),2),
       ((8,10,6),8)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {6,7,8}
      [((8,5,1),3),
       ((7,6,1),14),
       ((6,8,2),10),
       ((7,8,3),3),
       ((6,10,4),4),
       ((7,10,5),2),
       ((8,10,6),8)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {5,6,7,8}
      [((8,5,1),3),
       ((7,6,1),14),
       ((5,8,1),3),
       ((6,8,2),10),
       ((5,10,3),6),
       ((6,10,4),4),
       ((7,10,5),2),
       ((8,10,6),8)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {5},
       {6},
       {5,6},
       {7},
       {5,7},
       {6,7},
       {5,6,7},
       {8},
       {5,8},
       {6,8},
       {5,6,8},
       {7,8},
       {5,7,8},
       {6,7,8},
       {5,6,7,8}} := by decide +kernel
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
end Flow146_02
end Omega.Turnpike.SubsetCertificate
