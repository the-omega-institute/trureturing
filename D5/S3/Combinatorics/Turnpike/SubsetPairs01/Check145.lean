/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs01/Check145
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs01.Check136
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow145_01
def τ : Triangle 7 := ⟨(1,4,5),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5}
      [((5,10,3),15), ((5,11,4),6)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6}
      [((6,9,3),7), ((6,10,4),6), ((6,11,5),13)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6}
      [((6,9,3),7), ((5,10,3),9), ((6,10,4),6), ((6,11,5),13)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7}
      [((7,9,4),6), ((7,10,5),13), ((7,11,6),4)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7}
      [((7,9,4),6), ((5,10,3),15), ((7,11,6),4)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7}
      [((6,9,3),7), ((6,10,4),6), ((7,10,5),9), ((6,11,5),4), ((7,11,6),4)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7}
      [((6,9,3),7), ((5,10,3),9), ((6,10,4),6), ((6,11,5),13), ((7,11,6),4)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8}
      [((8,7,3),3), ((8,9,5),7), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,8}
      [((8,7,3),3), ((8,9,5),7), ((5,10,3),13), ((8,10,6),2), ((5,11,4),6), ((8,11,7),11)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8}
      [((8,7,3),3), ((6,9,3),7), ((6,10,4),6), ((8,10,6),4), ((6,11,5),13), ((8,11,7),11)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,8}
      [((8,7,3),3),
       ((6,9,3),7),
       ((5,10,3),6),
       ((6,10,4),5),
       ((8,10,6),4),
       ((5,11,4),1),
       ((6,11,5),13),
       ((8,11,7),11)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8}
      [((8,7,3),3),
       ((7,9,4),6),
       ((8,9,5),1),
       ((7,10,5),12),
       ((8,10,6),3),
       ((7,11,6),1),
       ((8,11,7),11)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,7,8}
      [((8,7,3),3),
       ((8,9,5),7),
       ((5,10,3),13),
       ((7,10,5),2),
       ((5,11,4),6),
       ((7,11,6),4),
       ((8,11,7),11)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8}
      [((8,7,3),3),
       ((6,9,3),7),
       ((6,10,4),6),
       ((7,10,5),9),
       ((6,11,5),4),
       ((7,11,6),4),
       ((8,11,7),11)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {5,6,7,8}
      [((8,7,3),3),
       ((6,9,3),7),
       ((5,10,3),6),
       ((6,10,4),6),
       ((7,10,5),3),
       ((6,11,5),10),
       ((7,11,6),4),
       ((8,11,7),11)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 1 2 U L := by
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
end Flow145_01
end Omega.Turnpike.SubsetCertificate
