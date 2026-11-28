/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs12/Check012
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetCertificatePair02
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow012_12
def τ : Triangle 7 := ⟨(0,1,2),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8}
      [((8,8,4),4), ((9,8,5),4), ((10,8,6),10), ((11,8,7),11)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9}
      [((7,9,4),2), ((8,9,5),4), ((9,9,6),6), ((10,9,7),10)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9}
      [((7,9,4),2),
       ((8,8,4),2),
       ((8,9,5),2),
       ((9,8,5),2),
       ((9,9,6),4),
       ((10,8,6),7),
       ((10,9,7),3),
       ((11,8,7),8)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10}
      [((6,10,4),4), ((7,10,5),2), ((8,10,6),4), ((9,10,7),6), ((11,10,9),6)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10}
      [((6,10,4),4),
       ((7,10,5),2),
       ((9,8,5),2),
       ((8,10,6),4),
       ((10,8,6),7),
       ((9,10,7),4),
       ((11,8,7),7),
       ((11,10,9),6)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10}
      [((6,10,4),4),
       ((7,10,5),2),
       ((8,9,5),2),
       ((8,10,6),2),
       ((9,9,6),6),
       ((10,9,7),10),
       ((11,10,9),6)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10}
      [((6,10,4),4),
       ((7,10,5),2),
       ((8,9,5),2),
       ((8,10,6),2),
       ((9,9,6),6),
       ((10,8,6),3),
       ((10,9,7),7),
       ((11,8,7),4),
       ((11,10,9),6)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {11}
      [((6,11,5),4), ((7,11,6),2), ((8,11,7),4), ((10,11,9),6), ((11,11,10),14)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,11}
      [((8,8,4),4),
       ((6,11,5),4),
       ((7,11,6),2),
       ((10,8,6),9),
       ((11,8,7),11),
       ((10,11,9),1),
       ((11,11,10),9)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,11}
      [((7,9,4),2),
       ((6,11,5),4),
       ((9,9,6),6),
       ((8,11,7),4),
       ((10,9,7),7),
       ((10,11,9),3),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,11}
      [((7,9,4),2),
       ((8,8,4),2),
       ((6,11,5),4),
       ((9,9,6),6),
       ((10,8,6),5),
       ((8,11,7),2),
       ((10,9,7),3),
       ((11,8,7),6),
       ((10,11,9),2),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10,11}
      [((6,10,4),4),
       ((6,11,5),4),
       ((7,11,6),2),
       ((8,10,6),4),
       ((9,10,7),6),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10,11}
      [((6,10,4),4),
       ((6,11,5),4),
       ((7,11,6),2),
       ((8,10,6),4),
       ((10,8,6),5),
       ((9,10,7),6),
       ((11,8,7),5),
       ((10,11,9),5),
       ((11,10,9),1),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10,11}
      [((6,10,4),4),
       ((6,11,5),4),
       ((7,11,6),2),
       ((8,10,6),4),
       ((9,9,6),5),
       ((9,10,7),1),
       ((10,9,7),10),
       ((11,10,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10,11}
      [((6,10,4),4),
       ((6,11,5),4),
       ((7,11,6),2),
       ((8,10,6),4),
       ((9,9,6),5),
       ((9,10,7),1),
       ((10,9,7),10),
       ((11,10,9),6),
       ((11,11,10),14)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 1)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 1 2 0 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 1)).powerset =
      {∅,
       {8},
       {9},
       {8,9},
       {10},
       {8,10},
       {9,10},
       {8,9,10},
       {11},
       {8,11},
       {9,11},
       {8,9,11},
       {10,11},
       {8,10,11},
       {9,10,11},
       {8,9,10,11}} := by decide +kernel
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
end Flow012_12
end Omega.Turnpike.SubsetCertificate
