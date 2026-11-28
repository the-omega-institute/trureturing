/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs12/Check246
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs12.Check245
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow246_12
def τ : Triangle 7 := ⟨(2,4,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5}
      [((9,5,2),14), ((10,5,3),6)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {6}
      [((8,6,2),12), ((9,6,3),6)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,6}
      [((8,6,2),12), ((9,5,2),2), ((9,6,3),6)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8}
      [((6,8,2),3), ((7,8,3),6), ((9,8,5),11), ((10,8,6),11)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,8}
      [((6,8,2),3), ((9,5,2),11), ((7,8,3),6), ((9,8,5),5), ((10,8,6),11)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {6,8}
      [((6,8,2),3), ((8,6,2),11), ((7,8,3),6), ((9,8,5),11), ((10,8,6),11)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,6,8}
      [((6,8,2),3), ((8,6,2),11), ((7,8,3),6), ((9,8,5),11), ((10,8,6),11)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10}
      [((7,10,5),8), ((8,10,6),11), ((9,10,7),4), ((10,10,8),4)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,10}
      [((9,5,2),14), ((10,5,3),6), ((7,10,5),8), ((8,10,6),11), ((9,10,7),2), ((10,10,8),4)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {6,10}
      [((8,6,2),12), ((9,6,3),6), ((7,10,5),8), ((9,10,7),4), ((10,10,8),4)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,6,10}
      [((8,6,2),2),
       ((9,5,2),12),
       ((10,5,3),6),
       ((7,10,5),8),
       ((8,10,6),10),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10}
      [((6,8,2),3),
       ((7,8,3),6),
       ((7,10,5),2),
       ((9,8,5),9),
       ((8,10,6),11),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,8,10}
      [((6,8,2),3),
       ((9,5,2),11),
       ((10,5,3),6),
       ((7,10,5),8),
       ((9,8,5),3),
       ((8,10,6),11),
       ((9,10,7),2),
       ((10,10,8),4)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {6,8,10}
      [((6,8,2),3),
       ((8,6,2),11),
       ((7,8,3),6),
       ((7,10,5),2),
       ((9,8,5),9),
       ((8,10,6),1),
       ((10,8,6),10),
       ((9,10,7),4),
       ((10,10,8),1)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {5,6,8,10}
      [((6,8,2),3),
       ((8,6,2),8),
       ((9,5,2),3),
       ((7,8,3),6),
       ((7,10,5),2),
       ((9,8,5),9),
       ((8,10,6),4),
       ((10,8,6),7),
       ((9,10,7),4),
       ((10,10,8),4)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 1)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 1 2 0 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 1)).powerset =
      {∅,
       {5},
       {6},
       {5,6},
       {8},
       {5,8},
       {6,8},
       {5,6,8},
       {10},
       {5,10},
       {6,10},
       {5,6,10},
       {8,10},
       {5,8,10},
       {6,8,10},
       {5,6,8,10}} := by decide +kernel
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
end Flow246_12
end Omega.Turnpike.SubsetCertificate
