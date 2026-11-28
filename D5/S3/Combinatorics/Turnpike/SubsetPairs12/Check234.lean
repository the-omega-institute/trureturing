/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs12/Check234
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs12.Check156
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow234_12
def τ : Triangle 7 := ⟨(2,3,4),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8}
      [((10,8,6),3), ((11,8,7),8)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9}
      [((9,9,6),3), ((10,9,7),8), ((11,9,8),12)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9}
      [((9,9,6),3), ((10,9,7),8), ((11,9,8),12)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10}
      [((8,10,6),2), ((9,10,7),8), ((10,10,8),12), ((11,10,9),16)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10}
      [((8,10,6),2), ((10,8,6),1), ((9,10,7),8), ((10,10,8),12), ((11,10,9),16)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10}
      [((8,10,6),2), ((9,9,6),1), ((9,10,7),8), ((10,10,8),12), ((11,10,9),16)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10}
      [((8,10,6),2), ((9,9,6),1), ((9,10,7),8), ((10,10,8),12), ((11,10,9),16)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {11}
      [((8,11,7),2), ((9,11,8),12), ((10,11,9),13), ((11,11,10),11)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,11}
      [((10,8,6),3),
       ((8,11,7),2),
       ((11,8,7),6),
       ((9,11,8),12),
       ((10,11,9),10),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,11}
      [((9,9,6),3),
       ((8,11,7),2),
       ((10,9,7),6),
       ((9,11,8),9),
       ((11,9,8),3),
       ((10,11,9),7),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,11}
      [((9,9,6),3),
       ((8,11,7),2),
       ((11,8,7),6),
       ((9,11,8),9),
       ((11,9,8),3),
       ((10,11,9),13),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10,11}
      [((8,10,6),2),
       ((9,10,7),8),
       ((9,11,8),4),
       ((10,10,8),8),
       ((10,11,9),5),
       ((11,10,9),11),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10,11}
      [((8,10,6),2),
       ((10,8,6),1),
       ((9,10,7),8),
       ((9,11,8),4),
       ((10,10,8),8),
       ((10,11,9),4),
       ((11,10,9),12),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10,11}
      [((8,10,6),2),
       ((9,9,6),1),
       ((9,10,7),8),
       ((9,11,8),3),
       ((10,10,8),9),
       ((10,11,9),4),
       ((11,10,9),12),
       ((11,11,10),11)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10,11}
      [((8,10,6),2),
       ((9,9,6),1),
       ((9,10,7),8),
       ((9,11,8),3),
       ((10,10,8),9),
       ((10,11,9),4),
       ((11,10,9),12),
       ((11,11,10),11)] := by
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
end Flow234_12
end Omega.Turnpike.SubsetCertificate
