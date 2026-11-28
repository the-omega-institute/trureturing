/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs12/Check134
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs12.Check126
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow134_12
def τ : Triangle 7 := ⟨(1,3,4),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8}
      [((9,8,5),9), ((10,8,6),14)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9}
      [((8,9,5),2), ((9,9,6),12), ((10,9,7),14)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9}
      [((8,9,5),2), ((9,8,5),7), ((9,9,6),5), ((10,8,6),9), ((10,9,7),5)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10}
      [((7,10,5),9), ((8,10,6),2), ((9,10,7),12), ((10,10,8),11)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10}
      [((7,10,5),9), ((8,10,6),2), ((10,8,6),12), ((9,10,7),12), ((10,10,8),2)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10}
      [((7,10,5),9), ((8,10,6),2), ((9,9,6),12), ((10,9,7),14)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10}
      [((7,10,5),9), ((8,10,6),2), ((9,9,6),12), ((10,9,7),14)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {11}
      [((6,11,5),6), ((7,11,6),14), ((8,11,7),2), ((9,11,8),11)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,11}
      [((6,11,5),6), ((9,8,5),3), ((7,11,6),14), ((8,11,7),2), ((9,11,8),9)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,11}
      [((6,11,5),6), ((8,9,5),2), ((7,11,6),14), ((10,9,7),14), ((9,11,8),11)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,11}
      [((6,11,5),6), ((8,9,5),2), ((9,8,5),1), ((7,11,6),14), ((10,9,7),14), ((9,11,8),11)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {10,11}
      [((6,11,5),6),
       ((7,10,5),3),
       ((7,11,6),13),
       ((8,10,6),1),
       ((8,11,7),1),
       ((9,10,7),12),
       ((10,10,8),11)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,10,11}
      [((6,11,5),6),
       ((7,10,5),3),
       ((7,11,6),13),
       ((10,8,6),1),
       ((8,11,7),2),
       ((9,10,7),12),
       ((10,10,8),11)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {9,10,11}
      [((6,11,5),6),
       ((7,10,5),3),
       ((7,11,6),13),
       ((8,10,6),1),
       ((8,11,7),1),
       ((9,10,7),12),
       ((10,9,7),3),
       ((10,10,8),11)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 1 2 0 {8,9,10,11}
      [((6,11,5),6),
       ((7,10,5),3),
       ((7,11,6),13),
       ((8,10,6),1),
       ((8,11,7),1),
       ((9,10,7),12),
       ((10,9,7),3),
       ((10,10,8),11)] := by
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
end Flow134_12
end Omega.Turnpike.SubsetCertificate
