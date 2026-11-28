/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check456
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check356
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow456_02
def τ : Triangle 7 := ⟨(4,5,6),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7}
      [((7,10,5),3), ((7,11,6),14)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9}
      [((9,8,5),3), ((9,11,8),13)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9}
      [((9,8,5),3), ((7,11,6),14), ((9,11,8),13)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {10}
      [((10,7,5),2), ((10,8,6),9), ((10,10,8),6)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,10}
      [((10,7,5),2), ((7,10,5),1), ((10,8,6),9), ((7,11,6),5), ((10,10,8),5)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,10}
      [((10,7,5),2), ((9,8,5),1), ((10,8,6),8), ((10,10,8),6), ((9,11,8),7)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9,10}
      [((10,7,5),2), ((9,8,5),1), ((10,8,6),8), ((7,11,6),6), ((10,10,8),6), ((9,11,8),7)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {11}
      [((11,6,5),3), ((11,7,6),2), ((11,11,10),20)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,11}
      [((11,6,5),3), ((11,7,6),2), ((7,11,6),12), ((11,11,10),18)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,11}
      [((11,6,5),3), ((11,7,6),2), ((9,11,8),13), ((11,11,10),17)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9,11}
      [((11,6,5),3), ((11,7,6),2), ((7,11,6),12), ((9,11,8),13), ((11,11,10),5)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {10,11}
      [((11,6,5),3), ((11,7,6),2), ((10,8,6),9), ((10,10,8),6), ((11,11,10),20)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,10,11}
      [((11,6,5),3),
       ((11,7,6),2),
       ((10,8,6),9),
       ((7,11,6),3),
       ((10,10,8),6),
       ((11,11,10),20)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,10,11}
      [((11,6,5),3),
       ((11,7,6),2),
       ((10,8,6),9),
       ((10,10,8),6),
       ((9,11,8),7),
       ((11,11,10),20)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {7,9,10,11}
      [((11,6,5),3),
       ((11,7,6),2),
       ((10,8,6),9),
       ((7,11,6),3),
       ((10,10,8),6),
       ((9,11,8),7),
       ((11,11,10),20)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
      {∅,
       {7},
       {9},
       {7,9},
       {10},
       {7,10},
       {9,10},
       {7,9,10},
       {11},
       {7,11},
       {9,11},
       {7,9,11},
       {10,11},
       {7,10,11},
       {9,10,11},
       {7,9,10,11}} := by decide +kernel
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
end Flow456_02
end Omega.Turnpike.SubsetCertificate
