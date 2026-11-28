/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs02/Check123
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs02.Check056
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow123_02
def τ : Triangle 7 := ⟨(1,2,3),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8}
      [((8,10,6),6), ((8,11,7),16)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9}
      [((9,9,6),6), ((9,10,7),13), ((9,11,8),2)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9}
      [((9,9,6),6), ((9,10,7),13), ((8,11,7),3), ((9,11,8),2)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {10}
      [((10,8,6),2), ((10,9,7),12), ((10,10,8),2), ((10,11,9),12)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,10}
      [((10,8,6),2),
       ((8,10,6),4),
       ((10,9,7),12),
       ((8,11,7),4),
       ((10,10,8),2),
       ((10,11,9),12)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,10}
      [((10,8,6),2), ((9,9,6),4), ((10,9,7),8), ((9,10,7),8), ((10,10,8),2), ((10,11,9),12)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9,10}
      [((10,8,6),2), ((9,9,6),4), ((10,9,7),8), ((9,10,7),8), ((10,10,8),2), ((10,11,9),12)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {11}
      [((11,8,7),2), ((11,9,8),2), ((11,10,9),12), ((11,11,10),14)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,11}
      [((8,10,6),6),
       ((11,8,7),2),
       ((8,11,7),14),
       ((11,9,8),2),
       ((11,10,9),7),
       ((11,11,10),9)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,11}
      [((9,9,6),6), ((11,8,7),2), ((9,10,7),13), ((11,9,8),2), ((11,11,10),14)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9,11}
      [((9,9,6),6),
       ((11,8,7),2),
       ((9,10,7),5),
       ((8,11,7),9),
       ((11,9,8),2),
       ((11,10,9),8),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {10,11}
      [((10,8,6),2),
       ((10,9,7),12),
       ((10,10,8),2),
       ((11,10,9),11),
       ((10,11,9),1),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,10,11}
      [((10,8,6),2),
       ((8,10,6),4),
       ((10,9,7),12),
       ((8,11,7),4),
       ((10,10,8),2),
       ((11,10,9),7),
       ((10,11,9),5),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {9,10,11}
      [((10,8,6),2),
       ((9,9,6),4),
       ((10,9,7),8),
       ((9,10,7),8),
       ((10,10,8),2),
       ((11,10,9),3),
       ((10,11,9),9),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 2 1 {8,9,10,11}
      [((10,8,6),2),
       ((9,9,6),4),
       ((10,9,7),8),
       ((9,10,7),8),
       ((10,10,8),2),
       ((11,10,9),3),
       ((10,11,9),9),
       ((11,11,10),14)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 2 1 U L := by
  intro U hU
  have cover : (positiveSupport (edge τ 0)).powerset =
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
end Flow123_02
end Omega.Turnpike.SubsetCertificate
