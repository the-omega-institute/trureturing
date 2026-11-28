/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs01/Check134
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetPairs01.Check126
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow134_01
def τ : Triangle 7 := ⟨(1,3,4),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6}
      [((6,11,5),9)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7}
      [((7,10,5),9), ((7,11,6),14)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7}
      [((7,10,5),9), ((7,11,6),14)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8}
      [((8,9,5),3), ((8,10,6),14), ((8,11,7),16)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8}
      [((8,9,5),3), ((8,10,6),14), ((6,11,5),6), ((8,11,7),16)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8}
      [((8,9,5),3), ((7,10,5),6), ((8,10,6),14), ((8,11,7),16)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8}
      [((8,9,5),3), ((7,10,5),6), ((8,10,6),14), ((8,11,7),16)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9}
      [((9,8,5),1), ((9,9,6),3), ((9,10,7),16), ((9,11,8),11)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9}
      [((9,8,5),1), ((9,9,6),3), ((9,10,7),16), ((6,11,5),8), ((9,11,8),11)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9}
      [((9,8,5),1), ((9,9,6),3), ((7,10,5),8), ((9,10,7),16), ((7,11,6),11), ((9,11,8),11)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9}
      [((9,8,5),1), ((9,9,6),3), ((7,10,5),8), ((9,10,7),16), ((7,11,6),11), ((9,11,8),11)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9}
      [((9,8,5),1), ((8,9,5),3), ((8,10,6),14), ((9,10,7),10), ((8,11,7),6), ((9,11,8),11)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9}
      [((9,8,5),1),
       ((8,9,5),3),
       ((8,10,6),14),
       ((9,10,7),10),
       ((6,11,5),5),
       ((8,11,7),6),
       ((9,11,8),11)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9}
      [((9,8,5),1),
       ((8,9,5),3),
       ((7,10,5),5),
       ((8,10,6),14),
       ((9,10,7),5),
       ((8,11,7),11),
       ((9,11,8),11)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9}
      [((9,8,5),1),
       ((8,9,5),3),
       ((7,10,5),5),
       ((8,10,6),14),
       ((9,10,7),5),
       ((8,11,7),11),
       ((9,11,8),11)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {10}
      [((10,8,6),1), ((10,9,7),3), ((10,10,8),11)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,10}
      [((10,8,6),1), ((10,9,7),3), ((10,10,8),11), ((6,11,5),9)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,10}
      [((10,8,6),1), ((10,9,7),3), ((7,10,5),9), ((10,10,8),11), ((7,11,6),13)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,10}
      [((10,8,6),1), ((10,9,7),3), ((7,10,5),9), ((10,10,8),11), ((7,11,6),13)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,10}
      [((10,8,6),1), ((8,9,5),3), ((8,10,6),13), ((10,10,8),11), ((8,11,7),16)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,10}
      [((10,8,6),1), ((8,9,5),3), ((8,10,6),13), ((10,10,8),11), ((6,11,5),6), ((8,11,7),16)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,10}
      [((10,8,6),1),
       ((8,9,5),3),
       ((7,10,5),6),
       ((8,10,6),7),
       ((10,10,8),11),
       ((7,11,6),6),
       ((8,11,7),16)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,10}
      [((10,8,6),1), ((8,9,5),3), ((8,10,6),13), ((10,10,8),11), ((6,11,5),6), ((8,11,7),16)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9,10}
      [((9,8,5),1), ((9,9,6),3), ((9,10,7),16), ((10,10,8),8), ((9,11,8),3)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9,10}
      [((10,8,6),1), ((9,9,6),3), ((9,10,7),16), ((10,10,8),8), ((6,11,5),9), ((9,11,8),3)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9,10}
      [((9,8,5),1), ((9,9,6),3), ((7,10,5),8), ((9,10,7),16), ((7,11,6),11), ((9,11,8),11)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9,10}
      [((9,8,5),1), ((9,9,6),3), ((7,10,5),8), ((9,10,7),16), ((7,11,6),11), ((9,11,8),11)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9,10}
      [((9,8,5),1), ((8,9,5),3), ((8,10,6),14), ((9,10,7),10), ((8,11,7),6), ((9,11,8),11)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9,10}
      [((9,8,5),1),
       ((8,9,5),3),
       ((8,10,6),14),
       ((9,10,7),10),
       ((6,11,5),5),
       ((8,11,7),6),
       ((9,11,8),11)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9,10}
      [((9,8,5),1),
       ((8,9,5),3),
       ((7,10,5),5),
       ((8,10,6),14),
       ((9,10,7),5),
       ((8,11,7),11),
       ((9,11,8),11)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9,10}
      [((9,8,5),1),
       ((8,9,5),3),
       ((7,10,5),5),
       ((8,10,6),14),
       ((9,10,7),5),
       ((8,11,7),11),
       ((9,11,8),11)] := by
  decide +kernel
theorem covered : ∀ U ∈ (positiveSupport (edge τ 0)).powerset,
    ∃ L, PartialFlowCheck (numericAtoms τ) p 0 1 2 U L := by
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
end Flow134_01
end Omega.Turnpike.SubsetCertificate
