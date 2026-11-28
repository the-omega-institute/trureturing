/- GID: D5/S3/Combinatorics/Turnpike/SubsetPairs01/Check012
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sparse partial flows for one triangle and position pair -/

module
public import D5.S3.Combinatorics.Turnpike.PartialFlow
public import D5.S3.Combinatorics.Turnpike.SubsetRelations.Check456
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateData
/-! Omega original.
# Exact sparse partial flows for one triangle and position pair
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
open Omega.Turnpike
open scoped BigOperators
namespace Flow012_01
def τ : Triangle 7 := ⟨(0,1,2),by decide⟩
def p (z : Fin 3) := numerator (edge τ z)
set_option maxRecDepth 10000
private theorem case_0 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 ∅
      [] := by
  decide +kernel
private theorem case_1 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6}
      [((6,10,4),4), ((6,11,5),4)] := by
  decide +kernel
private theorem case_2 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7}
      [((7,9,4),4), ((7,10,5),4), ((7,11,6),11)] := by
  decide +kernel
private theorem case_3 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7}
      [((7,9,4),4), ((7,10,5),4), ((7,11,6),11)] := by
  decide +kernel
private theorem case_4 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8}
      [((8,8,4),4), ((8,9,5),4), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_5 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8}
      [((8,8,4),4), ((8,9,5),4), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_6 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8}
      [((8,8,4),4), ((8,9,5),4), ((8,10,6),4), ((7,11,6),7), ((8,11,7),11)] := by
  decide +kernel
private theorem case_7 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8}
      [((8,8,4),4), ((8,9,5),4), ((8,10,6),4), ((7,11,6),7), ((8,11,7),11)] := by
  decide +kernel
private theorem case_8 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9}
      [((9,8,5),4), ((9,9,6),7), ((9,10,7),4)] := by
  decide +kernel
private theorem case_9 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9}
      [((9,8,5),4), ((9,9,6),7), ((6,10,4),4)] := by
  decide +kernel
private theorem case_10 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9}
      [((9,8,5),4), ((7,9,4),4), ((9,9,6),3), ((9,10,7),4), ((7,11,6),8)] := by
  decide +kernel
private theorem case_11 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9}
      [((9,8,5),4), ((7,9,4),4), ((9,9,6),3), ((9,10,7),4), ((7,11,6),8)] := by
  decide +kernel
private theorem case_12 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9}
      [((8,8,4),4), ((9,8,5),4), ((9,9,6),7), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_13 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9}
      [((8,8,4),4), ((9,8,5),4), ((9,9,6),7), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_14 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9}
      [((8,8,4),4), ((9,8,5),4), ((9,9,6),7), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_15 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9}
      [((8,8,4),4), ((9,8,5),4), ((9,9,6),7), ((8,10,6),4), ((8,11,7),11)] := by
  decide +kernel
private theorem case_16 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {10}
      [((10,8,6),9), ((10,9,7),7), ((10,11,9),6)] := by
  decide +kernel
private theorem case_17 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,10}
      [((10,8,6),9), ((10,9,7),7), ((6,10,4),4), ((6,11,5),4), ((10,11,9),6)] := by
  decide +kernel
private theorem case_18 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,10}
      [((10,8,6),9), ((7,9,4),4), ((10,9,7),3), ((7,10,5),4), ((7,11,6),2), ((10,11,9),6)] := by
  decide +kernel
private theorem case_19 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,10}
      [((10,8,6),9), ((10,9,7),7), ((6,10,4),4), ((6,11,5),4), ((7,11,6),2), ((10,11,9),6)] := by
  decide +kernel
private theorem case_20 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,10}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((8,11,7),8),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_21 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,10}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((8,11,7),8),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_22 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,10}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((7,11,6),2),
       ((8,11,7),8),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_23 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,10}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((7,11,6),2),
       ((8,11,7),8),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_24 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9,10}
      [((9,8,5),4), ((10,8,6),5), ((9,9,6),6), ((10,9,7),1), ((9,10,7),4), ((10,11,9),6)] := by
  decide +kernel
private theorem case_25 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9,10}
      [((10,8,6),9), ((9,9,6),2), ((10,9,7),5), ((6,10,4),4), ((6,11,5),4), ((10,11,9),6)] := by
  decide +kernel
private theorem case_26 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9,10}
      [((9,8,5),4),
       ((10,8,6),5),
       ((7,9,4),4),
       ((10,9,7),3),
       ((9,10,7),4),
       ((7,11,6),6),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_27 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9,10}
      [((9,8,5),4),
       ((10,8,6),5),
       ((7,9,4),4),
       ((10,9,7),3),
       ((9,10,7),4),
       ((7,11,6),6),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_28 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9,10}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_29 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9,10}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_30 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9,10}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_31 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9,10}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6)] := by
  decide +kernel
private theorem case_32 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {11}
      [((11,8,7),9), ((11,10,9),4), ((11,11,10),14)] := by
  decide +kernel
private theorem case_33 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,11}
      [((11,8,7),9), ((6,10,4),4), ((6,11,5),4), ((11,11,10),14)] := by
  decide +kernel
private theorem case_34 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,11}
      [((11,8,7),9), ((7,9,4),4), ((7,10,5),4), ((7,11,6),11), ((11,11,10),14)] := by
  decide +kernel
private theorem case_35 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,11}
      [((11,8,7),9),
       ((7,9,4),4),
       ((11,10,9),4),
       ((6,11,5),4),
       ((7,11,6),11),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_36 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,11}
      [((8,8,4),4), ((11,8,7),5), ((8,9,5),4), ((8,10,6),4), ((8,11,7),6), ((11,11,10),14)] := by
  decide +kernel
private theorem case_37 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,11}
      [((8,8,4),4), ((11,8,7),5), ((8,9,5),4), ((8,10,6),4), ((8,11,7),6), ((11,11,10),14)] := by
  decide +kernel
private theorem case_38 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,11}
      [((8,8,4),3),
       ((11,8,7),6),
       ((7,9,4),1),
       ((8,9,5),4),
       ((11,10,9),4),
       ((7,11,6),11),
       ((8,11,7),5),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_39 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,11}
      [((8,8,4),3),
       ((11,8,7),6),
       ((7,9,4),1),
       ((8,9,5),4),
       ((11,10,9),4),
       ((7,11,6),11),
       ((8,11,7),5),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_40 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9,11}
      [((9,8,5),4), ((11,8,7),5), ((9,9,6),7), ((9,10,7),4), ((11,11,10),14)] := by
  decide +kernel
private theorem case_41 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9,11}
      [((11,8,7),9), ((9,9,6),7), ((6,10,4),4), ((6,11,5),4), ((11,11,10),14)] := by
  decide +kernel
private theorem case_42 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9,11}
      [((9,8,5),4),
       ((11,8,7),5),
       ((7,9,4),4),
       ((9,9,6),3),
       ((9,10,7),4),
       ((7,11,6),8),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_43 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9,11}
      [((11,8,7),9),
       ((7,9,4),4),
       ((9,9,6),3),
       ((9,10,7),2),
       ((11,10,9),2),
       ((6,11,5),4),
       ((7,11,6),8),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_44 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((11,8,7),1),
       ((9,9,6),7),
       ((8,10,6),4),
       ((8,11,7),10),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_45 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((11,8,7),1),
       ((9,9,6),7),
       ((8,10,6),4),
       ((8,11,7),10),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_46 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((11,8,7),1),
       ((9,9,6),7),
       ((11,10,9),4),
       ((7,11,6),4),
       ((8,11,7),10),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_47 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((11,8,7),1),
       ((9,9,6),7),
       ((11,10,9),4),
       ((7,11,6),4),
       ((8,11,7),10),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_48 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {10,11}
      [((10,8,6),9), ((10,9,7),7), ((11,10,9),4), ((10,11,9),2), ((11,11,10),14)] := by
  decide +kernel
private theorem case_49 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,10,11}
      [((10,8,6),9),
       ((10,9,7),7),
       ((6,10,4),4),
       ((6,11,5),4),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_50 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,10,11}
      [((10,8,6),1),
       ((11,8,7),8),
       ((7,9,4),4),
       ((10,9,7),3),
       ((7,10,5),4),
       ((7,11,6),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_51 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,10,11}
      [((10,8,6),1),
       ((11,8,7),8),
       ((7,9,4),4),
       ((10,9,7),3),
       ((7,10,5),4),
       ((7,11,6),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_52 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,10,11}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((8,11,7),8),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_53 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,10,11}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((8,11,7),8),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_54 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,10,11}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((7,11,6),2),
       ((8,11,7),8),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_55 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,10,11}
      [((8,8,4),4),
       ((10,8,6),5),
       ((8,9,5),4),
       ((10,9,7),3),
       ((8,10,6),4),
       ((7,11,6),2),
       ((8,11,7),8),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_56 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {9,10,11}
      [((9,8,5),4),
       ((10,8,6),5),
       ((9,9,6),6),
       ((10,9,7),1),
       ((9,10,7),4),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_57 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,9,10,11}
      [((10,8,6),5),
       ((11,8,7),4),
       ((9,9,6),6),
       ((10,9,7),1),
       ((6,10,4),4),
       ((6,11,5),4),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_58 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,9,10,11}
      [((9,8,5),4),
       ((11,8,7),5),
       ((7,9,4),4),
       ((9,9,6),1),
       ((10,9,7),2),
       ((9,10,7),4),
       ((7,11,6),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_59 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,9,10,11}
      [((10,8,6),2),
       ((11,8,7),7),
       ((7,9,4),4),
       ((9,9,6),3),
       ((9,10,7),4),
       ((6,11,5),4),
       ((7,11,6),6),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_60 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {8,9,10,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_61 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,8,9,10,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_62 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {7,8,9,10,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
  decide +kernel
private theorem case_63 :
    PartialFlowCheck (numericAtoms τ) p 0 1 2 {6,7,8,9,10,11}
      [((8,8,4),4),
       ((9,8,5),4),
       ((10,8,6),1),
       ((9,9,6),7),
       ((8,10,6),3),
       ((9,10,7),1),
       ((8,11,7),10),
       ((10,11,9),6),
       ((11,11,10),14)] := by
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
       {6,7,8,9,10},
       {11},
       {6,11},
       {7,11},
       {6,7,11},
       {8,11},
       {6,8,11},
       {7,8,11},
       {6,7,8,11},
       {9,11},
       {6,9,11},
       {7,9,11},
       {6,7,9,11},
       {8,9,11},
       {6,8,9,11},
       {7,8,9,11},
       {6,7,8,9,11},
       {10,11},
       {6,10,11},
       {7,10,11},
       {6,7,10,11},
       {8,10,11},
       {6,8,10,11},
       {7,8,10,11},
       {6,7,8,10,11},
       {9,10,11},
       {6,9,10,11},
       {7,9,10,11},
       {6,7,9,10,11},
       {8,9,10,11},
       {6,8,9,10,11},
       {7,8,9,10,11},
       {6,7,8,9,10,11}} := by decide +kernel
  rw [cover] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  · subst U; exact ⟨_, case_32⟩
  · subst U; exact ⟨_, case_33⟩
  · subst U; exact ⟨_, case_34⟩
  · subst U; exact ⟨_, case_35⟩
  · subst U; exact ⟨_, case_36⟩
  · subst U; exact ⟨_, case_37⟩
  · subst U; exact ⟨_, case_38⟩
  · subst U; exact ⟨_, case_39⟩
  · subst U; exact ⟨_, case_40⟩
  · subst U; exact ⟨_, case_41⟩
  · subst U; exact ⟨_, case_42⟩
  · subst U; exact ⟨_, case_43⟩
  · subst U; exact ⟨_, case_44⟩
  · subst U; exact ⟨_, case_45⟩
  · subst U; exact ⟨_, case_46⟩
  · subst U; exact ⟨_, case_47⟩
  · subst U; exact ⟨_, case_48⟩
  · subst U; exact ⟨_, case_49⟩
  · subst U; exact ⟨_, case_50⟩
  · subst U; exact ⟨_, case_51⟩
  · subst U; exact ⟨_, case_52⟩
  · subst U; exact ⟨_, case_53⟩
  · subst U; exact ⟨_, case_54⟩
  · subst U; exact ⟨_, case_55⟩
  · subst U; exact ⟨_, case_56⟩
  · subst U; exact ⟨_, case_57⟩
  · subst U; exact ⟨_, case_58⟩
  · subst U; exact ⟨_, case_59⟩
  · subst U; exact ⟨_, case_60⟩
  · subst U; exact ⟨_, case_61⟩
  · subst U; exact ⟨_, case_62⟩
  · subst U; exact ⟨_, case_63⟩
end Flow012_01
end Omega.Turnpike.SubsetCertificate
