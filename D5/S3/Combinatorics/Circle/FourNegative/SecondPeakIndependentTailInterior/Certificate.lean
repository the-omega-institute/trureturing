/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Certificate
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:private-consumed-UXWV-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Constructed integer endpoint checks for both original source rows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Values
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb r s v from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private modelExpr model_nonnegative from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Arithmetic
open private bank terminal order blocks word physical_inventory positive_bank from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Physical
open private Nq head_coordinates modulus_coordinate cap_coordinate negative_coordinates mass_coordinates from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Values
open private qHead qNewHead qMask qMass qNegative qPeak qExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
open PacketNormalForm
open private size sourceMod base oldValue newValue negatives chain_values packet_masses from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private offsets lengths from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
private def iMass (p : Parameters) (row bankIndex : Fin 4) : ℤ :=
  ((bank p bankIndex).map (if row = 0 then oldValue p.a p.b p.c p.d
    else newValue p.a p.b p.c p.d)).sum
private def iNegative (p : Parameters) (row j : Fin 4) : ℤ :=
  (if row = 0 then oldValue p.a p.b p.c p.d else newValue p.a p.b p.c p.d)
    (terminal p (order j))
private def iPeak (p : Parameters) (row j : Fin 4) : ℤ :=
  let m := iMass p row
  let n := iNegative p row
  let e := if row = 0 then 0 else base p.a p.b p.c p.d 0
  ![e+m 0,e+m 0+n 0+m 1,e+m 0+n 0+m 1+n 1+m 2,
    e+m 0+n 0+m 1+n 1+m 2+n 2+m 3] j
private def iCap (p : Parameters) (row : Fin 4) : ℤ :=
  if row = 0 then sourceMod p.a p.b p.c p.d/2 else sourceMod p.a p.b p.c p.d

private theorem expr_coordinate (p : Parameters) (row kind j : Fin 4)
    (hr : row.val < 2) (hk : kind.val < 2) :
    modelExpr p row kind j =
      if kind = 0 then ((iPeak p row j+iNegative p row j : ℤ) : ℚ)
      else ((iCap p row-iPeak p row j : ℤ) : ℚ) := by
  have hn00 := (negative_coordinates p 0).1
  have hn01 := (negative_coordinates p 1).1
  have hn02 := (negative_coordinates p 2).1
  have hn03 := (negative_coordinates p 3).1
  have hn10 := (negative_coordinates p 0).2
  have hn11 := (negative_coordinates p 1).2
  have hn12 := (negative_coordinates p 2).2
  have hn13 := (negative_coordinates p 3).2
  dsimp only [order] at hn00 hn01 hn02 hn03 hn10 hn11 hn12 hn13
  fin_cases row <;> fin_cases kind <;> fin_cases j
  all_goals first | omega | skip
  all_goals dsimp [modelExpr,qExpr,qPeak,iPeak,iMass,iNegative,iCap,order]
  all_goals push_cast
  all_goals simp_rw [(mass_coordinates p _).1,(mass_coordinates p _).2,
    hn00,hn01,hn02,hn03,hn10,hn11,hn12,hn13,
    (head_coordinates p _).1,cap_coordinate,modulus_coordinate]
  all_goals dsimp only [Nq]
  all_goals ring

private theorem endpoint_inequalities (p : Parameters) (row j : Fin 4) (hr : row.val < 2) :
    0 ≤ iPeak p row j+iNegative p row j ∧ iPeak p row j ≤ iCap p row := by
  have hs := model_nonnegative p row 0 j hr (by decide)
  have ht := model_nonnegative p row 1 j hr (by decide)
  rw [expr_coordinate p row 0 j hr (by decide),if_pos rfl] at hs
  rw [expr_coordinate p row 1 j hr (by decide),if_neg (by decide)] at ht
  have hs' : 0 ≤ iPeak p row j+iNegative p row j := by exact_mod_cast hs
  have ht' : 0 ≤ iCap p row-iPeak p row j := by exact_mod_cast ht
  exact ⟨hs',by omega⟩

private theorem old_packet_checks (p : Parameters) :
    packetChecks (oldValue p.a p.b p.c p.d) (sourceMod p.a p.b p.c p.d/2) 0 (blocks p) := by
  have h0 := endpoint_inequalities p 0 0 (by decide)
  have h1 := endpoint_inequalities p 0 1 (by decide)
  have h2 := endpoint_inequalities p 0 2 (by decide)
  have h3 := endpoint_inequalities p 0 3 (by decide)
  simpa [packetChecks,blocks,iPeak,iMass,iNegative,iCap,order,add_assoc] using
    (show (0 ≤ iPeak p 0 0+iNegative p 0 0) ∧ iPeak p 0 0 ≤ iCap p 0 ∧
      (0 ≤ iPeak p 0 1+iNegative p 0 1) ∧ iPeak p 0 1 ≤ iCap p 0 ∧
      (0 ≤ iPeak p 0 2+iNegative p 0 2) ∧ iPeak p 0 2 ≤ iCap p 0 ∧
      (0 ≤ iPeak p 0 3+iNegative p 0 3) ∧ iPeak p 0 3 ≤ iCap p 0 ∧ True from
      ⟨h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,True.intro⟩)

private theorem new_packet_checks (p : Parameters) :
    packetChecks (newValue p.a p.b p.c p.d) (sourceMod p.a p.b p.c p.d) 0
      (withEar (size p.a p.b p.c p.d) 0 (blocks p)) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  have hear := (chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)).2.2.2
  have h0 := endpoint_inequalities p 1 0 (by decide)
  have h1 := endpoint_inequalities p 1 1 (by decide)
  have h2 := endpoint_inequalities p 1 2 (by decide)
  have h3 := endpoint_inequalities p 1 3 (by decide)
  simpa [packetChecks,withEar,blocks,iPeak,iMass,iNegative,iCap,order,
    List.map_append,List.sum_append,hear,add_comm,add_left_comm,add_assoc] using
    (show (0 ≤ iPeak p 1 0+iNegative p 1 0) ∧ iPeak p 1 0 ≤ iCap p 1 ∧
      (0 ≤ iPeak p 1 1+iNegative p 1 1) ∧ iPeak p 1 1 ≤ iCap p 1 ∧
      (0 ≤ iPeak p 1 2+iNegative p 1 2) ∧ iPeak p 1 2 ≤ iCap p 1 ∧
      (0 ≤ iPeak p 1 3+iNegative p 1 3) ∧ iPeak p 1 3 ≤ iCap p 1 ∧ True from
      ⟨h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,True.intro⟩)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
