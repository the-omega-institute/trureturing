/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableCertificates
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Sixteen exact universal physical window and stock inequalities per residue row. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.TableData
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.ResidueCertificates1
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.ResidueCertificates2
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.ResidueCertificates3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

theorem residue_bounds (i : Fin 24) (R : ℕ) :
    let row:=residueRows i
    rowBounds 8 row.p (72*(R:ℤ)+row.r) row.h
      (row.p*(72*(R:ℤ)+row.r)-row.offset) row.m
      (row.block*(R:ℤ)+row.constant) row.before := by
  fin_cases i
  · exact residue_bounds_0 R (by positivity)
  · exact residue_bounds_1 R (by positivity)
  · exact residue_bounds_2 R (by positivity)
  · exact residue_bounds_3 R (by positivity)
  · exact residue_bounds_4 R (by positivity)
  · exact residue_bounds_5 R (by positivity)
  · exact residue_bounds_6 R (by positivity)
  · exact residue_bounds_7 R (by positivity)
  · exact residue_bounds_8 R (by positivity)
  · exact residue_bounds_9 R (by positivity)
  · exact residue_bounds_10 R (by positivity)
  · exact residue_bounds_11 R (by positivity)
  · exact residue_bounds_12 R (by positivity)
  · exact residue_bounds_13 R (by positivity)
  · exact residue_bounds_14 R (by positivity)
  · exact residue_bounds_15 R (by positivity)
  · exact residue_bounds_16 R (by positivity)
  · exact residue_bounds_17 R (by positivity)
  · exact residue_bounds_18 R (by positivity)
  · exact residue_bounds_19 R (by positivity)
  · exact residue_bounds_20 R (by positivity)
  · exact residue_bounds_21 R (by positivity)
  · exact residue_bounds_22 R (by positivity)
  · exact residue_bounds_23 R (by positivity)

theorem residue_submask (i : Fin 24) (R : ℕ) :
    Submask (residueRows i).m ((residueRows i).block*R+(residueRows i).constant) := by
  fin_cases i
  · exact residue_submask_0 R
  · exact residue_submask_1 R
  · exact residue_submask_2 R
  · exact residue_submask_3 R
  · exact residue_submask_4 R
  · exact residue_submask_5 R
  · exact residue_submask_6 R
  · exact residue_submask_7 R
  · exact residue_submask_8 R
  · exact residue_submask_9 R
  · exact residue_submask_10 R
  · exact residue_submask_11 R
  · exact residue_submask_12 R
  · exact residue_submask_13 R
  · exact residue_submask_14 R
  · exact residue_submask_15 R
  · exact residue_submask_16 R
  · exact residue_submask_17 R
  · exact residue_submask_18 R
  · exact residue_submask_19 R
  · exact residue_submask_20 R
  · exact residue_submask_21 R
  · exact residue_submask_22 R
  · exact residue_submask_23 R

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
