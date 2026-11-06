/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row00
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row00
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row01
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row01
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row02
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row02
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row03
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row03
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row04
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row04
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row05
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row05
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row06
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row06
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row07
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row07
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row08
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row08
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row09
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row09
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row10
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row10
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row11
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row11
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row12
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row12
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row13
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row13
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row14
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row14
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row15
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row15
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row16
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row16
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row17
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row17
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row18
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Row18
/-! # The sum of all nineteen exact exceptional19 zero-row cardinalities -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private rowZeroCount from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic
open private row_count_0 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row00
open private row_count_1 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row01
open private row_count_2 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row02
open private row_count_3 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row03
open private row_count_4 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row04
open private row_count_5 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row05
open private row_count_6 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row06
open private row_count_7 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row07
open private row_count_8 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row08
open private row_count_9 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row09
open private row_count_10 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row10
open private row_count_11 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row11
open private row_count_12 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row12
open private row_count_13 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row13
open private row_count_14 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row14
open private row_count_15 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row15
open private row_count_16 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row16
open private row_count_17 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row17
open private row_count_18 from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Row18

private theorem row_zero_count (m : ℕ) (hm : 27 ≤ m) :
    (∑ v ∈ Finset.range 19, rowZeroCount m v) = 1882 * m-93 := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, m=n + 27 := ⟨m-27,by omega⟩
  norm_num [Finset.sum_range_succ,
    row_count_0,row_count_1,row_count_2,row_count_3,row_count_4,
    row_count_5,row_count_6,row_count_7,row_count_8,row_count_9,
    row_count_10,row_count_11,row_count_12,row_count_13,row_count_14,
    row_count_15,row_count_16,row_count_17,row_count_18]
  omega



end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
