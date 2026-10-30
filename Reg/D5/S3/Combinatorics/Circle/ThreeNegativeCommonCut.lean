import D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut

structure Source where
  a : ℕ
  c : ℕ

def Assumptions (q : Source) : Prop := 2 ≤ q.c ∧ q.c < q.a

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
