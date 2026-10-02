/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding
   mirror-E: none(waiver:royal-dyck-encoding)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Interleaves two occurrence orders according to a Dyck word. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalEncoding

open DyckStep

def weave : List ℕ → List ℕ → List DyckStep → Option (List ℕ)
  | [], [], [] => some []
  | a :: p, q, U :: d => (weave p q d).map (a :: ·)
  | p, a :: q, D :: d => (weave p q d).map (a :: ·)
  | _, _, _ => none
def select (s : DyckStep) : List DyckStep → List ℕ → List ℕ
  | t :: d, a :: w => if t = s then a :: select s d w else select s d w
  | _, _ => []
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalEncoding
