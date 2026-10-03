/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs
   mirror-E: none(waiver:fixed-signed-strip-cycle-walk-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Defs, mathlib/module/Mathlib.Algebra.Polynomial.Eval.Defs]
   utility: none
   digest: Cigler's identification of signed strip Dyck path sums with walks on a cycle. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkDefs

open Polynomial D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs

/-! Fixed public statement: Cigler, *Some sequences and number triangles which are related to
    Narayana polynomials and to q-Narayana polynomials for q=-1*, arXiv:2608.03363v2, §3,
    Conjecture 1, equation (74): for `k ≥ 1`, with `U_k` the adjacency matrix of the cycle on
    `4k` vertices, `c_{2n+1}^{(4k-2)} = U_k^{2n+1}(0,1)` and
    `c_{2n+2}^{(4k-2)} = U_k^{2n+2}(0,0) = 2 c_{2n+1}^{(4k-2)}`, where `c_r^{(H)}` is the sum over
    Dyck paths of semilength `r` in the strip of height `H` with down-step weights
    `(1, 1, -1, -1, …)`, that is `stripSum tauMinus H r` at `t = 1`.  The entry
    `U_k^r(0, a)` is the number of walks of `r` steps `±1` on `ℤ/4kℤ` from `0` to `a`. -/

/-- The number of walks of length `r` on the cycle `ℤ/Nℤ` from `0` to `a`, each step `±1`. -/
def walkCount (N r : ℕ) (a : ZMod N) : ℕ :=
  (Finset.univ.filter fun f : Fin r → Bool =>
    (∑ i, if f i then (1 : ZMod N) else -1) = a).card

/-- The signed count `c_r^{(H)} = c_r^{(H)}(1)`. -/
noncomputable def signedStrip (H r : ℕ) : ℤ := (stripSum tauMinus H r).eval 1

/-- Conjecture 1, equation (74). -/
def claim : Prop :=
  ∀ k n : ℕ, 1 ≤ k →
    signedStrip (4 * k - 2) (2 * n + 1) = walkCount (4 * k) (2 * n + 1) 1 ∧
      signedStrip (4 * k - 2) (2 * n + 2) = walkCount (4 * k) (2 * n + 2) 0 ∧
      (walkCount (4 * k) (2 * n + 2) 0 : ℤ) = 2 * signedStrip (4 * k - 2) (2 * n + 1)

end D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkDefs
