/- GID: D5/S0/Computability/CodeFixedPoint
   generality: G
   mirror-B: D5/B/S0/Computability/CodeFixedPoint
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Every computable transformation of partial recursive codes fixes some code's behavior. -/

import Mathlib.Computability.PartrecCode

namespace D5.S0.Computability.CodeFixedPoint

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)
open Encodable (encode)
open Denumerable (ofNat)

/-- **The code fixed-point theorem.** Every computable transformation `F` of
partial recursive codes admits a code `e` whose described program behaves
exactly as the program described by `F e`. This is a thin honest wrapper
around Mathlib's `Nat.Partrec.Code.fixed_point` (Rogers' fixed-point
theorem), restated with the fixed code on the left of the equality. -/
theorem code_fixed_point {F : Code → Code} (hF : Computable F) :
    ∃ e : Code, eval e = eval (F e) :=
  (Nat.Partrec.Code.fixed_point hF).imp fun _e h => h.symm

/-- The successor transformation on code numerals — decode, add one on the
numeral side, re-encode — is computable. -/
theorem succ_code_transformation_computable :
    Computable fun c : Code => ofNat Code (encode c + 1) :=
  (Computable.ofNat Code).comp (Primrec.succ.to_comp.comp Computable.encode)

/-- Witness instantiation of the fixed point: some pair of consecutive code
numerals describes one and the same partial function, so the numbering of
programs repeats behavior at adjacent addresses. -/
theorem exists_consecutive_codes_equal_behavior :
    ∃ e : Code, eval e = eval (ofNat Code (encode e + 1)) :=
  code_fixed_point succ_code_transformation_computable

end D5.S0.Computability.CodeFixedPoint
