/- GID: D5/S3/Arith/CharacterSums/KotesovecConjectureTwo
   generality: I
   mirror-B: D5/B/S3/Arith/CharacterSums/KotesovecConjectureTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Biquadratefree powerful moduli and four further moduli have nonzero sums. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19384
admission_basis: open-problem-resolution (#19242; Proved)
Direct frozen dependency: D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration
  Lean name: D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast
  declaration statement_id: sha256:6062729cd00b090edb5dfcccd635f4a563a8a66f60deb5d1c6d91f2195edc1b1
claimTwo retains its preregistered expression. The module uses open-problem
resolution for admission. escape_witness: none.
Per-declaration proof-shape proposals and immediate consumers:
(Names without a module prefix belong to this module.)
definition: claimTwo; consumers: result.
proof_shape: result = content; consumers: external conjecture settlement.
-/

import D5.S3.Arith.CharacterSums.KotesovecConjectureOne

namespace D5.S3.Arith.CharacterSums.KotesovecConjectureTwo

open D5.S3.Arith.CharacterSums.KotesovecConjectureOne

/-- Conjecture 2: A368959 contains all the terms of A338325, and 243, 972, 1944 and 2401. -/
def claimTwo : Prop :=
  (∀ m : ℕ, InA338325 m → InA368959 m) ∧
    InA368959 243 ∧ InA368959 972 ∧ InA368959 1944 ∧ InA368959 2401


theorem result : claimTwo := by
  refine ⟨family_inclusion, ?_, ?_, ?_, ?_⟩
  · exact good_to_membership 243 good_243
  · exact good_to_membership 972 (show Good (4*243) from
      good_mul (by exact Nat.coprime_iff_gcd_eq_one.mp rfl)
        (good_prime_square (p := 2) (by exact Nat.prime_two)) good_243)
  · exact good_to_membership 1944 (show Good (8*243) from
      good_mul (by exact Nat.coprime_iff_gcd_eq_one.mp rfl)
        (good_prime_cube (p := 2) (by exact Nat.prime_two)) good_243)
  · exact good_to_membership 2401 good_2401


end D5.S3.Arith.CharacterSums.KotesovecConjectureTwo
