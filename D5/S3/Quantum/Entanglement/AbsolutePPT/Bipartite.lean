/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/Bipartite
   mirror-E: none(waiver:shared-generic-primitives)
   anchors: []
   utility: none
   digest: Shared second-factor partial transpose and literal all-unitary APPT on finite product systems. -/

import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
Canonical shared definitions extracted from KickedIsingNegativityRefutation
and QutritPerturbationAttainment. Those instance owners retain their original
public definitions as transparent delegates, with the same types and meanings.
The abbreviations keep those delegates transparent to their existing proofs.

These are consumed mathematical primitives, not independent theorem deposits:
ContractionAttainment uses partialTranspose in its ordered-pair identity and
positivity proof, and APPT in contraction_appt and five_row_attainment.
No physical instance, fixed local dimension or restricted unitary family is
part of either definition. utility: none reflects mathematical operations and
predicates rather than an enumerator, checker, numeric reduction or instance.
-/

set_option autoImplicit false
open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

/-- Transpose only the second factor, with no finiteness or dimension assumption. -/
abbrev partialTranspose {A B : Type*} (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun p q => ρ (p.1,q.2) (q.1,p.2)

/-- Positivity of the second-factor partial transpose after every global unitary. -/
abbrev APPT {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ U : unitaryGroup (A × B) ℂ, partialTranspose ((U : Matrix _ _ ℂ) * M * (U : Matrix _ _ ℂ)ᴴ) |>.PosSemidef

end D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
