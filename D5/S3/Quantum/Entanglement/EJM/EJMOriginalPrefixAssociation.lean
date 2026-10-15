/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation
   mirror-E: none(waiver:original-prefix-cache-association)
   anchors: []
   utility: none
   digest: Arbitrary actual base-four prefixes retain all original local associations and leave future coordinates unknown. -/

/- Prepared source, uncompiled. This new module preserves the already accepted
EJMOriginalReplayAssembly source and avoids invalidating its 69 anchor imports.
Leading zero outcomes and arbitrary-code truncation retain their original depth.
No scalar-table receipt or full original global acceptance is asserted. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
  (coordinate prefixCache prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
  (initial AssociatedCache initial_associated step_associated)

/-- Before twenty updates, every original coordinate at or beyond the exact
prefix depth is still unknown. The depth is independent of the magnitude of
code, so zero-valued leading digits are retained and arbitrary codes are legal. -/
theorem prefixPartial_future_none (depth : ℕ) :
    ∀ (code : ℕ), depth ≤ 20 → ∀ (g : Fin 20), depth ≤ g.val →
      prefixPartial depth code g = none := by
  induction depth with
  | zero =>
    intro code within g future
    rfl
  | succ depth ih =>
    intro code within g future
    have below : depth < 20 := by omega
    have actualCoordinate : (coordinate depth).val = depth := by
      exact Nat.mod_eq_of_lt below
    have different : g ≠ coordinate depth := by
      intro same
      have sameValue := congrArg Fin.val same
      omega
    rw [prefixPartial, Function.update_of_ne different]
    exact ih (code / 4) (by omega) g (by omega)

/-- Every actual base-four prefix retains all thirty-two original local cache
associations. This uses only the original initial association and the proved
unknown-coordinate update law; no DAG split or global acceptance is assumed. -/
theorem prefix_associated (depth : ℕ) :
    ∀ (code : ℕ), depth ≤ 20 →
      AssociatedCache (prefixCache depth code) (prefixPartial depth code) := by
  induction depth with
  | zero =>
    intro code within
    exact initial_associated
  | succ depth ih =>
    intro code within
    have below : depth < 20 := by omega
    have unknown : prefixPartial depth (code / 4) (coordinate depth) = none := by
      apply prefixPartial_future_none depth (code / 4) (by omega) (coordinate depth)
      change depth ≤ depth % 20
      exact le_of_eq (Nat.mod_eq_of_lt below).symm
    let a : Fin 4 := ⟨code % 4, Nat.mod_lt _ (by decide)⟩
    change AssociatedCache
      (step (prefixCache depth (code / 4)) (coordinate depth) a)
      (Function.update (prefixPartial depth (code / 4)) (coordinate depth) (some a))
    exact step_associated _ _ (ih (code / 4) (by omega)) (coordinate depth) a unknown

/- Library search: no equivalent arbitrary-code prefix association or future
unknown-coordinate theorem was found in EJMOriginalReplayAssembly, the D5 EJM
modules or the persistent original-prefix prototypes. Existing initial_associated
and step_associated are reused directly. No literature novelty is claimed.
admission_basis: escape-witness
prefixPartial_future_none: proof_shape: content; escape_witness: structural
prefix induction establishes unknown status of every future actual coordinate.
Consumer: prefix_associated uses it at the next literal coordinate.
prefix_associated: proof_shape: content; escape_witness: structural induction
propagates all original local associations along every arbitrary-code prefix.
The live planned consumer is local terminal-table induction: select an actual
cache entry from this association and use the existing triangle_valid_lower or
singleton_valid_lower after checking its scalar lower-table entry. No full local
assignment receipt is inferred from a scalar equality. The anonymous prepared
consumer fragments demonstrate that interface and are not retained wrappers.
Both new public declarations still lack compiled source-owned four-slot audit
proofs and current binding evidence; unfinished registration is associated with
https://github.com/the-omega-institute/trureturing/issues/16309
This linked issue is no proof or validated registration. Mathematical source
preparation and subsequent kernel validation continue independently. -/

#print axioms prefixPartial_future_none
#print axioms prefix_associated
end D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
