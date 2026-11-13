/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: none
   digest: Induction on every original base-four prefix keeps all future coordinates unknown and preserves all thirty-two local cache associations. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
  (initial AssociatedCache initial_associated step_associated)

/-- The natural original coordinate at a prefix depth. The assembly theorem
restricts this coordinate to depths below twenty. -/
def coordinate (depth : ℕ) : Fin 20 := ⟨depth % 20, Nat.mod_lt _ (by decide)⟩

/-- All thirty-two original states are computed from the actual initial cache
and every digit of the prefix, including leading zero outcomes. -/
def prefixCache : ℕ → ℕ → Cache
  | 0, _ => initial
  | depth + 1, code => step (prefixCache depth (code / 4)) (coordinate depth)
      ⟨code % 4, Nat.mod_lt _ (by decide)⟩

/-- The partial assignment follows exactly the same prefix and updates as the
cache. Its depth remains explicit, so leading zeros never discard coordinates. -/
def prefixPartial : ℕ → ℕ → Partial (Fin 20) (Fin 4)
  | 0, _ => fun _ => none
  | depth + 1, code => Function.update (prefixPartial depth (code / 4))
      (coordinate depth) (some ⟨code % 4, Nat.mod_lt _ (by decide)⟩)

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

#print axioms prefixPartial_future_none
#print axioms prefix_associated
end D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
