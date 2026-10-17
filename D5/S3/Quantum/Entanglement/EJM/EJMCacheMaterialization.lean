/- Prepared benchmark helper only. Field-by-field equality establishes
that a literal prefix cache is exactly the computed cache, including its whole
state, integer lower, hash and every future-transition payload. These proofs
do not assume source correctness or earn complete global acceptance. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState

def LocalSame {N : ℕ} (a b : CachedLocal N) : Prop :=
  a.state = b.state ∧ a.row.hash = b.row.hash ∧ a.row.lower = b.row.lower ∧
    a.row.slots = b.row.slots ∧ a.row.edges = b.row.edges

instance {N : ℕ} (a b : CachedLocal N) : Decidable (LocalSame a b) := by
  unfold LocalSame
  infer_instance

def checkSame (a b : Cache) : Bool :=
  decide ((∀ k, LocalSame (a.triangle k) (b.triangle k)) ∧
    ∀ k, LocalSame (a.singleton k) (b.singleton k))

private theorem local_eq {N : ℕ} (a b : CachedLocal N) (h : LocalSame a b) : a = b := by
  cases a with
  | mk aState aRow =>
    cases b with
    | mk bState bRow =>
      cases aRow with
      | mk aHash aLower aSlots aEdges =>
        cases bRow with
        | mk bHash bLower bSlots bEdges =>
          obtain ⟨hs, hh, hl, ho, he⟩ := h
          cases hs
          cases hh
          cases hl
          cases ho
          cases he
          rfl

theorem checked_same (a b : Cache) (h : checkSame a b = true) : a = b := by
  change decide ((∀ k, LocalSame (a.triangle k) (b.triangle k)) ∧
    ∀ k, LocalSame (a.singleton k) (b.singleton k)) = true at h
  have full := of_decide_eq_true h
  cases a with
  | mk aTriangles aSingletons =>
    cases b with
    | mk bTriangles bSingletons =>
      have ht : aTriangles = bTriangles := by
        funext k
        exact local_eq _ _ (full.1 k)
      have hs : aSingletons = bSingletons := by
        funext k
        exact local_eq _ _ (full.2 k)
      cases ht
      cases hs
      rfl

#print axioms checked_same
end D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
