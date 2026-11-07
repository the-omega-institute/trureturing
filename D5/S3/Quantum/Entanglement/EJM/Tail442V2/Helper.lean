/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Helper
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.node442_split,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.node0_bound,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.cachedLocal_eq_of_fields,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.fields_of_cachedLocal_eq,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.step_at18_eq_of_local_fields,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.tail442,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.cache_eq_of_checked
   digest: Full local-field equality and all original branch bounds support the exact node-442 replay check without discarding cache or partial-assignment inputs. -/

/- Prepared candidate only: not deployed, parsed, elaborated or kernel accepted.
   Pinned source: H276e23e3c6556d941ea7b5d0b8af938ea8b7db31.
   Proposed temporary module: D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper.
   No existing raw-cut acceptance theorem is imported or used. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper

open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
  (check checked_split checked_split_node)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial Accepted)
open EJMCacheState (Cache CachedLocal triangleStep singletonStep step lower)
open EJMLocalCacheData (triangleIncidence singletonIncidence)
open EJMPartialBoundData (scale)

abbrev ReplayNode :=
  Node EJMOriginalGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut

/-- Boolean constructor check avoids requiring equality of function-valued Nodes. -/
private def isBound : ReplayNode → Bool
  | .bound => true
  | _ => false

private theorem bound_of_isBound (node : ReplayNode)
    (accepted : isBound node = true) : node = .bound := by
  cases node with
  | bound => rfl
  | symmetry s => simp only [isBound, Bool.false_eq_true] at accepted
  | split i children => simp only [isBound, Bool.false_eq_true] at accepted

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
-- Independent original decoder receipt: no cache, shape substitution or cut theorem.
private theorem node442_split_receipt :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkSplit
      (EJMOriginalGlobalDAGData.nodes 3 ⟨442, by decide⟩)
      (coordinate 18) (fun _ : Fin 4 => ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node442_split : EJMOriginalGlobalDAGData.nodes 3 ⟨442, by decide⟩ =
    .split (coordinate 18) (fun _ : Fin 4 => ⟨0, by decide⟩) :=
  checked_split_node _ _ _ node442_split_receipt

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
-- Separate receipt for the exact original child node and its actual remaining fuel.
private theorem node0_bound_receipt :
    isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node0_bound : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ node0_bound_receipt

/-- State includes the row index and both action IDs; all four MirrorRow fields
are also premises. This relation asserts complete equality, not association. -/
def FullLocalFields {N : ℕ} (actual proposed : CachedLocal N) : Prop :=
  actual.state = proposed.state ∧
    actual.row.hash = proposed.row.hash ∧ actual.row.lower = proposed.row.lower ∧
    actual.row.slots = proposed.row.slots ∧ actual.row.edges = proposed.row.edges

theorem cachedLocal_eq_of_fields {N : ℕ} (actual proposed : CachedLocal N)
    (fields : FullLocalFields actual proposed) : actual = proposed := by
  cases actual with
  | mk actualState actualRow =>
    cases proposed with
    | mk proposedState proposedRow =>
      cases actualRow with
      | mk actualHash actualLower actualSlots actualEdges =>
        cases proposedRow with
        | mk proposedHash proposedLower proposedSlots proposedEdges =>
          obtain ⟨hs, hh, hl, ho, he⟩ := fields
          cases hs
          cases hh
          cases hl
          cases ho
          cases he
          rfl

theorem fields_of_cachedLocal_eq {N : ℕ} (actual proposed : CachedLocal N)
    (equal : actual = proposed) : FullLocalFields actual proposed := by
  cases equal
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem cache_eq_of_rows (actual proposed : Cache)
    (triangle : ∀ k, actual.triangle k = proposed.triangle k)
    (singleton : ∀ k, actual.singleton k = proposed.singleton k) : actual = proposed := by
  cases actual with
  | mk actualTriangles actualSingletons =>
    cases proposed with
    | mk proposedTriangles proposedSingletons =>
      have ht : actualTriangles = proposedTriangles := funext triangle
      have hs : actualSingletons = proposedSingletons := funext singleton
      cases ht
      cases hs
      rfl

/-- All sixteen triangle and sixteen singleton outputs must match completely.
At an affected row, a proved full triangleStep/singletonStep equality supplies
these fields via fields_of_cachedLocal_eq. At an unaffected row, prove that the
whole old CachedLocal is copied. Finite enumeration may discharge the 32 cases.
No row hash, lower or association alone can discharge either premise. -/
theorem step_at18_eq_of_local_fields (cache nextCache : Cache) (a : Fin 4)
    (triangle : ∀ k : Fin 16, FullLocalFields
      (match triangleIncidence (coordinate 18) k with
       | none => cache.triangle k
       | some i => triangleStep (cache.triangle k) i a)
      (nextCache.triangle k))
    (singleton : ∀ k : Fin 16, FullLocalFields
      (match singletonIncidence (coordinate 18) k with
       | none => cache.singleton k
       | some i => singletonStep (cache.singleton k) i a)
      (nextCache.singleton k)) :
    step cache (coordinate 18) a = nextCache := by
  apply cache_eq_of_rows
  · intro k
    change (match triangleIncidence (coordinate 18) k with
      | none => cache.triangle k
      | some i => triangleStep (cache.triangle k) i a) = nextCache.triangle k
    exact cachedLocal_eq_of_fields _ _ (triangle k)
  · intro k
    change (match singletonIncidence (coordinate 18) k with
      | none => cache.singleton k
      | some i => singletonStep (cache.singleton k) i a) = nextCache.singleton k
    exact cachedLocal_eq_of_fields _ _ (singleton k)

/-- Exact original check at this tail, for its entire cache and actual partial.
Only the node equalities are reusable between contexts. Every caller still
supplies its own four full step equalities and original lower inequalities. -/
theorem tail442 (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (nextCache : Fin 4 → Cache)
    (next : ∀ a, step cache (coordinate 18) a = nextCache a)
    (bounds : ∀ a, scale ≤ lower (nextCache a)) :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨442, by decide⟩ cache p = true := by
  apply checked_split EJMOriginalGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale 2 ⟨442, by decide⟩ cache p
    (coordinate 18) (fun _ : Fin 4 => ⟨0, by decide⟩) node442_split
  intro a
  rw [next a]
  simp only [check, node0_bound]
  exact decide_eq_true (bounds a)


instance {N : ℕ} (actual proposed : CachedLocal N) :
    Decidable (FullLocalFields actual proposed) := by
  unfold FullLocalFields
  infer_instance

/-- Full equality guard checks all 32 states and every MirrorRow field. -/
def checkFullCache (actual proposed : Cache) : Bool :=
  decide ((∀ k, FullLocalFields (actual.triangle k) (proposed.triangle k)) ∧
    ∀ k, FullLocalFields (actual.singleton k) (proposed.singleton k))

theorem cache_eq_of_checked (actual proposed : Cache)
    (accepted : checkFullCache actual proposed = true) : actual = proposed := by
  change decide ((∀ k, FullLocalFields (actual.triangle k) (proposed.triangle k)) ∧
    ∀ k, FullLocalFields (actual.singleton k) (proposed.singleton k)) = true at accepted
  have fields := of_decide_eq_true accepted
  apply cache_eq_of_rows
  · intro k
    exact cachedLocal_eq_of_fields _ _ (fields.1 k)
  · intro k
    exact cachedLocal_eq_of_fields _ _ (fields.2 k)

#print axioms node442_split
#print axioms node0_bound
#print axioms step_at18_eq_of_local_fields
#print axioms tail442
#print axioms cache_eq_of_checked

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
