/- Prepared representation experiment, not compiled. The same complete local
states and mirror rows live in two array-backed vectors. The original local
transition functions, original lower sum and original replay are retained.
The generic simulation proof, once kernel checked, transfers a full numeric
receipt without a numeric equality receipt at each step. This experiment
asserts neither faster kernel evaluation nor complete global acceptance. -/
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
import Init.Data.Vector.MapIdx
import Init.Data.Vector.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMVectorCachePilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache CachedLocal)

section Simulation
variable {Coord Value Sym Source Target : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- A commuting state view transfers every actual-context replay. The node,
fuel, partial event, gap, lower predicate and symmetry predicate are identical.
This theorem does not identify distinct contexts with a shared node shape. -/
theorem check_view
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (sourceStep : Source → Coord → Value → Source)
    (targetStep : Target → Coord → Value → Target)
    (sourceLower : Source → ℤ) (targetLower : Target → ℤ)
    (view : Source → Target)
    (step_view : ∀ s i a, view (sourceStep s i a) = targetStep (view s) i a)
    (lower_view : ∀ s, sourceLower s = targetLower (view s))
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (fuel : ℕ) (index : Fin N) (s : Source) (p : Partial Coord Value) :
    check nodes sourceStep sourceLower dominates gap fuel index s p =
      check nodes targetStep targetLower dominates gap fuel index (view s) p := by
  induction fuel generalizing index s p with
  | zero => rfl
  | succ fuel ih =>
    cases node : nodes (fuel + 1) index with
    | bound => simp only [check, node, lower_view]
    | symmetry cut => simp only [check, node]
    | split i children =>
      simp only [check, node]
      apply congrArg (fun f : Value → Bool => decide (∀ a, f a = true))
      funext a
      rw [ih, step_view]
end Simulation

structure VectorCache where
  triangle : Vector (CachedLocal 41294) 16
  singleton : Vector (CachedLocal 8689) 16

def pack (cache : Cache) : VectorCache :=
  ⟨Vector.ofFn cache.triangle, Vector.ofFn cache.singleton⟩

def view (cache : VectorCache) : Cache :=
  ⟨fun k => cache.triangle[k.val], fun k => cache.singleton[k.val]⟩

theorem view_pack (cache : Cache) : view (pack cache) = cache := by
  cases cache with
  | mk triangles singletons =>
    apply congrArg₂ Cache.mk
    · funext k
      simp only [view, pack, Vector.getElem_ofFn]
    · funext k
      simp only [view, pack, Vector.getElem_ofFn]

/-- mapFinIdx constructs both complete vectors at each actual branch.
Unchanged blocks copy the same full CachedLocal value; changed blocks use the
unchanged original transition, including its entire next mirror payload. -/
def step (cache : VectorCache) (g : Fin 20) (a : Fin 4) : VectorCache :=
  ⟨cache.triangle.mapFinIdx fun k current hk =>
      match triangleIncidence g ⟨k, hk⟩ with
      | none => current
      | some i => EJMCacheState.triangleStep current i a,
   cache.singleton.mapFinIdx fun k current hk =>
      match singletonIncidence g ⟨k, hk⟩ with
      | none => current
      | some i => EJMCacheState.singletonStep current i a⟩

/-- Keep the original exact integer lower sum; only its state representation
changes. In particular, no packed approximation or scalar-only state is used. -/
def lower (cache : VectorCache) : ℤ := EJMCacheState.lower (view cache)

theorem view_step (cache : VectorCache) (g : Fin 20) (a : Fin 4) :
    view (step cache g a) = EJMCacheState.step (view cache) g a := by
  apply congrArg₂ Cache.mk
  · funext k
    simp only [view, step, EJMCacheState.step, Vector.getElem_mapFinIdx]
    rfl
  · funext k
    simp only [view, step, EJMCacheState.step, Vector.getElem_mapFinIdx]
    rfl

theorem lower_view (cache : VectorCache) :
    lower cache = EJMCacheState.lower (view cache) := rfl

/-- Prefix conversion is structural and polymorphic in the complete action
list. It is not an equality test over a materialized numerical cache. -/
theorem view_foldl {Action : Type*} (actions : List Action)
    (coordinate : Action → Fin 20) (outcome : Action → Fin 4)
    (cache : VectorCache) :
    view (actions.foldl (fun s a => step s (coordinate a) (outcome a)) cache) =
      actions.foldl
        (fun s a => EJMCacheState.step s (coordinate a) (outcome a)) (view cache) := by
  exact (List.foldl_hom view (fun s a => (view_step s (coordinate a) (outcome a)).symm)).symm

#print axioms check_view
#print axioms view_pack
#print axioms view_step
#print axioms view_foldl
end D5.S3.Quantum.Entanglement.EJM.EJMVectorCachePilot
