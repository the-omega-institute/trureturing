/- GID: D5/S3/Factorization/Galois/SparseCharacterSynchronization
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/SparseCharacterSynchronization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse edge differences detect exactly the common phase iff the graph is preconnected. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
namespace D5.S3.Factorization.Galois.SparseCharacterSynchronization

/-- Compare labels on ordered adjacent vertex pairs in a single coefficient group. -/
def edgeDifference {V : Type u} (G : SimpleGraph V) (A : Type v) [AddCommGroup A] :
    (V → A) →+ ({e : V × V // G.Adj e.1 e.2} → A) where
  toFun x := fun e => x e.val.1 - x e.val.2
  map_zero' := by funext e; exact sub_self _
  map_add' x y := by
    funext e
    change (x e.val.1 + y e.val.1) - (x e.val.2 + y e.val.2) = _
    change _ = (x e.val.1 - x e.val.2) + (y e.val.1 - y e.val.2)
    abel

/-- Sparse comparisons leave only a common phase exactly when every pair of vertices
is joined by a path. The empty vertex set is included by preconnectedness. -/
theorem edge_difference_kernel_eq_constants_iff
    {V : Type u} (G : SimpleGraph V) (A : Type v) [AddCommGroup A] [Nontrivial A] :
    (edgeDifference G A).ker = (Pi.constAddMonoidHom V A).range ↔ G.Preconnected := by
  classical
  constructor
  · intro h u v
    by_contra huv
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    let x : V → A := fun w => if G.Reachable u w then 0 else a
    have hx : x ∈ (edgeDifference G A).ker := by
      rw [AddMonoidHom.mem_ker]
      funext e
      have he : G.Reachable u e.val.1 ↔ G.Reachable u e.val.2 :=
        ⟨fun hw => hw.trans e.property.reachable,
          fun hw => hw.trans e.property.symm.reachable⟩
      change x e.val.1 - x e.val.2 = 0
      simp [x, he]
    rw [h] at hx
    obtain ⟨b, hb⟩ := hx
    have hu : b = 0 := by
      have : b = x u := congrFun hb u
      simpa [x] using this
    have hv : b = a := by
      have : b = x v := congrFun hb v
      simpa [x, huv] using this
    exact ha (hv.symm.trans hu)
  · intro hG
    apply le_antisymm
    · intro x hx
      have hadj {a b : V} (hab : G.Adj a b) : x a = x b := by
        have he := congrFun (AddMonoidHom.mem_ker.mp hx) ⟨(a, b), hab⟩
        exact sub_eq_zero.mp he
      have hwalk {a b : V} (p : G.Walk a b) : x a = x b := by
        induction p with
        | nil => rfl
        | @cons a b c hab p ih => exact (hadj hab).trans ih
      by_cases hV : Nonempty V
      · obtain ⟨base⟩ := hV
        refine ⟨x base, ?_⟩
        funext w
        exact (hG base w).elim hwalk
      · refine ⟨0, ?_⟩
        funext w
        exact False.elim (hV ⟨w⟩)
    · rintro x ⟨a, rfl⟩
      rw [AddMonoidHom.mem_ker]
      funext e
      exact sub_self a

#print axioms edge_difference_kernel_eq_constants_iff

end D5.S3.Factorization.Galois.SparseCharacterSynchronization
