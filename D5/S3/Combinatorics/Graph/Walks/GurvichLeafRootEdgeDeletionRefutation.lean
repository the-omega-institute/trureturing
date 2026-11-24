/- GID: D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim; result=D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result; claim=D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.claim
   digest: Deleting the first edge of a rooted six-vertex path can destroy inherence. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases

/-! The rooted six-vertex path remains avoidable in every containing host.
Deleting its first edge lets a four-arm tree confine every copy. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace GurvichLeafRootEdgeDeletionRefutation

open SimpleGraph
open scoped Sym2

variable {V : Type} {G : SimpleGraph V} {n : ℕ}

private def Extension {H : SimpleGraph (Fin n)}
    (f : Copy H G) (s t : Fin n) (x y : V) : Prop :=
  x ∉ Set.range f ∧ y ∉ Set.range f ∧ x ≠ y ∧ G.Adj (f s) x ∧ G.Adj (f t) y

private def Avoidable {H : SimpleGraph (Fin n)} (f : Copy H G) (s t : Fin n) : Prop :=
  ∀ x y, (h : Extension f s t x y) →
    (G.induce (Set.range f)ᶜ).Reachable ⟨x, h.1⟩ ⟨y, h.2.1⟩

private def Inherent (H : SimpleGraph (Fin n)) (s t : Fin n) : Prop :=
  ∀ (m : ℕ) (G : SimpleGraph (Fin m)), Nonempty (Copy H G) → ∃ f : Copy H G, Avoidable f s t

/-- The complete finite statement of Gurvich–Krnc–Milanič–Vyalyi Conjecture 6.4. -/
public noncomputable def claim : Prop := by
  classical
  exact ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (s t u : Fin n),
    H.degree s ≤ H.degree t → s ≠ t → (∀ v, H.Adj s v ↔ v = u) → Inherent H s t →
      Inherent (H.deleteEdges {s(s, u)}) s t

private abbrev Path6 (G : SimpleGraph V) := Copy (pathGraph 6) G

private def pathOfSteps (f : Fin 6 → V) (hf : Function.Injective f)
    (steps : ∀ i : Fin 5, G.Adj (f i.castSucc) (f i.succ)) : Path6 G where
  toHom := {
    toFun := f
    map_rel' := by
      intro i j hij
      rcases pathGraph_adj.mp hij with h | h
      · let k : Fin 5 := ⟨i.val, by omega⟩
        have hi : k.castSucc = i := Fin.ext rfl
        have hj : k.succ = j := Fin.ext h
        simpa only [hi, hj] using steps k
      · let k : Fin 5 := ⟨j.val, by omega⟩
        have hj : k.castSucc = j := Fin.ext rfl
        have hi : k.succ = i := Fin.ext h
        simpa only [hi, hj] using (steps k).symm }
  injective' := hf

private theorem path_step (p : Path6 G) (i : Fin 5) : G.Adj (p i.castSucc) (p i.succ) :=
  p.toHom.map_rel (pathGraph_adj.mpr (Or.inl rfl))

private def reversePath (p : Path6 G) : Path6 G where
  toHom := {
    toFun := fun i => p i.rev
    map_rel' := by
      intro i j hij
      apply p.toHom.map_rel
      have h := pathGraph_adj.mp hij
      rw [pathGraph_adj, Fin.val_rev, Fin.val_rev]
      omega }
  injective' := p.injective.comp Fin.rev_injective

private theorem reverse_range (p : Path6 G) : Set.range (reversePath p) = Set.range p := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by change p i.rev.rev = p i; simp⟩

private def relist {k : ℕ} (p : Path6 G) (new : Fin k → V)
    (hnew : Function.Injective new) (hout : ∀ j, new j ∉ Set.range p)
    (order : Fin 6 ↪ Fin (6 + k))
    (steps : ∀ i : Fin 5, G.Adj (Fin.append p new (order i.castSucc))
      (Fin.append p new (order i.succ))) : Path6 G :=
  pathOfSteps ((Fin.append p new) ∘ order)
    ((Fin.append_injective_iff.mpr ⟨p.injective, hnew,
      fun i j h => hout j ⟨i, h⟩⟩).comp order.injective) steps

private def shift (p : Path6 G) (x : V) (hx : x ∉ Set.range p) (edge : G.Adj (p 5) x) :
    Path6 G :=
  relist p ![x] (Function.injective_of_subsingleton _) (fun j => by
    have : j = 0 := Subsingleton.elim _ _
    subst j
    exact hx)
    ⟨![1, 2, 3, 4, 5, 6], by decide⟩ (by
      intro i
      fin_cases i
      · exact path_step p 1
      · exact path_step p 2
      · exact path_step p 3
      · exact path_step p 4
      · exact edge)

private theorem shift_misses_first (p : Path6 G) (x : V) (hx : x ∉ Set.range p)
    (edge : G.Adj (p 5) x) : p 0 ∉ Set.range (shift p x hx edge) := by
  rintro ⟨i, hi⟩
  fin_cases i
  · exact (by decide : (1 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (2 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (3 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (4 : Fin 6) ≠ 0) (p.injective hi)
  · exact (by decide : (5 : Fin 6) ≠ 0) (p.injective hi)
  · exact hx ⟨0, hi.symm⟩

private theorem simplicial_first (p : Path6 G)
    (h : ∀ x, G.Adj (p 0) x → x ∈ Set.range p) : Avoidable p 0 3 :=
  fun x _ e => (e.1 (h x e.2.2.2.1)).elim

end GurvichLeafRootEdgeDeletionRefutation
