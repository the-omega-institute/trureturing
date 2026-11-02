/- GID: D5/S3/Geometry/PrescribedSubdivisionHomology
   generality: G
   mirror-B: D5/B/S3/Geometry/PrescribedSubdivisionHomology
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Symbolic iteration of literal triple edge subdivisions with exact path vertices. -/
import D5.S3.Geometry.FiniteGraphSuspensionMoves
import D5.S3.Combinatorics.Graph.Products.PrescribedSubdivision

/-!
# Simultaneous prescribed triple subdivisions

The homological input is the literal triple-subdivision isomorphism, from
Barmak, Proposition 7.2. Partial graphs retain every original vertex and
use an indexed internal carrier with three times the current multiplicity
vertices on each edge. Zero multiplicity retains the original edge.
Injectivity of unordered endpoint pairs controls deletion at zero stages.
An explicit graph isomorphism identifies every increment with one literal
triple subdivision. Well-founded recursion on the sum of multiplicities
gives the reduced integral singular homology shift without nested expanded
carriers or a supplied graph or homology correctness premise.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Products

namespace D5.S3.Geometry.PrescribedSubdivisionHomology

open FiniteGraphSuspensionMoves

variable {V E : Type}

/-- The input graph reconstructed from ALL supplied unordered endpoint pairs. -/
def baseGraph (D : PrescribedSubdivision.Data V E) : SimpleGraph V where
  Adj x y := ∃ e, (x = D.left e ∧ y = D.right e) ∨
    (x = D.right e ∧ y = D.left e)
  symm.symm := by
    rintro x y ⟨e, h | h⟩
    · exact ⟨e, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨e, Or.inl ⟨h.2, h.1⟩⟩
  loopless.irrefl := by
    rintro x ⟨e, h | h⟩
    · exact D.different e (h.1.symm.trans h.2)
    · exact D.different e (h.2.symm.trans h.1)

namespace Partial

abbrev Vertex (_D : PrescribedSubdivision.Data V E) (n : E → ℕ) :=
  V ⊕ (Σ e : E, Fin (3 * n e))

variable (D : PrescribedSubdivision.Data V E)

/-- At a zero entry the actual original edge is still present. -/
def Arc (n : E → ℕ) : Vertex D n → Vertex D n → Prop
  | .inl x, .inl y => ∃ e, n e = 0 ∧ x = D.left e ∧ y = D.right e
  | .inl x, .inr ⟨e, i⟩ => x = D.left e ∧ i.val = 0
  | .inr ⟨e, i⟩, .inl y => y = D.right e ∧ i.val + 1 = 3 * n e
  | .inr ⟨e, i⟩, .inr ⟨f, j⟩ => e = f ∧ i.val + 1 = j.val

def graph (n : E → ℕ) : SimpleGraph (Vertex D n) where
  Adj x y := Arc D n x y ∨ Arc D n y x
  symm.symm _ _ := Or.symm
  loopless.irrefl := by
    rintro (x | ⟨e, i⟩) h
    · rcases h with ⟨f, _, hx, hy⟩ | ⟨f, _, hx, hy⟩
      all_goals exact D.different f (hx.symm.trans hy)
    · rcases h with h | h
      all_goals have : i.val + 1 = i.val := h.2; omega

include D in
@[simp] theorem inner_eq_iff (n : E → ℕ) (e f : E)
    (i : Fin (3 * n e)) (j : Fin (3 * n f)) :
    (Sum.inr ⟨e, i⟩ : Vertex D n) = .inr ⟨f, j⟩ ↔ e = f ∧ i.val = j.val := by
  constructor
  · intro h
    have hs := Sum.inr.inj h
    exact ⟨congrArg Sigma.fst hs,
      congrArg (fun z : Σ e : E, Fin (3 * n e) => z.2.val) hs⟩
  · rintro ⟨rfl, h⟩
    exact congrArg (fun i => (Sum.inr ⟨e, i⟩ : Vertex D n)) (Fin.ext h)

@[simp] theorem adj_old_old (n : E → ℕ) (x y : V) :
    (graph D n).Adj (.inl x) (.inl y) ↔ ∃ e, n e = 0 ∧
      ((x = D.left e ∧ y = D.right e) ∨ (x = D.right e ∧ y = D.left e)) := by
  change ((∃ e, n e = 0 ∧ x = D.left e ∧ y = D.right e) ∨
    (∃ e, n e = 0 ∧ y = D.left e ∧ x = D.right e)) ↔ _
  constructor
  · rintro (⟨e, hn, hx, hy⟩ | ⟨e, hn, hy, hx⟩)
    · exact ⟨e, hn, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨e, hn, Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨e, hn, h | h⟩
    · exact Or.inl ⟨e, hn, h.1, h.2⟩
    · exact Or.inr ⟨e, hn, h.2, h.1⟩

@[simp] theorem adj_old_inner (n : E → ℕ) (x : V) (e : E) (i : Fin (3 * n e)) :
    (graph D n).Adj (.inl x) (.inr ⟨e, i⟩) ↔
      (x = D.left e ∧ i.val = 0) ∨ (x = D.right e ∧ i.val + 1 = 3 * n e) := Iff.rfl

@[simp] theorem adj_inner_inner (n : E → ℕ) (e f : E)
    (i : Fin (3 * n e)) (j : Fin (3 * n f)) :
    (graph D n).Adj (.inr ⟨e, i⟩) (.inr ⟨f, j⟩) ↔
      e = f ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  change ((e = f ∧ _) ∨ (f = e ∧ _)) ↔ _
  constructor
  · rintro (⟨h, hij⟩ | ⟨h, hji⟩)
    · exact ⟨h, Or.inl hij⟩
    · exact ⟨h.symm, Or.inr hji⟩
  · rintro ⟨h, hij | hji⟩
    · exact Or.inl ⟨h, hij⟩
    · exact Or.inr ⟨h.symm, hji⟩

variable [DecidableEq E]

/-- Add one triple subdivision on just the indicated edge. -/
def bump (n : E → ℕ) (e f : E) : ℕ := if f = e then n f + 1 else n f

@[simp] theorem bump_self (n : E → ℕ) (e : E) : bump n e e = n e + 1 := by
  simp [bump]

@[simp] theorem bump_other (n : E → ℕ) (e f : E) (h : f ≠ e) : bump n e f = n f := by
  simp [bump, h]

/-- The old path vertices retain exactly their original labels and indices. -/
def old (n : E → ℕ) (e : E) : Vertex D n → Vertex D (bump n e)
  | .inl x => .inl x
  | .inr ⟨f, i⟩ => .inr ⟨f, ⟨i.val, by
      by_cases h : f = e
      · subst f
        simp only [bump_self]
        have hi := i.isLt
        omega
      · simpa only [bump_other n e f h] using i.isLt⟩⟩

/-- The only new vertices have the three indices immediately after the old path. -/
def fresh (n : E → ℕ) (e : E) (i : Fin 3) : Vertex D (bump n e) :=
  .inr ⟨e, ⟨3 * n e + i.val, by simp only [bump_self]; have := i.isLt; omega⟩⟩

private theorem old_injective (n : E → ℕ) (e : E) : Function.Injective (old D n e) := by
  rintro (x | ⟨f, i⟩) (y | ⟨g, j⟩) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · have hh := (inner_eq_iff D _ _ _ _ _).mp h
    exact (inner_eq_iff D _ _ _ _ _).mpr hh

private theorem fresh_injective (n : E → ℕ) (e : E) : Function.Injective (fresh D n e) := by
  intro i j h
  have hh := (inner_eq_iff D _ _ _ _ _).mp h
  exact Fin.ext (Nat.add_left_cancel hh.2)

private theorem old_ne_fresh (n : E → ℕ) (e : E) (x : Vertex D n) (i : Fin 3) :
    old D n e x ≠ fresh D n e i := by
  cases x with
  | inl x => simp [old, fresh]
  | inr x =>
    rcases x with ⟨f, j⟩
    intro h
    have hh := (inner_eq_iff D _ _ _ _ _).mp h
    obtain ⟨rfl, hj⟩ := hh
    change j.val = 3 * n f + i.val at hj
    have := j.isLt
    omega

/-- A proved bijection, not an assumed graph isomorphism. -/
def labels (n : E → ℕ) (e : E) : (Vertex D n ⊕ Fin 3) ≃ Vertex D (bump n e) :=
  Equiv.ofBijective (Sum.elim (old D n e) (fresh D n e)) ⟨by
    rintro (x | i) (y | j) h
    · exact congrArg Sum.inl (old_injective D n e h)
    · exact False.elim (old_ne_fresh D n e x j h)
    · exact False.elim (old_ne_fresh D n e y i h.symm)
    · exact congrArg Sum.inr (fresh_injective D n e h), by
    rintro (x | ⟨f, i⟩)
    · exact ⟨.inl (.inl x), rfl⟩
    · by_cases hf : f = e
      · subst f
        by_cases hi : i.val < 3 * n e
        · refine ⟨.inl (.inr ⟨e, ⟨i.val, hi⟩⟩), ?_⟩
          exact (inner_eq_iff D _ _ _ _ _).mpr ⟨rfl, rfl⟩
        · have hib := i.isLt
          simp only [bump_self] at hib
          refine ⟨.inr ⟨i.val - 3 * n e, by omega⟩, ?_⟩
          dsimp only [Sum.elim, fresh]
          apply (inner_eq_iff D (bump n e) e e _ _).mpr
          exact ⟨rfl, by change 3 * n e + (i.val - 3 * n e) = i.val; omega⟩
      · have hi : i.val < 3 * n f := by simpa [bump, hf] using i.isLt
        refine ⟨.inl (.inr ⟨f, ⟨i.val, hi⟩⟩), ?_⟩
        exact (inner_eq_iff D _ _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- The last old vertex before the right endpoint, or the left endpoint at zero. -/
def tip (n : E → ℕ) (e : E) : Vertex D n :=
  if h : n e = 0 then .inl (D.left e)
  else .inr ⟨e, ⟨3 * n e - 1, by omega⟩⟩

@[simp] theorem old_eq_tip (n : E → ℕ) (e : E) (x : V) :
    (Sum.inl x : Vertex D n) = tip D n e ↔ n e = 0 ∧ x = D.left e := by
  by_cases h : n e = 0 <;> simp [tip, h]

@[simp] theorem inner_eq_tip (n : E → ℕ) (e f : E) (i : Fin (3 * n f)) :
    (Sum.inr ⟨f, i⟩ : Vertex D n) = tip D n e ↔ f = e ∧ i.val + 1 = 3 * n e := by
  by_cases h : n e = 0
  · simp only [tip, h, ↓reduceDIte, Sum.inr_ne_inl, false_iff, not_and]
    intro hf
    subst f
    have := i.isLt
    omega
  · simp only [tip, h, ↓reduceDIte, inner_eq_iff D]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨hf, by omega⟩
    · rintro ⟨hf, hi⟩
      exact ⟨hf, by omega⟩

/-- The edge to which the terminal triple-subdivision theorem is applied. -/
theorem tip_adjacent (n : E → ℕ) (e : E) :
    (graph D n).Adj (tip D n e) (.inl (D.right e)) := by
  by_cases h : n e = 0
  · simp only [tip, h, ↓reduceDIte, adj_old_old D]
    exact ⟨e, h, Or.inl ⟨rfl, rfl⟩⟩
  · apply Or.inl
    change Arc D n (tip D n e) (.inl (D.right e))
    simp only [tip, h, ↓reduceDIte, Arc]
    exact ⟨True.intro, by omega⟩

private def Tail (n : E → ℕ) (e : E) (x y : Vertex D n) : Prop :=
  (x = tip D n e ∧ y = .inl (D.right e)) ∨
    (x = .inl (D.right e) ∧ y = tip D n e)

private theorem endpoints_unique
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (e f : E)
    (h : (D.left f = D.left e ∧ D.right f = D.right e) ∨
      (D.left f = D.right e ∧ D.right f = D.left e)) : f = e :=
  hinj ((Sym2.eq_iff).mpr h)

/-- All old adjacencies survive except precisely the last edge of path e.
The zero-stage old--old case is where unordered endpoint injectivity is essential. -/
private theorem old_old_adj
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (n : E → ℕ) (e : E) (x y : Vertex D n) :
    (graph D (bump n e)).Adj (old D n e x) (old D n e y) ↔
      (graph D n).Adj x y ∧ ¬ Tail D n e x y := by
  have old_case (a b : V) :
      (graph D (bump n e)).Adj (.inl a) (.inl b) ↔
        (graph D n).Adj (.inl a) (.inl b) ∧
          ¬ Tail D n e (.inl a) (.inl b) := by
    simp only [adj_old_old D, Tail, old_eq_tip D, Sum.inl.injEq]
    constructor
    · rintro ⟨f, hf, hab⟩
      have hfe : f ≠ e := by intro h; subst f; simp at hf
      have hn : n f = 0 := by simpa [bump, hfe] using hf
      refine ⟨⟨f, hn, hab⟩, ?_⟩
      rintro (⟨⟨he, ha⟩, hb⟩ | ⟨hb, ⟨he, ha⟩⟩)
      · apply hfe
        apply endpoints_unique D hinj e f
        rcases hab with h | h
        · exact Or.inl ⟨h.1.symm.trans ha, h.2.symm.trans hb⟩
        · exact Or.inr ⟨h.2.symm.trans hb, h.1.symm.trans ha⟩
      · apply hfe
        apply endpoints_unique D hinj e f
        rcases hab with h | h
        · exact Or.inr ⟨h.1.symm.trans hb, h.2.symm.trans ha⟩
        · exact Or.inl ⟨h.2.symm.trans ha, h.1.symm.trans hb⟩
    · rintro ⟨⟨f, hf, hab⟩, htail⟩
      have hfe : f ≠ e := by
        intro h
        subst f
        apply htail
        rcases hab with h | h
        · exact Or.inl ⟨⟨hf, h.1⟩, h.2⟩
        · exact Or.inr ⟨h.1, ⟨hf, h.2⟩⟩
      exact ⟨f, by simpa [bump, hfe] using hf, hab⟩
  have mixed_case (a : V) (f : E) (i : Fin (3 * n f)) :
      (graph D (bump n e)).Adj (old D n e (.inl a)) (old D n e (.inr ⟨f, i⟩)) ↔
        (graph D n).Adj (.inl a) (.inr ⟨f, i⟩) ∧
          ¬ Tail D n e (.inl a) (.inr ⟨f, i⟩) := by
    dsimp only [old]
    rw [adj_old_inner D (bump n e), adj_old_inner D n]
    by_cases hf : f = e
    · subst f
      have hi := i.isLt
      simp only [bump_self, Tail, Sum.inr_ne_inl,
        and_false, false_or, Sum.inl.injEq, inner_eq_tip D, eq_self, true_and]
      have hnew : ¬ i.val + 1 = 3 * (n e + 1) := by omega
      have hfirst : i.val = 0 → ¬ i.val + 1 = 3 * n e := by omega
      simp only [hnew, and_false, or_false]
      constructor
      · rintro ⟨ha, hi0⟩
        refine ⟨Or.inl ⟨ha, hi0⟩, ?_⟩
        rintro ⟨_, ht⟩
        exact hfirst hi0 ht
      · rintro ⟨h, ht⟩
        exact h.resolve_right ht
    · simp [bump, hf, Tail, inner_eq_tip D]
  cases x with
  | inl a =>
    cases y with
    | inl b => exact old_case a b
    | inr y => rcases y with ⟨f, i⟩; exact mixed_case a f i
  | inr x =>
    rcases x with ⟨f, i⟩
    cases y with
    | inl b =>
      rw [SimpleGraph.adj_comm, mixed_case]
      simp only [SimpleGraph.adj_comm, Tail, or_comm, and_comm]
    | inr y =>
      rcases y with ⟨g, j⟩
      simp [old, adj_inner_inner D, Tail]

private theorem old_fresh_adj (n : E → ℕ) (e : E) (x : Vertex D n) (i : Fin 3) :
    (graph D (bump n e)).Adj (old D n e x) (fresh D n e i) ↔
      (i = 0 ∧ x = tip D n e) ∨ (i = 2 ∧ x = .inl (D.right e)) := by
  have hi := i.isLt
  cases x with
  | inl a =>
    dsimp only [old, fresh]
    rw [adj_old_inner D (bump n e)]
    simp only [bump_self, old_eq_tip D,
      Sum.inl.injEq, Fin.ext_iff, Fin.val_zero]
    rw [show (2 : Fin 3).val = 2 from rfl]
    have hleft : 3 * n e + i.val = 0 ↔ i.val = 0 ∧ n e = 0 := by omega
    have hright : 3 * n e + i.val + 1 = 3 * (n e + 1) ↔ i.val = 2 := by omega
    rw [hleft, hright]
    tauto
  | inr x =>
    rcases x with ⟨f, j⟩
    have hj := j.isLt
    by_cases hf : f = e
    · subst f
      simp only [old, fresh, adj_inner_inner D, true_and, inner_eq_tip D,
        eq_self, Sum.inr_ne_inl, and_false, or_false, Fin.ext_iff, Fin.val_zero]
      omega
    · simp [old, fresh, adj_inner_inner D, hf, inner_eq_tip D]

private theorem fresh_fresh_adj (n : E → ℕ) (e : E) (i j : Fin 3) :
    (graph D (bump n e)).Adj (fresh D n e i) (fresh D n e j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [fresh, adj_inner_inner D, eq_self, true_and]
  omega

/-- Exact symbolic graph identification for ONE increment of an arbitrary
partial path system, including zero entries and every ambient original edge. -/
def stepIso
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (n : E → ℕ) (e : E) :
    tripleSubdivision (graph D n) (tip D n e) (.inl (D.right e)) ≃g
      graph D (bump n e) where
  toEquiv := labels D n e
  map_rel_iff' := by
    rintro (x | i) (y | j)
    · change (graph D (bump n e)).Adj (old D n e x) (old D n e y) ↔
        (graph D n).Adj x y ∧ ¬ Tail D n e x y
      exact old_old_adj D hinj n e x y
    · change (graph D (bump n e)).Adj (old D n e x) (fresh D n e j) ↔ _
      exact old_fresh_adj D n e x j
    · change (graph D (bump n e)).Adj (fresh D n e i) (old D n e y) ↔ _
      rw [SimpleGraph.adj_comm]
      exact old_fresh_adj D n e y i
    · change (graph D (bump n e)).Adj (fresh D n e i) (fresh D n e j) ↔ _
      exact fresh_fresh_adj D n e i j

/-- At zero there are no fresh vertices, and the graph is exactly the original. -/
def zeroIso : baseGraph D ≃g graph D (fun _ => 0) where
  toEquiv := Equiv.ofBijective Sum.inl ⟨Sum.inl_injective, by
    rintro (x | ⟨e, i⟩)
    · exact ⟨x, rfl⟩
    · exact Fin.elim0 i⟩
  map_rel_iff' := by
    intro x y
    change (graph D (fun _ => 0)).Adj (.inl x) (.inl y) ↔ (baseGraph D).Adj x y
    simp [baseGraph]

/-- The terminal positive-only path graph is the final partial graph, with
exactly the same vertices, not a cardinality-based replacement of labels. -/
def positiveIso : graph D D.k ≃g D.graph where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro (x | ⟨e, i⟩) (y | ⟨f, j⟩)
    · change (False ∨ False) ↔ _
      simp only [false_or, adj_old_old D]
      have hz : ∀ e : E, D.k e ≠ 0 := fun e => Nat.ne_of_gt (D.positive e)
      simp [hz]
    · rfl
    · rfl
    · rfl

section Finite
variable [Fintype V] [DecidableEq V] [Fintype E]

private theorem sum_bump (n : E → ℕ) (e : E) :
    (∑ f, bump n e f) = (∑ f, n f) + 1 := by
  have h (f : E) : bump n e f = n f + if f = e then 1 else 0 := by
    by_cases hf : f = e <;> simp [bump, hf]
  simp only [h, Finset.sum_add_distrib]
  simp

/-- Well-founded symbolic iteration. The measure is the ACTUAL sum of
multiplicities. Each recursive call consumes one proved literal triple move. -/
def reducedHomologyIso
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (n : E → ℕ) (q : ℕ) (hq : 1 ≤ q) :
    Reduced (graph D n) (q + ∑ e, n e) ≅ Reduced (baseGraph D) q := by
  by_cases hz : ∀ e, n e = 0
  · have hn : n = fun _ => 0 := funext hz
    subst n
    simpa using graphReducedIso (zeroIso D).symm q
  · let e : E := Classical.choose (not_forall.mp hz)
    have he : n e ≠ 0 := Classical.choose_spec (not_forall.mp hz)
    let p : E → ℕ := fun f => if f = e then n f - 1 else n f
    have hp : bump p e = n := by
      funext f
      by_cases hf : f = e
      · subst f
        simp only [bump_self, p, ite_true]
        omega
      · simp [bump, p, hf]
    have hs : (∑ f, n f) = (∑ f, p f) + 1 := by
      rw [← hp, sum_bump]
    have hlt : (∑ f, p f) < ∑ f, n f := by omega
    have ih := reducedHomologyIso hinj p q hq
    have step : Reduced (graph D (bump p e)) ((q + ∑ f, p f) + 1) ≅
        Reduced (graph D p) (q + ∑ f, p f) :=
      (graphReducedIso (stepIso D hinj p e) _).symm ≪≫
        tripleSubdivisionReducedHomologyIso (graph D p) (tip_adjacent D p e)
          (q + ∑ f, p f) (by omega)
    rw [hp] at step
    simpa only [hs, Nat.add_assoc] using step ≪≫ ih
termination_by ∑ e, n e
decreasing_by omega

end Finite
end Partial

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Replacing every supplied edge e by its exact path with 3*k(e) fresh
vertices shifts integral reduced SINGULAR homology by sum k, for every q≥1.
The original graph is reconstructed from the entire endpoint inventory. -/
def reducedHomologyIso (D : PrescribedSubdivision.Data V E)
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (q : ℕ) (hq : 1 ≤ q) :
    Reduced D.graph (q + ∑ e, D.k e) ≅ Reduced (baseGraph D) q :=
  (graphReducedIso (Partial.positiveIso D) _).symm ≪≫
    Partial.reducedHomologyIso D hinj D.k q hq

/-- Consume a real adjacency inventory for a supplied ambient graph. This
requires neither a graph isomorphism nor the desired homology shift as input. -/
def reducedHomologyIsoOfAdjacency (D : PrescribedSubdivision.Data V E)
    (G : SimpleGraph V)
    (hedges : ∀ x y, G.Adj x y ↔ ∃ e,
      (x = D.left e ∧ y = D.right e) ∨ (x = D.right e ∧ y = D.left e))
    (hinj : Function.Injective (fun e : E => s(D.left e, D.right e)))
    (q : ℕ) (hq : 1 ≤ q) :
    Reduced D.graph (q + ∑ e, D.k e) ≅ Reduced G q :=
  reducedHomologyIso D hinj q hq ≪≫ graphReducedIso
    ({ toEquiv := Equiv.refl V
       map_rel_iff' := fun {x y} => hedges x y } : baseGraph D ≃g G) q

end D5.S3.Geometry.PrescribedSubdivisionHomology
