/- GID: D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kotzig's odd-prime construction is a perfect one-factorization of the complete graph. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.OddPrimePerfectOneFactorization

/-- The vertices of Kotzig's construction are the residues modulo `p` together
with one distinguished vertex. -/
abbrev Vertex (p : Nat) := Option (ZMod p)

/-- The partner of a vertex in the factor indexed by `a`. -/
def partner {p : Nat} (a : ZMod p) : Vertex p -> Vertex p
  | none => some a
  | some x => if x = a then none else some (2 * a - x)

/-- The factor indexed by `a`, defined by the partner relation. -/
def factor {p : Nat} (a : ZMod p) : SimpleGraph (Vertex p) :=
  SimpleGraph.fromRel fun u v => v = partner a u

/-- The union of the factors indexed by `a` and `b`. -/
def pairGraph {p : Nat} (a b : ZMod p) : SimpleGraph (Vertex p) :=
  factor a ⊔ factor b

/-- The finite-vertex displacement produced by two alternating reflections. -/
def translationStep {p : Nat} (a b : ZMod p) : ZMod p :=
  2 * (b - a)

variable {p : Nat} [Fact p.Prime]

private lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  simpa [ZMod.ringChar_zmod_n] using hp2

private lemma partner_involutive (a : ZMod p) : Function.Involutive (partner a) := by
  intro v
  rcases v with _ | x
  · simp [partner]
  · by_cases hxa : x = a
    · simp [partner, hxa]
    · have hra : 2 * a - x ≠ a := by
        intro h
        apply hxa
        calc
          x = 2 * a - (2 * a - x) := by ring
          _ = 2 * a - a := by rw [h]
          _ = a := by ring
      simp [partner, hxa, hra]

private lemma partner_ne (hp2 : p ≠ 2) (a : ZMod p) (v : Vertex p) :
    partner a v ≠ v := by
  rcases v with _ | x
  · simp [partner]
  · by_cases hxa : x = a
    · simp [partner, hxa]
    · simp only [partner, if_neg hxa, Option.some.injEq, ne_eq]
      intro h
      apply hxa
      apply mul_left_cancel₀ (two_ne_zero_zmod (p := p) hp2)
      simpa [two_mul] using (sub_eq_iff_eq_add.mp h).symm

private lemma factor_adj_iff (hp2 : p ≠ 2) (a : ZMod p) (u v : Vertex p) :
    (factor a).Adj u v ↔ v = partner a u := by
  rw [factor, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ((congrArg (partner a) h).trans (partner_involutive a v)).symm
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro huv
    exact partner_ne hp2 a u (h.symm.trans huv.symm)

private theorem factor_isPerfectMatching (hp2 : p ≠ 2) (a : ZMod p) :
    (⊤ : (factor a).Subgraph).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨partner a v, ?_, ?_⟩
  · change (factor a).Adj v (partner a v)
    exact (factor_adj_iff hp2 _ _ _).2 rfl
  · intro w hw
    change (factor a).Adj v w at hw
    exact (factor_adj_iff hp2 _ _ _).1 hw

private lemma factor_adj_none_some_iff (hp2 : p ≠ 2) (a x : ZMod p) :
    (factor a).Adj none (some x) ↔ a = x := by
  simp [factor_adj_iff hp2, partner, eq_comm]

private lemma factor_adj_some_none_iff (hp2 : p ≠ 2) (a x : ZMod p) :
    (factor a).Adj (some x) none ↔ a = x := by
  rw [(factor a).adj_comm, factor_adj_none_some_iff hp2]

private lemma factor_adj_some_some_iff (hp2 : p ≠ 2) (a x y : ZMod p) :
    (factor a).Adj (some x) (some y) ↔ x ≠ y ∧ x + y = 2 * a := by
  rw [factor_adj_iff hp2]
  by_cases hxa : x = a
  · subst x
    constructor
    · simp [partner]
    · rintro ⟨hxy, hsum⟩
      exfalso
      apply hxy
      have hEq : a + y = a + a := by simpa [two_mul] using hsum
      have hya : y = a := add_left_cancel hEq
      exact hya.symm
  · simp only [partner, if_neg hxa, Option.some.injEq]
    constructor
    · intro h
      constructor
      · intro hxy
        apply hxa
        apply mul_left_cancel₀ (two_ne_zero_zmod (p := p) hp2)
        calc
          2 * x = x + y := by rw [hxy]; ring
          _ = 2 * a := by rw [h]; ring
      · simpa [add_comm] using (eq_sub_iff_add_eq.mp h)
    · rintro ⟨_, hsum⟩
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using hsum

private def midpoint (x y : ZMod p) : ZMod p := (x + y) / 2

private lemma midpoint_spec (hp2 : p ≠ 2) (x y : ZMod p) :
    2 * midpoint x y = x + y := by
  unfold midpoint
  rw [div_eq_mul_inv]
  calc
    2 * ((x + y) * 2⁻¹) = (2 * 2⁻¹) * (x + y) := by ring
    _ = x + y := by rw [mul_inv_cancel₀ (two_ne_zero_zmod hp2), one_mul]

private theorem unique_factor_of_edge (hp2 : p ≠ 2) (u v : Vertex p) (huv : u ≠ v) :
    ∃! a : ZMod p, (factor a).Adj u v := by
  rcases u with _ | x <;> rcases v with _ | y
  · exact (huv rfl).elim
  · refine ⟨y, (factor_adj_none_some_iff hp2 y y).2 rfl, ?_⟩
    intro a ha
    exact (factor_adj_none_some_iff hp2 a y).1 ha
  · refine ⟨x, (factor_adj_some_none_iff hp2 x x).2 rfl, ?_⟩
    intro a ha
    exact (factor_adj_some_none_iff hp2 a x).1 ha
  · have hxy : x ≠ y := by simpa using huv
    refine ⟨midpoint x y, ?_, ?_⟩
    · change (factor (midpoint x y)).Adj (some x) (some y)
      rw [factor_adj_some_some_iff hp2]
      exact ⟨hxy, (midpoint_spec hp2 x y).symm⟩
    · intro a ha
      rw [factor_adj_some_some_iff hp2] at ha
      apply mul_left_cancel₀ (two_ne_zero_zmod hp2)
      rw [midpoint_spec hp2]
      exact ha.2.symm

/-- The edge from infinity to `x` belongs precisely to the factor indexed by `x`. -/
theorem edge_owner_infinity (hp2 : p ≠ 2) (a x : ZMod p) :
    (factor a).Adj none (some x) ↔ a = x := by
  exact factor_adj_none_some_iff hp2 a x

/-- A finite edge belongs precisely to the factor indexed by its field midpoint. -/
theorem edge_owner_pair (hp2 : p ≠ 2) (a x y : ZMod p) (hxy : x ≠ y) :
    (factor a).Adj (some x) (some y) ↔ a = (x + y) / 2 := by
  rw [factor_adj_some_some_iff hp2]
  constructor
  · intro hadj
    apply (eq_div_iff (two_ne_zero_zmod hp2)).2
    simpa [mul_comm] using hadj.2.symm
  · intro h
    refine ⟨hxy, ?_⟩
    have hmul := (eq_div_iff (two_ne_zero_zmod hp2)).1 h
    simpa [mul_comm] using hmul.symm

private lemma factors_edge_disjoint (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b)
    {u v : Vertex p} : ¬((factor a).Adj u v ∧ (factor b).Adj u v) := by
  rintro ⟨ha, hb⟩
  have huv : u ≠ v := fun h => by
    subst v
    exact (factor a).irrefl ha
  have unique := unique_factor_of_edge hp2 u v huv
  exact hab (unique.unique ha hb)

private lemma pairGraph_neighborSet (hp2 : p ≠ 2) (a b : ZMod p) (v : Vertex p) :
    (pairGraph a b).neighborSet v = {partner a v, partner b v} := by
  ext w
  simp [pairGraph, SimpleGraph.mem_neighborSet, factor_adj_iff hp2]

private lemma partner_ne_partner (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b)
    (v : Vertex p) : partner a v ≠ partner b v := by
  intro h
  have ha : (factor a).Adj v (partner a v) := (factor_adj_iff hp2 _ _ _).2 rfl
  have hb : (factor b).Adj v (partner a v) := (factor_adj_iff hp2 _ _ _).2 h
  exact factors_edge_disjoint hp2 hab ⟨ha, hb⟩

/-- Distinct factors give exactly two neighbors at every vertex. -/
theorem pairGraph_two_regular (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    ∀ v, ((pairGraph a b).neighborSet v).ncard = 2 := by
  intro v
  rw [pairGraph_neighborSet hp2]
  simp [partner_ne_partner hp2 hab v]

private lemma translationStep_ne_zero (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    translationStep a b ≠ 0 := by
  exact mul_ne_zero (two_ne_zero_zmod hp2) (sub_ne_zero.mpr hab.symm)

/-- For distinct factor indices, the alternating-reflection translation has
the full additive order of `ZMod p`. -/
theorem translationStep_addOrderOf (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    addOrderOf (translationStep a b) = p := by
  apply addOrderOf_eq_prime
  · simp [nsmul_eq_mul, translationStep]
  · exact translationStep_ne_zero hp2 hab

private lemma translation_reachable (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b)
    (x : ZMod p) :
    (pairGraph a b).Reachable (some x) (some (x + translationStep a b)) := by
  by_cases hxa : x = a
  · subst x
    apply SimpleGraph.Adj.reachable
    simp only [pairGraph, SimpleGraph.sup_adj]
    right
    rw [factor_adj_iff hp2]
    simp [partner, hab, translationStep]
    ring
  · by_cases hxb : 2 * a - x = b
    · have htarget : x + translationStep a b = b := by
        rw [translationStep, ← hxb]
        ring
      rw [htarget]
      apply SimpleGraph.Adj.reachable
      simp only [pairGraph, SimpleGraph.sup_adj]
      left
      rw [factor_adj_iff hp2]
      simp [partner, hxa, hxb]
    · have hleft :
          (pairGraph a b).Adj (some x) (some (2 * a - x)) := by
        simp [pairGraph, factor_adj_iff hp2, partner, hxa]
      have hright :
          (pairGraph a b).Adj (some (2 * a - x))
            (some (x + translationStep a b)) := by
        simp only [pairGraph, SimpleGraph.sup_adj]
        right
        rw [factor_adj_iff hp2]
        simp [partner, hxb, translationStep]
        ring
      exact hleft.reachable.trans hright.reachable

private lemma reachable_add_nsmul_translationStep (hp2 : p ≠ 2) {a b : ZMod p}
    (hab : a ≠ b) (n : Nat) :
    (pairGraph a b).Reachable (some a)
      (some (a + n • translationStep a b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact ih.trans (by
        simpa [succ_nsmul, add_assoc, add_mul] using
          translation_reachable hp2 hab (a + n • translationStep a b))

private theorem pairGraph_connected (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    (pairGraph a b).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  intro v
  rcases v with _ | x
  · rfl
  · have hbase : (pairGraph a b).Reachable none (some a) := by
      apply SimpleGraph.Adj.reachable
      simp [pairGraph, factor_adj_none_some_iff hp2]
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective
      ((x - a) / translationStep a b)
    refine hbase.trans ?_
    have hreach := reachable_add_nsmul_translationStep hp2 hab n
    convert hreach using 1
    congr 1
    rw [nsmul_eq_mul, hn, div_mul_cancel₀ _ (translationStep_ne_zero hp2 hab),
      add_sub_cancel]

private theorem pairGraph_isCycles (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    (pairGraph a b).IsCycles := by
  intro v _
  exact pairGraph_two_regular hp2 hab v

private theorem pairGraph_isHamiltonian (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    (pairGraph a b).IsHamiltonian := by
  intro _
  let v : Vertex p := none
  let c : (pairGraph a b).ConnectedComponent :=
    (pairGraph a b).connectedComponentMk v
  have hv : v ∈ c.supp := by
    simp [c, SimpleGraph.ConnectedComponent.supp]
  have hn : ((pairGraph a b).neighborSet v).Nonempty := by
    refine ⟨partner a v, ?_⟩
    rw [SimpleGraph.mem_neighborSet]
    simp only [pairGraph, SimpleGraph.sup_adj]
    exact Or.inl ((factor_adj_iff hp2 _ _ _).2 rfl)
  obtain ⟨q, hqcycle, hqverts⟩ :=
    (pairGraph_isCycles hp2 hab).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  refine ⟨v, q, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail]
  refine ⟨hqcycle, (hqcycle.isPath_tail.isHamiltonian_iff).2 ?_⟩
  intro w
  have hwc : w ∈ c.supp := by
    change (pairGraph a b).connectedComponentMk w =
      (pairGraph a b).connectedComponentMk v
    exact SimpleGraph.ConnectedComponent.sound ((pairGraph_connected hp2 hab) w v)
  have hwverts : w ∈ q.toSubgraph.verts := by
    rw [hqverts]
    exact hwc
  have hwsupport : w ∈ q.support := q.mem_verts_toSubgraph.mp hwverts
  rw [q.support_tail_of_not_nil hqcycle.not_nil]
  by_cases hwv : w = v
  · subst w
    exact q.end_mem_tail_support hqcycle.not_nil
  · have hwcons : w ∈ v :: q.support.tail := by
      rw [q.cons_tail_support]
      exact hwsupport
    exact (List.mem_cons.mp hwcons).resolve_left hwv

/-- Kotzig's construction gives a perfect one-factorization of the complete
graph on `Option (ZMod p)` for every odd prime `p`. -/
theorem odd_prime_perfect_one_factorization (hp2 : p ≠ 2) :
    (∀ a : ZMod p, (⊤ : (factor a).Subgraph).IsPerfectMatching) ∧
    (∀ u v : Vertex p, u ≠ v → ∃! a : ZMod p, (factor a).Adj u v) ∧
    (∀ a b : ZMod p, a ≠ b → (pairGraph a b).IsHamiltonian) := by
  exact ⟨factor_isPerfectMatching hp2, unique_factor_of_edge hp2,
    fun _ _ => pairGraph_isHamiltonian hp2⟩

#print axioms edge_owner_infinity
#print axioms edge_owner_pair
#print axioms pairGraph_two_regular
#print axioms translationStep_addOrderOf
#print axioms odd_prime_perfect_one_factorization

end D5.S3.ConceptDynamics.GraphColoring.OddPrimePerfectOneFactorization
