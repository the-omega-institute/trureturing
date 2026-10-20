/- GID: D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/KhesinLiEquivalenceClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Connected normalized encoder classes have cardinality divisible by 3^k. -/

/-
proof_shape: addInputRow: not-applicable(definition); consumers: RenormStep.rowOperation (constructor type), Step.rowOperation (constructor type)
proof_shape: Step: not-applicable(definition); consumers: NormalizedStep, lc_class_step
proof_shape: RenormStep: not-applicable(definition); consumers: NormalizedStep, lc_class_step
proof_shape: Normalized: not-applicable(definition); consumers: NormalizedStep, actionHom, action_free, action_row, claim, classSize, connected_nonzero_row, coordinateHom_commute, lcOnClass, lcPerm, lcPerm_commute, lc_class_step, normalized_input_pivot, normalized_lc_input, normalized_lc_pivot, normalized_pivot_pivot, other_row_pow, result, rotate_cube, rotate_input_row, rotate_other_row, rotate_own_row, rotate_pivot_row, rotationPerm, rotationPerm_commute, rotationPerm_cube, rotation_row_pow, site_nonadj, site_normalized
proof_shape: NormalizedStep: not-applicable(definition); consumers: actionHom, action_free, action_row, claim, classSize, coordinateHom_commute, lcOnClass, lcPerm, lcPerm_commute, lc_class_step, other_row_pow, result, rotationPerm, rotationPerm_commute, rotationPerm_cube, rotation_row_pow
proof_shape: classSize: not-applicable(definition); consumers: claim, result
proof_shape: claim: not-applicable(definition); consumers: result (theorem type)
proof_shape: lc_source: bind-only; consumers: lc_class_step
proof_shape: lc_adj: bind-only; consumers: lc_braid, lc_commute, lc_incident, lc_involutive, lc_non_neighbor, normalized_lc_input, normalized_lc_pivot, rotate_input_row, rotate_pivot_row
proof_shape: lc_incident: bind-only; consumers: lc_involutive, rotate_input_row, rotate_pivot_row
proof_shape: lc_non_neighbor: bind-only; consumers: lc_commute, normalized_lc_input, normalized_lc_pivot, rotate_other_row
proof_shape: lc_involutive: bind-only; consumers: lcPerm, rotate_cube
proof_shape: lc_commute: bind-only; consumers: lcPerm_commute
proof_shape: lc_braid: bind-only; consumers: rotate_cube
proof_shape: normalized_input_pivot: bind-only; consumers: connected_nonzero_row, normalized_lc_pivot, rotate_cube, rotate_input_row, rotate_other_row, rotate_pivot_row, site_nonadj
proof_shape: normalized_pivot_pivot: bind-only; consumers: rotate_other_row, site_nonadj
proof_shape: normalized_lc_input: bind-only; consumers: rotate_other_row, site_normalized
proof_shape: normalized_lc_pivot: bind-only; consumers: site_normalized
proof_shape: lc_class_step: bind-only; consumers: lcOnClass
proof_shape: rotate_cube: bind-only; consumers: rotationPerm_cube
proof_shape: cyclic_eval: bind-only; consumers: action_row, bitRotation_free, cyclicHom_commute
proof_shape: cyclicHom_commute: bind-only; consumers: coordinateHom_commute
proof_shape: bitRotation: not-applicable(definition); consumers: action_free, action_row, bitRotation_cube, bitRotation_free, rotate_own_row, rotation_row_pow
proof_shape: bitRotation_cube: bind-only; consumers: action_free, action_row, bitRotation_free
proof_shape: bitRotation_free: bind-only; consumers: action_free
proof_shape: free_action_card_dvd: bind-only; consumers: result
proof_shape: site: not-applicable(definition); consumers: lcOnClass, lcPerm, lcPerm_commute, site_nonadj, site_normalized
proof_shape: site_normalized: bind-only; consumers: lcOnClass
proof_shape: site_nonadj: bind-only; consumers: lcPerm_commute
proof_shape: lcOnClass: not-applicable(definition); consumers: lcPerm
proof_shape: lcPerm: not-applicable(definition); consumers: lcPerm_commute, rotationPerm, rotationPerm_commute
proof_shape: lcPerm_commute: bind-only; consumers: rotationPerm_commute
proof_shape: rotationPerm: not-applicable(definition); consumers: actionHom, action_row, coordinateHom_commute, other_row_pow, rotationPerm_cube, rotation_row_pow
proof_shape: rotationPerm_cube: bind-only; consumers: actionHom, action_row, coordinateHom_commute
proof_shape: rotationPerm_commute: bind-only; consumers: coordinateHom_commute
proof_shape: coordinateHom_commute: bind-only; consumers: actionHom, action_row
proof_shape: actionHom: not-applicable(definition); consumers: action_free, action_row, result
proof_shape: rowPair: not-applicable(definition); consumers: action_free, action_row, connected_nonzero_row, other_row_pow, rotate_other_row, rotate_own_row, rotation_row_pow
proof_shape: free_ne_pivot: bind-only; consumers: connected_nonzero_row, rotate_input_row, rotate_pivot_row
proof_shape: rotate_input_row: bind-only; consumers: rotate_own_row
proof_shape: rotate_pivot_row: bind-only; consumers: rotate_own_row
proof_shape: rotate_other_row: bind-only; consumers: other_row_pow
proof_shape: rotate_own_row: bind-only; consumers: rotation_row_pow
proof_shape: connected_nonzero_row: content; consumers: action_free
proof_shape: rotation_row_pow: bind-only; consumers: action_row
proof_shape: other_row_pow: bind-only; consumers: action_row
proof_shape: action_row: bind-only; consumers: action_free
proof_shape: action_free: content; consumers: result
proof_shape: result: content; consumers: none
escape_witness: none
admission_basis: open-problem-resolution (#19189; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lc
    statement_id: sha256:9f294d833f9432cb07f2efb1392793f29502edb5cbbaf03040dfb51b165eae79
  D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.cyclicHom
    statement_id: sha256:76c351568d336aba3acf1f4ef5ba9d787ae25e2e84c67a483f65f3e5d090846b
  D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lcSeq
    statement_id: sha256:cf3d985ac05293bf2cacb55e059beb758fb7c5ab957b6091dac7c4bf62249932
  D5/S3/Combinatorics/Graph/Brooks/Cuts.mem_of_walk_closed
    statement_id: sha256:476eee0dcb6c6799096786aad17f4a9642d2614705c1bf829b2b8c8fb90a78ae
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19215
The source's XOR local-complementation expression is inlined in Step.complement;
private lc_source identifies it with the frozen lc used throughout the proof.
-/

import D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
import D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition
import D5.S3.Combinatorics.Graph.Brooks.Cuts

open D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph (lc lcSeq)
open D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition (cyclicHom)

/-! Encoder graphs for A. B. Khesin and A. M. Li, "Equivalence Classes of Quantum Error-Correcting Codes",
arXiv:2406.12083v1: Section 2 (local complementation), Conjecture 6.3 (the operations), Claim 6.4 (normalized
encoders), Section 7 (classes computed by one operation followed by renormalization) and Conjecture 7.1. An encoder graph
of an `[n, k]` code has input vertices `inl i` and output vertices `inr j`; local Clifford decorations are removed. -/

namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses



/-- Operation 4: add the input–output row of input `j` to that of input `i` (mod 2); all other adjacencies are kept
(the relation is symmetric, so `fromRel` adds nothing beyond excluding loops). -/
def addInputRow {k n : ℕ} (G : SimpleGraph (Fin k ⊕ Fin n)) (i j : Fin k) : SimpleGraph (Fin k ⊕ Fin n) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl a, Sum.inr o =>
        if a = i then Xor (G.Adj (Sum.inl i) (Sum.inr o)) (G.Adj (Sum.inl j) (Sum.inr o)) else G.Adj x y
    | Sum.inr o, Sum.inl a =>
        if a = i then Xor (G.Adj (Sum.inl i) (Sum.inr o)) (G.Adj (Sum.inl j) (Sum.inr o)) else G.Adj x y
    | _, _ => G.Adj x y

/-- The operations of Conjecture 6.3 on decoration-free encoder graphs: 1 local complementation about any vertex,
2 permuting the outputs, 3 permuting the inputs, 4 row operations on the input–output adjacency matrix, 5 removing an
input–input edge. (Operation 6, local operations on output edges, acts on the removed decorations only.) -/
inductive Step {k n : ℕ} : SimpleGraph (Fin k ⊕ Fin n) → SimpleGraph (Fin k ⊕ Fin n) → Prop
  | complement (G : SimpleGraph (Fin k ⊕ Fin n)) (v : Fin k ⊕ Fin n) : Step G (SimpleGraph.fromRel fun x y => Xor (G.Adj x y) (G.Adj v x ∧ G.Adj v y))
  | permuteOutputs (G : SimpleGraph (Fin k ⊕ Fin n)) (σ : Equiv.Perm (Fin n)) :
      Step G (G.map (Equiv.sumCongr (Equiv.refl (Fin k)) σ).toEmbedding)
  | permuteInputs (G : SimpleGraph (Fin k ⊕ Fin n)) (τ : Equiv.Perm (Fin k)) :
      Step G (G.map (Equiv.sumCongr τ (Equiv.refl (Fin n))).toEmbedding)
  | rowOperation (G : SimpleGraph (Fin k ⊕ Fin n)) (i j : Fin k) (h : i ≠ j) : Step G (addInputRow G i j)
  | removeInputEdge (G : SimpleGraph (Fin k ⊕ Fin n)) (i j : Fin k) : Step G (G.deleteEdges {s(Sum.inl i, Sum.inl j)})

/-- The renormalization steps of Section 7: operations 2–5. -/
inductive RenormStep {k n : ℕ} : SimpleGraph (Fin k ⊕ Fin n) → SimpleGraph (Fin k ⊕ Fin n) → Prop
  | permuteOutputs (G : SimpleGraph (Fin k ⊕ Fin n)) (σ : Equiv.Perm (Fin n)) :
      RenormStep G (G.map (Equiv.sumCongr (Equiv.refl (Fin k)) σ).toEmbedding)
  | permuteInputs (G : SimpleGraph (Fin k ⊕ Fin n)) (τ : Equiv.Perm (Fin k)) :
      RenormStep G (G.map (Equiv.sumCongr τ (Equiv.refl (Fin n))).toEmbedding)
  | rowOperation (G : SimpleGraph (Fin k ⊕ Fin n)) (i j : Fin k) (h : i ≠ j) : RenormStep G (addInputRow G i j)
  | removeInputEdge (G : SimpleGraph (Fin k ⊕ Fin n)) (i j : Fin k) :
      RenormStep G (G.deleteEdges {s(Sum.inl i, Sum.inl j)})

/-- Claim 6.4: no input–input edges, the input–output adjacency matrix is in reduced row echelon form with the pivot
outputs `0, …, k − 1` matched to the inputs in order, and no pivot–pivot edges. -/
def Normalized {k n : ℕ} (G : SimpleGraph (Fin k ⊕ Fin n)) : Prop :=
  (∀ i j : Fin k, ¬ G.Adj (Sum.inl i) (Sum.inl j)) ∧
  (∀ (i : Fin k) (j : Fin n), j.val < k → (G.Adj (Sum.inl i) (Sum.inr j) ↔ j.val = i.val)) ∧
  (∀ j j' : Fin n, j.val < k → j'.val < k → ¬ G.Adj (Sum.inr j) (Sum.inr j'))

/-- Section 7: one operation followed by renormalization, between normalized encoders. -/
def NormalizedStep {k n : ℕ} (G H : SimpleGraph (Fin k ⊕ Fin n)) : Prop :=
  Normalized G ∧ Normalized H ∧ ∃ Z, Step G Z ∧ Relation.ReflTransGen RenormStep Z H

/-- The size of the equivalence class of `G` among normalized encoders (Section 7, disjoint-set classes). -/
noncomputable def classSize {k n : ℕ} (G : SimpleGraph (Fin k ⊕ Fin n)) : ℕ :=
  Nat.card {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}

/-- Conjecture 7.1: "For positive integers n > k, the equivalence classes of [n,k] codes with a single connected
component have sizes divisible by 3^k." -/
def claim : Prop :=
  ∀ k n : ℕ, 0 < k → k < n → ∀ G : SimpleGraph (Fin k ⊕ Fin n), Normalized G →
    (∀ H : SimpleGraph (Fin k ⊕ Fin n), Normalized H → Relation.EqvGen NormalizedStep G H → H.Connected) →
      3 ^ k ∣ classSize G

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses

set_option maxHeartbeats 1000000

private theorem lc_source {V : Type} (G : SimpleGraph V) (v : V) :
    lc G v = SimpleGraph.fromRel (fun x y => Xor (G.Adj x y) (G.Adj v x ∧ G.Adj v y)) := by
  ext x y
  rw [SimpleGraph.fromRel_adj]
  change (x ≠ y ∧ (G.Adj x y ↔ ¬ (G.Adj v x ∧ G.Adj v y))) ↔ _
  rw [G.adj_comm y x]
  unfold Xor
  tauto

private theorem lc_adj {V : Type} (G : SimpleGraph V) (v x y : V) :
    (lc G v).Adj x y ↔
      x ≠ y ∧ Xor (G.Adj x y) (G.Adj v x ∧ G.Adj v y) := by
  change (x ≠ y ∧ (G.Adj x y ↔ ¬ (G.Adj v x ∧ G.Adj v y))) ↔ _
  unfold Xor
  tauto

private theorem lc_incident {V : Type} (G : SimpleGraph V) (v x : V) :
    (lc G v).Adj v x ↔ G.Adj v x := by
  simp only [lc_adj, G.loopless.irrefl, false_and, Xor]
  have hne : G.Adj v x → v ≠ x := G.ne_of_adj
  tauto

private theorem lc_non_neighbor {V : Type} (G : SimpleGraph V) (v x y : V)
    (h : ¬ G.Adj v x) : (lc G v).Adj x y ↔ G.Adj x y := by
  simp only [lc_adj, h, false_and, Xor]
  have hne : G.Adj x y → x ≠ y := G.ne_of_adj
  tauto

private theorem lc_involutive {V : Type} (G : SimpleGraph V) (v : V) :
    lc (lc G v) v = G := by
  ext x y
  rw [lc_adj, lc_incident, lc_incident, lc_adj]
  by_cases h : x = y
  · subst y; simp
  · simp only [h, ne_eq, not_false_eq_true, true_and]
    simp only [Xor]
    tauto

private theorem lc_commute {V : Type} (G : SimpleGraph V) (u v : V)
    (huv : ¬ G.Adj u v) :
    lc (lc G u) v = lc (lc G v) u := by
  ext x y
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  rw [lc_adj (lc G u) v x y, lc_adj (lc G v) u x y]
  rw [lc_non_neighbor G u v x huv, lc_non_neighbor G u v y huv,
    lc_non_neighbor G v u x hvu, lc_non_neighbor G v u y hvu]
  rw [lc_adj, lc_adj]
  by_cases h : x = y
  · subst y; simp
  · simp only [h, ne_eq, not_false_eq_true, true_and]
    simp only [Xor]
    tauto

private theorem lc_braid {V : Type} (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    lc (lc (lc G u) v) u =
      lc (lc (lc G v) u) v := by
  classical
  ext x y
  have huv' : u ≠ v := G.ne_of_adj huv
  have hvu : G.Adj v u := huv.symm
  have hvu' : v ≠ u := huv'.symm
  by_cases hxy : x = y
  · subst y; simp
  by_cases hxu : x = u
  · subst x
    by_cases hyu : y = u
    · subst y; simp
    by_cases hyv : y = v
    · subst y; simp [lc_adj, huv, hvu, huv', huv'.symm, Xor]
    · simp only [lc_adj, G.loopless.irrefl]
      simp_all only [ne_comm, ne_eq, not_false_eq_true, not_true_eq_false, true_and, false_and,
        and_true, and_false, Xor]
      all_goals tauto
  by_cases hxv : x = v
  · subst x
    by_cases hyu : y = u
    · subst y; simp [lc_adj, huv, hvu, huv', huv'.symm, Xor]
    by_cases hyv : y = v
    · subst y; simp
    · simp only [lc_adj, G.loopless.irrefl]
      simp_all only [ne_comm, ne_eq, not_false_eq_true, not_true_eq_false, true_and, false_and,
        and_true, and_false, Xor]
      all_goals tauto
  by_cases hyu : y = u
  · subst y
    simp only [lc_adj, G.loopless.irrefl]
    simp_all only [ne_comm, G.adj_comm, ne_eq, not_false_eq_true, not_true_eq_false, true_and,
      false_and, and_true, and_false, Xor]
    all_goals tauto
  by_cases hyv : y = v
  · subst y
    simp only [lc_adj, G.loopless.irrefl]
    simp_all only [ne_comm, G.adj_comm, ne_eq, not_false_eq_true, not_true_eq_false, true_and,
      false_and, and_true, and_false, Xor]
    all_goals tauto
  · have hux : u ≠ x := Ne.symm hxu
    have hvx : v ≠ x := Ne.symm hxv
    have huy : u ≠ y := Ne.symm hyu
    have hvy : v ≠ y := Ne.symm hyv
    by_cases h1 : G.Adj u x <;> by_cases h2 : G.Adj u y <;>
      by_cases h3 : G.Adj v x <;> by_cases h4 : G.Adj v y <;>
      simp_all [lc_adj, G.adj_comm, Xor]

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
set_option maxHeartbeats 1000000

variable {k n : ℕ}

private theorem normalized_input_pivot (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i j : Fin k) : G.Adj (Sum.inl i) (Sum.inr (Fin.castLE hkn j)) ↔ i = j := by
  rw [hG.2.1 i _ j.isLt]
  exact ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩

private theorem normalized_pivot_pivot (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i j : Fin k) : ¬ G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr (Fin.castLE hkn j)) :=
  hG.2.2 _ _ i.isLt j.isLt

private theorem normalized_lc_input (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G) (i : Fin k) :
    Normalized (lc G (Sum.inl i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simpa only [lc_non_neighbor G _ _ _ (hG.1 i a)] using hG.1 a b
  · intro a j hj
    rw [lc_non_neighbor G _ _ _ (hG.1 i a)]
    exact hG.2.1 a j hj
  · intro j j' hj hj' he
    obtain ⟨hne, he⟩ := (lc_adj G _ _ _).1 he
    have hnot := hG.2.2 j j' hj hj'
    have ht : G.Adj (Sum.inl i) (Sum.inr j) ∧ G.Adj (Sum.inl i) (Sum.inr j') :=
      he.or.resolve_left hnot
    have hv : j.val = j'.val := ((hG.2.1 i j hj).1 ht.1).trans
      ((hG.2.1 i j' hj').1 ht.2).symm
    exact hne (congrArg Sum.inr (Fin.ext hv))

private theorem normalized_lc_pivot (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i : Fin k) : Normalized (lc G (Sum.inr (Fin.castLE hkn i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b he
    obtain ⟨hne, he⟩ := (lc_adj G _ _ _).1 he
    have hnot := hG.1 a b
    have ht : G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inl a) ∧ G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inl b) :=
      he.or.resolve_left hnot
    have ha := (normalized_input_pivot G hG hkn a i).1 ht.1.symm
    have hb := (normalized_input_pivot G hG hkn b i).1 ht.2.symm
    exact hne (congrArg Sum.inl (ha.trans hb.symm))
  · intro a j hj
    have hnot : ¬ G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr j) := hG.2.2 _ j i.isLt hj
    rw [(lc G (Sum.inr (Fin.castLE hkn i))).adj_comm, lc_non_neighbor G _ _ _ hnot,
      G.adj_comm]
    exact hG.2.1 a j hj
  · intro j j' hj hj'
    have hnot : ¬ G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr j) := hG.2.2 _ _ i.isLt hj
    rw [lc_non_neighbor G _ _ _ hnot]
    exact hG.2.2 j j' hj hj'

private theorem lc_class_step (G : SimpleGraph (Fin k ⊕ Fin n)) (v : Fin k ⊕ Fin n)
    (hG : Normalized G) (hH : Normalized (lc G v)) :
    Relation.EqvGen NormalizedStep G (lc G v) := by
  refine .rel _ _ ⟨hG, hH, _, .complement G v, ?_⟩
  rw [← lc_source G v]

private theorem rotate_cube (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i : Fin k) :
    lcSeq (lcSeq (lcSeq G [Sum.inl i, Sum.inr (Fin.castLE hkn i)]) [Sum.inl i, Sum.inr (Fin.castLE hkn i)]) [Sum.inl i, Sum.inr (Fin.castLE hkn i)] = G := by
  have he : G.Adj (Sum.inl i) (Sum.inr (Fin.castLE hkn i)) := (normalized_input_pivot G hG hkn i i).2 rfl
  dsimp only [lcSeq, List.foldl_cons, List.foldl_nil]
  rw [lc_braid G _ _ he, lc_involutive, lc_involutive, lc_involutive]

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses

variable {A : Type*}

private theorem cyclic_eval (m : ℕ) [NeZero m] (p : Equiv.Perm A) (hp : p ^ m = 1)
    (e : Multiplicative (ZMod m)) : cyclicHom m p hp e = p ^ e.toAdd.val := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd, zpow_natCast] using
    (D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition.cyclicHom_int m p hp (e.toAdd.val : ℤ))

private theorem cyclicHom_commute (p q : Equiv.Perm A) (hp : p ^ 3 = 1) (hq : q ^ 3 = 1)
    (hc : Commute p q) (a b : Multiplicative (ZMod 3)) :
    Commute (cyclicHom 3 p hp a) (cyclicHom 3 q hq b) :=
  by
    rw [cyclic_eval, cyclic_eval]
    exact hc.pow_pow _ _

private def bitRotation : Equiv.Perm (Bool × Bool) :=
  (Equiv.swap (true, true) (true, false)).trans
    (Equiv.swap (false, true) (true, true))

private theorem bitRotation_cube : bitRotation ^ 3 = 1 :=
  Equiv.Perm.support_eq_empty_iff.mp rfl

private theorem bitRotation_free (e : Multiplicative (ZMod 3)) (z : Bool × Bool)
    (hz : z ≠ (false, false)) (hf : cyclicHom 3 bitRotation bitRotation_cube e z = z) : e = 1 := by
  rw [cyclic_eval] at hf
  revert e z
  decide

private theorem free_action_card_dvd {M X : Type*} [Group M] [MulAction M X]
    (hf : ∀ (g : M) (x : X), g • x = x → g = 1) : Nat.card M ∣ Nat.card X := by
  have hs : ∀ x : X, MulAction.stabilizer M x = ⊥ := by
    intro x
    exact (Subgroup.eq_bot_iff_forall _).2 (fun g hg => hf g x hg)
  have hc := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hs)
  rw [Nat.card_prod] at hc
  rw [hc]
  exact dvd_mul_left _ _

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses

variable {k n : ℕ}

private def site (hkn : k ≤ n) (i : Fin k) : Bool → Fin k ⊕ Fin n
  | false => Sum.inl i
  | true => Sum.inr (Fin.castLE hkn i)

private theorem site_normalized (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G) (hkn : k ≤ n)
    (i : Fin k) (b : Bool) : Normalized (lc G (site hkn i b)) := by
  cases b
  · exact normalized_lc_input G hG i
  · exact normalized_lc_pivot G hG hkn i

private theorem site_nonadj (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G) (hkn : k ≤ n)
    (i j : Fin k) (hij : i ≠ j) (a b : Bool) : ¬ G.Adj (site hkn i a) (site hkn j b) := by
  cases a <;> cases b
  · exact hG.1 i j
  · exact fun h => hij ((normalized_input_pivot G hG hkn i j).1 h)
  · exact fun h => hij ((normalized_input_pivot G hG hkn j i).1 h.symm).symm
  · exact normalized_pivot_pivot G hG hkn i j

private def lcOnClass (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i : Fin k) (b : Bool)
    (H : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H} :=
  ⟨lc H.1 (site hkn i b), site_normalized H.1 H.2.1 hkn i b,
    Relation.EqvGen.trans _ _ _ H.2.2 (lc_class_step H.1 _ H.2.1 (site_normalized H.1 H.2.1 hkn i b))⟩

private def lcPerm (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i : Fin k) (b : Bool) :
    Equiv.Perm ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :=
  Function.Involutive.toPerm (lcOnClass G hkn i b)
    (fun H => Subtype.ext (lc_involutive H.1 _))

private theorem lcPerm_commute (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i j : Fin k)
    (hij : i ≠ j) (a b : Bool) : Commute (lcPerm G hkn i a) (lcPerm G hkn j b) := by
  apply Equiv.ext
  intro H
  apply Subtype.ext
  exact lc_commute H.1 _ _ (site_nonadj H.1 H.2.1 hkn j i hij.symm b a)

private def rotationPerm (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i : Fin k) :
    Equiv.Perm ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) := lcPerm G hkn i true * lcPerm G hkn i false

private theorem rotationPerm_cube (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i : Fin k) :
    rotationPerm G hkn i ^ 3 = 1 := by
  apply Equiv.ext
  intro H
  apply Subtype.ext
  change lcSeq (lcSeq (lcSeq H.1 [Sum.inl i, Sum.inr (Fin.castLE hkn i)]) [Sum.inl i, Sum.inr (Fin.castLE hkn i)]) [Sum.inl i, Sum.inr (Fin.castLE hkn i)] = H.1
  exact rotate_cube H.1 H.2.1 hkn i

private theorem rotationPerm_commute (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i j : Fin k)
    (hij : i ≠ j) : Commute (rotationPerm G hkn i) (rotationPerm G hkn j) :=
  ((lcPerm_commute G hkn i j hij true true).mul_right
    (lcPerm_commute G hkn i j hij true false)).mul_left
  ((lcPerm_commute G hkn i j hij false true).mul_right
    (lcPerm_commute G hkn i j hij false false))


private theorem coordinateHom_commute (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) :
    Pairwise fun i j => ∀ a b, Commute ((fun i => cyclicHom 3 (rotationPerm G hkn i) (rotationPerm_cube G hkn i)) i a) ((fun i => cyclicHom 3 (rotationPerm G hkn i) (rotationPerm_cube G hkn i)) j b) := by
  intro i j hij a b
  exact cyclicHom_commute _ _ _ _ (rotationPerm_commute G hkn i j hij) a b

private noncomputable def actionHom (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) :
    (Fin k → Multiplicative (ZMod 3)) →* Equiv.Perm ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :=
  MonoidHom.noncommPiCoprod ((fun i => cyclicHom 3 (rotationPerm G hkn i) (rotationPerm_cube G hkn i))) (coordinateHom_commute G hkn)

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
set_option maxHeartbeats 1000000

variable {k n : ℕ}


private noncomputable def rowPair (hkn : k ≤ n) (i : Fin k) (G : SimpleGraph (Fin k ⊕ Fin n))
    (x : {j : Fin n // k ≤ j.val}) : Bool × Bool := by
  classical
  exact (decide (G.Adj (Sum.inl i) (Sum.inr x.1)), decide (G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr x.1)))

private theorem free_ne_pivot (hkn : k ≤ n) (i : Fin k) (x : {j : Fin n // k ≤ j.val}) :
    (Sum.inr (Fin.castLE hkn i) : Fin k ⊕ Fin n) ≠ Sum.inr x.1 := by
  intro h
  have hh : i.val = x.1.val := congrArg (fun z : Fin k ⊕ Fin n => z.elim Fin.val Fin.val) h
  have hi := i.isLt
  have hx := x.2
  omega

private theorem rotate_input_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i : Fin k) (x : {j : Fin n // k ≤ j.val}) :
    (lcSeq G [Sum.inl i, Sum.inr (Fin.castLE hkn i)]).Adj (Sum.inl i) (Sum.inr x.1) ↔ G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr x.1) := by
  have hep : G.Adj (Sum.inl i) (Sum.inr (Fin.castLE hkn i)) := (normalized_input_pivot G hG hkn i i).2 rfl
  have hne := free_ne_pivot hkn i x
  dsimp only [lcSeq, List.foldl_cons, List.foldl_nil]
  rw [lc_adj]
  rw [(lc G (Sum.inl i)).adj_comm (Sum.inr (Fin.castLE hkn i)) (Sum.inl i), lc_incident]
  rw [lc_incident, lc_adj]
  have hs : Sum.inl i ≠ Sum.inr x.1 := Sum.inl_ne_inr
  simp only [hs, hne, hep, ne_eq, not_false_eq_true, true_and, Xor]
  tauto

private theorem rotate_pivot_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i : Fin k) (x : {j : Fin n // k ≤ j.val}) :
    (lcSeq G [Sum.inl i, Sum.inr (Fin.castLE hkn i)]).Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr x.1) ↔
      Xor (G.Adj (Sum.inl i) (Sum.inr x.1)) (G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr x.1)) := by
  have hep : G.Adj (Sum.inl i) (Sum.inr (Fin.castLE hkn i)) := (normalized_input_pivot G hG hkn i i).2 rfl
  dsimp only [lcSeq, List.foldl_cons, List.foldl_nil]
  rw [lc_incident, lc_adj]
  simp only [free_ne_pivot hkn i x, hep, ne_eq, not_false_eq_true, true_and, Xor]
  tauto

private theorem rotate_other_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i j : Fin k) (hij : i ≠ j) (x : {j : Fin n // k ≤ j.val}) :
    rowPair hkn i (lcSeq G [Sum.inl j, Sum.inr (Fin.castLE hkn j)]) x = rowPair hkn i G x := by
  classical
  have hinput : ¬ G.Adj (Sum.inl j) (Sum.inl i) := hG.1 j i
  have hpivot : ¬ G.Adj (Sum.inl j) (Sum.inr (Fin.castLE hkn i)) := by
    rw [normalized_input_pivot G hG hkn j i]
    exact hij.symm
  have hpi : ¬ (lc G (Sum.inl j)).Adj (Sum.inr (Fin.castLE hkn j)) (Sum.inl i) := by
    rw [(lc G (Sum.inl j)).adj_comm, lc_non_neighbor G _ _ _ hinput,
      normalized_input_pivot G hG hkn i j]
    exact hij
  have hpp : ¬ (lc G (Sum.inl j)).Adj (Sum.inr (Fin.castLE hkn j)) (Sum.inr (Fin.castLE hkn i)) :=
    normalized_pivot_pivot _ (normalized_lc_input G hG j) hkn j i
  simp only [rowPair, lcSeq, List.foldl_cons, List.foldl_nil,
    lc_non_neighbor _ _ _ _ hpi, lc_non_neighbor G _ _ _ hinput,
    lc_non_neighbor _ _ _ _ hpp, lc_non_neighbor G _ _ _ hpivot]

private theorem rotate_own_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k ≤ n) (i : Fin k) (x : {j : Fin n // k ≤ j.val}) :
    rowPair hkn i (lcSeq G [Sum.inl i, Sum.inr (Fin.castLE hkn i)]) x = bitRotation (rowPair hkn i G x) := by
  classical
  by_cases hb : G.Adj (Sum.inl i) (Sum.inr x.1) <;>
    by_cases hc : G.Adj (Sum.inr (Fin.castLE hkn i)) (Sum.inr x.1) <;>
    apply Prod.ext <;>
    simp [rowPair, bitRotation, Equiv.swap_apply_def,
      rotate_input_row G hG hkn i x, rotate_pivot_row G hG hkn i x, hb, hc, Xor]

private theorem connected_nonzero_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hG : Normalized G)
    (hkn : k < n) (hconn : G.Connected) (i : Fin k) :
    ∃ x : {j : Fin n // k ≤ j.val}, rowPair hkn.le i G x ≠ (false, false) := by
  classical
  by_contra hall
  push Not at hall
  have hfree (x : {j : Fin n // k ≤ j.val}) :
      ¬ G.Adj (Sum.inl i) (Sum.inr x.1) ∧ ¬ G.Adj (Sum.inr (Fin.castLE hkn.le i)) (Sum.inr x.1) := by
    have hb := congrArg Prod.fst (hall x)
    have hc := congrArg Prod.snd (hall x)
    simpa only [rowPair, Prod.fst, Prod.snd, decide_eq_false_iff_not] using And.intro hb hc
  have hu : ∀ y, G.Adj (Sum.inl i) y → y = Sum.inl i ∨ y = Sum.inr (Fin.castLE hkn.le i) := by
    intro y hy
    cases y with
    | inl j => exact (hG.1 i j hy).elim
    | inr j =>
      right
      by_cases hj : j.val < k
      · apply congrArg Sum.inr
        apply Fin.ext
        exact (hG.2.1 i j hj).1 hy
      · exact ((hfree ⟨j, by omega⟩).1 hy).elim
  have hp : ∀ y, G.Adj (Sum.inr (Fin.castLE hkn.le i)) y → y = Sum.inl i ∨ y = Sum.inr (Fin.castLE hkn.le i) := by
    intro y hy
    cases y with
    | inl j =>
      left
      exact congrArg Sum.inl ((normalized_input_pivot G hG hkn.le j i).1 hy.symm)
    | inr j =>
      by_cases hj : j.val < k
      · have hn : ¬ G.Adj (Sum.inr (Fin.castLE hkn.le i)) (Sum.inr j) := hG.2.2 _ _ i.isLt hj
        exact (hn hy).elim
      · exact ((hfree ⟨j, by omega⟩).2 hy).elim
  have closed : ∀ {x y}, x = Sum.inl i ∨ x = Sum.inr (Fin.castLE hkn.le i) → G.Adj x y →
      y = Sum.inl i ∨ y = Sum.inr (Fin.castLE hkn.le i) := by
    intro x y hx hxy
    rcases hx with rfl | rfl
    · exact hu y hxy
    · exact hp y hxy
  have walk_closed : ∀ {x y}, G.Walk x y → (x = Sum.inl i ∨ x = Sum.inr (Fin.castLE hkn.le i)) →
      y = Sum.inl i ∨ y = Sum.inr (Fin.castLE hkn.le i) := by
    intro x y w
    exact BrooksSubcubic.mem_of_walk_closed G
      {z | z = Sum.inl i ∨ z = Sum.inr (Fin.castLE hkn.le i)}
      (fun a ha b hab => closed ha hab) w
  let f : {j : Fin n // k ≤ j.val} := ⟨⟨k, hkn⟩, le_rfl⟩
  obtain ⟨w⟩ := hconn (Sum.inl i) (Sum.inr f.1)
  rcases walk_closed w (Or.inl rfl) with h | h
  · exact Sum.inr_ne_inl h
  · exact free_ne_pivot hkn.le i f h.symm

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses


namespace D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses

set_option maxHeartbeats 1000000
variable {k n : ℕ}

private theorem rotation_row_pow (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i : Fin k)
    (x : {j : Fin n // k ≤ j.val}) (t : ℕ) (H : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :
    rowPair hkn i ((rotationPerm G hkn i ^ t) H).1 x =
      (bitRotation ^ t) (rowPair hkn i H.1 x) := by
  have hs : Function.Semiconj
      (fun Y : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H} =>
        rowPair hkn i Y.1 x) (rotationPerm G hkn i) bitRotation :=
    fun Y => rotate_own_row Y.1 Y.2.1 hkn i x
  simpa only [Equiv.Perm.coe_pow] using hs.iterate_right t H

private theorem other_row_pow (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (i j : Fin k) (hij : i ≠ j)
    (x : {j : Fin n // k ≤ j.val}) (t : ℕ) (H : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :
    rowPair hkn i ((rotationPerm G hkn j ^ t) H).1 x = rowPair hkn i H.1 x := by
  have hs : Function.Semiconj
      (fun Y : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H} =>
        rowPair hkn i Y.1 x) (rotationPerm G hkn j) id :=
    fun Y => rotate_other_row Y.1 Y.2.1 hkn i j hij x
  simpa only [Equiv.Perm.coe_pow, Function.iterate_id, id_eq] using hs.iterate_right t H

private theorem action_row (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k ≤ n) (a : (Fin k → Multiplicative (ZMod 3)))
    (i : Fin k) (x : {j : Fin n // k ≤ j.val}) (H : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :
    rowPair hkn i (actionHom G hkn a H).1 x =
      cyclicHom 3 bitRotation bitRotation_cube (a i) (rowPair hkn i H.1 x) := by
  classical
  let f : Fin k → Equiv.Perm ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) := fun j => (fun i => cyclicHom 3 (rotationPerm G hkn i) (rotationPerm_cube G hkn i)) j (a j)
  have comm : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise (fun j l => Commute (f j) (f l)) :=
    fun _ _ _ _ hij => coordinateHom_commute G hkn hij _ _
  have prod_keep : ∀ Y : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H},
      rowPair hkn i (((Finset.univ.erase i).noncommProd f
        (fun _ hj _ hl h => comm (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hl) h)) Y).1 x =
        rowPair hkn i Y.1 x := by
    apply Finset.noncommProd_induction
      (p := fun p : Equiv.Perm ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) => ∀ Y : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H},
        rowPair hkn i (p Y).1 x = rowPair hkn i Y.1 x)
    · intro p q hp hq Y
      exact (hp (q Y)).trans (hq Y)
    · intro Y; rfl
    · intro j hj Y
      change rowPair hkn i ((cyclicHom 3 (rotationPerm G hkn j) _ (a j)) Y).1 x = _
      rw [cyclic_eval]
      exact other_row_pow G hkn i j (Finset.ne_of_mem_erase hj).symm x _ Y
  change rowPair hkn i ((MonoidHom.noncommPiCoprod ((fun i => cyclicHom 3 (rotationPerm G hkn i) (rotationPerm_cube G hkn i)))
    (coordinateHom_commute G hkn) a) H).1 x = _
  rw [MonoidHom.noncommPiCoprod_apply]
  change rowPair hkn i (((Finset.univ : Finset (Fin k)).noncommProd f comm) H).1 x = _
  rw [← Finset.mul_noncommProd_erase _ (Finset.mem_univ i) f comm]
  change rowPair hkn i (f i (((Finset.univ.erase i).noncommProd f _) H)).1 x = _
  rw [show ∀ Y : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}, rowPair hkn i (f i Y).1 x =
      cyclicHom 3 bitRotation bitRotation_cube (a i) (rowPair hkn i Y.1 x) from
    fun Y => by
      dsimp only [f]
      rw [cyclic_eval, cyclic_eval]
      exact rotation_row_pow G hkn i x _ Y]
  rw [prod_keep]

private theorem action_free (G : SimpleGraph (Fin k ⊕ Fin n)) (hkn : k < n)
    (hc : ∀ H : SimpleGraph (Fin k ⊕ Fin n), Normalized H → Relation.EqvGen NormalizedStep G H → H.Connected)
    (a : (Fin k → Multiplicative (ZMod 3))) (H : {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) (h : actionHom G hkn.le a H = H) : a = 1 := by
  funext i
  obtain ⟨x, hx⟩ := connected_nonzero_row H.1 H.2.1 hkn (hc H.1 H.2.1 H.2.2) i
  have he := action_row G hkn.le a i x H
  rw [h] at he
  exact bitRotation_free (a i) _ hx he.symm

theorem result : claim := by
  intro k n hk hkn G hG hc
  let := MulAction.compHom {H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H} (actionHom G hkn.le)
  have hd : Nat.card ((Fin k → Multiplicative (ZMod 3))) ∣ Nat.card ({H : SimpleGraph (Fin k ⊕ Fin n) // Normalized H ∧ Relation.EqvGen NormalizedStep G H}) :=
    free_action_card_dvd (fun a H h => action_free G hkn hc a H h)
  have hg : Nat.card ((Fin k → Multiplicative (ZMod 3))) = 3 ^ k := by
    simp [Nat.card_eq_fintype_card]
  simpa only [hg, classSize] using hd

end D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses
