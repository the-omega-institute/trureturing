/- GID: D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves the forbidden-subgraph conjecture of Fuentes, Keeler, Munizzi and Pollack (arXiv:2511.19585): every graph state that violates monogamy of mutual information is carried by local complementations to a graph with an induced four-star K_{1,3}, a generalized star for the partition that separates the three leaves; connected graphs reaching no induced four-star have at most six vertices and satisfy MMI. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: local complementation at vertices
  of a vertex set commutes with restriction to it (`comap_lc`, `comap_lcSeq`, `claw_comap`); along
  a vertex ordering in which every vertex has an earlier neighbour (`chain`), the 120 certificates
  `certs1` to `certs6`, checked by `decide` (`lev`, `claw6`, `prep`, `step`, `ladder`), show that a
  connected graph reaching no induced four-star has at most six vertices and is locally equivalent
  to a relabelling of `K_1`, `K_2`, `P_3`, `P_4`, `C_5` or the triangular prism (`cls`); local
  complementation is an involutive row or column operation on every adjacency block, so the
  entropies are invariant (`lc_eq`, `compl_eq`, `relabel`); entropies add over a vertex set with
  no edges to its complement (`blocks`, `split`, `split_mmi`); the representatives satisfy MMI
  (`crit`, `ame`, `ame_mmi`, `p4_mmi`, `rep_mmi`); induction on the number of vertices (`main`)
admission_basis: open-problem-resolution (issue #10534)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph

/-- Local complementation at `v`: the edges among the neighbours of `v` are complemented. -/
def lc {V : Type} (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (G.Adj a b ↔ ¬ (G.Adj v a ∧ G.Adj v b))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [G.adj_comm, and_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (lc G v).Adj := fun a b => by unfold lc; infer_instance

/-- Local complementation at the vertices of `s`, in order. -/
def lcSeq {V : Type} (G : SimpleGraph V) (s : List V) : SimpleGraph V :=
  s.foldl lc G

private instance lcSeqDec {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (s : List V) → DecidableRel (lcSeq G s).Adj
  | [] => inferInstanceAs (DecidableRel G.Adj)
  | v :: s => @lcSeqDec V _ (lc G v) _ s

/-- `c` is adjacent to `i`, `j`, `k`, which are distinct and pairwise non-adjacent. -/
def IsClaw {V : Type} (G : SimpleGraph V) (c i j k : V) : Prop :=
  G.Adj c i ∧ G.Adj c j ∧ G.Adj c k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ¬ G.Adj i j ∧ ¬ G.Adj i k ∧ ¬ G.Adj j k

private instance {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (c i j k : V) :
    Decidable (IsClaw G c i j k) := by unfold IsClaw; infer_instance

/-- The graph on `Fin n` with the listed edges. -/
private def ofEdges (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a.val, b.val) ∈ E

private instance (n : ℕ) (E : List (ℕ × ℕ)) : DecidableRel (ofEdges n E).Adj :=
  fun a b => by unfold ofEdges; infer_instance

/-- Edges of the representatives `K_2`, `P_3`, `P_4`, `C_5` and the triangular prism. -/
private def repEdges : ℕ → List (ℕ × ℕ)
  | 2 => [(0, 1)]
  | 3 => [(0, 1), (1, 2)]
  | 4 => [(0, 3), (1, 2), (2, 3)]
  | 5 => [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]
  | 6 => [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
  | _ => []

/-- The representatives: `K_1`, `K_2` (`n = 2`), the path `P_3`, the path `1 - 2 - 3 - 0`, the
5-cycle `0 - 1 - 3 - 4 - 2 - 0` and the triangular prism with triangles `012`, `345` and matching
`03`, `14`, `25`; the edgeless graph for other `n`. -/
private def rep (n : ℕ) : SimpleGraph (Fin n) := ofEdges n (repEdges n)

private instance (n : ℕ) : DecidableRel (rep n).Adj := fun a b => by unfold rep; infer_instance

/-- `R` with a new last vertex adjacent to the vertices `i` with `t i`. -/
private def ext {k : ℕ} (R : SimpleGraph (Fin k)) (t : Fin k → Bool) :
    SimpleGraph (Fin (k + 1)) where
  Adj a b := a ≠ b ∧
    if ha : a.val < k then
      if hb : b.val < k then R.Adj ⟨a, ha⟩ ⟨b, hb⟩ else t ⟨a, ha⟩ = true
    else if hb : b.val < k then t ⟨b, hb⟩ = true else False
  symm := ⟨fun a b h => ⟨h.1.symm, by
    obtain ⟨_, h⟩ := h
    by_cases ha : a.val < k <;> by_cases hb : b.val < k <;> simp_all [R.adj_comm]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance {k : ℕ} (R : SimpleGraph (Fin k)) [DecidableRel R.Adj] (t : Fin k → Bool) :
    DecidableRel (ext R t).Adj := fun a b => by unfold ext; infer_instance

/-- A certificate for one extension: an induced claw, or the next representative up to
relabelling, each after the listed local complementations. -/
private inductive Cert (k : ℕ) where
  | none
  | claw (s : List (Fin (k + 1))) (c i j l : Fin (k + 1))
  | rep (s : List (Fin (k + 1))) (σ : Fin (k + 1) → Fin (k + 1))

/-- Whether a certificate names a claw. -/
private def Cert.isClaw {k : ℕ} : Cert k → Bool
  | .claw .. => true
  | _ => false

/-- The binary code of a set of vertices. -/
private def code {k : ℕ} (t : Fin k → Bool) : ℕ := ∑ i : Fin k, if t i then 2 ^ (i : ℕ) else 0

/-- Checks a certificate against the extension of `rep k` by `t`. -/
private def check (k : ℕ) (t : Fin k → Bool) : Cert k → Bool
  | .none => false
  | .claw s c i j l => decide (IsClaw (lcSeq (ext (rep k) t) s) c i j l)
  | .rep s σ => decide (Function.Bijective σ ∧
      ∀ a b, (lcSeq (ext (rep k) t) s).Adj a b ↔ (rep (k + 1)).Adj (σ a) (σ b))

/-- Certificates for the extensions of `rep 1`, indexed by `code`. -/
private def certs1 : List (Cert 1) := [
  .none, .rep [] ![0, 1]]

/-- Certificates for the extensions of `rep 2`, indexed by `code`. -/
private def certs2 : List (Cert 2) := [
  .none, .rep [] ![1, 0, 2], .rep [] ![0, 1, 2], .rep [1] ![0, 1, 2]]

/-- Certificates for the extensions of `rep 3`, indexed by `code`. -/
private def certs3 : List (Cert 3) := [
  .none, .rep [] ![2, 3, 0, 1], .claw [] 1 0 2 3, .rep [3] ![0, 2, 1, 3], .rep [] ![0, 3, 2, 1],
  .rep [0, 3, 2] ![0, 1, 3, 2], .rep [3] ![0, 3, 1, 2], .rep [3, 2] ![0, 1, 3, 2]]

/-- Certificates for the extensions of `rep 4`, indexed by `code`. -/
private def certs4 : List (Cert 4) := [
  .none, .claw [0, 3] 2 0 1 4, .claw [1, 2] 3 0 1 4, .rep [] ![0, 3, 4, 2, 1], .claw [] 2 1 3 4,
  .claw [] 2 1 3 4, .claw [2] 3 0 1 4, .rep [1] ![0, 3, 4, 2, 1], .claw [] 3 0 2 4,
  .claw [3] 2 0 1 4, .claw [] 3 0 2 4, .rep [0] ![0, 3, 4, 2, 1], .claw [2, 4] 3 0 1 2,
  .claw [0] 2 1 3 4, .claw [1] 3 0 2 4, .rep [3, 0] ![0, 3, 1, 2, 4]]

/-- Certificates for the extensions of `rep 5`, indexed by `code`. -/
private def certs5 : List (Cert 5) := [
  .none, .claw [] 0 1 2 5, .claw [] 1 0 3 5, .claw [0] 2 1 4 5, .claw [] 2 0 4 5,
  .claw [0] 1 2 3 5, .claw [] 1 0 3 5, .claw [1] 2 0 4 5, .claw [] 3 1 4 5, .claw [] 0 1 2 5,
  .claw [1] 0 2 3 5, .claw [0] 2 1 4 5, .claw [] 2 0 4 5, .claw [] 3 1 4 5, .claw [] 2 0 4 5,
  .claw [0] 3 1 4 5, .claw [] 4 2 3 5, .claw [] 0 1 2 5, .claw [] 1 0 3 5, .claw [] 4 2 3 5,
  .claw [2] 0 1 4 5, .claw [0] 1 2 3 5, .claw [] 1 0 3 5, .claw [0] 4 2 3 5, .claw [3] 1 0 4 5,
  .claw [] 0 1 2 5, .claw [1] 0 2 3 5, .claw [1] 4 2 3 5, .claw [2] 0 1 4 5, .claw [2] 3 1 4 5,
  .claw [3] 2 0 4 5, .rep [0] ![0, 1, 2, 4, 5, 3]]

/-- Certificates for the extensions of `rep 6`, indexed by `code`. -/
private def certs6 : List (Cert 6) := [
  .none, .claw [] 0 1 3 6, .claw [] 1 0 4 6, .claw [] 0 2 3 6, .claw [] 2 0 5 6,
  .claw [] 0 1 3 6, .claw [] 1 0 4 6, .claw [0] 0 1 2 6, .claw [] 3 0 4 6, .claw [0, 1] 2 0 5 6,
  .claw [] 1 0 4 6, .claw [] 1 2 4 6, .claw [] 2 0 5 6, .claw [] 2 1 5 6, .claw [] 1 0 4 6,
  .claw [0] 0 1 2 6, .claw [] 4 1 3 6, .claw [] 0 1 3 6, .claw [0, 1] 0 2 4 6, .claw [] 0 2 3 6,
  .claw [] 2 0 5 6, .claw [] 0 1 3 6, .claw [] 2 0 5 6, .claw [0] 0 1 2 6, .claw [] 3 0 5 6,
  .claw [] 4 1 5 6, .claw [] 3 0 5 6, .claw [0] 4 1 5 6, .claw [] 2 0 5 6, .claw [] 2 1 5 6,
  .claw [] 2 0 5 6, .claw [0] 0 1 2 6, .claw [] 5 2 3 6, .claw [] 0 1 3 6, .claw [] 1 0 4 6,
  .claw [] 0 2 3 6, .claw [0, 1] 2 0 3 6, .claw [] 0 1 3 6, .claw [] 1 0 4 6, .claw [0] 0 1 2 6,
  .claw [] 3 0 4 6, .claw [] 5 2 4 6, .claw [] 1 0 4 6, .claw [] 1 2 4 6, .claw [] 3 0 4 6,
  .claw [0] 5 2 4 6, .claw [] 1 0 4 6, .claw [0] 0 1 2 6, .claw [] 4 1 3 6, .claw [] 0 1 3 6,
  .claw [] 5 2 3 6, .claw [] 0 2 3 6, .claw [] 4 1 3 6, .claw [] 0 1 3 6, .claw [1] 5 2 3 6,
  .claw [0] 0 1 2 6, .claw [0] 3 1 2 6, .claw [3] 3 4 5 6, .claw [3] 0 2 4 6, .claw [3] 1 2 4 6,
  .claw [3] 0 1 5 6, .claw [3] 2 1 5 6, .claw [3] 0 4 5 6, .claw [0] 0 1 2 6]

/-- The certificate table of level `k`. -/
private def certs : (k : ℕ) → List (Cert k)
  | 1 => certs1
  | 2 => certs2
  | 3 => certs3
  | 4 => certs4
  | 5 => certs5
  | 6 => certs6
  | _ => []

/-- `H` reaches an induced claw, or `rep k` up to relabelling, by local complementations. -/
private def Ladder (k : ℕ) (H : SimpleGraph (Fin k)) : Prop :=
  (∃ (s : List (Fin k)) (c i j l : Fin k), IsClaw (lcSeq H s) c i j l) ∨
    ∃ (s : List (Fin k)) (σ : Fin k → Fin k), Function.Bijective σ ∧
      lcSeq H s = (rep k).comap σ


open Classical in
/-- The adjacency block of `G` with rows in `A` and columns outside `A`, over `ZMod 2`. -/
private noncomputable def cut {V : Type} [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    Matrix {x // x ∈ A} {x // x ∉ A} (ZMod 2) :=
  (G.adjMatrix (ZMod 2)).submatrix Subtype.val Subtype.val

/-- The entanglement entropy of `A` in the graph state of `G` (Fuentes et al., eq. `EEadj`): the
rank over `ZMod 2` of the adjacency block with rows in `A` and columns outside `A`. -/
noncomputable def entropy {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) : ℕ :=
  (cut G A).rank

/-- The graph state of `G` violates an instance of MMI: pairwise disjoint `I`, `J`, `K` with
`S_IJ + S_IK + S_JK < S_I + S_J + S_K + S_IJK`. -/
def ViolatesMMI {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) : Prop :=
  ∃ I J K : Finset W, Disjoint I J ∧ Disjoint I K ∧ Disjoint J K ∧
    entropy G (I ∪ J) + entropy G (I ∪ K) + entropy G (J ∪ K) <
      entropy G I + entropy G J + entropy G K + entropy G (I ∪ J ∪ K)

/-- `H` is a generalized star with centre `C` and parts `P`: the parts are nonempty and pairwise
disjoint, together with `C` they partition the vertices, no edge joins two different parts, and
every part has a vertex adjacent to a vertex of `C`. -/
def IsGeneralizedStar {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (C : Finset V) {k : ℕ} (P : Fin k → Finset V) : Prop :=
  (∀ p, (P p).Nonempty) ∧ (∀ p q, p ≠ q → Disjoint (P p) (P q)) ∧ (∀ p, Disjoint C (P p)) ∧
    C ∪ Finset.univ.biUnion P = Finset.univ ∧
      (∀ p q, p ≠ q → ∀ x ∈ P p, ∀ y ∈ P q, ¬ H.Adj x y) ∧
        (∀ p, ∃ x ∈ P p, ∃ c ∈ C, H.Adj x c)

/-- The forbidden-subgraph conjecture of Fuentes, Keeler, Munizzi and Pollack: every graph state
that violates MMI is LC-equivalent to a graph `H` with an induced four-star `K_{1,3}`, and `H` is
a generalized star with respect to the partition that places the three leaves in their own parts
and all other vertices in the centre. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ViolatesMMI G →
    ∃ (s : List (Fin n)) (c i j k : Fin n), IsClaw (lcSeq G s) c i j k ∧
      IsGeneralizedStar (lcSeq G s) (Finset.univ \ {i, j, k}) ![{i}, {j}, {k}]

/-- The conjecture holds. -/
theorem result : claim := by
  intro n G hviol
  classical
  -- local complementation commutes with pulling back along an injective map
  have comap_lc : ∀ {W U : Type} (f : W → U), Function.Injective f →
      ∀ (H : SimpleGraph U) (w : W), (lc H (f w)).comap f = lc (H.comap f) w := by
    intro W U f hf H w
    ext a b
    simp only [SimpleGraph.comap_adj, lc, ne_eq, hf.eq_iff]
  have comap_lcSeq : ∀ {W U : Type} (f : W → U), Function.Injective f →
      ∀ (s : List W) (H : SimpleGraph U), (lcSeq H (s.map f)).comap f = lcSeq (H.comap f) s := by
    intro W U f hf s
    induction s with
    | nil => intro H; rfl
    | cons w s ih =>
      intro H
      change (lcSeq (lc H (f w)) (s.map f)).comap f = lcSeq (lc (H.comap f) w) s
      rw [ih, comap_lc f hf]
  have lcSeq_append : ∀ {U : Type} (H : SimpleGraph U) (s t : List U),
      lcSeq H (s ++ t) = lcSeq (lcSeq H s) t := by
    intro U H s t
    exact List.foldl_append
  have claw_comap : ∀ {W U : Type} (f : W → U), Function.Injective f →
      ∀ (H : SimpleGraph U) (c i j l : W), IsClaw (H.comap f) c i j l →
        IsClaw H (f c) (f i) (f j) (f l) := by
    intro W U f hf H c i j l ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, hf.ne h4, hf.ne h5, hf.ne h6, h7, h8, h9⟩
  -- a vertex outside `S` with a neighbour in `S` keeps one under local complementation in `S`
  have keep_nbr : ∀ {U : Type} (S : Set U) (x : U), x ∉ S → ∀ (s : List U), (∀ v ∈ s, v ∈ S) →
      ∀ H : SimpleGraph U, (∃ y ∈ S, H.Adj y x) → ∃ y ∈ S, (lcSeq H s).Adj y x := by
    intro U S x hx s
    induction s with
    | nil => intro _ H h; exact h
    | cons v s ih =>
      intro hs H ⟨y, hyS, hy⟩
      have hvS : v ∈ S := hs v List.mem_cons_self
      apply ih (fun w hw => hs w (List.mem_cons_of_mem _ hw)) (lc H v)
      by_cases hvx : H.Adj v x
      · exact ⟨v, hvS, fun h => hx (h ▸ hvS), by simp [hvx]⟩
      · exact ⟨y, hyS, fun h => hx (h ▸ hyS), by simp [hy, hvx]⟩
  -- a graph on `Fin (k + 1)` is its restriction to `Fin k` extended by the last vertex
  have decomp : ∀ (k : ℕ) (H : SimpleGraph (Fin (k + 1))) (t : Fin k → Bool),
      (∀ i, t i = true ↔ H.Adj i.castSucc (Fin.last k)) → H = ext (H.comap Fin.castSucc) t := by
    intro k H t ht
    ext a b
    have hlast : ∀ x : Fin (k + 1), ¬ x.val < k → x = Fin.last k :=
      fun x hx => Fin.ext (by simp only [Fin.val_last]; omega)
    simp only [ext]
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · simp only [ha, hb, dite_true, SimpleGraph.comap_adj]
      exact ⟨fun h => ⟨H.ne_of_adj h, h⟩, fun h => h.2⟩
    · obtain rfl := hlast b hb
      simp only [ha, hb, dite_true, dite_false, ht]
      exact ⟨fun h => ⟨H.ne_of_adj h, h⟩, fun h => h.2⟩
    · obtain rfl := hlast a ha
      simp only [ha, hb, dite_true, dite_false, ht]
      exact ⟨fun h => ⟨H.ne_of_adj h, h.symm⟩, fun h => h.2.symm⟩
    · obtain rfl := hlast a ha
      obtain rfl := hlast b hb
      simp
  -- a certificate that checks gives a claw or the next representative
  have sound : ∀ (k : ℕ) (t : Fin k → Bool) (c : Cert k), check k t c = true →
      (∃ (s : List (Fin (k + 1))) (c i j l : Fin (k + 1)),
          IsClaw (lcSeq (ext (rep k) t) s) c i j l) ∨
        ∃ (s : List (Fin (k + 1))) (σ : Fin (k + 1) → Fin (k + 1)), Function.Bijective σ ∧
          lcSeq (ext (rep k) t) s = (rep (k + 1)).comap σ := by
    intro k t c h
    cases c with
    | none => simp [check] at h
    | claw s c i j l => exact Or.inl ⟨s, c, i, j, l, of_decide_eq_true h⟩
    | rep s σ =>
      obtain ⟨hσ, hadj⟩ := of_decide_eq_true h
      exact Or.inr ⟨s, σ, hσ, by ext a b; exact hadj a b⟩
  have lev : ∀ k, 1 ≤ k → k ≤ 6 → ∀ t : Fin k → Bool, (∃ i, t i = true) →
      check k t ((certs k).getD (code t) .none) = true := by
    intro k hk1 hk6
    interval_cases k <;> decide +kernel
  -- one extension step, up to the certificate
  have prep : ∀ (k : ℕ) (H : SimpleGraph (Fin (k + 1))), Ladder k (H.comap Fin.castSucc) →
      (∃ i : Fin k, H.Adj i.castSucc (Fin.last k)) →
      (∃ (s : List (Fin (k + 1))) (c i j l : Fin (k + 1)), IsClaw (lcSeq H s) c i j l) ∨
        ∃ (s : List (Fin (k + 1))) (τ : Fin (k + 1) ≃ Fin (k + 1)) (t : Fin k → Bool),
          (∃ i, t i = true) ∧ (lcSeq H s).comap τ = ext (rep k) t := by
    intro k H hL hnbr
    have hcs : Function.Injective (Fin.castSucc : Fin k → Fin (k + 1)) := Fin.castSucc_injective k
    rcases hL with ⟨s, c, i, j, l, hc⟩ | ⟨s, σ, hσ, hs⟩
    · refine Or.inl ⟨s.map Fin.castSucc, _, _, _, _, claw_comap _ hcs _ c i j l ?_⟩
      rw [comap_lcSeq _ hcs]
      exact hc
    · right
      set H1 := lcSeq H (s.map Fin.castSucc) with hH1
      have h1 : ∀ a b : Fin k, H1.Adj a.castSucc b.castSucc ↔ (rep k).Adj (σ a) (σ b) := by
        intro a b
        have := congrArg (fun G : SimpleGraph (Fin k) => G.Adj a b)
          ((comap_lcSeq _ hcs s H).trans hs)
        exact Iff.of_eq this
      set e : Fin k ≃ Fin k := Equiv.ofBijective σ hσ with he
      set τ : Fin (k + 1) ≃ Fin (k + 1) :=
        finSuccEquivLast.trans (e.symm.optionCongr.trans finSuccEquivLast.symm) with hτ
      have τc : ∀ a : Fin k, τ a.castSucc = (e.symm a).castSucc := by
        intro a
        simp only [hτ, Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionCongr_apply,
          Option.map_some, finSuccEquivLast_symm_some]
      have τl : τ (Fin.last k) = Fin.last k := by
        simp only [hτ, Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
          Option.map_none, finSuccEquivLast_symm_none]
      set H2 := H1.comap τ with hH2
      obtain ⟨y, ⟨i0, rfl⟩, hy⟩ := keep_nbr (Set.range Fin.castSucc) (Fin.last k)
        (fun ⟨i, hi⟩ => Fin.castSucc_ne_last i hi) (s.map Fin.castSucc)
        (fun v hv => by
          obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv
          exact ⟨w, rfl⟩)
        H (by
          obtain ⟨i, hi⟩ := hnbr
          exact ⟨_, ⟨i, rfl⟩, hi⟩)
      have ht : ∀ i : Fin k, decide (H2.Adj i.castSucc (Fin.last k)) = true ↔
          H2.Adj i.castSucc (Fin.last k) := fun i => decide_eq_true_iff
      refine ⟨s.map Fin.castSucc, τ, fun i : Fin k => decide (H2.Adj i.castSucc (Fin.last k)),
        ⟨e i0, ?_⟩, ?_⟩
      · rw [ht, hH2, SimpleGraph.comap_adj, τc, τl, Equiv.symm_apply_apply]
        exact hy
      · refine (decomp k H2 _ ht).trans ?_
        congr 1
        ext a b
        rw [SimpleGraph.comap_adj, hH2, SimpleGraph.comap_adj, τc, τc, h1, he,
          Equiv.ofBijective_apply_symm_apply σ hσ, Equiv.ofBijective_apply_symm_apply σ hσ]
  -- the last step: every extension of the prism reaches a claw
  have claw6 : ∀ t : Fin 6 → Bool, (∃ i, t i = true) →
      ∃ (s : List (Fin 7)) (c i j l : Fin 7), IsClaw (lcSeq (ext (rep 6) t) s) c i j l := by
    intro t ht
    have hcl : ∀ t : Fin 6 → Bool, (∃ i, t i = true) →
        ((certs 6).getD (code t) .none).isClaw = true := by
      decide +kernel
    have hch := lev 6 (by omega) le_rfl t ht
    have hc := hcl t ht
    revert hch hc
    cases (certs 6).getD (code t) .none with
    | none => intro h; simp [check] at h
    | claw s c i j l => intro h _; exact ⟨s, c, i, j, l, of_decide_eq_true h⟩
    | rep s σ => intro _ h; simp [Cert.isClaw] at h
  -- the ladder step
  have step : ∀ k, 1 ≤ k → k ≤ 5 → ∀ H : SimpleGraph (Fin (k + 1)),
      Ladder k (H.comap Fin.castSucc) → (∃ i : Fin k, H.Adj i.castSucc (Fin.last k)) →
        Ladder (k + 1) H := by
    intro k hk1 hk5 H hL hnbr
    rcases prep k H hL hnbr with hc | ⟨s, τ, t, ht, hH⟩
    · exact Or.inl hc
    have hτ : Function.Injective τ := τ.injective
    rcases sound k t _ (lev k hk1 (by omega) t ht) with ⟨s2, c, i, j, l, hc⟩ | ⟨s2, σ, hσ, hs⟩
    · refine Or.inl ⟨s ++ s2.map τ, τ c, τ i, τ j, τ l, ?_⟩
      rw [lcSeq_append]
      refine claw_comap τ hτ _ c i j l ?_
      rw [comap_lcSeq τ hτ, hH]
      exact hc
    · refine Or.inr ⟨s ++ s2.map τ, σ ∘ τ.symm, hσ.comp τ.symm.bijective, ?_⟩
      rw [lcSeq_append]
      have h2 : (lcSeq (lcSeq H s) (s2.map τ)).comap τ = (rep (k + 1)).comap σ := by
        rw [comap_lcSeq τ hτ, hH]
        exact hs
      ext a b
      have := congrArg (fun G : SimpleGraph (Fin (k + 1)) => G.Adj (τ.symm a) (τ.symm b)) h2
      simp only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] at this
      rw [SimpleGraph.comap_adj, Function.comp_apply, Function.comp_apply]
      exact Iff.of_eq this
  -- a connected graph has a chain of distinct vertices, each adjacent to an earlier one
  have chain : ∀ {W : Type} [Fintype W] (H : SimpleGraph W), H.Connected → ∀ m, 1 ≤ m →
      m ≤ Fintype.card W → ∃ g : Fin m → W, Function.Injective g ∧
        ∀ j : Fin m, 0 < j.val → ∃ i : Fin m, i < j ∧ H.Adj (g i) (g j) := by
    intro W _ H hH m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hmV
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨x⟩ := hH.nonempty
        exact ⟨fun _ => x, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega),
          fun j hj => absurd hj (by have := j.isLt; omega)⟩
      obtain ⟨g, hg, hch⟩ := ih hm (by omega)
      have hu : ∃ u, u ∉ Set.range g := by
        by_contra h
        push Not at h
        have := Fintype.card_le_of_surjective g h
        simp only [Fintype.card_fin] at this
        omega
      obtain ⟨u, hu⟩ := hu
      obtain ⟨p⟩ := hH.preconnected (g ⟨0, hm⟩) u
      obtain ⟨d, -, ⟨i0, hi0⟩, hdn⟩ := p.exists_boundary_dart (Set.range g) ⟨_, rfl⟩ hu
      refine ⟨Fin.snoc (α := fun _ => W) g d.snd, Fin.snoc_injective_iff.2 ⟨hg, hdn⟩, ?_⟩
      intro j hj
      induction j using Fin.lastCases with
      | last =>
        refine ⟨i0.castSucc, Fin.castSucc_lt_last i0, ?_⟩
        simp only [Fin.snoc_last, Fin.snoc_castSucc, hi0]
        exact d.adj
      | cast j =>
        obtain ⟨i, hij, hadj⟩ := hch j (by simpa using hj)
        refine ⟨i.castSucc, Fin.castSucc_lt_castSucc_iff.2 hij, ?_⟩
        simp only [Fin.snoc_castSucc]
        exact hadj
  -- a chain restricts to its first `m` vertices, whose last vertex has an earlier neighbour
  have restrict : ∀ {W : Type} (H : SimpleGraph W) (m : ℕ), 1 ≤ m → ∀ g : Fin (m + 1) → W,
      (∀ j : Fin (m + 1), 0 < j.val → ∃ i : Fin (m + 1), i < j ∧ H.Adj (g i) (g j)) →
      (∀ j : Fin m, 0 < j.val → ∃ i : Fin m, i < j ∧ H.Adj (g i.castSucc) (g j.castSucc)) ∧
        ∃ i : Fin m, (H.comap g).Adj i.castSucc (Fin.last m) := by
    intro W H m hm g hch
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨i, hij, hadj⟩ := hch j.castSucc hj
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2
        (Fin.ne_last_of_lt (lt_trans hij (Fin.castSucc_lt_last j)))
      exact ⟨i', Fin.castSucc_lt_castSucc_iff.1 hij, hadj⟩
    · obtain ⟨i, hij, hadj⟩ := hch (Fin.last m) (by simp only [Fin.val_last]; omega)
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hij)
      exact ⟨i', hadj⟩
  -- the ladder along a chain of at most six vertices
  have ladder : ∀ {W : Type} (H : SimpleGraph W) (m : ℕ), 1 ≤ m → m ≤ 6 →
      ∀ g : Fin m → W, Function.Injective g →
        (∀ j : Fin m, 0 < j.val → ∃ i : Fin m, i < j ∧ H.Adj (g i) (g j)) →
          Ladder m (H.comap g) := by
    intro W H m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hm6 g hg hch
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · refine Or.inr ⟨[], id, Function.bijective_id, ?_⟩
        ext a b
        have : a = b := Fin.ext (by have := a.isLt; have := b.isLt; omega)
        subst this
        simp
      · obtain ⟨hch', hnbr⟩ := restrict H m hm g hch
        exact step m hm (by omega) (H.comap g)
          (ih hm (by omega) (g ∘ Fin.castSucc) (hg.comp (Fin.castSucc_injective m)) hch') hnbr
  -- a connected piece of `G` reaches a claw of `G`, or is a relabelled representative
  have cls : ∀ {W : Type} [Fintype W] [DecidableEq W] (f : W → Fin n), Function.Injective f →
      (G.comap f).Connected →
      (∃ (s : List (Fin n)) (c i j l : Fin n), IsClaw (lcSeq G s) c i j l) ∨
        (Fintype.card W ≤ 6 ∧ ∃ (s : List W) (e : W ≃ Fin (Fintype.card W)),
          lcSeq (G.comap f) s = (rep (Fintype.card W)).comap e) := by
    intro W _ _ f hf hc
    have lift : ∀ (s : List W) (c i j l : W), IsClaw (lcSeq (G.comap f) s) c i j l →
        ∃ (s : List (Fin n)) (c i j l : Fin n), IsClaw (lcSeq G s) c i j l := by
      intro s c i j l h
      refine ⟨s.map f, _, _, _, _, claw_comap f hf _ c i j l ?_⟩
      rw [comap_lcSeq f hf]
      exact h
    have hV : 1 ≤ Fintype.card W := Fintype.card_pos_iff.2 hc.nonempty
    by_cases h7 : 7 ≤ Fintype.card W
    · left
      obtain ⟨g, hg, hch⟩ := chain (G.comap f) hc 7 (by omega) h7
      obtain ⟨hch', hnbr⟩ := restrict (G.comap f) 6 (by omega) g hch
      have hL := ladder (G.comap f) 6 (by omega) le_rfl (g ∘ Fin.castSucc)
        (hg.comp (Fin.castSucc_injective 6)) hch'
      rcases prep 6 ((G.comap f).comap g) hL hnbr with ⟨s, c, i, j, l, hc'⟩ | ⟨s, τ, t, ht, hH⟩
      · refine lift (s.map g) _ _ _ _ (claw_comap g hg _ c i j l ?_)
        rw [comap_lcSeq g hg]
        exact hc'
      · obtain ⟨s2, c, i, j, l, hc'⟩ := claw6 t ht
        refine lift ((s ++ s2.map τ).map g) _ _ _ _
          (claw_comap g hg _ (τ c) (τ i) (τ j) (τ l) ?_)
        rw [comap_lcSeq g hg, lcSeq_append]
        refine claw_comap τ τ.injective _ c i j l ?_
        rw [comap_lcSeq τ τ.injective, hH]
        exact hc'
    · obtain ⟨g, hg, hch⟩ := chain (G.comap f) hc (Fintype.card W) hV le_rfl
      have hgb : Function.Bijective g :=
        (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩
      rcases ladder (G.comap f) _ hV (by omega) g hg hch with
        ⟨s, c, i, j, l, hc'⟩ | ⟨s, σ, hσ, hs⟩
      · refine Or.inl (lift (s.map g) _ _ _ _ (claw_comap g hg _ c i j l ?_))
        rw [comap_lcSeq g hg]
        exact hc'
      · refine Or.inr ⟨by omega, s.map g,
          (Equiv.ofBijective g hgb).symm.trans (Equiv.ofBijective σ hσ), ?_⟩
        ext a b
        obtain ⟨a', rfl⟩ := hgb.surjective a
        obtain ⟨b', rfl⟩ := hgb.surjective b
        have := congrArg (fun H : SimpleGraph (Fin (Fintype.card W)) => H.Adj a' b')
          ((comap_lcSeq g hg s (G.comap f)).trans hs)
        simp only [SimpleGraph.comap_adj] at this
        simp only [SimpleGraph.comap_adj, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply,
          Equiv.ofBijective_apply]
        exact Iff.of_eq this
  -- a block-diagonal matrix has the sum of the ranks of its blocks
  have blocks : ∀ {m₁ m₂ n₁ n₂ : Type} [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
      [DecidableEq m₁] [DecidableEq m₂] [DecidableEq n₁] [DecidableEq n₂]
      (M₁ : Matrix m₁ n₁ (ZMod 2)) (M₂ : Matrix m₂ n₂ (ZMod 2)),
      (Matrix.fromBlocks M₁ 0 0 M₂).rank = M₁.rank + M₂.rank := by
    intro m₁ m₂ n₁ n₂ _ _ _ _ _ _ _ _ M₁ M₂
    unfold Matrix.rank
    have key : (Matrix.fromBlocks M₁ 0 0 M₂).mulVecLin =
        (LinearEquiv.sumArrowLequivProdArrow m₁ m₂ (ZMod 2) (ZMod 2)).symm.toLinearMap ∘ₗ
          (M₁.mulVecLin.prodMap M₂.mulVecLin) ∘ₗ
            (LinearEquiv.sumArrowLequivProdArrow n₁ n₂ (ZMod 2) (ZMod 2)).toLinearMap := by
      ext x i
      rcases i with i | i <;> simp [Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, LinearEquiv.sumArrowLequivProdArrow]
    rw [key, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      LinearMap.range_prodMap, LinearEquiv.finrank_map_eq]
    let e : ↥(M₁.mulVecLin.range.prod M₂.mulVecLin.range) ≃ₗ[ZMod 2]
        ↥M₁.mulVecLin.range × ↥M₂.mulVecLin.range :=
      { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
        invFun := fun y => ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [e.finrank_eq, Module.finrank_prod]
  -- a set and its complement have the same entropy
  have compl_eq : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V),
      entropy G Aᶜ = entropy G A := by
    intro V _ _ G A
    unfold entropy
    have h : cut G Aᶜ = (cut G A).transpose.submatrix
        (Equiv.subtypeEquivRight (fun x => Finset.mem_compl))
        (Equiv.subtypeEquivRight (fun x => by simp)) := by
      ext r c
      simp only [cut, SimpleGraph.adjMatrix_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Equiv.subtypeEquivRight_apply]
      by_cases h : G.Adj r c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [h, Matrix.rank_submatrix, Matrix.rank_transpose]
  -- relabelling the vertices
  have relabel : ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (e : W ≃ V) (A : Finset W),
      entropy (G.comap e) A = entropy G (A.map e.toEmbedding) := by
    intro V W _ _ _ _ G e A
    unfold entropy
    have h : cut (G.comap e) A = (cut G (A.map e.toEmbedding)).submatrix
        (Equiv.subtypeEquiv e (fun x => by simp))
        (Equiv.subtypeEquiv e (fun x => by simp)) := by
      ext r c
      rfl
    rw [h, Matrix.rank_submatrix]
  -- local complementation leaves every entropy unchanged
  have lc_eq : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
      (A : Finset V), entropy (lc G v) A = entropy G A := by
    intro V _ _ G v A
    -- the case `v ∈ A`: a row operation by an involution
    have mem : ∀ B : Finset V, v ∈ B → entropy (lc G v) B = entropy G B := by
      intro B hv
      classical
      unfold entropy
      set N : Matrix {x // x ∈ B} {x // x ∈ B} (ZMod 2) :=
        fun a a' => if G.Adj v a ∧ (a' : V) = v then 1 else 0 with hN
      have hNN : N * N = 0 := by
        ext a a''
        simp only [hN, Matrix.zero_apply]
        apply Finset.sum_eq_zero
        intro a' _
        by_cases h : (a' : V) = v
        · simp [h]
        · simp [h]
      have h2 : N + N = 0 := by
        ext a b
        simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
      have hE : (1 + N) * (1 + N) = 1 := by
        rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hNN, add_zero, add_assoc, h2,
          add_zero]
      have hdet : IsUnit (1 + N).det := by
        have := congrArg Matrix.det hE
        rw [Matrix.det_mul, Matrix.det_one] at this
        exact isUnit_iff_exists_inv.2 ⟨_, this⟩
      have hM : cut (lc G v) B = (1 + N) * cut G B := by
        ext a b
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
          Finset.sum_eq_single ⟨v, hv⟩]
        · simp only [hN, cut, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, lc]
          have hab : (a : V) ≠ b := fun h => b.2 (h ▸ a.2)
          by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj v a <;> by_cases h3 : G.Adj v b <;>
            simp +decide [h1, h2, h3, hab]
        · intro a' _ ha'
          have : (a' : V) ≠ v := fun h => ha' (Subtype.ext h)
          simp [hN, this]
        · simp
      rw [hM, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
    by_cases hv : v ∈ A
    · exact mem A hv
    · rw [← compl_eq (lc G v), ← compl_eq G]
      exact mem Aᶜ (Finset.mem_compl.2 hv)
  -- rows of `A'` with independent restrictions outside `A` bound the entropy of `A` from below
  have crit : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A A' : Finset V)
      (hA' : A' ⊆ A) (h : ∀ T ⊆ A', T.Nonempty → ∃ b ∉ A, Odd (T.filter (G.Adj · b)).card),
      A'.card ≤ entropy G A := by
    intro V _ _ G A A' hA' h
    classical
    unfold entropy
    set r : {x // x ∈ A'} → {x // x ∈ A} := fun x => ⟨x.1, hA' x.2⟩ with hr
    have hli : LinearIndependent (ZMod 2) ((cut G A).submatrix r id).row := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      by_contra hi
      set T : Finset V := (Finset.univ.filter (fun j => g j ≠ 0)).map (Function.Embedding.subtype _)
        with hT
      have hTA : T ⊆ A' := by
        intro x hx
        simp only [hT, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype] at hx
        obtain ⟨j, -, rfl⟩ := hx
        exact j.2
      obtain ⟨b, hbA, hodd⟩ := h T hTA ⟨i.1, by simp [hT, hi]⟩
      have hz := congrFun hg ⟨b, hbA⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row,
        Matrix.submatrix_apply, id, cut, SimpleGraph.adjMatrix_apply, hr] at hz
      have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      have hsum : (∑ j : {x // x ∈ A'}, g j * if G.Adj (j : V) b then (1 : ZMod 2) else 0) =
          ((T.filter (G.Adj · b)).card : ZMod 2) := by
        rw [hT, Finset.filter_map, Finset.card_map, Finset.card_filter, Nat.cast_sum]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Function.comp_apply, Function.Embedding.coe_subtype]
        by_cases hj : g j = 0
        · simp [hj]
        · rw [h01 _ hj]
          by_cases hb : G.Adj (j : V) b <;> simp [hb]
      rw [hsum, (ZMod.natCast_eq_one_iff_odd).2 hodd] at hz
      exact one_ne_zero hz
    have := Matrix.rank_submatrix_le (cut G A) r id
    rw [hli.rank_matrix, Fintype.card_coe] at this
    exact this
  -- the entropy is at most the size of the set and of its complement
  have le_card : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V),
      entropy G A ≤ A.card ∧ entropy G A ≤ Aᶜ.card := by
    intro V _ _ G A
    unfold entropy
    refine ⟨?_, ?_⟩
    · have := Matrix.rank_le_card_height (cut G A)
      simpa using this
    · have := Matrix.rank_le_card_width (cut G A)
      rw [Fintype.card_subtype] at this
      simpa [Finset.filter_not, Finset.compl_eq_univ_sdiff] using this
  -- a checked independence criterion gives the maximal entropy `min |A| (n - |A|)`
  have ame : ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (h : ∀ A : Finset (Fin n), 2 * A.card ≤ n → ∀ T ⊆ A, T.Nonempty →
        ∃ b ∉ A, (T.filter (H.Adj · b)).card % 2 = 1) (A : Finset (Fin n)),
      entropy H A = min A.card (n - A.card) := by
    intro n H _ h A
    classical
    have hlow : ∀ B : Finset (Fin n), 2 * B.card ≤ n → B.card ≤ entropy H B := by
      intro B hB
      refine crit H B B le_rfl (fun T hT hne => ?_)
      obtain ⟨b, hb, hodd⟩ := h B hB T hT hne
      refine ⟨b, hb, ?_⟩
      rw [Nat.odd_iff]
      convert hodd using 3
      ext x
      simp only [Finset.mem_filter]
    have hc : Aᶜ.card = n - A.card := by rw [Finset.card_compl, Fintype.card_fin]
    obtain ⟨h1, h2⟩ := le_card H A
    rw [hc] at h2
    by_cases hA : 2 * A.card ≤ n
    · have := hlow A hA
      omega
    · have := hlow Aᶜ (by rw [hc]; omega)
      rw [compl_eq, hc] at this
      omega
  -- maximal entropies satisfy MMI
  have ame_mmi : ∀ {n : ℕ} (hn : n ≤ 6) (H : SimpleGraph (Fin n))
      (hS : ∀ A, entropy H A = min A.card (n - A.card)), ¬ ViolatesMMI H := by
    intro n hn H hS
    rintro ⟨I, J, K, hIJ, hIK, hJK, hlt⟩
    have harith : ∀ i ≤ 6, ∀ j ≤ 6, ∀ k ≤ 6, i + j + k ≤ n →
        min i (n - i) + min j (n - j) + min k (n - k) + min (i + j + k) (n - (i + j + k)) ≤
          min (i + j) (n - (i + j)) + min (i + k) (n - (i + k)) + min (j + k) (n - (j + k)) := by
      interval_cases n <;> decide
    have hsub : (I ∪ J ∪ K).card ≤ n := by
      simpa using Finset.card_le_univ (I ∪ J ∪ K)
    rw [hS, hS, hS, hS, hS, hS, hS, Finset.card_union_of_disjoint hIJ,
      Finset.card_union_of_disjoint hIK, Finset.card_union_of_disjoint hJK,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hIK, hJK⟩),
      Finset.card_union_of_disjoint hIJ] at hlt
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hIK, hJK⟩),
      Finset.card_union_of_disjoint hIJ] at hsub
    have := harith I.card (by omega) J.card (by omega) K.card (by omega) hsub
    omega
  -- the path `P_4` satisfies MMI
  have p4_mmi : ¬ ViolatesMMI (rep 4) := by
    classical
    rintro ⟨I, J, K, hIJ, hIK, hJK, hlt⟩
    have h0 : entropy (rep 4) ∅ = 0 := by
      have := (le_card (rep 4) ∅).1
      simpa using this
    have hU : entropy (rep 4) Finset.univ = 0 := by
      have := (le_card (rep 4) Finset.univ).2
      simpa using this
    by_cases hI : I = ∅
    · subst hI
      simp only [Finset.empty_union, h0] at hlt
      omega
    by_cases hJ : J = ∅
    · subst hJ
      simp only [Finset.empty_union, Finset.union_empty, h0] at hlt
      omega
    by_cases hK : K = ∅
    · subst hK
      simp only [Finset.union_empty, h0] at hlt
      omega
    by_cases hD : I ∪ J ∪ K = Finset.univ
    · have hc : ∀ X Y Z : Finset (Fin 4), Disjoint X Z → Disjoint Y Z → X ∪ Y ∪ Z = Finset.univ →
          (X ∪ Y)ᶜ = Z := by
        intro X Y Z hXZ hYZ hXYZ
        ext x
        have hx : x ∈ X ∪ Y ∪ Z := hXYZ ▸ Finset.mem_univ x
        simp only [Finset.mem_compl, Finset.mem_union] at hx ⊢
        constructor
        · intro h
          tauto
        · intro hz h
          rcases h with h | h
          · exact Finset.disjoint_left.1 hXZ h hz
          · exact Finset.disjoint_left.1 hYZ h hz
      have e1 := hc I J K hIK hJK hD
      have e2 : (I ∪ K)ᶜ = J := hc I K J hIJ hJK.symm (by rw [← hD]; ac_rfl)
      have e3 : (J ∪ K)ᶜ = I := hc J K I hIJ.symm hIK.symm (by rw [← hD]; ac_rfl)
      rw [← compl_eq (rep 4) (I ∪ J), e1, ← compl_eq (rep 4) (I ∪ K), e2,
        ← compl_eq (rep 4) (J ∪ K), e3, hD, hU] at hlt
      omega
    -- all four parts are nonempty, so each of I, J, K is a single vertex
    have hcard : (I ∪ J ∪ K).card ≤ 3 := by
      have := (Finset.card_lt_iff_ne_univ _).2 hD
      simp only [Fintype.card_fin] at this
      omega
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hIK, hJK⟩),
      Finset.card_union_of_disjoint hIJ] at hcard
    have pI := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hI)
    have pJ := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ)
    have pK := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hK)
    have hI1 : I.card = 1 := by omega
    have hJ1 : J.card = 1 := by omega
    have hK1 : K.card = 1 := by omega
    -- lower bounds for the pairs
    let lb : Finset (Fin 4) → ℕ := fun P => if P = {0, 3} ∨ P = {1, 2} then 1 else 2
    have hlb : ∀ P : Finset (Fin 4), P.card = 2 → lb P ≤ entropy (rep 4) P := by
      have hc : ∀ P : Finset (Fin 4), P.card = 2 → ∃ A' ∈ P.powerset, lb P = A'.card ∧
          ∀ T ∈ A'.powerset, T.Nonempty → ∃ b ∉ P, (T.filter ((rep 4).Adj · b)).card % 2 = 1 := by
        decide
      intro P hP
      obtain ⟨A', hA', hlbA, hcrit⟩ := hc P hP
      rw [hlbA]
      refine crit (rep 4) P A' (Finset.mem_powerset.1 hA') (fun T hT hne => ?_)
      obtain ⟨b, hb, hodd⟩ := hcrit T (Finset.mem_powerset.2 hT) hne
      refine ⟨b, hb, ?_⟩
      rw [Nat.odd_iff]
      convert hodd using 3
      ext x
      simp only [Finset.mem_filter]
    have hsum : ∀ X Y Z : Finset (Fin 4), X.card = 1 → Y.card = 1 → Z.card = 1 → Disjoint X Y →
        Disjoint X Z → Disjoint Y Z → 5 ≤ lb (X ∪ Y) + lb (X ∪ Z) + lb (Y ∪ Z) := by
      decide
    have hpair : ∀ X Y : Finset (Fin 4), X.card = 1 → Y.card = 1 → Disjoint X Y →
        (X ∪ Y).card = 2 := by
      intro X Y hX hY hXY
      rw [Finset.card_union_of_disjoint hXY, hX, hY]
    have b1 := hlb _ (hpair I J hI1 hJ1 hIJ)
    have b2 := hlb _ (hpair I K hI1 hK1 hIK)
    have b3 := hlb _ (hpair J K hJ1 hK1 hJK)
    have b4 := hsum I J K hI1 hJ1 hK1 hIJ hIK hJK
    have u1 := (le_card (rep 4) I).1
    have u2 := (le_card (rep 4) J).1
    have u3 := (le_card (rep 4) K).1
    have u4 := (le_card (rep 4) (I ∪ J ∪ K)).2
    have hc4 : (I ∪ J ∪ K)ᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin,
        Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hIK, hJK⟩),
        Finset.card_union_of_disjoint hIJ]
      omega
    omega
  -- every representative satisfies MMI
  have rep_mmi : ∀ (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6), ¬ ViolatesMMI (rep k) := by
    intro k hk1 hk6
    interval_cases k
    · exact ame_mmi (by norm_num) _ (ame _ (by decide))
    · exact ame_mmi (by norm_num) _ (ame _ (by decide))
    · exact ame_mmi (by norm_num) _ (ame _ (by decide))
    · exact p4_mmi
    · exact ame_mmi (by norm_num) _ (ame _ (by decide +kernel))
    · exact ame_mmi (by norm_num) _ (ame _ (by decide +kernel))
  have lcSeq_eq : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : List V) (A :
      Finset V), entropy (lcSeq G s) A = entropy G A := by
    intro V _ _ G s A
    induction s generalizing G with
    | nil => rfl
    | cons v s ih => exact (ih (lc G v)).trans (lc_eq G v A)
  -- a graph carried to a relabelled representative satisfies MMI with it
  have transfer : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (k : ℕ)
      (s : List W) (e : W ≃ Fin k) (h : lcSeq H s = (rep k).comap e)
      (hk : ¬ ViolatesMMI (rep k)), ¬ ViolatesMMI H := by
    intro W _ _ H k s e h hk
    rintro ⟨I, J, K, hIJ, hIK, hJK, hlt⟩
    have hS : ∀ A, entropy H A = entropy (rep k) (A.map e.toEmbedding) := fun A => by
      rw [← lcSeq_eq H s, h, relabel]
    simp only [hS, Finset.map_union] at hlt
    exact hk ⟨_, _, _, (Finset.disjoint_map _).2 hIJ, (Finset.disjoint_map _).2 hIK,
      (Finset.disjoint_map _).2 hJK, hlt⟩
  -- entropies add over a set without edges to its complement
  have split : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (X : Finset W)
      (hX : ∀ x ∈ X, ∀ y ∉ X, ¬ H.Adj x y) (A : Finset W),
      entropy H A = entropy (H.comap (Subtype.val : {x // x ∈ X} → W)) (A.subtype (· ∈ X)) +
        entropy (H.comap (Subtype.val : {x // x ∉ X} → W)) (A.subtype (· ∉ X)) := by
    intro W _ _ H X hX A
    classical
    -- `{a // p a}` splits into the parts inside and outside `X`
    have eqv : ∀ (p : W → Prop) [DecidablePred p] (q₁ : {x // x ∈ X} → Prop)
        (q₂ : {x // x ∉ X} → Prop) (h₁ : ∀ y, q₁ y ↔ p y.1) (h₂ : ∀ y, q₂ y ↔ p y.1),
        {e : {a // p a} ≃ {y // q₁ y} ⊕ {y // q₂ y} //
          (∀ a (h : a.1 ∈ X), e a = Sum.inl ⟨⟨a.1, h⟩, (h₁ _).2 a.2⟩) ∧
          (∀ a (h : a.1 ∉ X), e a = Sum.inr ⟨⟨a.1, h⟩, (h₂ _).2 a.2⟩)} := by
      intro p _ q₁ q₂ h₁ h₂
      refine ⟨{ toFun := fun a => if h : a.1 ∈ X then Sum.inl ⟨⟨a.1, h⟩, (h₁ _).2 a.2⟩
                  else Sum.inr ⟨⟨a.1, h⟩, (h₂ _).2 a.2⟩
                invFun := Sum.elim (fun y => ⟨y.1.1, (h₁ y.1).1 y.2⟩)
                  (fun y => ⟨y.1.1, (h₂ y.1).1 y.2⟩)
                left_inv := fun a => by by_cases h : a.1 ∈ X <;> simp [h]
                right_inv := fun y => by
                  rcases y with y | y
                  · simp [y.1.2]
                  · simp [y.1.2] }, fun a h => by simp [h], fun a h => by simp [h]⟩
    obtain ⟨eR, hR1, hR2⟩ := eqv (· ∈ A) (· ∈ A.subtype (· ∈ X)) (· ∈ A.subtype (· ∉ X))
      (fun y => Finset.mem_subtype) (fun y => Finset.mem_subtype)
    obtain ⟨eC, hC1, hC2⟩ := eqv (· ∉ A) (· ∉ A.subtype (· ∈ X)) (· ∉ A.subtype (· ∉ X))
      (fun y => by rw [Finset.mem_subtype]) (fun y => by rw [Finset.mem_subtype])
    unfold entropy
    rw [← blocks]
    have hM : cut H A = (Matrix.fromBlocks (cut (H.comap (Subtype.val : {x // x ∈ X} → W))
        (A.subtype (· ∈ X))) 0 0 (cut (H.comap (Subtype.val : {x // x ∉ X} → W))
        (A.subtype (· ∉ X)))).submatrix eR eC := by
      ext a b
      simp only [Matrix.submatrix_apply]
      by_cases ha : a.1 ∈ X <;> by_cases hb : b.1 ∈ X
      · rw [hR1 a ha, hC1 b hb]
        rfl
      · rw [hR1 a ha, hC2 b hb]
        simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, cut, Matrix.submatrix_apply,
          SimpleGraph.adjMatrix_apply]
        rw [if_neg (hX _ ha _ hb)]
      · rw [hR2 a ha, hC1 b hb]
        simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, cut, Matrix.submatrix_apply,
          SimpleGraph.adjMatrix_apply]
        rw [if_neg (fun h => hX _ hb _ ha h.symm)]
      · rw [hR2 a ha, hC2 b hb]
        rfl
    rw [hM, Matrix.rank_submatrix]
  have split_mmi : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (X : Finset W)
      (hX : ∀ x ∈ X, ∀ y ∉ X, ¬ H.Adj x y)
      (h₁ : ¬ ViolatesMMI (H.comap (Subtype.val : {x // x ∈ X} → W)))
      (h₂ : ¬ ViolatesMMI (H.comap (Subtype.val : {x // x ∉ X} → W))), ¬ ViolatesMMI H := by
    intro W _ _ H X hX h₁ h₂
    rintro ⟨I, J, K, hIJ, hIK, hJK, hlt⟩
    have hsub : ∀ (p : W → Prop) [DecidablePred p] (A B : Finset W),
        (A ∪ B).subtype p = A.subtype p ∪ B.subtype p := by
      intro p _ A B
      ext y
      simp [Finset.mem_subtype]
    have hdis : ∀ (p : W → Prop) [DecidablePred p] (A B : Finset W), Disjoint A B →
        Disjoint (A.subtype p) (B.subtype p) := by
      intro p _ A B h
      exact Finset.disjoint_left.2 fun y hy hy' =>
        Finset.disjoint_left.1 h (Finset.mem_subtype.1 hy) (Finset.mem_subtype.1 hy')
    simp only [split H X hX, hsub] at hlt
    have a := not_lt.1 fun hlt => h₁ ⟨_, _, _, hdis _ _ _ hIJ, hdis _ _ _ hIK, hdis _ _ _ hJK, hlt⟩
    have b := not_lt.1 fun hlt => h₂ ⟨_, _, _, hdis _ _ _ hIJ, hdis _ _ _ hIK, hdis _ _ _ hJK, hlt⟩
    omega
  -- without a claw reachable in `G`, every piece of `G` satisfies MMI
  have main : (¬ ∃ (s : List (Fin n)) (c i j l : Fin n), IsClaw (lcSeq G s) c i j l) →
      ∀ (m : ℕ) {W : Type} [Fintype W] [DecidableEq W], Fintype.card W = m →
        ∀ f : W → Fin n, Function.Injective f → ¬ ViolatesMMI (G.comap f) := by
    intro hno m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro W _ _ hW f hf
    rcases isEmpty_or_nonempty W with hE | ⟨⟨w⟩⟩
    · rintro ⟨I, J, K, -, -, -, hlt⟩
      have hz : ∀ A : Finset W, entropy (G.comap f) A = 0 := fun A => by
        have := (le_card (G.comap f) A).1
        rw [Finset.eq_empty_of_isEmpty A] at this ⊢
        simpa using this
      simp only [hz] at hlt
      omega
    set H := G.comap f with hHdef
    set C := H.connectedComponentMk w with hC
    set X : Finset W := Finset.univ.filter (fun y => y ∈ C.supp) with hXdef
    have hwX : w ∈ X := by
      simp [hXdef, hC, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hX : ∀ x ∈ X, ∀ y ∉ X, ¬ H.Adj x y := by
      intro x hx y hy hxy
      apply hy
      simp only [hXdef, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
      rw [← hx]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    refine split_mmi H X hX ?_ ?_
    · have hconn : (G.comap (f ∘ (Subtype.val : {x // x ∈ X} → W))).Connected := by
        let e : {x // x ∈ X} ≃ C.supp :=
          Equiv.subtypeEquivRight (fun y => by simp [hXdef])
        have hg : SimpleGraph.comap e C.toSimpleGraph = G.comap (f ∘ Subtype.val) := by
          ext a b
          rfl
        rw [← hg]
        exact (SimpleGraph.Iso.comap e C.toSimpleGraph).connected_iff.2
          C.connected_toSimpleGraph
      rcases cls (f ∘ Subtype.val) (hf.comp Subtype.val_injective) hconn with
        hc | ⟨h6, s, e, hs⟩
      · exact absurd hc hno
      · have h1 : 1 ≤ Fintype.card {x // x ∈ X} := Fintype.card_pos_iff.2 ⟨⟨w, hwX⟩⟩
        exact transfer _ _ s e hs (rep_mmi _ h1 h6)
    · have hlt : Fintype.card {x // x ∉ X} < m := by
        rw [← hW, Fintype.card_subtype_compl, Fintype.card_coe]
        have : 0 < X.card := Finset.card_pos.2 ⟨w, hwX⟩
        have : X.card ≤ Fintype.card W := Finset.card_le_univ X
        omega
      exact ih _ hlt rfl (f ∘ Subtype.val) (hf.comp Subtype.val_injective)
  have hclaw : ∃ (s : List (Fin n)) (c i j l : Fin n), IsClaw (lcSeq G s) c i j l := by
    by_contra hno
    have := main hno _ rfl id Function.injective_id
    rw [SimpleGraph.comap_id] at this
    exact this hviol
  obtain ⟨s, c, i, j, k, hc⟩ := hclaw
  refine ⟨s, c, i, j, k, hc, ?_⟩
  obtain ⟨hci, hcj, hck, hij, hik, hjk, nij, nik, njk⟩ := hc
  have nji : ¬ (lcSeq G s).Adj j i := fun h => nij h.symm
  have nki : ¬ (lcSeq G s).Adj k i := fun h => nik h.symm
  have nkj : ¬ (lcSeq G s).Adj k j := fun h => njk h.symm
  have hcC : c ∈ Finset.univ \ {i, j, k} := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and]
    rintro (h | h | h)
    · exact (lcSeq G s).loopless.irrefl c (h ▸ hci)
    · exact (lcSeq G s).loopless.irrefl c (h ▸ hcj)
    · exact (lcSeq G s).loopless.irrefl c (h ▸ hck)
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun p => ?_, ?_, fun p q hpq => ?_, fun p => ?_⟩
  · fin_cases p <;> simp
  · fin_cases p <;> fin_cases q <;>
      first
      | exact absurd rfl hpq
      | simp [hij, hik, hjk, hij.symm, hik.symm, hjk.symm]
  · fin_cases p <;> simp
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, Finset.mem_biUnion, iff_true]
    by_cases hx : x = i ∨ x = j ∨ x = k
    · right
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · exact Or.inl hx
  · intro x hx y hy
    fin_cases p <;> fin_cases q <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Fin.zero_eta,
        Fin.reduceFinMk, Fin.reduceEq, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
        Finset.mem_singleton, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
        not_true_eq_false] at hx hy hpq <;>
      subst hx hy <;> assumption
  · fin_cases p
    · exact ⟨i, by simp, c, hcC, hci.symm⟩
    · exact ⟨j, by simp, c, hcC, hcj.symm⟩
    · exact ⟨k, by simp, c, hcC, hck.symm⟩

end D5.S3.Quantum.Entanglement.GraphStateMonogamyForbiddenSubgraph
