/- GID: D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.claim; result=D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result; claim=D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.claim
   digest: A 6-regular biconnected 28-vertex graph has Delta^4 ln(i! N(i)) > 0 at i = 10. -/

/-
proof_shape: matchingCount: definition (i-edge matchings of K_n inside the edge set, using the
  frozen MatchingFiber.Matching)
proof_shape: matchingNumber: definition (supremum of the i with N(i) > 0)
proof_shape: Biconnected: definition (connected, and connected after deleting any vertex)
proof_shape: claim: definition (published question, read as a universal statement)
proof_shape: result: content (kernel evaluation of the edge set, the degrees and the cascade
  values N(10..14) of one 28-vertex graph, the matching-number argument, and the inequality
  Delta^4 ln(i! N(i)) > 0 at i = 10)
proof_shape: private theorems: content (the deletion and product rules for matching counts by
  explicit bijections, the vertex-count bound, relabelling invariance, the bridge to
  MatchingFiber.Matching, kernel enumeration of the block counts and connector steps, the
  cascade induction, and biconnectivity from a Hamiltonian cycle)
escape_witness: result (form (2) of §3.2: the counts N(10..14) of the graph and the positive
  fourth difference are produced by the counting chain and the kernel evaluation; no existing
  statement gives them)
admission_basis: open-problem-resolution (issue #12197; Refuted)
Direct frozen dependencies:
  D5/S3/Zeros/Convolution/MatchingFiber.Matching
-/

import D5.S3.Zeros.Convolution.MatchingFiber
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation

open Finset
open D5.S3.Zeros.Convolution

/-- `N(i)`: the number of `i`-edge matchings of `G` (configurations of `i` dimers), i.e. the
`i`-edge matchings of `K_n` all of whose edges are edges of `G`. -/
noncomputable def matchingCount {n : ℕ} (G : SimpleGraph (Fin n)) (i : ℕ) : ℕ :=
  Nat.card {M : MatchingFiber.Matching n i // ∀ e ∈ M.val, e ∈ G.edgeSet}

/-- `ν(G)`: the largest number of pairwise disjoint edges of `G`. -/
noncomputable def matchingNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {i | 0 < matchingCount G i}

/-- A graph is biconnected when it is connected and stays connected after deleting any one
vertex. -/
def Biconnected {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v, (G.induce {v}ᶜ).Connected

/-- The question of Butera, Federbush and Pernici (arXiv:1502.06734, Section IV), read as a
universal statement: for every regular biconnected finite simple graph, every `k ∈ {2, 3, 4}`
and every `i` with `i + k ≤ ν`, `Δ^k ln(i! N(i)) ≤ 0`. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∃ d, G.IsRegularOfDegree d) → Biconnected G →
      ∀ k i : ℕ, 2 ≤ k → k ≤ 4 → i + k ≤ matchingNumber G →
        (fwdDiff 1)^[k]
          (fun j : ℕ => Real.log ((j.factorial * matchingCount G j : ℕ) : ℝ)) i ≤ 0

section Counting

variable {V : Type*}

/-- Two edges share no vertex. -/
private def EdgeDisjoint (e f : Sym2 V) : Prop := ∀ v, v ∈ e → v ∉ f

private instance [Fintype V] [DecidableEq V] (e f : Sym2 V) : Decidable (EdgeDisjoint e f) := by
  unfold EdgeDisjoint; infer_instance

variable [Fintype V] [DecidableEq V]

/-- The `i`-edge matchings contained in `E`, as a computable finset. -/
private def matchingsIn (E : Finset (Sym2 V)) (i : ℕ) : Finset (Finset (Sym2 V)) :=
  (E.powersetCard i).filter (fun S => ∀ e ∈ S, ∀ f ∈ S, e ≠ f → EdgeDisjoint e f)

/-- The matching counts of an edge set, as a sequence. -/
private def cnt (E : Finset (Sym2 V)) (i : ℕ) : ℕ := (matchingsIn E i).card

/-- The Cauchy product of two sequences. -/
private def conv (f g : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ range (i + 1), f j * g (i - j)

/-- Splitting the matchings of `E` according to whether they contain the edge `e`. -/
private theorem card_matchingsIn_succ (E : Finset (Sym2 V)) (e : Sym2 V) (he : e ∈ E)
    (i : ℕ) :
    cnt E (i + 1) = cnt (E.erase e) (i + 1) + cnt (E.filter (fun f => EdgeDisjoint e f)) i := by
  have hsymm : ∀ {e f : Sym2 V}, EdgeDisjoint e f → EdgeDisjoint f e :=
    fun h v hv hve => h v hve hv
  have hself : ∀ e : Sym2 V, ¬ EdgeDisjoint e e := by
    intro e h
    induction e using Sym2.ind with
    | h a b => exact h a (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a b)
  simp only [cnt]
  have hsplit : matchingsIn E (i + 1) =
      (matchingsIn E (i + 1)).filter (fun S => e ∈ S) ∪
        (matchingsIn E (i + 1)).filter (fun S => e ∉ S) :=
    (filter_union_filter_not_eq (p := fun S => e ∈ S) _).symm
  rw [hsplit, card_union_of_disjoint (disjoint_filter_filter_not _ _ _), add_comm]
  congr 1
  · congr 1
    have hsub : ∀ S : Finset (Sym2 V), S ⊆ E.erase e ↔ S ⊆ E ∧ e ∉ S := by
      intro S
      constructor
      · intro h
        exact ⟨h.trans (erase_subset _ _), fun he' => notMem_erase e E (h he')⟩
      · rintro ⟨h1, h2⟩ x hx
        exact mem_erase.mpr ⟨fun hxe => h2 (hxe ▸ hx), h1 hx⟩
    ext S
    simp only [matchingsIn, mem_filter, mem_powersetCard, hsub]
    tauto
  · refine card_bij (fun S _ => S.erase e) ?_ ?_ ?_
    · intro S hS
      simp only [matchingsIn, mem_filter, mem_powersetCard] at hS ⊢
      obtain ⟨⟨⟨hSE, hc⟩, hm⟩, heS⟩ := hS
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro f hf
        rw [mem_erase] at hf
        exact mem_filter.mpr ⟨hSE hf.2, hm e heS f hf.2 (Ne.symm hf.1)⟩
      · rw [card_erase_of_mem heS, hc]; rfl
      · intro f hf g hg hfg
        exact hm f (mem_of_mem_erase hf) g (mem_of_mem_erase hg) hfg
    · intro S hS T hT hST
      simp only [matchingsIn, mem_filter] at hS hT
      rw [← insert_erase hS.2, ← insert_erase hT.2, hST]
    · intro T hT
      simp only [matchingsIn, mem_filter, mem_powersetCard] at hT
      obtain ⟨⟨hTE, hc⟩, hm⟩ := hT
      have heT : e ∉ T := fun h => hself e (mem_filter.mp (hTE h)).2
      refine ⟨insert e T, ?_, erase_insert heT⟩
      simp only [matchingsIn, mem_filter, mem_powersetCard]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, mem_insert_self e T⟩
      · intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · exact he
        · exact (mem_filter.mp (hTE hf)).1
      · rw [card_insert_of_notMem heT, hc]
      · intro f hf g hg hfg
        rw [mem_insert] at hf hg
        rcases hf with hf | hf <;> rcases hg with hg | hg
        · exact absurd (hf.trans hg.symm) hfg
        · subst hf; exact (mem_filter.mp (hTE hg)).2
        · subst hg; exact hsymm (mem_filter.mp (hTE hf)).2
        · exact hm f hf g hg hfg

/-- The matching sequence of a union of two vertex-disjoint edge sets is the Cauchy product of
the two matching sequences. -/
private theorem card_matchingsIn_union (E₁ E₂ : Finset (Sym2 V))
    (hd : ∀ e ∈ E₁, ∀ f ∈ E₂, EdgeDisjoint e f) :
    cnt (E₁ ∪ E₂) = conv (cnt E₁) (cnt E₂) := by
  have hsymm : ∀ {e f : Sym2 V}, EdgeDisjoint e f → EdgeDisjoint f e :=
    fun h v hv hve => h v hve hv
  have hself : ∀ e : Sym2 V, ¬ EdgeDisjoint e e := by
    intro e h
    induction e using Sym2.ind with
    | h a b => exact h a (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a b)
  funext i
  simp only [cnt, conv]
  have hdisj : ∀ e ∈ E₁, e ∉ E₂ := fun e he he2 => hself e (hd e he e he2)
  have key : ∀ (A B : Finset (Sym2 V)), A ⊆ E₁ → B ⊆ E₂ →
      (A ∪ B).filter (· ∈ E₁) = A ∧ (A ∪ B).filter (· ∉ E₁) = B := by
    intro A B hA hB
    constructor
    · ext e; simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨heA | heB, he1⟩
        · exact heA
        · exact absurd (hB heB) (hdisj e he1)
      · intro heA; exact ⟨Or.inl heA, hA heA⟩
    · ext e; simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨heA | heB, he1⟩
        · exact absurd (hA heA) he1
        · exact heB
      · intro heB; exact ⟨Or.inr heB, fun he1 => hdisj e he1 (hB heB)⟩
  rw [card_eq_sum_card_fiberwise (f := fun S => (S.filter (· ∈ E₁)).card) (t := range (i + 1))]
  · refine sum_congr rfl (fun j hj => ?_)
    rw [mem_range] at hj
    rw [← card_product]
    symm
    refine card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_
    · rintro ⟨A, B⟩ hAB
      simp only [mem_product, matchingsIn, mem_filter, mem_powersetCard] at hAB
      obtain ⟨⟨⟨hA, hAc⟩, hAm⟩, ⟨⟨hB, hBc⟩, hBm⟩⟩ := hAB
      have hAB : Disjoint A B := by
        rw [disjoint_left]; intro e heA heB; exact hdisj e (hA heA) (hB heB)
      simp only [mem_filter, matchingsIn, mem_powersetCard]
      refine ⟨⟨⟨union_subset_union hA hB, ?_⟩, ?_⟩, ?_⟩
      · rw [card_union_of_disjoint hAB, hAc, hBc]; omega
      · intro e he f hf hef
        rcases mem_union.mp he with heA | heB <;> rcases mem_union.mp hf with hfA | hfB
        · exact hAm e heA f hfA hef
        · exact hd e (hA heA) f (hB hfB)
        · exact hsymm (hd f (hA hfA) e (hB heB))
        · exact hBm e heB f hfB hef
      · simp only [(key A B hA hB).1]; exact hAc
    · rintro ⟨A, B⟩ hAB ⟨A', B'⟩ hAB' h
      simp only [mem_product, matchingsIn, mem_filter, mem_powersetCard] at hAB hAB'
      obtain ⟨h1, h2⟩ := key A B hAB.1.1.1 hAB.2.1.1
      obtain ⟨h1', h2'⟩ := key A' B' hAB'.1.1.1 hAB'.2.1.1
      simp only at h
      have hA : A = A' := by rw [← h1, ← h1', h]
      have hB : B = B' := by rw [← h2, ← h2', h]
      rw [hA, hB]
    · intro S hS
      simp only [mem_filter, matchingsIn, mem_powersetCard] at hS
      obtain ⟨⟨⟨hSE, hSc⟩, hSm⟩, hSj⟩ := hS
      refine ⟨(S.filter (· ∈ E₁), S.filter (· ∉ E₁)), ?_, ?_⟩
      · simp only [mem_product, matchingsIn, mem_filter, mem_powersetCard]
        have hcard := card_filter_add_card_filter_not (s := S) (p := fun e => e ∈ E₁)
        refine ⟨⟨⟨fun e he => (mem_filter.mp he).2, hSj⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
        · intro e he f hf hef
          exact hSm e he.1 f hf.1 hef
        · intro e he
          obtain ⟨heS, he1⟩ := mem_filter.mp he
          rcases mem_union.mp (hSE heS) with h | h
          · exact absurd h he1
          · exact h
        · omega
        · intro e he f hf hef
          exact hSm e he.1 f hf.1 hef
      · simp only
        exact filter_union_filter_not_eq (p := fun e => e ∈ E₁) S
  · intro S hS
    simp only [mem_coe, matchingsIn, mem_filter, mem_powersetCard] at hS
    simp only [coe_range, Set.mem_Iio]
    have := card_filter_le S (· ∈ E₁)
    omega
/-- A matching with `i` edges covers `2i` vertices. -/
private theorem matchingsIn_eq_empty (E : Finset (Sym2 V)) (s : Finset V)
    (hs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (i : ℕ)
    (h : s.card < 2 * i) : matchingsIn E i = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro S hS
  simp only [matchingsIn, mem_filter, mem_powersetCard] at hS
  obtain ⟨⟨hSE, hSc⟩, hSm⟩ := hS
  have hpair : ∀ e ∈ S, (s.filter (· ∈ e)).card = 2 := by
    intro e he
    have hE := hSE he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h' => hdiag _ hE (by simp [h'])
      have : s.filter (· ∈ s(a, b)) = {a, b} := by
        ext v; simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hs _ hE _ (Sym2.mem_mk_left _ _), Or.inl rfl⟩
          · exact ⟨hs _ hE _ (Sym2.mem_mk_right _ _), Or.inr rfl⟩
      rw [this, card_pair hab]
  have hsub : S.biUnion (fun e => s.filter (· ∈ e)) ⊆ s := by
    intro v hv
    obtain ⟨e, -, hv⟩ := mem_biUnion.mp hv
    exact (mem_filter.mp hv).1
  have hcard : (S.biUnion (fun e => s.filter (· ∈ e))).card = 2 * i := by
    rw [card_biUnion]
    · rw [sum_congr rfl hpair, sum_const, smul_eq_mul, hSc, mul_comm]
    · intro e he f hf hef
      rw [Function.onFun, disjoint_left]
      intro v hv hv'
      exact hSm e he f hf hef v (mem_filter.mp hv).2 (mem_filter.mp hv').2
  have := card_le_card hsub
  omega

/-- Relabelling the vertices injectively preserves the number of matchings. -/
private theorem card_matchingsIn_image {W : Type*} [Fintype W] [DecidableEq W] (g : V → W)
    (hg : Function.Injective g) (E : Finset (Sym2 V)) :
    cnt (E.image (Sym2.map g)) = cnt E := by
  funext i
  simp only [cnt]
  have hφ : Function.Injective (Sym2.map g) := Sym2.map.injective hg
  have hdis : ∀ e f : Sym2 V,
      EdgeDisjoint (Sym2.map g e) (Sym2.map g f) ↔ EdgeDisjoint e f := by
    intro e f
    constructor
    · intro h v hve hvf
      exact h (g v) (Sym2.mem_map.mpr ⟨v, hve, rfl⟩) (Sym2.mem_map.mpr ⟨v, hvf, rfl⟩)
    · intro h w hwe hwf
      obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hwe
      obtain ⟨u', hu', hgu⟩ := Sym2.mem_map.mp hwf
      exact h u hu (hg hgu ▸ hu')
  symm
  refine card_bij (fun S _ => S.image (Sym2.map g)) ?_ ?_ ?_
  · intro S hS
    simp only [matchingsIn, mem_filter, mem_powersetCard] at hS ⊢
    obtain ⟨⟨hSE, hc⟩, hm⟩ := hS
    refine ⟨⟨image_subset_image hSE, by rw [card_image_of_injective _ hφ, hc]⟩, ?_⟩
    intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
    exact (hdis e' f').mpr (hm e' he' f' hf' (fun h => hef (h ▸ rfl)))
  · intro S _ T _ h
    exact image_injective hφ h
  · intro T hT
    simp only [matchingsIn, mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨hTE, hc⟩, hm⟩ := hT
    refine ⟨E.filter (fun e => Sym2.map g e ∈ T), ?_, ?_⟩
    · have himg : (E.filter (fun e => Sym2.map g e ∈ T)).image (Sym2.map g) = T := by
        ext f
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨e, ⟨-, he⟩, rfl⟩; exact he
        · intro hf
          obtain ⟨e, he, rfl⟩ := mem_image.mp (hTE hf)
          exact ⟨e, ⟨he, hf⟩, rfl⟩
      simp only [matchingsIn, mem_filter, mem_powersetCard]
      refine ⟨⟨filter_subset _ _, ?_⟩, ?_⟩
      · rw [← card_image_of_injective _ hφ, himg, hc]
      · intro e he f hf hef
        exact (hdis e f).mp (hm _ he.2 _ hf.2 (fun h => hef (hφ h)))
    · ext f
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨e, ⟨-, he⟩, rfl⟩; exact he
      · intro hf
        obtain ⟨e, he, rfl⟩ := mem_image.mp (hTE hf)
        exact ⟨e, ⟨he, hf⟩, rfl⟩

end Counting

/-- The `i`-matchings of `K_n` inside `E(G)` are the `i`-matchings of `G`. -/
private theorem matchingCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : ℕ) : matchingCount G i = cnt G.edgeFinset i := by
  have hdis : ∀ e f : Sym2 (Fin n), Disjoint e.toFinset f.toFinset ↔ EdgeDisjoint e f := by
    intro e f
    simp only [Finset.disjoint_left, Sym2.mem_toFinset, EdgeDisjoint]
  have hiff : ∀ M : Finset (Sym2 (Fin n)), M ∈ matchingsIn G.edgeFinset i ↔
      (M.card = i ∧ (∀ e ∈ M, ¬ e.IsDiag) ∧
        (M : Set (Sym2 (Fin n))).Pairwise (fun e f => Disjoint e.toFinset f.toFinset)) ∧
      ∀ e ∈ M, e ∈ G.edgeSet := by
    intro M
    simp only [matchingsIn, mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, hc⟩, hp⟩
      refine ⟨⟨hc, fun e he => G.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp (hsub he)), fun e he f hf hef => (hdis e f).mpr
        (hp e (mem_coe.mp he) f (mem_coe.mp hf) hef)⟩,
        fun e he => SimpleGraph.mem_edgeFinset.mp (hsub he)⟩
    · rintro ⟨⟨hc, -, hp⟩, hE⟩
      exact ⟨⟨fun e he => SimpleGraph.mem_edgeFinset.mpr (hE e he), hc⟩,
        fun e he f hf hef => (hdis e f).mp (hp (mem_coe.mpr he) (mem_coe.mpr hf) hef)⟩
  rw [matchingCount, cnt, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun M => ⟨M.1.1, (hiff M.1.1).mpr ⟨M.1.2, M.2⟩⟩
      invFun := fun S => ⟨⟨S.1, ((hiff S.1).mp S.2).1⟩, ((hiff S.1).mp S.2).2⟩
      left_inv := fun M => rfl
      right_inv := fun S => rfl }

section Ring

/-- Vertex `t` of block `b`. -/
private def vtx (b : Fin 4) (t : Fin 7) : Fin 28 := ⟨7 * b.val + t.val, by omega⟩

/-- `K_7` minus the edge `{0, 1}`, with the vertices whose positions lie in `U` removed. -/
private def baseBlock (U : Finset ℕ) : Finset (Sym2 (Fin 7)) :=
  ((univ ×ˢ univ).filter (fun p : Fin 7 × Fin 7 =>
      p.1 < p.2 ∧ ¬ (p.1.val = 0 ∧ p.2.val = 1) ∧ p.1.val ∉ U ∧ p.2.val ∉ U)).image
    (fun p => s(p.1, p.2))

/-- The edges of block `b`, with the positions in `U` removed. -/
private def blockEdges (b : Fin 4) (U : Finset ℕ) : Finset (Sym2 (Fin 28)) :=
  (baseBlock U).image (Sym2.map (vtx b))

/-- The connector from position `1` of block `b` to position `0` of block `b + 1`. -/
private def conn (b : Fin 4) : Sym2 (Fin 28) := s(vtx b 1, vtx (b + 1) 0)

/-- Positions of block `b` covered by the connectors in `T`. -/
private def removed (T : Finset (Fin 4)) (b : Fin 4) : Finset ℕ :=
  (if b ∈ T then {1} else ∅) ∪ (if b - 1 ∈ T then {0} else ∅)

/-- The four blocks after deleting the vertices covered by the connectors in `T`. -/
private def leaf (T : Finset (Fin 4)) : Finset (Sym2 (Fin 28)) :=
  blockEdges 0 (removed T 0) ∪ blockEdges 1 (removed T 1) ∪ blockEdges 2 (removed T 2) ∪
    blockEdges 3 (removed T 3)

/-- The connectors whose index is at least `b`. -/
private def rest (b : ℕ) : Finset (Fin 4) := univ.filter (fun c => b ≤ c.val)

/-- The blocks after using the connectors in `T`, together with the connectors not yet
decided. -/
private def stage (T : Finset (Fin 4)) (b : ℕ) : Finset (Sym2 (Fin 28)) :=
  leaf T ∪ (rest b).image conn

/-- Vertex `x` is position `x % 7` of block `x / 7`. Two vertices are adjacent when they lie in
the same block and are not positions `0` and `1`, or when one is position `1` of a block and
the other is position `0` of the next block. -/
private def radj (x y : Fin 28) : Prop :=
  x ≠ y ∧ ((x.val / 7 = y.val / 7 ∧ x.val % 7 + y.val % 7 ≠ 1) ∨
    (x.val % 7 = 1 ∧ y.val % 7 = 0 ∧ y.val / 7 = (x.val / 7 + 1) % 4) ∨
    (y.val % 7 = 1 ∧ x.val % 7 = 0 ∧ x.val / 7 = (y.val / 7 + 1) % 4))

private instance : DecidableRel radj := fun x y => by unfold radj; infer_instance

/-- The 28-vertex graph: four copies of `K_7` minus an edge `{x_b, y_b}`, joined in a ring by
the edges `{y_b, x_{b+1}}`. -/
private def ringGraph : SimpleGraph (Fin 28) where
  Adj := radj
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private instance : DecidableRel ringGraph.Adj := fun x y => inferInstanceAs (Decidable (radj x y))

/-- A Hamiltonian cycle of `ringGraph`. -/
private def cyc : List (Fin 28) :=
  [0, 2, 3, 4, 5, 6, 1, 7, 9, 10, 11, 12, 13, 8, 14, 16, 17, 18, 19, 20, 15, 21, 23, 24, 25, 26,
    27, 22]

/-- The matching counts of `K_7 - e`, `K_6` and `K_5`. -/
private def blockVal (U : Finset ℕ) (x : ℕ) : ℕ :=
  if 0 ∈ U ∧ 1 ∈ U then [1, 10, 15].getD x 0
  else if 0 ∈ U ∨ 1 ∈ U then [1, 15, 45, 15].getD x 0 else [1, 20, 95, 90].getD x 0

/-- The matching sequence of `leaf T`. -/
private def leafCount (T : Finset (Fin 4)) : ℕ → ℕ :=
  conv (conv (conv (blockVal (removed T 0)) (blockVal (removed T 1))) (blockVal (removed T 2)))
    (blockVal (removed T 3))

private def fin4 (b : ℕ) : Fin 4 := ⟨b % 4, Nat.mod_lt _ (by norm_num)⟩

/-- `casc n T b j`: the `j`-matchings of `stage T b`, computed by deciding the connectors
`b, …, b + n - 1` one at a time. -/
private def casc : ℕ → Finset (Fin 4) → ℕ → ℕ → ℕ
  | 0, T, _, j => leafCount T j
  | n + 1, T, b, j =>
    casc n T (b + 1) j + (match j with
      | 0 => 0
      | j + 1 => casc n (insert (fin4 b) T) (b + 1) j)

set_option maxRecDepth 100000 in
/-- The matching counts of the blocks, by enumeration. -/
private theorem base_counts (U : Finset ℕ)
    (hU : U ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ))) :
    cnt (baseBlock U) = blockVal U := by
  have hlow : ∀ U ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)),
      ∀ x < 4, (matchingsIn (baseBlock U) x).card = blockVal U x := by
    intro U hU x hx
    simp only [mem_insert, mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl <;> interval_cases x <;> decide +kernel
  funext x
  rcases Nat.lt_or_ge x 4 with hx | hx
  · exact hlow U hU x hx
  · change (matchingsIn (baseBlock U) x).card = blockVal U x
    rw [matchingsIn_eq_empty (baseBlock U) univ (by simp) ?_ x (by simp; omega)]
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + 4 := ⟨x - 4, by omega⟩
      simp only [mem_insert, mem_singleton] at hU
      rcases hU with rfl | rfl | rfl | rfl <;> simp [blockVal]
    · intro e he
      simp only [baseBlock, mem_image, mem_filter] at he
      obtain ⟨p, ⟨-, hp, -⟩, rfl⟩ := he
      simpa using hp.ne

set_option maxRecDepth 100000 in
/-- Deciding connector `b`: removing it, or using it and deleting its two end vertices. -/
private theorem stage_step : ∀ b < 4, ∀ T : Finset (Fin 4), (∀ c ∈ T, c.val < b) →
    conn (fin4 b) ∈ stage T b ∧ (stage T b).erase (conn (fin4 b)) = stage T (b + 1) ∧
      (stage T b).filter (fun f => EdgeDisjoint (conn (fin4 b)) f) =
        stage (insert (fin4 b) T) (b + 1) := by
  have h1 : ∀ b < 4, ∀ T : Finset (Fin 4), (∀ c ∈ T, c.val < b) →
      conn (fin4 b) ∈ stage T b := by decide +kernel
  have h2 : ∀ b < 4, ∀ T : Finset (Fin 4), (∀ c ∈ T, c.val < b) →
      (stage T b).erase (conn (fin4 b)) = stage T (b + 1) := by decide +kernel
  have h3 : ∀ b < 4, ∀ T : Finset (Fin 4), (∀ c ∈ T, c.val < b) →
      (stage T b).filter (fun f => EdgeDisjoint (conn (fin4 b)) f) =
        stage (insert (fin4 b) T) (b + 1) := by decide +kernel
  exact fun b hb T hT => ⟨h1 b hb T hT, h2 b hb T hT, h3 b hb T hT⟩

/-- The cascade computes the matching sequence of `stage T b`. -/
private theorem casc_spec : ∀ n (T : Finset (Fin 4)) (b : ℕ), b + n = 4 →
    (∀ c ∈ T, c.val < b) → cnt (stage T b) = casc n T b := by
  have vtx_inj : ∀ c : Fin 4, Function.Injective (vtx c) := by
    intro c t t' h
    simp only [vtx, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hidx : ∀ (c : Fin 4) (U : Finset ℕ), ∀ e ∈ blockEdges c U, ∀ v ∈ e,
      v.val / 7 = c.val := by
    intro c U e he v hv
    obtain ⟨e', -, rfl⟩ := mem_image.mp he
    obtain ⟨t, -, rfl⟩ := Sym2.mem_map.mp hv
    have := t.isLt
    simp only [vtx]
    omega
  have hdisj : ∀ (c c' : Fin 4) (U U' : Finset ℕ), c ≠ c' →
      ∀ e ∈ blockEdges c U, ∀ f ∈ blockEdges c' U', EdgeDisjoint e f :=
    fun c c' U U' hcc e he f hf v hve hvf =>
      hcc (Fin.ext ((hidx c U e he v hve).symm.trans (hidx c' U' f hf v hvf)))
  have hcases : ∀ (T : Finset (Fin 4)) (c : Fin 4),
      removed T c ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset ℕ)) := by
    intro T c
    unfold removed
    split_ifs <;> decide
  have hblock : ∀ (T : Finset (Fin 4)) (c : Fin 4),
      cnt (blockEdges c (removed T c)) = blockVal (removed T c) :=
    fun T c => (card_matchingsIn_image (vtx c) (vtx_inj c) _).trans (base_counts _ (hcases T c))
  have hleaf : ∀ T, cnt (leaf T) = leafCount T := by
    intro T
    have h01 : ∀ e ∈ blockEdges 0 (removed T 0), ∀ f ∈ blockEdges 1 (removed T 1),
        EdgeDisjoint e f := hdisj 0 1 _ _ (by decide)
    have h012 : ∀ e ∈ blockEdges 0 (removed T 0) ∪ blockEdges 1 (removed T 1),
        ∀ f ∈ blockEdges 2 (removed T 2), EdgeDisjoint e f := by
      intro e he
      rcases mem_union.mp he with he | he
      exacts [hdisj 0 2 _ _ (by decide) e he, hdisj 1 2 _ _ (by decide) e he]
    have h0123 : ∀ e ∈ blockEdges 0 (removed T 0) ∪ blockEdges 1 (removed T 1) ∪
        blockEdges 2 (removed T 2), ∀ f ∈ blockEdges 3 (removed T 3), EdgeDisjoint e f := by
      intro e he
      rcases mem_union.mp he with he | he
      · rcases mem_union.mp he with he | he
        exacts [hdisj 0 3 _ _ (by decide) e he, hdisj 1 3 _ _ (by decide) e he]
      · exact hdisj 2 3 _ _ (by decide) e he
    unfold leaf leafCount
    rw [card_matchingsIn_union _ _ h0123, card_matchingsIn_union _ _ h012,
      card_matchingsIn_union _ _ h01, hblock, hblock, hblock, hblock]
  have h0 : ∀ E : Finset (Sym2 (Fin 28)), cnt E 0 = 1 := by
    intro E
    simp [cnt, matchingsIn, filter_singleton]
  intro n
  induction n with
  | zero =>
    intro T b hb _
    obtain rfl : b = 4 := by omega
    have hrest : rest 4 = ∅ := by decide
    rw [stage, hrest, image_empty, union_empty, hleaf]
    funext j
    rfl
  | succ n ih =>
    intro T b hb hT
    obtain ⟨hmem, herase, hfilt⟩ := stage_step b (by omega) T hT
    have hT' : ∀ c ∈ insert (fin4 b) T, c.val < b + 1 := by
      intro c hc
      rcases mem_insert.mp hc with rfl | hc
      · change b % 4 < b + 1
        omega
      · have := hT c hc
        omega
    have ih1 := ih T (b + 1) (by omega) (fun c hc => by have := hT c hc; omega)
    have ih2 := ih (insert (fin4 b) T) (b + 1) (by omega) hT'
    funext j
    cases j with
    | zero =>
      change cnt (stage T b) 0 = casc n T (b + 1) 0 + 0
      rw [show casc n T (b + 1) 0 + 0 = casc n T (b + 1) 0 from rfl, ← ih1, h0, h0]
    | succ j =>
      change cnt (stage T b) (j + 1) =
        casc n T (b + 1) (j + 1) + casc n (insert (fin4 b) T) (b + 1) j
      rw [card_matchingsIn_succ _ _ hmem, herase, hfilt, ih1, ih2]

/-- `ringGraph` is biconnected: `cyc` is a Hamiltonian cycle, and deleting a vertex from it
leaves a Hamiltonian path of the remaining vertices. -/
private theorem ringGraph_biconnected : Biconnected ringGraph := by
  have hconn : ∀ {W : Type} (H : SimpleGraph W) (l : List W) (hne : l ≠ []),
      l.IsChain H.Adj → (∀ x, x ∈ l) → H.Connected := by
    intro W H l hne hc hall
    classical
    refine (SimpleGraph.connected_iff_exists_forall_reachable H).mpr ⟨l.head hne, fun x => ?_⟩
    refine ⟨(SimpleGraph.Walk.ofSupport l hne hc).takeUntil x ?_⟩
    rw [SimpleGraph.Walk.support_ofSupport]
    exact hall x
  have hpath : ∀ v : Fin 28, (cyc.rotate (cyc.idxOf v + 1)).dropLast ≠ [] ∧
      ((cyc.rotate (cyc.idxOf v + 1)).dropLast).IsChain ringGraph.Adj ∧
      v ∉ (cyc.rotate (cyc.idxOf v + 1)).dropLast ∧
      ∀ w, w ≠ v → w ∈ (cyc.rotate (cyc.idxOf v + 1)).dropLast := by
    decide +kernel
  refine ⟨hconn ringGraph cyc (by decide) (by decide +kernel) (by decide +kernel), fun v => ?_⟩
  obtain ⟨hne, hc, hv, hw⟩ := hpath v
  have hs : ∀ a ∈ (cyc.rotate (cyc.idxOf v + 1)).dropLast, a ∈ ({v}ᶜ : Set (Fin 28)) :=
    fun a ha hav => hv (Set.mem_singleton_iff.mp hav ▸ ha)
  refine hconn _ (((cyc.rotate (cyc.idxOf v + 1)).dropLast).pmap Subtype.mk hs)
    (by rw [Ne, List.pmap_eq_nil_iff]; exact hne)
    (List.isChain_pmap_of_isChain (S := (ringGraph.induce {v}ᶜ).Adj) (f := Subtype.mk)
      (fun a b _ _ h => h) hc hs) ?_
  intro x
  exact List.mem_pmap.mpr ⟨x.1, hw x.1 x.2, rfl⟩

end Ring

/-- The answer to the question is negative: `ringGraph` is 6-regular and biconnected, has
`ν = 14`, and the fourth difference of `ln(i! N(i))` at `i = 10` is positive. -/
theorem result : ¬ claim := by
  intro h
  have hE : ringGraph.edgeFinset = stage ∅ 0 := by decide +kernel
  have hN : ∀ i, matchingCount ringGraph i = casc 4 ∅ 0 i := by
    intro i
    rw [matchingCount_eq, hE]
    exact congrFun (casc_spec 4 ∅ 0 rfl (by simp)) i
  have hvals : casc 4 ∅ 0 10 = 845745750 ∧ casc 4 ∅ 0 11 = 506745000 ∧
      casc 4 ∅ 0 12 = 141530625 ∧ casc 4 ∅ 0 13 = 9922500 ∧ casc 4 ∅ 0 14 = 101250 := by
    decide +kernel
  have hnu : matchingNumber ringGraph = 14 := by
    unfold matchingNumber
    refine IsGreatest.csSup_eq ⟨by simp [hN, hvals.2.2.2.2], fun i hi => ?_⟩
    by_contra hlt
    have h0 : matchingsIn ringGraph.edgeFinset i = ∅ :=
      matchingsIn_eq_empty _ univ (by simp)
        (fun e he => ringGraph.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)) i
        (by simp; omega)
    simp [matchingCount_eq, cnt, h0] at hi
  have hreg : ringGraph.IsRegularOfDegree 6 := by
    intro v
    revert v
    decide +kernel
  have hfac : Nat.factorial 10 = 3628800 ∧ Nat.factorial 11 = 39916800 ∧
      Nat.factorial 12 = 479001600 ∧ Nat.factorial 13 = 6227020800 ∧
      Nat.factorial 14 = 87178291200 := by decide
  have hD := h 28 ringGraph ⟨6, hreg⟩ ringGraph_biconnected 4 10 (by norm_num) le_rfl
    (by rw [hnu])
  rw [fwdDiff_iter_eq_sum_shift] at hD
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hN] at hD
  norm_num [Nat.choose, hfac, hvals] at hD
  have key := Real.log_lt_log
    (show (0 : ℝ) < 20227638816000000 ^ 4 * 61787613888000000 ^ 4 by positivity)
    (show (20227638816000000 : ℝ) ^ 4 * 61787613888000000 ^ 4 <
      3069042177600000 * 67793395824000000 ^ 6 * 8826801984000000 by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at key
  push_cast at key
  linarith

end D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
