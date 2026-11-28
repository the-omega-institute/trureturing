import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
import OmegaMath.Combinatorics.Graph.RootedAncestorReconstruction
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Group

compile_only_with_mathlib

/-! Omega original.

Root-path birth indices and oldest-anchor estimates for group gains on clique trees.
-/

open scoped BigOperators
namespace SimpleGraph.CliqueTreeGroupSeparator

universe u v w
variable {V : Type u} {I : Type v} {H : Type w}

variable {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

noncomputable def route (hT : T.IsTree) (r a : I) : T.Walk r a :=
  (hT.existsUnique_path r a).exists.choose

theorem route_path (hT : T.IsTree) (r a : I) : (route hT r a).IsPath :=
  (hT.existsUnique_path r a).exists.choose_spec

/-- Adjacent bags extend one another’s root paths by one edge. -/
theorem route_adj (hT : T.IsTree) (r : I) {a b : I} (h : T.Adj a b) :
    route hT r b = (route hT r a).concat h ∨
      route hT r a = (route hT r b).concat h.symm := by
  classical
  by_cases ha : a ∈ (route hT r b).support
  · exact Or.inl (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h ha)
  · exact Or.inr (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h.symm
      (hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (route_path ..) (route_path ..) h ha))

open Classical in
/-- First occurrence on one root path, with an out-of-path default for absent vertices. -/
noncomputable def birthIndex (R : RootedAncestors I) (K : I → Set V) (a : I) (x : V) : ℕ :=
  if h : ∃ i, i ≤ R.depth a ∧ x ∈ K (R.atDepth a i) then Nat.find h else R.depth a + 1

variable (R : RootedAncestors I)

theorem birth_spec (a : I) (x : V) (hx : x ∈ K a) :
    birthIndex R K a x ≤ R.depth a ∧ x ∈ K (R.atDepth a (birthIndex R K a x)) := by
  classical
  have h : ∃ i, i ≤ R.depth a ∧ x ∈ K (R.atDepth a i) :=
    ⟨R.depth a, le_rfl, by simpa only [R.atDepth_self] using hx⟩
  simp only [birthIndex, dite_eq_left h]
  exact Nat.find_spec h

theorem birth_le {a : I} {x : V} {i : ℕ} (hi : i ≤ R.depth a)
    (hx : x ∈ K (R.atDepth a i)) : birthIndex R K a x ≤ i := by
  classical
  have h : ∃ i, i ≤ R.depth a ∧ x ∈ K (R.atDepth a i) := ⟨i, hi, hx⟩
  simp only [birthIndex, dite_eq_left h]
  exact Nat.find_min' h ⟨hi, hx⟩

/-- A common vertex has exactly the same first occurrence in a path and any containing prefix.
This is the oldest-anchor simplification: no common-ancestor construction is needed. -/
theorem birth_prefix {a : I} {j : ℕ} (hj : j ≤ R.depth a) {x : V}
    (hx : x ∈ K (R.atDepth a j)) :
    birthIndex R K (R.atDepth a j) x = birthIndex R K a x := by
  apply Nat.le_antisymm
  · have hb := birth_le R hj hx
    have hm : x ∈ K (R.atDepth a (birthIndex R K a x)) := by
      classical
      have h : ∃ i, i ≤ R.depth a ∧ x ∈ K (R.atDepth a i) := ⟨j, hj, hx⟩
      simpa only [birthIndex, dite_eq_left h] using (Nat.find_spec h).2
    apply birth_le R (by rw [R.depth_atDepth a j hj]; exact hb)
    simpa only [R.atDepth_atDepth a _ j hb hj] using hm
  · have hb := birth_spec R (R.atDepth a j) x hx
    have hi : birthIndex R K (R.atDepth a j) x ≤ j := by
      simpa only [R.depth_atDepth a j hj] using hb.1
    apply birth_le R (hi.trans hj)
    simpa only [R.atDepth_atDepth a _ j hi hj] using hb.2

/-- Running intersection fills the whole interval after a vertex's first occurrence. -/
theorem birth_interval (hK : IsCliqueTree T G K) (r a : I) (x : V) (hx : x ∈ K a)
    {j : ℕ} (_hj : j ≤ (route hK.isTree r a).length)
    (hborn : birthIndex (RootedAncestors.ofTree hK.isTree r) K a x ≤ j) :
    x ∈ K ((route hK.isTree r a).getVert j) := by
  let p := route hK.isTree r a
  let R := RootedAncestors.ofTree hK.isTree r
  have hb := birth_spec R a x hx
  let i := birthIndex R K a x
  have hi : i ≤ p.length := hb.1
  have hix : x ∈ K (p.getVert i) := hb.2
  change i ≤ j at hborn
  have hs : ((p.drop i).getVert (j - i)) = p.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  apply hK.running (p.drop i) ((route_path hK.isTree r a).drop i) x hix hx
  rw [← hs]
  exact Walk.getVert_mem_support _ _

end SimpleGraph.CliqueTreeGroupSeparator

open scoped BigOperators
namespace SimpleGraph.CliqueTreeGroupSeparator
open Classical

universe u w
variable {V : Type u} {H : Type w} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

omit [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] in
/-- Triangle bounds include repeated vertices after normalizing diagonal gains. -/
theorem clique_triangle {G : SimpleGraph V} (g : V → V → H) {δ : ℝ}
    (hδ : 0 ≤ δ) (hzero : ∀ x, g x x = 1)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ δ)
    {C : Set V} (hC : G.IsClique C) {a b c : V}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) :
    Dist.dist (g a b * g b c) (g a c) ≤ δ := by
  by_cases hab : a = b
  · subst b; simpa [hzero] using hδ
  by_cases hbc : b = c
  · subst c; simpa [hzero] using hδ
  by_cases hac : a = c
  · subst c; simpa [hzero, hrev a b (hC ha hb hab)] using hδ
  exact htri a b c (hC ha hb hab) (hC hb hc hbc) (hC ha hc hac)

/-- Auxiliary gauges are transported separately from the frozen vertex potential. -/
def gauge (g : V → V → H) (a : ℕ → V) : ℕ → H
  | 0 => 1
  | n + 1 => gauge g a n * g (a n) (a (n + 1))

def localValue (g : V → V → H) (a : ℕ → V) (n : ℕ) (x : V) : H :=
  gauge g a n * g (a n) x

omit [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] in
/-- Both exact transitions in §1.3: an unchanged anchor, and an anchor equal to x. -/
theorem local_step_exact (g : V → V → H) (hzero : ∀ x, g x x = 1)
    (a : ℕ → V) (n : ℕ) (x : V) (he : a (n + 1) = a n ∨ a (n + 1) = x) :
    localValue g a (n + 1) x = localValue g a n x := by
  rcases he with he | he <;> simp [localValue, gauge, he, hzero]

omit [IsIsometricSMul Hᵐᵒᵖ H] in
theorem local_step_dist (g : V → V → H) (a : ℕ → V) (n : ℕ) (x : V) :
    Dist.dist (localValue g a n x) (localValue g a (n + 1) x) =
      Dist.dist (g (a n) (a (n + 1)) * g (a (n + 1)) x) (g (a n) x) := by
  simp only [localValue, gauge, mul_assoc, dist_mul_left]
  exact _root_.dist_comm _ _

open Classical in
noncomputable def charged (a : ℕ → V) (x : V) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => a (i + 1) ≠ a i ∧ a (i + 1) ≠ x)

/-- Every inexact transition has a distinct new anchor. The first separator
therefore controls the count independently of the path length. -/
theorem charged_card_le {A : Type*} [LinearOrder A] (a : ℕ → V) (age : V → A)
    (N : ℕ) (x : V) (S : Finset V)
    (hmono : ∀ i j, i ≤ j → j ≤ N → age (a i) ≤ age (a j))
    (hstrict : ∀ i < N, a (i + 1) ≠ a i → age (a i) < age (a (i + 1)))
    (hfirst : ∀ i < N, a (i + 1) ≠ x → a (i + 1) ∈ S) :
    (charged a x N).card ≤ (S.erase x).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun i => a (i + 1))
  · intro i hi
    obtain ⟨hi, hchange, hne⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_erase.mpr ⟨hne, hfirst i (Finset.mem_range.mp hi) hne⟩
  · intro i hi j hj he
    obtain ⟨hi, hchange, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj, hjchange, _⟩ := Finset.mem_filter.mp hj
    change a (i + 1) = a (j + 1) at he
    have hiN := Finset.mem_range.mp hi
    have hjN := Finset.mem_range.mp hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hle := hmono (i + 1) j (by omega) (by omega)
      have hlt := hstrict j hjN hjchange
      rw [he] at hle
      exact (not_lt_of_ge hle) hlt
    · have hle := hmono (j + 1) i (by omega) (by omega)
      have hlt := hstrict i hiN hchange
      rw [he] at hlt
      exact (not_lt_of_ge hle) hlt

/-- Telescoping charges only the two nonexact cases; the final move to x costs zero. -/
theorem local_transport_bound (g : V → V → H) (hzero : ∀ x, g x x = 1)
    (a : ℕ → V) (x : V) (N : ℕ) {δ : ℝ}
    (hstep : ∀ i < N,
      Dist.dist (g (a i) (a (i + 1)) * g (a (i + 1)) x) (g (a i) x) ≤ δ) :
    Dist.dist (localValue g a 0 x) (localValue g a N x) ≤
      ((charged a x N).card : ℝ) * δ := by
  classical
  have step (i : ℕ) (hi : i < N) :
      Dist.dist (localValue g a i x) (localValue g a (i + 1) x) ≤
        if a (i + 1) ≠ a i ∧ a (i + 1) ≠ x then δ else 0 := by
    split_ifs with h
    · rw [local_step_dist]; exact hstep i hi
    · have he : a (i + 1) = a i ∨ a (i + 1) = x := by tauto
      rw [local_step_exact g hzero a i x he, _root_.dist_self]
  have telescope (n : ℕ) (hn : n ≤ N) :
      Dist.dist (localValue g a 0 x) (localValue g a n x) ≤
        ∑ i ∈ Finset.range n, if a (i + 1) ≠ a i ∧ a (i + 1) ≠ x then δ else 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      exact (_root_.dist_triangle _ (localValue g a n x) _).trans (by
        rw [Finset.sum_range_succ]
        exact add_le_add (ih (by omega)) (step n (by omega)))
  simpa [charged, Finset.sum_ite] using telescope N le_rfl

/-- The group-theoretic first-separator estimate for one birth-to-birth trace.
The order and first-separator hypotheses are purely combinatorial. -/
theorem separator_trace_bound {G : SimpleGraph V}
    (g : V → V → H) {δ : ℝ} (hδ : 0 ≤ δ) (hzero : ∀ x, g x x = 1)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ δ)
    (B : ℕ → Set V) {A : Type*} [LinearOrder A] (a : ℕ → V) (age : V → A)
    (N : ℕ) (u v : V) (S : Finset V) (s : ℕ)
    (hclique : ∀ i ≤ N, G.IsClique (B i))
    (hanchor : ∀ i ≤ N, a i ∈ B i)
    (hnext : ∀ i < N, a (i + 1) ∈ B i)
    (hu : ∀ i ≤ N, u ∈ B i) (hv : v ∈ B N)
    (hmono : ∀ i j, i ≤ j → j ≤ N → age (a i) ≤ age (a j))
    (hstrict : ∀ i < N, a (i + 1) ≠ a i → age (a i) < age (a (i + 1)))
    (hfirst : ∀ i < N, a (i + 1) ≠ u → a (i + 1) ∈ S)
    (huS : u ∈ S) (hcard : S.card ≤ s) :
    Dist.dist (localValue g a 0 u * g u v) (localValue g a N v) ≤ (s : ℝ) * δ := by
  have htransport := local_transport_bound g hzero a u N (fun i hi =>
    clique_triangle g hδ hzero hrev htri (hclique i (by omega))
      (hanchor i (by omega)) (hnext i hi) (hu i (by omega)))
  have hcount := charged_card_le a age N u S hmono hstrict hfirst
  have hlast : Dist.dist (localValue g a N u * g u v) (localValue g a N v) ≤ δ := by
    simpa only [localValue, mul_assoc, dist_mul_left] using
      clique_triangle g hδ hzero hrev htri (hclique N le_rfl)
        (hanchor N le_rfl) (hu N le_rfl) hv
  have hsize : (charged a u N).card + 1 ≤ s := by
    have := Finset.card_erase_add_one huS
    omega
  calc
    _ ≤ Dist.dist (localValue g a 0 u * g u v) (localValue g a N u * g u v) +
        Dist.dist (localValue g a N u * g u v) (localValue g a N v) := _root_.dist_triangle _ _ _
    _ ≤ ((charged a u N).card : ℝ) * δ + δ := by
      rw [dist_mul_right]; exact add_le_add htransport hlast
    _ = (((charged a u N).card + 1 : ℕ) : ℝ) * δ := by push_cast; ring
    _ ≤ (s : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) hδ

end SimpleGraph.CliqueTreeGroupSeparator

namespace SimpleGraph.CliqueTreeGroupSeparator
open Classical
universe u v
variable {V : Type u} {I : Type v} {T : SimpleGraph I} {G : SimpleGraph V}
  {K : I → Set V}

/-- Running intersection, stated entirely on a single coherent root path. -/
theorem birth_mem_prefix (hK : IsCliqueTree T G K) (r b : I)
    {x : V} {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ (RootedAncestors.ofTree hK.isTree r).depth b)
    (hx : x ∈ K ((RootedAncestors.ofTree hK.isTree r).atDepth b k))
    (hb : birthIndex (RootedAncestors.ofTree hK.isTree r) K b x ≤ j) :
    x ∈ K ((RootedAncestors.ofTree hK.isTree r).atDepth b j) := by
  let R := RootedAncestors.ofTree hK.isTree r
  let c := R.atDepth b k
  have hbc := birth_prefix R hk hx
  have hjc : j ≤ R.depth c := by dsimp [c]; rw [R.depth_atDepth b k hk]; exact hjk
  have hborn : birthIndex R K c x ≤ j := by rw [hbc]; exact hb
  have hm := birth_interval hK r c x hx hjc hborn
  change x ∈ K (R.atDepth c j) at hm
  simpa only [c, R.atDepth_atDepth b j k hjk hk] using hm

variable [Finite V] [LinearOrder V]

/-- Birth depth with a fixed tie order on vertices. -/
noncomputable def ageKey (R : RootedAncestors I) (K : I → Set V) (b : I) (x : V) :
    ℕ ×ₗ V := toLex (birthIndex R K b x, x)

omit [Finite V] [LinearOrder V] in
theorem ageKey_injective (R : RootedAncestors I) (b : I) :
    Function.Injective (ageKey R K b) := by
  intro x y h
  exact congrArg (fun z : ℕ ×ₗ V => (ofLex z).2) h

omit [Finite V] in
theorem ageKey_birth_le (R : RootedAncestors I) {b : I} {x y : V}
    (h : ageKey R K b x ≤ ageKey R K b y) :
    birthIndex R K b x ≤ birthIndex R K b y :=
  Prod.Lex.monotone_fst _ _ h

omit [Finite V] [LinearOrder V] in
theorem ageKey_prefix (R : RootedAncestors I) {b : I} {j : ℕ}
    (hj : j ≤ R.depth b) {x : V} (hx : x ∈ K (R.atDepth b j)) :
    ageKey R K (R.atDepth b j) x = ageKey R K b x := by
  simp only [ageKey, birth_prefix R hj hx]

/-- Choose the oldest vertex of a nonempty bag. -/
noncomputable def oldest (R : RootedAncestors I) (K : I → Set V)
    (hne : ∀ b, (K b).Nonempty) (b : I) : V :=
  (Finset.exists_min_image (K b).toFinite.toFinset (ageKey R K b)
    (by simpa using hne b)).choose

theorem oldest_spec (R : RootedAncestors I) (hne : ∀ b, (K b).Nonempty) (b : I) :
    oldest R K hne b ∈ K b ∧ ∀ x ∈ K b,
      ageKey R K b (oldest R K hne b) ≤ ageKey R K b x := by
  have h := (Finset.exists_min_image (K b).toFinite.toFinset (ageKey R K b)
    (by simpa using hne b)).choose_spec
  simpa only [oldest, Set.Finite.mem_toFinset] using h

/-- The next oldest anchor belongs to the parent bag, because any separator
member was already born by the parent's depth. -/
theorem oldest_parent (hK : IsCliqueTree T G K) (r b : I)
    (hne : ∀ b, (K b).Nonempty)
    (hs : ∀ a c, T.Adj a c → (K a ∩ K c).Nonempty)
    {j : ℕ} (hj : j < (RootedAncestors.ofTree hK.isTree r).depth b) :
    oldest (RootedAncestors.ofTree hK.isTree r) K hne
      ((RootedAncestors.ofTree hK.isTree r).atDepth b (j + 1)) ∈
        K ((RootedAncestors.ofTree hK.isTree r).atDepth b j) := by
  let R := RootedAncestors.ofTree hK.isTree r
  change j < R.depth b at hj
  let p := R.atDepth b j
  let c := R.atDepth b (j + 1)
  let x := oldest R K hne c
  have hadj : T.Adj p c := (route hK.isTree r b).adj_getVert_succ hj
  obtain ⟨y, hyp, hyc⟩ := hs p c hadj
  have hx := oldest_spec R hne c
  have hmin := hx.2 y hyc
  have hkeyx := ageKey_prefix R (by omega : j + 1 ≤ R.depth b) hx.1
  have hkeyy := ageKey_prefix R (by omega : j + 1 ≤ R.depth b) hyc
  change ageKey R K c x ≤ ageKey R K c y at hmin
  rw [hkeyx, hkeyy] at hmin
  have hborn : birthIndex R K b x ≤ j :=
    (ageKey_birth_le R hmin).trans (birth_le R (by omega) hyp)
  have hnext : j + 1 ≤ R.depth b := by omega
  exact birth_mem_prefix hK r b (Nat.le_succ j) hnext hx.1 hborn

/-- Anchor ages are nondecreasing along a root path. -/
theorem oldest_step (hK : IsCliqueTree T G K) (r b : I)
    (hne : ∀ b, (K b).Nonempty)
    (hs : ∀ a c, T.Adj a c → (K a ∩ K c).Nonempty)
    {j : ℕ} (hj : j < (RootedAncestors.ofTree hK.isTree r).depth b) :
    ageKey (RootedAncestors.ofTree hK.isTree r) K b
        (oldest (RootedAncestors.ofTree hK.isTree r) K hne
          ((RootedAncestors.ofTree hK.isTree r).atDepth b j)) ≤
      ageKey (RootedAncestors.ofTree hK.isTree r) K b
        (oldest (RootedAncestors.ofTree hK.isTree r) K hne
          ((RootedAncestors.ofTree hK.isTree r).atDepth b (j + 1))) := by
  let R := RootedAncestors.ofTree hK.isTree r
  change j < R.depth b at hj
  have hx := oldest_parent hK r b hne hs hj
  have hm := (oldest_spec R hne (R.atDepth b j)).2 _ hx
  rw [ageKey_prefix R (by omega) (oldest_spec R hne _).1,
    ageKey_prefix R (by omega) hx] at hm
  exact hm

/-- Every later anchor belongs to the persistent endpoint's
first separator. This is the main first-separator combinatorial assertion. -/
theorem oldest_first_separator (hK : IsCliqueTree T G K) (r b : I)
    (hne : ∀ b, (K b).Nonempty) {u : V} (hu : u ∈ K b)
    {j : ℕ} (hj : birthIndex (RootedAncestors.ofTree hK.isTree r) K b u < j)
    (hj' : j ≤ (RootedAncestors.ofTree hK.isTree r).depth b) :
    oldest (RootedAncestors.ofTree hK.isTree r) K hne
      ((RootedAncestors.ofTree hK.isTree r).atDepth b j) ∈
        K ((RootedAncestors.ofTree hK.isTree r).atDepth b
          (birthIndex (RootedAncestors.ofTree hK.isTree r) K b u)) ∩
        K ((RootedAncestors.ofTree hK.isTree r).atDepth b
          (birthIndex (RootedAncestors.ofTree hK.isTree r) K b u + 1)) := by
  let R := RootedAncestors.ofTree hK.isTree r
  change birthIndex R K b u < j at hj
  change j ≤ R.depth b at hj'
  let x := oldest R K hne (R.atDepth b j)
  change x ∈ K (R.atDepth b (birthIndex R K b u)) ∩
    K (R.atDepth b (birthIndex R K b u + 1))
  have hx := oldest_spec R hne (R.atDepth b j)
  have huend : u ∈ K (R.atDepth b (R.depth b)) := by
    rw [R.atDepth_self]; exact hu
  have huj : u ∈ K (R.atDepth b j) :=
    birth_mem_prefix hK r b hj' le_rfl huend hj.le
  have hm := hx.2 u huj
  rw [ageKey_prefix R hj' hx.1, ageKey_prefix R hj' huj] at hm
  have hb : birthIndex R K b x ≤ birthIndex R K b u := ageKey_birth_le R hm
  have hj0 : birthIndex R K b u ≤ j := hj.le
  have hj1 : birthIndex R K b u + 1 ≤ j := hj
  exact ⟨birth_mem_prefix hK r b hj0 hj' hx.1 hb,
    birth_mem_prefix hK r b hj1 hj' hx.1 (hb.trans (Nat.le_succ _))⟩

end SimpleGraph.CliqueTreeGroupSeparator

namespace SimpleGraph.CliqueTreeGroupSeparator
open Classical
universe u v w
variable {V : Type u} {I : Type v} {H : Type w} [Group H]
  {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

theorem gauge_congr (g : V → V → H) (a b : ℕ → V) (n : ℕ)
    (h : ∀ i ≤ n, a i = b i) : gauge g a n = gauge g b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gauge, ih (fun i hi => h i (by omega)), h n (by omega), h (n + 1) le_rfl]

theorem gauge_shift (g : V → V → H) (a : ℕ → V) (i n : ℕ) :
    gauge g a (i + n) = gauge g a i * gauge g (fun j => a (i + j)) n := by
  induction n with
  | zero => simp [gauge]
  | succ n ih =>
    rw [show i + (n + 1) = (i + n) + 1 by omega, gauge, ih, gauge]
    simp only [Nat.add_assoc, mul_assoc]

def pathAnchors (R : RootedAncestors I) (a : I → V) (b : I) (n : ℕ) : V :=
  a (R.atDepth b n)

noncomputable def frozen (R : RootedAncestors I) (a : I → V) (g : V → V → H)
    (b : I) (x : V) : H :=
  localValue g (pathAnchors R a b) (birthIndex R K b x) x

/-- Freezing at first occurrence commutes with every containing path prefix. -/
theorem frozen_prefix (R : RootedAncestors I) (a : I → V) (g : V → V → H)
    {b : I} {j : ℕ} (hj : j ≤ R.depth b) {x : V} (hx : x ∈ K (R.atDepth b j)) :
    frozen (K := K) R a g (R.atDepth b j) x = frozen (K := K) R a g b x := by
  have hb := birth_le R hj hx
  unfold frozen localValue
  rw [birth_prefix R hj hx]
  have hc (n : ℕ) (hn : n ≤ j) :
      pathAnchors R a (R.atDepth b j) n = pathAnchors R a b n := by
    simp only [pathAnchors, R.atDepth_atDepth b n j hn hj]
  rw [gauge_congr g _ _ _ (fun i hi => hc i (hi.trans hb)), hc _ hb]

/-- Adjacent bags agree on the frozen value of any common member. -/
theorem frozen_adj (hK : IsCliqueTree T G K) (r : I) (a : I → V) (g : V → V → H)
    {b c : I} (hbc : T.Adj b c) {x : V} (hx : x ∈ K b ∩ K c) :
    frozen (K := K) (RootedAncestors.ofTree hK.isTree r) a g b x =
      frozen (K := K) (RootedAncestors.ofTree hK.isTree r) a g c x := by
  let R := RootedAncestors.ofTree hK.isTree r
  have orient {b c : I} (h : T.Adj b c)
      (he : route hK.isTree r c = (route hK.isTree r b).concat h)
      (hx : x ∈ K b) : frozen (K := K) R a g b x = frozen (K := K) R a g c x := by
    have hd : R.depth b ≤ R.depth c := by
      change (route hK.isTree r b).length ≤ (route hK.isTree r c).length
      rw [he, Walk.length_concat]; omega
    have hb : R.atDepth c (R.depth b) = b := by
      change (route hK.isTree r c).getVert (route hK.isTree r b).length = b
      rw [he, Walk.concat_eq_append, Walk.getVert_append]
      simp
    have hx' : x ∈ K (R.atDepth c (R.depth b)) := by rw [hb]; exact hx
    simpa only [hb] using frozen_prefix R a g hd hx'
  rcases route_adj hK.isTree r hbc with he | he
  · exact orient hbc he hx.1
  · exact (orient hbc.symm he hx.2).symm

omit [Group H] in
/-- Running intersection glues common-member equality along arbitrary tree paths. -/
theorem glue_values {p : I → V → H} (hK : IsCliqueTree T G K)
    (hag : ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, p a x = p b x) :
    ∃ φ : V → H, ∀ a x, x ∈ K a → φ x = p a x := by
  have along {a b} (q : T.Walk a b) (x : V) (hx : ∀ c ∈ q.support, x ∈ K c) :
      p a x = p b x := by
    induction q with
    | nil => rfl
    | cons hab q ih =>
      exact (hag _ _ hab x ⟨hx _ (by simp), hx _ (by simp)⟩).trans
        (ih (fun c hc => hx c (by simp [hc])))
  refine ⟨fun x => p (hK.cover x).choose x, fun a x hx => ?_⟩
  obtain ⟨q, hq⟩ := (hK.isTree.existsUnique_path (hK.cover x).choose a).exists
  exact along q x (hK.running q hq x (hK.cover x).choose_spec hx)

theorem exists_frozen_potential (hK : IsCliqueTree T G K) (r : I) (a : I → V)
    (g : V → V → H) :
    ∃ φ : V → H, ∀ b x, x ∈ K b →
      φ x = frozen (K := K) (RootedAncestors.ofTree hK.isTree r) a g b x :=
  glue_values hK (fun _ _ h _ hx => frozen_adj hK r a g h hx)

/-- Nonempty separators and vertex coverage force all bags to be nonempty,
including a one-bag tree. -/
theorem bags_nonempty [Nonempty V] (hK : IsCliqueTree T G K)
    (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty) (a : I) : (K a).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨b, hb⟩ := hK.cover x
  by_cases he : a = b
  · exact ⟨x, he ▸ hb⟩
  let p := route hK.isTree a b
  have h := p.adj_snd (Walk.not_nil_of_ne he)
  obtain ⟨y, hy, _⟩ := hs a p.snd h
  exact ⟨y, hy⟩

end SimpleGraph.CliqueTreeGroupSeparator

namespace SimpleGraph.CliqueTreeGroupSeparator
open Classical
universe u v w
variable {V : Type u} {I : Type v} {H : Type w}
  [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]
  {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

theorem frozen_forward_bound [Finite V] [LinearOrder V]
    (hK : IsCliqueTree T G K) (r : I) (hne : ∀ b, (K b).Nonempty)
    (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (s : ℕ) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ s)
    (g : V → V → H) {δ : ℝ} (hδ : 0 ≤ δ) (hzero : ∀ x, g x x = 1)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ δ)
    (b : I) (u v : V) (hu : u ∈ K b) (hv : v ∈ K b)
    (hij : birthIndex (RootedAncestors.ofTree hK.isTree r) K b u ≤
      birthIndex (RootedAncestors.ofTree hK.isTree r) K b v) :
    Dist.dist
      (frozen (K := K) (RootedAncestors.ofTree hK.isTree r)
        (oldest (RootedAncestors.ofTree hK.isTree r) K hne) g b u * g u v)
      (frozen (K := K) (RootedAncestors.ofTree hK.isTree r)
        (oldest (RootedAncestors.ofTree hK.isTree r) K hne) g b v) ≤
      (max 1 s : ℕ) * δ := by
  let R := RootedAncestors.ofTree hK.isTree r
  let a := oldest R K hne
  let A := pathAnchors R a b
  let i := birthIndex R K b u
  let j := birthIndex R K b v
  have hi := birth_spec R b u hu
  have hj := birth_spec R b v hv
  change i ≤ j at hij
  change i ≤ R.depth b ∧ u ∈ K (R.atDepth b i) at hi
  change j ≤ R.depth b ∧ v ∈ K (R.atDepth b j) at hj
  change Dist.dist (localValue g A i u * g u v) (localValue g A j v) ≤ _
  have hmax : (1 : ℝ) ≤ (max 1 s : ℕ) := by exact_mod_cast (le_max_left 1 s)
  by_cases he : i = j
  · rw [he]
    have ht := clique_triangle g hδ hzero hrev htri (hK.clique (R.atDepth b j))
      (oldest_spec R hne _).1 (he ▸ hi.2) hj.2
    have hlocal : Dist.dist (localValue g A j u * g u v) (localValue g A j v) ≤ δ := by
      simpa only [localValue, A, pathAnchors, mul_assoc, dist_mul_left] using ht
    exact hlocal.trans (by simpa using mul_le_mul_of_nonneg_right hmax hδ)
  have hij' : i < j := lt_of_le_of_ne hij he
  let N := j - i
  let B (n : ℕ) := K (R.atDepth b (i + n))
  let a' (n : ℕ) := A (i + n)
  let S : Finset V := (K (R.atDepth b i) ∩ K (R.atDepth b (i + 1))).toFinite.toFinset
  have hN : i + N = j := Nat.add_sub_of_le hij
  have hindices (n : ℕ) (hn : n ≤ N) : i + n ≤ R.depth b := by omega
  have hclique (n : ℕ) (_hn : n ≤ N) : G.IsClique (B n) := hK.clique _
  have hanchor (n : ℕ) (_hn : n ≤ N) : a' n ∈ B n := (oldest_spec R hne _).1
  have hnext (n : ℕ) (hn : n < N) : a' (n + 1) ∈ B n := by
    have hlt : i + n < R.depth b := by omega
    simpa only [a', A, pathAnchors, B, Nat.add_assoc] using oldest_parent hK r b hne hs hlt
  have hu' (n : ℕ) (hn : n ≤ N) : u ∈ B n := by
    have huend : u ∈ K (R.atDepth b (R.depth b)) := by rw [R.atDepth_self]; exact hu
    exact birth_mem_prefix hK r b (hindices n hn) le_rfl huend (by change i ≤ i + n; omega)
  have hv' : v ∈ B N := by simpa only [B, hN] using hj.2
  have hmono0 (k l : ℕ) (hkl : k ≤ l) : l ≤ R.depth b →
      ageKey R K b (A k) ≤ ageKey R K b (A l) := by
    induction l, hkl using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ l hkl ih =>
      intro hl
      exact (ih (by omega)).trans (oldest_step hK r b hne hs (by
        change l < R.depth b; omega))
  have hmono (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ N) :
      ageKey R K b (a' k) ≤ ageKey R K b (a' l) :=
    hmono0 _ _ (by omega) (hindices l hl)
  have hstrict (n : ℕ) (hn : n < N) (hchange : a' (n + 1) ≠ a' n) :
      ageKey R K b (a' n) < ageKey R K b (a' (n + 1)) := by
    apply lt_of_le_of_ne (hmono n (n + 1) (by omega) (by omega))
    intro heq
    exact hchange ((ageKey_injective R b heq).symm)
  have hfirst (n : ℕ) (hn : n < N) (_hneu : a' (n + 1) ≠ u) : a' (n + 1) ∈ S := by
    have hbound : i + (n + 1) ≤ R.depth b := hindices _ (by omega)
    have hborn : birthIndex R K b u < i + (n + 1) := by change i < i + (n + 1); omega
    have hm := oldest_first_separator hK r b hne hu hborn hbound
    simpa only [S, Set.Finite.mem_toFinset, a', A, pathAnchors, a, i, R] using hm
  have huS : u ∈ S := by
    simp only [S, Set.Finite.mem_toFinset]
    exact ⟨hi.2, by simpa only [B] using hu' 1 (by dsimp [N]; omega)⟩
  have hadj : T.Adj (R.atDepth b i) (R.atDepth b (i + 1)) :=
    (route hK.isTree r b).adj_getVert_succ (by change i < R.depth b; omega)
  have hcard : S.card ≤ s := by
    rw [show S.card = (K (R.atDepth b i) ∩ K (R.atDepth b (i + 1))).ncard from
      (Set.ncard_eq_toFinset_card _ _).symm]
    exact hsep _ _ hadj
  have ht := separator_trace_bound g hδ hzero hrev htri B a' (ageKey R K b) N u v S s
    hclique hanchor hnext hu' hv' hmono hstrict hfirst huS hcard
  have hval (x : V) : localValue g A j x = gauge g A i * localValue g a' N x := by
    rw [← hN, localValue, gauge_shift]
    simp only [localValue, a', hN, mul_assoc]
  have hzero' : localValue g A i u = gauge g A i * localValue g a' 0 u := by
    simp [localValue, gauge, a']
  rw [hzero', hval v, mul_assoc, dist_mul_left]
  exact ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_right 1 s)) hδ)

/-- Normalize only the diagonal; original edge gains are preserved. -/
noncomputable def diagonalGain (g : V → V → H) (x y : V) : H := if x = y then 1 else g x y

end SimpleGraph.CliqueTreeGroupSeparator
