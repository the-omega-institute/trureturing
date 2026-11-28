/- GID: D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Vector, mathlib/module/Mathlib.Topology.Algebra.Monoid, mathlib/module/Mathlib.Topology.Order.Compact, mathlib/module/Mathlib.Topology.Order.Lattice]
   utility: none
   digest: Compact positive assignment slack and finite-block losses for min-plus walks. -/
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61AssignmentGuards
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Vector
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import OmegaBuild.Commands

compile_only_with_mathlib

/-! The compact-block argument in Theorem 2.2 of the Q6.1 assignment manuscript.
All compactness is over the reals. Loss and vertex potentials are in total-score
units, and the cycle-mean rate is in per-coordinate units. -/

namespace Q61CompactAssignmentSlack

open Maths MeyerovitchYoungQ61Complete Q61AssignmentGuards Set
open scoped BigOperators

noncomputable section

variable {W V E : Type*} [Fintype W] [Nonempty W]

/-- The real mean weight of a cheapest column assignment. -/
def assignmentMean (A : Matrix W W ℝ) : ℝ := by
  classical
  exact (Finset.univ.inf' Finset.univ_nonempty (assignmentCost A)) / (Fintype.card W : ℝ)

/-- Scale the manuscript's mean-potential inequality to total scores, while retaining
a minimizing permutation for every edge. -/
theorem exists_minimizing_assignments (G : EdgeGraph V E) (M : E → Matrix W W ℝ)
    (rate : ℝ) (P : V → ℝ)
    (hP : ∀ e, assignmentMean (M e) ≤ rate + P (G.source e) - P (G.target e)) :
    ∃ σ : E → Equiv.Perm W,
      (∀ e τ, assignmentCost (M e) (σ e) ≤ assignmentCost (M e) τ) ∧
      ∀ e, assignmentCost (M e) (σ e) ≤
        (Fintype.card W : ℝ) * rate +
          (Fintype.card W : ℝ) * P (G.source e) - (Fintype.card W : ℝ) * P (G.target e) := by
  classical
  have hmin (e : E) : ∃ σ : Equiv.Perm W,
      Finset.univ.inf' Finset.univ_nonempty (assignmentCost (M e)) =
        assignmentCost (M e) σ := by
    obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (assignmentCost (M e))
    exact ⟨σ, hσ⟩
  let σ : E → Equiv.Perm W := fun e => Classical.choose (hmin e)
  have hσ (e : E) :
      Finset.univ.inf' Finset.univ_nonempty (assignmentCost (M e)) =
        assignmentCost (M e) (σ e) := Classical.choose_spec (hmin e)
  refine ⟨σ, fun e τ => ?_, fun e => ?_⟩
  · rw [← hσ e]
    exact Finset.inf'_le _ (Finset.mem_univ τ)
  · have h := hP e
    unfold assignmentMean at h
    rw [hσ e] at h
    have hcard : 0 < (Fintype.card W : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := W))
    have hcost := (div_le_iff₀ hcard).mp h
    calc
      _ ≤ (rate + P (G.source e) - P (G.target e)) * (Fintype.card W : ℝ) := hcost
      _ = _ := by ring

/-- Anchored scores of spread at most `B`, including all of their boundary faces. -/
def projectiveBox (o : W) (B : ℝ) : Set (W → ℝ) :=
  {x | x o = 0 ∧ ∀ i j, x i - x j ≤ B}

def normalize (o : W) (x : W → ℝ) : W → ℝ :=
  fun j => x j - x o

theorem zero_mem_projectiveBox (o : W) {B : ℝ} (hB : 0 ≤ B) :
    (fun _ => 0) ∈ projectiveBox o B := by
  exact ⟨rfl, fun _ _ => by simpa only [sub_self] using hB⟩

theorem isCompact_projectiveBox (o : W) (B : ℝ) :
    IsCompact (projectiveBox o B) := by
  have hclosed : IsClosed (projectiveBox o B) := by
    rw [show projectiveBox o B =
        {x : W → ℝ | x o = 0} ∩ ⋂ i : W, ⋂ j : W, {x : W → ℝ | x i - x j ≤ B} by
      ext x
      simp [projectiveBox]]
    exact (isClosed_eq (continuous_apply o) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le ((continuous_apply i).sub (continuous_apply j)) continuous_const)
  have hcompact : IsCompact {x : W → ℝ | ∀ i, x i ∈ Icc (-B) B} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  refine hcompact.of_isClosed_subset hclosed ?_
  intro x hx i
  obtain ⟨ho, h⟩ := hx
  have hi := h i o
  have hj := h o i
  rw [ho] at hi hj
  exact ⟨by linarith only [hj], by linarith only [hi]⟩

private theorem endpointScores_append (M : E → Matrix W W ℝ) (a b : List E)
    (x : W → ℝ) :
    endpointScores M x (a ++ b) = endpointScores M (endpointScores M x a) b := by
  simp only [endpointScores, List.foldl_append]

private theorem continuous_endpointUpdate (A : Matrix W W ℝ) :
    Continuous (endpointUpdate A) := by
  apply continuous_pi
  intro j
  unfold endpointUpdate
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => (continuous_apply i).add continuous_const)

theorem continuous_endpointScores (M : E → Matrix W W ℝ) (a : List E) :
    Continuous (fun x => endpointScores M x a) := by
  induction a using List.reverseRecOn with
  | nil => exact continuous_id
  | append_singleton a e ih =>
    simpa only [endpointScores_snoc, Function.comp_def] using
      (continuous_endpointUpdate (M e)).comp ih

private theorem endpointUpdate_add_const (A : Matrix W W ℝ) (x : W → ℝ) (d : ℝ) :
    endpointUpdate A (fun i => x i + d) = fun j => endpointUpdate A x j + d := by
  funext j
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := W))
    (fun i => x i + A i j)
  change endpointUpdate A x j = x i + A i j at hi
  apply le_antisymm
  · have h := endpointUpdate_le A (fun i => x i + d) i j
    linarith only [h, hi]
  · change endpointUpdate A x j + d ≤
      Finset.univ.inf' Finset.univ_nonempty (fun i => x i + d + A i j)
    apply Finset.le_inf' Finset.univ_nonempty _
    intro k _
    linarith only [endpointUpdate_le A x k j]

private theorem endpointScores_add_const (M : E → Matrix W W ℝ) (a : List E)
    (x : W → ℝ) (d : ℝ) :
    endpointScores M (fun i => x i + d) a = fun j => endpointScores M x a j + d := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a e ih =>
    simp only [endpointScores_snoc, ih, endpointUpdate_add_const]

private theorem normalize_endpointUpdate_mem (o : W) {B : ℝ} (A : Matrix W W ℝ)
    (hrow : ∀ i j k, A i j - A i k ≤ B) (x : W → ℝ) :
    normalize o (endpointUpdate A x) ∈ projectiveBox o B := by
  refine ⟨sub_self _, fun j k => ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := W))
    (fun i => x i + A i k)
  change endpointUpdate A x k = x i + A i k at hi
  unfold normalize
  linarith only [hi, endpointUpdate_le A x i j, hrow i j k]

/-- A uniform bound on same-row column differences bounds the projective scores
at every prefix of the original min-plus recurrence. -/
theorem normalize_endpointScores_mem (M : E → Matrix W W ℝ) (o : W) {B : ℝ}
    (hrow : ∀ e i j k, M e i j - M e i k ≤ B) (a : List E) (x : W → ℝ)
    (hx : normalize o x ∈ projectiveBox o B) :
    normalize o (endpointScores M x a) ∈ projectiveBox o B := by
  induction a using List.reverseRecOn with
  | nil => exact hx
  | append_singleton a e _ =>
    rw [endpointScores_snoc]
    exact normalize_endpointUpdate_mem o (M e) (hrow e) _

/-- Loss in total-score units. Here `H` is the mean potential multiplied by
the number of Bob vertices. -/
def assignmentSlack (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)
    (s t : V) (a : List E) (x : W → ℝ) : ℝ :=
  (a.length : ℝ) * ((Fintype.card W : ℝ) * rate) + H s - H t -
    ((∑ j, endpointScores M x a j) - ∑ j, x j)

theorem continuous_assignmentSlack (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)
    (s t : V) (a : List E) : Continuous (assignmentSlack M rate H s t a) := by
  unfold assignmentSlack
  exact continuous_const.sub
    ((continuous_finsetSum Finset.univ fun j _ =>
      (continuous_apply j).comp (continuous_endpointScores M a)).sub
      (continuous_finsetSum Finset.univ fun j _ => continuous_apply j))

theorem assignmentSlack_normalize (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)
    (s t : V) (a : List E) (o : W) (x : W → ℝ) :
    assignmentSlack M rate H s t a (normalize o x) = assignmentSlack M rate H s t a x := by
  change assignmentSlack M rate H s t a (fun j => x j - x o) =
    assignmentSlack M rate H s t a x
  simp only [sub_eq_add_neg]
  unfold assignmentSlack
  rw [endpointScores_add_const]
  simp only [Finset.sum_add_distrib]
  ring

theorem assignmentSlack_append (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)
    (s t u : V) (a b : List E) (x : W → ℝ) :
    assignmentSlack M rate H s u (a ++ b) x =
      assignmentSlack M rate H s t a x +
        assignmentSlack M rate H t u b (endpointScores M x a) := by
  simp only [assignmentSlack, List.length_append, Nat.cast_add, endpointScores_append]
  ring

private theorem sum_constant_word (a : List E) (c : ℝ) :
    (a.map (fun _ => c)).sum = (a.length : ℝ) * c := by
  induction a with
  | nil => simp
  | cons e a ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

variable (G : EdgeGraph V E) (M : E → Matrix W W ℝ) (rate : ℝ) (H : V → ℝ)

section Certificate

variable (σ : E → Equiv.Perm W)
  (hcap : ∀ e, assignmentCost (M e) (σ e) ≤
    (Fintype.card W : ℝ) * rate + H (G.source e) - H (G.target e))

include hcap

theorem assignmentSlack_spec {s t : V} (p : G.Walk s t) (x : W → ℝ) :
    0 ≤ assignmentSlack M rate H s t p.edges x ∧
      (assignmentSlack M rate H s t p.edges x = 0 ↔
        TightAlong G M σ (fun _ => (Fintype.card W : ℝ) * rate) H x p) := by
  have hc := walk_assignment_certificate G M σ (fun _ => (Fintype.card W : ℝ) * rate)
    H hcap x p
  dsimp only at hc
  rw [sum_constant_word] at hc
  unfold assignmentSlack
  refine ⟨sub_nonneg.mpr hc.1, ?_⟩
  exact ⟨fun h => hc.2.mp (sub_eq_zero.mp h).symm, fun h => sub_eq_zero.mpr (hc.2.mpr h).symm⟩

end Certificate

/-- Slacks realized by legal length-`N` Alice words and projective inputs. -/
def blockSlacks (o : W) (B : ℝ) (N : ℕ) : Set ℝ :=
  {d | ∃ (s t : V) (p : G.Walk s t), p.length = N ∧
    ∃ x ∈ projectiveBox o B, assignmentSlack M rate H s t p.edges x = d}

/-- Finite Alice endpoints and words index a finite union of compact images.
The word determines the numerical slack once its endpoints are given. -/
theorem isCompact_blockSlacks [Finite V] [Finite E] (o : W) (B : ℝ) (N : ℕ) :
    IsCompact (blockSlacks G M rate H o B N) := by
  classical
  let Key := {k : V × V × List.Vector E N //
    ∃ p : G.Walk k.1 k.2.1, p.edges = k.2.2.toList}
  let imageSlack (k : Key) :=
    assignmentSlack M rate H k.val.1 k.val.2.1 k.val.2.2.toList '' projectiveBox o B
  have hset : blockSlacks G M rate H o B N = ⋃ k : Key, imageSlack k := by
    ext d
    simp only [blockSlacks, Set.mem_setOf_eq, Set.mem_iUnion, imageSlack, Set.mem_image]
    constructor
    · rintro ⟨s, t, p, hp, x, hx, hd⟩
      let k : Key := ⟨(s, t, ⟨p.edges, p.edges_length.trans hp⟩), ⟨p, rfl⟩⟩
      exact ⟨k, x, hx, hd⟩
    · rintro ⟨k, x, hx, hcost⟩
      obtain ⟨p, hp⟩ := k.property
      have hlen : p.length = N :=
        p.edges_length.symm.trans ((congrArg List.length hp).trans k.val.2.2.toList_length)
      exact ⟨k.val.1, k.val.2.1, p, hlen, x, hx,
        (congrArg (fun a => assignmentSlack M rate H k.val.1 k.val.2.1 a x) hp).trans hcost⟩
  rw [hset]
  exact isCompact_iUnion (f := imageSlack) fun k =>
    (isCompact_projectiveBox o B).image
      (continuous_assignmentSlack M rate H k.val.1 k.val.2.1 k.val.2.2.toList)

section Blocks

variable (σ : E → Equiv.Perm W)
  (hcap : ∀ e, assignmentCost (M e) (σ e) ≤
    (Fintype.card W : ℝ) * rate + H (G.source e) - H (G.target e))

include hcap

/-- Absence of a tight length-`N` walk gives one positive slack bound for
every legal word and every input in the box. If any such word and input exist,
the bound is realized by one of them. -/
theorem compact_block_assignment_slack [Finite V] [Finite E] (o : W) (B : ℝ) (N : ℕ)
    (hno : ∀ {s t} (p : G.Walk s t), p.length = N →
      ∀ x ∈ projectiveBox o B,
        ¬ TightAlong G M σ (fun _ => (Fintype.card W : ℝ) * rate) H x p) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ {s t} (p : G.Walk s t), p.length = N →
        ∀ x ∈ projectiveBox o B, δ ≤ assignmentSlack M rate H s t p.edges x) ∧
      ((blockSlacks G M rate H o B N).Nonempty → IsLeast (blockSlacks G M rate H o B N) δ) := by
  classical
  by_cases hne : (blockSlacks G M rate H o B N).Nonempty
  · obtain ⟨δ, hδ⟩ := (isCompact_blockSlacks G M rate H o B N).exists_isLeast hne
    have hpos : 0 < δ := by
      obtain ⟨s, t, p, hp, x, hx, hdx⟩ := hδ.1
      have hcert := assignmentSlack_spec G M rate H σ hcap p x
      rw [← hdx]
      exact lt_of_le_of_ne hcert.1 (Ne.symm (fun hz => hno p hp x hx (hcert.2.mp hz)))
    exact ⟨δ, hpos, fun {_ _} p hp x hx => hδ.2 ⟨_, _, p, hp, x, hx, rfl⟩, fun _ => hδ⟩
  · refine ⟨1, zero_lt_one, ?_, fun h => (hne h).elim⟩
    intro s t p hp x hx
    exact (hne ⟨_, s, t, p, hp, x, hx, rfl⟩).elim

omit hcap in
private theorem split_walk_at {s t : V} (p : G.Walk s t) (n : ℕ) (hn : n ≤ p.length) :
    ∃ u, ∃ (q : G.Walk s u) (r : G.Walk u t),
      q.length = n ∧ p.edges = q.edges ++ r.edges := by
  induction p with
  | nil =>
    have hz : n = 0 := Nat.eq_zero_of_le_zero hn
    exact ⟨s, .nil, .nil, hz.symm, rfl⟩
  | @concat t p e he ih =>
    by_cases h : n ≤ p.length
    · obtain ⟨u, q, r, hq, hp⟩ := ih h
      refine ⟨u, q, r.concat e he, hq, ?_⟩
      simp only [EdgeGraph.Walk.edges_concat, hp, List.append_assoc]
    · have hlen : (p.concat e he).length = n := by
        simp only [EdgeGraph.Walk.length_concat] at hn ⊢
        omega
      exact ⟨_, p.concat e he, .nil, hlen, by simp [EdgeGraph.Walk.edges]⟩

/-- Chaining applies to the exact scores after each prefix. Any suffix shorter
than the block length contributes its own nonnegative slack. -/
theorem assignmentSlack_ge_blocks (o : W) {B : ℝ}
    (hrow : ∀ e i j k, M e i j - M e i k ≤ B) {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (hblock : ∀ {s t} (p : G.Walk s t), p.length = N →
      ∀ x ∈ projectiveBox o B, δ ≤ assignmentSlack M rate H s t p.edges x)
    {s t : V} (p : G.Walk s t) (x : W → ℝ) (hx : normalize o x ∈ projectiveBox o B) :
    ((p.length / N : ℕ) : ℝ) * δ ≤ assignmentSlack M rate H s t p.edges x := by
  have chain (k : ℕ) : ∀ {u v} (w : G.Walk u v), k * N ≤ w.length →
      ∀ a : W → ℝ, normalize o a ∈ projectiveBox o B →
        (k : ℝ) * δ ≤ assignmentSlack M rate H u v w.edges a := by
    induction k with
    | zero =>
      intro u v w _ a _
      simpa only [Nat.cast_zero, zero_mul] using (assignmentSlack_spec G M rate H σ hcap w a).1
    | succ k ih =>
      intro u v w hw a ha
      rw [Nat.succ_mul] at hw
      have hprefix : N ≤ w.length := by omega
      obtain ⟨m, q, r, hq, he⟩ := split_walk_at G w N hprefix
      have hlen : w.length = q.length + r.length := by
        simpa only [EdgeGraph.Walk.edges_length, List.length_append] using
          congrArg List.length he
      have hr : k * N ≤ r.length := by omega
      have hqSlack := hblock q hq (normalize o a) ha
      rw [assignmentSlack_normalize] at hqSlack
      have hrSlack := ih r hr (endpointScores M a q.edges)
        (normalize_endpointScores_mem M o hrow q.edges a ha)
      rw [he, assignmentSlack_append M rate H u m v, Nat.cast_succ, add_mul, one_mul]
      calc
        (k : ℝ) * δ + δ = δ + (k : ℝ) * δ := add_comm _ _
        _ ≤ _ := add_le_add hqSlack hrSlack
  exact chain (p.length / N) p (Nat.div_mul_le_self _ _) x hx

/-- Zero initial scores and free terminal Bob vertex yield the original
`matrixMinimum`. The loss is charged for every complete block. -/
theorem matrixMinimum_le_with_block_loss (o : W) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ e i j k, M e i j - M e i k ≤ B) {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (hblock : ∀ {s t} (p : G.Walk s t), p.length = N →
      ∀ x ∈ projectiveBox o B, δ ≤ assignmentSlack M rate H s t p.edges x)
    {s t : V} (p : G.Walk s t) :
    (Fintype.card W : ℝ) * matrixMinimum M p.edges + ((p.length / N : ℕ) : ℝ) * δ ≤
      (p.length : ℝ) * ((Fintype.card W : ℝ) * rate) + H s - H t := by
  have hz : normalize o (fun _ => 0) ∈ projectiveBox o B := by
    have hzero : normalize o (fun _ => 0) = (fun _ => 0) := by
      funext j
      simp only [normalize, sub_self]
    rw [hzero]
    exact zero_mem_projectiveBox o hB
  have hloss := assignmentSlack_ge_blocks G M rate H σ hcap o hrow hN hblock p _ hz
  have hmin : (Fintype.card W : ℝ) * matrixMinimum M p.edges ≤
      ∑ j, endpointScores M (fun _ => 0) p.edges j := by
    calc
      (Fintype.card W : ℝ) * matrixMinimum M p.edges =
          ∑ _ : W, matrixMinimum M p.edges := by simp [nsmul_eq_mul]
      _ ≤ ∑ j, endpointScores M (fun _ => 0) p.edges j := by
        apply Finset.sum_le_sum
        intro j _
        rw [matrixMinimum_eq_inf]
        exact Finset.inf'_le _ (Finset.mem_univ j)
  simp only [assignmentSlack, EdgeGraph.Walk.edges_length, Finset.sum_const_zero, sub_zero]
    at hloss
  linarith only [hmin, hloss]

/-- The same positive minimum gives a uniform finite-horizon deficit in the
physical payoff for arbitrarily long legal Alice words. -/
theorem compact_block_payoff_bound [Finite V] [Finite E] (o : W) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ e i j k, M e i j - M e i k ≤ B) {N : ℕ} (hN : 0 < N)
    (hno : ∀ {s t} (p : G.Walk s t), p.length = N →
      ∀ x ∈ projectiveBox o B,
        ¬ TightAlong G M σ (fun _ => (Fintype.card W : ℝ) * rate) H x p) :
    ∃ δ : ℝ, 0 < δ ∧
      ((blockSlacks G M rate H o B N).Nonempty → IsLeast (blockSlacks G M rate H o B N) δ) ∧
      ∀ {s t} (p : G.Walk s t),
        (Fintype.card W : ℝ) * matrixMinimum M p.edges + ((p.length / N : ℕ) : ℝ) * δ ≤
          (p.length : ℝ) * ((Fintype.card W : ℝ) * rate) + H s - H t := by
  obtain ⟨δ, hpos, hblock, hmin⟩ :=
    compact_block_assignment_slack G M rate H σ hcap o B N hno
  exact ⟨δ, hpos, hmin, fun {_ _} p =>
    matrixMinimum_le_with_block_loss G M rate H σ hcap o hB hrow hN hblock p⟩

end Blocks

end

end Q61CompactAssignmentSlack
