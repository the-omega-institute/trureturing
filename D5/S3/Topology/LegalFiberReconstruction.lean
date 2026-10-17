/- GID: D5/S3/Topology/LegalFiberReconstruction
   generality: G
   mirror-B: D5/B/S3/Topology/LegalFiberReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact fibers on legal digit prefixes reconstruct a continuous surjection. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.LegalFiberReconstruction

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open Set Filter _root_.Topology

/-- Exactly the length-n restrictions of existing legal infinite digit streams. -/
abbrev Prefix (n : ℕ) :=
  {w : Fin n → Bool // ∃ p : LegalDigits, ∀ i : Fin n, p.val i.val = w i}

/-- The forward, zero-indexed finite restriction of a legal digit stream. -/
def legalPrefix (p : LegalDigits) (n : ℕ) : Prefix n :=
  ⟨fun i => p.val i.val, p, fun _ => rfl⟩

private theorem prescribed_point_branch {X : Type*}
    (K : (n : ℕ) → Prefix n → Set X)
    (hroot : K 0 (legalPrefix ⟨fun _ => false, by simp⟩ 0) = univ)
    (hcover : ∀ n (s : Prefix n) x, x ∈ K n s ↔
      ∃ t : Prefix (n + 1), (∀ i : Fin n, t.val i.castSucc = s.val i) ∧
        x ∈ K (n + 1) t) (x : X) :
    ∃ p : LegalDigits, ∀ n, x ∈ K n (legalPrefix p n) := by
  classical
  let Node (n : ℕ) := {s : Prefix n // x ∈ K n s}
  have supply {n : ℕ} (s : Node n) :
      ∃ t : Prefix (n + 1), (∀ i : Fin n, t.val i.castSucc = s.val.val i) ∧
        x ∈ K (n + 1) t := (hcover n s.val x).mp s.property
  let next {n : ℕ} (s : Node n) : Node (n + 1) :=
    ⟨(supply s).choose, (supply s).choose_spec.2⟩
  let chain : (n : ℕ) → Node n :=
    Nat.rec ⟨legalPrefix ⟨fun _ => false, by simp⟩ 0, by rw [hroot]; trivial⟩
      (fun _ s => next s)
  have step (n : ℕ) (i : Fin n) :
      (chain (n + 1)).val.val i.castSucc = (chain n).val.val i :=
    (supply (chain n)).choose_spec.1 i
  have stable : ∀ n (i : Fin n), (chain n).val.val i =
      (chain (i.val + 1)).val.val (Fin.last i.val) := by
    intro n
    induction n with
    | zero => intro i; exact Fin.elim0 i
    | succ n ih =>
      intro i
      by_cases hi : i.val < n
      · exact (step n ⟨i.val, hi⟩).trans (ih ⟨i.val, hi⟩)
      · have he : i = Fin.last n := Fin.ext (by simp; omega)
        subst i
        rfl
  let p : ℕ → Bool := fun j => (chain (j + 1)).val.val (Fin.last j)
  have legal : ∀ j, ¬ (p j = true ∧ p (j + 1) = true) := by
    intro j hj
    obtain ⟨q, hq⟩ := (chain (j + 2)).val.property
    apply q.property j
    constructor
    · rw [hq ⟨j, by omega⟩, stable (j + 2) ⟨j, by omega⟩]
      exact hj.1
    · rw [hq ⟨j + 1, by omega⟩, stable (j + 2) ⟨j + 1, by omega⟩]
      exact hj.2
  let name : LegalDigits := ⟨p, legal⟩
  have restriction (n : ℕ) : legalPrefix name n = (chain n).val := by
    apply Subtype.ext
    funext i
    exact (stable n i).symm
  exact ⟨name, fun n => (restriction n).symm ▸ (chain n).property⟩

/-- Legal nested compact fibers with branchwise vanishing real diameters give a
continuous surjection, with each value exactly characterized by the full intersection. -/
theorem continuous_reconstruction {X : Type*} [MetricSpace X] [CompactSpace X]
    (K : (n : ℕ) → Prefix n → Set X)
    (hne : ∀ n s, (K n s).Nonempty)
    (hc : ∀ n s, IsCompact (K n s))
    (hroot : K 0 (legalPrefix ⟨fun _ => false, by simp⟩ 0) = univ)
    (hcover : ∀ n (s : Prefix n) x, x ∈ K n s ↔
      ∃ t : Prefix (n + 1), (∀ i : Fin n, t.val i.castSucc = s.val i) ∧
        x ∈ K (n + 1) t)
    (hdiam : ∀ p : LegalDigits,
      Tendsto (fun n => Metric.diam (K n (legalPrefix p n))) atTop (𝓝 0)) :
    ∃ f : LegalDigits → X, Continuous f ∧ Function.Surjective f ∧
      ∀ p x, f p = x ↔ ∀ n, x ∈ K n (legalPrefix p n) := by
  classical
  have nested (p : LegalDigits) (n : ℕ) :
      K (n + 1) (legalPrefix p (n + 1)) ⊆ K n (legalPrefix p n) := by
    intro x hx
    exact (hcover n (legalPrefix p n) x).mpr ⟨legalPrefix p (n + 1), fun _ => rfl, hx⟩
  have unique (p : LegalDigits) : ∃! x, ∀ n, x ∈ K n (legalPrefix p n) := by
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => K n (legalPrefix p n)) (nested p) (fun n => hne n _)
      (hc 0 _) (fun n => (hc n _).isClosed)
    have hx' : ∀ n, x ∈ K n (legalPrefix p n) := mem_iInter.mp hx
    refine ⟨x, hx', ?_⟩
    intro y hy
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    exact ge_of_tendsto' (hdiam p) fun n =>
      Metric.dist_le_diam_of_mem (hc n _).isBounded (hy n) (hx' n)
  let f : LegalDigits → X := fun p => (unique p).choose
  have mem (p : LegalDigits) (n : ℕ) : f p ∈ K n (legalPrefix p n) :=
    (unique p).choose_spec.1 n
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [Metric.continuous_iff']
    intro p ε hε
    obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually (hdiam p) (gt_mem_nhds hε)).exists
    have neighborhood : ∀ᶠ q : LegalDigits in 𝓝 p,
        ∀ i ∈ Finset.range n, q.val i = p.val i := by
      apply (Filter.eventually_all_finset _).mpr
      intro i hi
      exact ((continuous_apply i).comp continuous_subtype_val).continuousAt
        ((isOpen_discrete {p.val i}).mem_nhds (Set.mem_singleton _))
    filter_upwards [neighborhood] with q hq
    have hpq : legalPrefix q n = legalPrefix p n := by
      apply Subtype.ext
      funext i
      exact hq i.val (Finset.mem_range.mpr i.isLt)
    exact (Metric.dist_le_diam_of_mem (hc n _).isBounded
      (hpq ▸ mem q n) (mem p n)).trans_lt hn
  · intro x
    obtain ⟨p, hp⟩ := prescribed_point_branch K hroot hcover x
    exact ⟨p, ((unique p).choose_spec.2 x hp).symm⟩
  · intro p x
    exact ⟨fun h n => h ▸ mem p n, fun hx => ((unique p).choose_spec.2 x hx).symm⟩

end D5.S3.Topology.LegalFiberReconstruction
