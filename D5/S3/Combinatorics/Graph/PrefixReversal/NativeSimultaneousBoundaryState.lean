/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeSimultaneousBoundaryState
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeSimultaneousBoundaryState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Advance Both Actual Native Boundary Templates on One Cycle. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualBoundaryAdvance
import D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursiveBoundaryAdvance
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private shiftPort shifted_special_port from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualBoundaryAdvance

universe v
variable {V : Type v} [DecidableEq V] {G : SimpleGraph V}

def NativeBoundaryPairs {m k : ℕ} (F : SupplyFrame m k) (odd : Bool)
    (raw : V → Configuration m) (pieces : List (Piece G)) : Prop :=
  ∀ p ∈ pieces, ∃ a b : Port k,
    raw p.start = specialPort F a ∧ raw p.finish = specialPort F b ∧
      (if odd then oddBoundary k else evenBoundary k) (code a) (code b)

private theorem advanced_native_boundary_pairs {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (odd : Bool)
    (raw : V → Configuration m) (hinj : Function.Injective raw)
    {x y ℓ₀ r₀ : V} (old : G.Walk x y) (rest : List (Piece G))
    (hn : (old.support ++ rest.flatMap fun p => p.walk.support).Nodup)
    (hx : raw x = leftPort F 0) (hy : raw y = leftPort F (k - 1))
    (hℓ₀ : raw ℓ₀ = leftPort (nextFrame F A u hbase) 0)
    (hr₀ : raw r₀ = rightPort (nextFrame F A u hbase) 0)
    (hb : NativeBoundaryPairs F odd raw rest)
    (b₀ : G.Walk ℓ₀ y) (b₁ : G.Walk r₀ x) :
    NativeBoundaryPairs (nextFrame F A u hbase) odd raw
      ([⟨ℓ₀, y, b₀⟩, ⟨r₀, x, b₁⟩] ++ rest) := by
  have hxnext : raw x = leftPort (nextFrame F A u hbase) 1 :=
    hx.trans (native_marked_index_shift hm F A u hbase 0).2.symm
  have hynext : raw y = leftPort (nextFrame F A u hbase) k := by
    have hs := (native_marked_index_shift hm F A u hbase (k - 1)).2
    rw [show k - 1 + 1 = k by omega] at hs
    exact hy.trans hs.symm
  have hadvance (a b : RawPort) :
      advance k (if odd then oddBoundary k else evenBoundary k) a b →
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) a b := by
    cases odd
    · exact (advance_even_boundary k hk a b).mp
    · exact (advance_odd_boundary k hk a b).mp
  intro p hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl) | hp
  · refine ⟨(0, 1), (⟨k, by omega⟩, 1), ?_, ?_, hadvance _ _ ?_⟩
    · simpa only [specialPort, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, if_false] using hℓ₀
    · simpa only [specialPort, Fin.val_mk, Fin.val_one, Nat.one_ne_zero, if_false] using hynext
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
  · refine ⟨(0, 0), (1, 1), ?_, ?_, hadvance _ _ ?_⟩
    · simpa only [specialPort, Fin.val_zero, if_true] using hr₀
    · simpa only [specialPort, Fin.val_one, Nat.one_ne_zero, if_false] using hxnext
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · obtain ⟨a, b, hs, hf, hpair⟩ := hb p hp
    have hnot : ¬ pair (code a) (code b) (k - 1, 1) (0, 1) := by
      intro hpair'
      have hpx : x ∈ p.walk.support := by
        rcases hpair' with ⟨_, hb'⟩ | ⟨ha', _⟩
        · have hbi : b.1.val = 0 := congrArg Prod.fst hb'
          have hbs : b.2.val = 1 := congrArg Prod.snd hb'
          have hf' : p.finish = x := hinj (hf.trans (by
            simpa only [specialPort, hbi, hbs, Nat.one_ne_zero, if_false] using hx.symm))
          exact hf' ▸ p.walk.end_mem_support
        · have hai : a.1.val = 0 := congrArg Prod.fst ha'
          have has : a.2.val = 1 := congrArg Prod.snd ha'
          have hs' : p.start = x := hinj (hs.trans (by
            simpa only [specialPort, hai, has, Nat.one_ne_zero, if_false] using hx.symm))
          exact hs' ▸ p.walk.start_mem_support
      exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2
        old.start_mem_support (List.mem_flatMap.mpr ⟨p, hp, hpx⟩)
    refine ⟨shiftPort a, shiftPort b,
      hs.trans (shifted_special_port hm F A u hbase a).symm,
      hf.trans (shifted_special_port hm F A u hbase b).symm, hadvance _ _ ?_⟩
    apply Or.inl
    simpa only [shiftPort, code, previousIndex, Fin.val_succ, Nat.add_sub_cancel] using
      (show 0 < a.1.val + 1 ∧ 0 < b.1.val + 1 ∧
        (if odd then oddBoundary k else evenBoundary k) (code a) (code b) ∧
        ¬ pair (code a) (code b) (k - 1, 1) (0, 1) from
        ⟨by omega, by omega, hpair, hnot⟩)

/-- Advance the two native endpoint templates on the same concrete
simultaneous state. The old orders exchange, so the next primary uses the
old opposite template and the next opposite uses the old primary template.
No next endpoint law, route factorization or half partition is assumed. -/
theorem native_actual_simultaneous_boundary_state {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (odd₀ odd₁ : Bool) (raw : V → Configuration m) (hinj : Function.Injective raw)
    {priorBase base ℓ z r x y₀ y₁ ℓ₀ r₀ ℓ₁ r₁ : V}
    (prior : G.Walk priorBase priorBase)
    (d : G.Walk ℓ z) (cross : G.Walk r x) (jointrest : List (Piece G))
    (old₀ : G.Walk ℓ y₀) (primaryrest : List (Piece G))
    (old₁ : G.Walk x y₁) (oppositerest : List (Piece G))
    (oldK oldH : Finset (Sym2 V))
    (hprior : ActualTwoOrderPartitions prior oldK oldH
      (⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest)
      (⟨ℓ, y₀, old₀⟩ :: primaryrest) (⟨x, y₁, old₁⟩ :: oppositerest))
    (hpriorSeam : s(r, ℓ) ∈ oldK)
    (hℓ : raw ℓ = leftPort F₀ 0) (hx : raw x = leftPort F₁ 0)
    (hy₀ : raw y₀ = leftPort F₀ (k - 1)) (hy₁ : raw y₁ = leftPort F₁ (k - 1))
    (hboundary₀ : NativeBoundaryPairs F₀ odd₀ raw primaryrest)
    (hboundary₁ : NativeBoundaryPairs F₁ odd₁ raw oppositerest)
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (new₀ : G.Walk z ℓ₀) (new₁ : G.Walk r₀ ℓ₁) (new₂ : G.Walk r₁ ℓ)
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hcurrent : ActualCyclePartition c (K ∪ H)
      (⟨z, ℓ₀, new₀⟩ :: ⟨r₀, ℓ₁, new₁⟩ :: ⟨r₁, ℓ, new₂⟩ ::
        ⟨r, x, cross⟩ :: jointrest))
    (hzero₀ : s(ℓ₀, r₀) ∈ K) (hzero₁ : s(ℓ₁, r₁) ∈ H)
    (herase₀ : K.erase s(ℓ₀, r₀) = oldH)
    (herase₁ : H.erase s(ℓ₁, r₁) = oldK)
    (hℓ₀ : raw ℓ₀ = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₀ : raw r₀ = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₁ : raw ℓ₁ = leftPort (nextFrame F₀ A u hbase₀) 0)
    (hr₁ : raw r₁ = rightPort (nextFrame F₀ A u hbase₀) 0) :
    ∃ primary₀ : G.Walk ℓ₀ y₁, ∃ primary₁ : G.Walk r₀ x,
      ∃ opposite₀ : G.Walk ℓ₁ y₀, ∃ opposite₁ : G.Walk r₁ ℓ,
      let joint : List (Piece G) :=
        ⟨ℓ₀, z, new₀.reverse⟩ :: ⟨r₀, ℓ₁, new₁⟩ :: ⟨r₁, ℓ, new₂⟩ ::
          ⟨r, x, cross⟩ :: jointrest
      let primary : List (Piece G) :=
        [⟨ℓ₀, y₁, primary₀⟩, ⟨r₀, x, primary₁⟩] ++ oppositerest
      let opposite : List (Piece G) :=
        [⟨ℓ₁, y₀, opposite₀⟩, ⟨r₁, ℓ, opposite₁⟩] ++ primaryrest
      ActualTwoOrderPartitions c K H joint primary opposite ∧
      NativeBoundaryPairs (nextFrame F₁ A u hbase₁) odd₁ raw primary ∧
      NativeBoundaryPairs (nextFrame F₀ A u hbase₀) odd₀ raw opposite ∧
      s(r₀, ℓ₀) ∈ K ∧
      ∃ hnext : G.Adj r₀ ℓ₀, ∃ tail₀ : G.Walk z y₀, ∃ tail₁ : G.Walk z y₁,
        tail₀.IsPath ∧ tail₁.IsPath ∧
        primary₀ = new₀.reverse.append tail₁ ∧
        opposite₀ = (new₁.reverse.concat hnext).append (new₀.reverse.append tail₀) ∧
        opposite₁ = new₂ := by
  have hn₀ : (old₀.support ++ primaryrest.flatMap fun p => p.walk.support).Nodup :=
    hprior.primary_partition.support.nodup_iff.mpr hprior.cycle.support_nodup
  have hn₁ : (old₁.support ++ oppositerest.flatMap fun p => p.walk.support).Nodup :=
    hprior.opposite_partition.support.nodup_iff.mpr hprior.cycle.support_nodup
  obtain ⟨primary₀, primary₁, opposite₀, opposite₁, hstate, _, _, _, hseam, hprefix⟩ :=
    actual_simultaneous_boundary_advance prior d cross jointrest old₀ primaryrest
      old₁ oppositerest oldK oldH hprior hpriorSeam c hc new₀ new₁ new₂ K H hdisjoint
      hcurrent hzero₀ hzero₁ herase₀ herase₁
  exact ⟨primary₀, primary₁, opposite₀, opposite₁, hstate,
    advanced_native_boundary_pairs hm hk F₁ A u hbase₁ odd₁ raw hinj old₁ oppositerest
      hn₁ hx hy₁ hℓ₀ hr₀ hboundary₁ primary₀ primary₁,
    advanced_native_boundary_pairs hm hk F₀ A u hbase₀ odd₀ raw hinj old₀ primaryrest
      hn₀ hℓ hy₀ hℓ₁ hr₁ hboundary₀ opposite₀ opposite₁,
    hseam, hprefix⟩

#print axioms native_actual_simultaneous_boundary_state

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
