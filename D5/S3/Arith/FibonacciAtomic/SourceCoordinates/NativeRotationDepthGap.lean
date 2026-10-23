/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native single rotations attain complete Fibonacci word and geometry depth ranges. -/

import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap

open GenealogicalFiberTransport (Source substitution composition)
open Geometry.AncestorAreaInstability (T U rotated)
open IntrinsicSubstitutionCoordinates (depth flag Q)
open ActualLeafHistoryRigidity (OutputContext)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open D5.S3.Combinatorics.Partitions.PaddedWordPartition (G)

/-- A genuine ordered associativity step in one native single-hole context. -/
def ContextRotation (C : OutputContext) (s t : Source) : Prop :=
  ∃ a b c : Source,
    s = C.plug (.mul (.mul a b) c) ∧ t = C.plug (.mul a (.mul b c))

/-- Undirected contextual associativity on actual sources, with ordinary graph distance. -/
def rotationGraph : SimpleGraph Source where
  Adj s t := s ≠ t ∧ ∃ C : OutputContext, ContextRotation C s t ∨ ContextRotation C t s
  symm := ⟨by rintro s t ⟨hne, C, h⟩; exact ⟨hne.symm, C, h.symm⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

/-- The unchanged right siblings place the three-leaf rotation at the leftmost address. -/
def leftContext : ℕ → OutputContext
  | 0 => .hole
  | k+1 => .left (leftContext k) (T (k+2))

private theorem context_spec (k : ℕ) :
    (leftContext k).plug (T 3) = T (k+3) ∧
    (leftContext k).plug (U 3) = rotated k ∧
    (leftContext k).holeAddress = List.replicate k false := by
  induction k with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ k ih =>
    have recurrence :=
      (SourceTransportCentralizer.source_transport_centralizer.1 (T (k+2))).mpr ⟨k+2,rfl⟩
    have hr : T (k+1+3) = .mul (T (k+3)) (T (k+2)) := by
      simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using recurrence
    exact ⟨by simpa only [leftContext, OutputContext.plug, ih.1] using hr.symm,
      by simp only [leftContext, OutputContext.plug, ih.2.1, rotated],
      by simp only [leftContext, OutputContext.holeAddress, ih.2.2, List.replicate_succ]⟩

theorem iterate_length (p : Source) (k : ℕ) :
    (substitution^[k] p).length =
      Nat.fib (k+1) * (composition p).1 + Nat.fib (k+2) * (composition p).2 := by
  induction k generalizing p with
  | zero => simpa using (Observer.ActualObserverAbsorbingNormalization.composition_total p).symm
  | succ k ih =>
    have h := (GenealogicalFiberTransport.fiberMap (composition p) 1 ⟨p,rfl⟩).property
    change composition (substitution p) = GraftAffineClosure.step (composition p) at h
    rw [Function.iterate_succ_apply, ih, h]
    simp only [GraftAffineClosure.step]
    rw [Nat.fib_add_two (n := k+1)]
    ring

private theorem length_lower (p : Source) (k : ℕ) :
    Nat.fib (k+1) ≤ (substitution^[k] p).length := by
  have ht := Observer.ActualObserverAbsorbingNormalization.composition_total p
  have hp := p.length_pos
  have hm := Nat.fib_mono (show k+1 ≤ k+2 by omega)
  rw [iterate_length]
  calc
    Nat.fib (k+1) ≤ Nat.fib (k+1) * ((composition p).1 + (composition p).2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ Nat.fib (k+1) * (composition p).1 + Nat.fib (k+2) * (composition p).2 := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) _

private theorem full_length_bound (n : ℕ) (hn : 3 ≤ n) (t : Source)
    (ht : t.length = Nat.fib (n + 1)) : depth t ≤ n := by
  have hroot := (IntrinsicSubstitutionCoordinates.intrinsic_coordinates t).2.2.1
  have hlow := length_lower (IntrinsicSubstitutionCoordinates.root t) (depth t)
  rw [hroot, ht] at hlow
  by_contra h
  have hlt : Nat.fib (n+1) < Nat.fib (depth t+1) :=
    (Nat.fib_lt_fib (by omega : 2 ≤ n+1)).mpr (by omega)
  omega

private theorem forward_Q (t : Source) (j : ℕ) :
    Q (substitution^[j] t) = (depth t + j, flag t) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero, Q]
  | succ j ih =>
    rw [Function.iterate_succ_apply',
      IntrinsicSubstitutionCoordinates.all_source_coordinate_law.2.1]
    have hd := congrArg Prod.fst ih
    have hf := congrArg Prod.snd ih
    change depth (substitution^[j] t) = depth t+j at hd
    change flag (substitution^[j] t) = flag t at hf
    rw [hd,hf]
    rfl

private theorem forward_word (s t : Source) (hw : wd s = wd t) (j : ℕ) :
    wd (substitution^[j] s) = wd (substitution^[j] t) := by
  induction j with
  | zero => exact hw
  | succ j ih =>
    simp only [Function.iterate_succ_apply',
      Geometry.GeometryEntranceRatio.wd_substitution, ih]

/-- All native single-edge witnesses, all common forward iterates, and both complete fiber extrema. -/
theorem native_rotation_depth_gap :
    (∀ n : ℕ, 3 ≤ n →
      (leftContext (n-3)).holeAddress = List.replicate (n-3) false ∧
      (leftContext (n-3)).plug (T 3) = T n ∧
      (leftContext (n-3)).plug (U 3) = U n ∧
      ContextRotation (leftContext (n-3)) (T n) (U n) ∧
      rotationGraph.Adj (T n) (U n) ∧ rotationGraph.dist (T n) (U n) = 1 ∧
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = Nat.fib (n+1) ∧ Q (T n) = (n,true) ∧ Q (U n) = (0,false) ∧
      (∀ j : ℕ, wd (substitution^[j] (T n)) = wd (substitution^[j] (U n)) ∧
        G (wd (substitution^[j] (T n))) = G (wd (substitution^[j] (U n))) ∧
        depth (substitution^[j] (T n)) = n+j ∧ depth (substitution^[j] (U n)) = j) ∧
      (∀ t : Source, wd t = wd (T n) → 0 ≤ depth t ∧ depth t ≤ n) ∧
      (∀ t : Source, G (wd t) = G (wd (T n)) → 0 ≤ depth t ∧ depth t ≤ n) ∧
      depth (T n) = n ∧ depth (U n) = 0) ∧
    (¬ ∃ A : ℝ, ∀ s t : Source, wd s = wd t → rotationGraph.Reachable s t →
      |(depth s : ℝ) - (depth t : ℝ)| ≤ A * (rotationGraph.dist s t : ℝ)) := by
  have family : ∀ n : ℕ, 3 ≤ n →
      (leftContext (n-3)).holeAddress = List.replicate (n-3) false ∧
      (leftContext (n-3)).plug (T 3) = T n ∧
      (leftContext (n-3)).plug (U 3) = U n ∧
      ContextRotation (leftContext (n-3)) (T n) (U n) ∧
      rotationGraph.Adj (T n) (U n) ∧ rotationGraph.dist (T n) (U n) = 1 ∧
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = Nat.fib (n+1) ∧ Q (T n) = (n,true) ∧ Q (U n) = (0,false) ∧
      (∀ j : ℕ, wd (substitution^[j] (T n)) = wd (substitution^[j] (U n)) ∧
        G (wd (substitution^[j] (T n))) = G (wd (substitution^[j] (U n))) ∧
        depth (substitution^[j] (T n)) = n+j ∧ depth (substitution^[j] (U n)) = j) ∧
      (∀ t : Source, wd t = wd (T n) → 0 ≤ depth t ∧ depth t ≤ n) ∧
      (∀ t : Source, G (wd t) = G (wd (T n)) → 0 ≤ depth t ∧ depth t ≤ n) ∧
      depth (T n) = n ∧ depth (U n) = 0 := by
    intro n hn
    have old := Geometry.AncestorAreaInstability.result.1 n hn
    have ht : depth (T n) = n := old.2.2.2.1
    have hu : depth (U n) = 0 := old.2.2.2.2.1
    have spec := context_spec (n-3)
    have he : n-3+3 = n := by omega
    rw [he] at spec
    have hc : ContextRotation (leftContext (n-3)) (T n) (U n) := by
      refine ⟨.of false,.of true,.of false,?_,?_⟩
      · exact spec.1.symm
      · exact spec.2.1.symm
    have adj : rotationGraph.Adj (T n) (U n) := by
      refine ⟨?_,leftContext (n-3),Or.inl hc⟩
      intro h
      have hd := congrArg depth h
      rw [ht,hu] at hd
      omega
    have hft : flag (T n) = true :=
      (IntrinsicSubstitutionCoordinates.intrinsic_coordinates (T n)).2.2.2.2.mpr (by rw [ht]; rfl)
    have hfu : flag (U n) = false := by
      cases h : flag (U n) with
      | false => rfl
      | true =>
        have hray := (IntrinsicSubstitutionCoordinates.intrinsic_coordinates (U n)).2.2.2.2.mp h
        rw [hu,Function.iterate_zero_apply] at hray
        have hlen := congrArg FreeMagma.length hray
        rw [old.2.2.1, old.2.1] at hlen
        have hmono := Nat.fib_mono (show 4 ≤ n+1 by omega)
        norm_num at hmono hlen
        omega
    refine ⟨spec.2.2,spec.1,spec.2.1,hc,adj,SimpleGraph.dist_eq_one_iff_adj.mpr adj,
      old.1,old.2.1,old.2.2.1.trans old.2.1,?_,?_,?_,?_,?_,ht,hu⟩
    · exact Prod.ext ht hft
    · exact Prod.ext hu hfu
    · intro j
      have hw := forward_word (T n) (U n) old.1 j
      have hd := congrArg Prod.fst (forward_Q (T n) j)
      have hz := congrArg Prod.fst (forward_Q (U n) j)
      exact ⟨hw,congrArg G hw,by simpa only [Q,ht] using hd,
        by simpa only [Q,hu,Nat.zero_add] using hz⟩
    · intro t hw
      refine ⟨Nat.zero_le _,full_length_bound n hn t ?_⟩
      have hs := congrArg List.length hw
      have wordLength (x : Source) : (wd x).length = x.length := by
        simpa only [wd,List.length_cons,FreeSemigroup.length] using FreeMagma.length_toFreeSemigroup x
      rw [wordLength,wordLength,old.2.1] at hs
      exact hs
    · intro t hg
      have hs := Geometry.GeometryEntranceRatio.tree_length (G (wd (T n))) ⟨t,hg⟩
      have htlen := Geometry.GeometryEntranceRatio.tree_length (G (wd (T n))) ⟨T n,rfl⟩
      exact ⟨Nat.zero_le _,
        full_length_bound n hn t (hs.trans (htlen.symm.trans old.2.1))⟩
  refine ⟨family,?_⟩
  rintro ⟨A,hA⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (max 3 A)
  have hthree : 3 ≤ n := by
    have h := (le_max_left (3 : ℝ) A).trans_lt hn
    exact_mod_cast h.le
  have h := family n hthree
  have hadj := h.2.2.2.2.1
  have hd := h.2.2.2.2.2.1
  have hw := h.2.2.2.2.2.2.1
  have htn : depth (T n) = n := (Geometry.AncestorAreaInstability.result.1 n hthree).2.2.2.1
  have hun : depth (U n) = 0 := (Geometry.AncestorAreaInstability.result.1 n hthree).2.2.2.2.1
  have hb := hA (T n) (U n) hw hadj.reachable
  rw [htn,hun,hd,Nat.cast_zero,Nat.cast_one,sub_zero,mul_one,
    abs_of_nonneg (Nat.cast_nonneg n)] at hb
  exact (not_lt_of_ge hb) ((le_max_right (3 : ℝ) A).trans_lt hn)

#print axioms native_rotation_depth_gap

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
