/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Acquisition/GlobalPortFringe
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual maximal physical spine and one terminal probe determine global ports. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.NativeBirthVectorDecoder
import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass

/-! The finite actual source carries its own maximal rays; no acquired height is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeRankedNavigationCompiler (pathCost pathThreshold atomic_navigation)

/-- Length of the actual extreme path in the specified semantic direction. -/
def spineHeight (d : Bool) : Source → Nat
  | .of _ => 0
  | .mul l r => 1 + if d then spineHeight d r else spineHeight d l

/-- Physical a is false and physical b is true; the equivalence is global. -/
def physicalPresence (pi : Bool ≃ Bool) (w : Address) (v : Source) : Bool :=
  decide (readout (w.map pi) v ≠ .absent)

/-- A mathematical quantity of the actual register, not a supplied input. -/
def physicalHeight (pi : Bool ≃ Bool) (v : Source) : Nat := spineHeight (pi false) v

private theorem spine_interval (d : Bool) (v : Source) (s : Nat) :
    readout (List.replicate s d) v ≠ .absent ↔ s ≤ spineHeight d v := by
  induction v generalizing s with
  | of b => cases s <;> cases b <;> simp [readout, spineHeight, List.replicate_succ]
  | mul l r il ir =>
    cases s with
    | zero => simp [readout, spineHeight]
    | succ s =>
      cases d <;> simp only [List.replicate_succ, readout, spineHeight,
        Bool.false_eq_true, ite_false, ite_true]
      · exact (il s).trans (by omega)
      · exact (ir s).trans (by omega)


private theorem atomic_presence (p : Address) (m : Nat) :
    readout p (substitution^[m] (.of true)) ≠ .absent ↔ pathThreshold p ≤ m := by
  have hread := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    p [] (substitution^[m] (.of true))
  simp only [List.append_nil] at hread
  constructor
  · intro hp
    cases hs : subtree p (substitution^[m] (.of true)) with
    | none => rw [hs] at hread; exact False.elim (hp hread)
    | some t => exact ((atomic_navigation p m t).mp hs).choose_spec.1
  · intro hm
    have hc : pathCost p ≤ pathThreshold p := by
      by_cases he : p = []
      · subst p; rfl
      · rw [Geometry.FiniteSourceMass.threshold_last p he]
        exact Nat.le_max_left _ _
    have hs := (atomic_navigation p m (substitution^[m-pathCost p] (.of true))).mpr
      ⟨m-pathCost p, hm, by omega, rfl⟩
    rw [hs] at hread
    rw [hread]
    cases substitution^[m-pathCost p] (.of true) with
    | of b => cases b <;> simp [readout]
    | mul l r => simp [readout]

private theorem left_threshold (s : Nat) :
    pathThreshold (List.replicate s false) = (if s = 0 then 0 else s+1) := by
  induction s with
  | zero => simp [pathThreshold]
  | succ s ih =>
    simp only [List.replicate_succ, pathThreshold, Bool.false_eq_true, ite_false, ih]
    by_cases hs : s = 0 <;> simp [hs] <;> omega

private theorem probe_threshold (s : Nat) (d : Bool) :
    pathThreshold (List.replicate s d ++ [!d,d]) =
      if d then 2*s+3 else s+4 := by
  induction s with
  | zero => cases d <;> simp [pathThreshold]
  | succ s ih =>
    cases d <;> simp only [List.replicate_succ, List.cons_append, pathThreshold,
      Bool.false_eq_true, ite_false, ite_true] at ih ⊢ <;> omega

private theorem atomic_height (m : Nat) (hm : 1 ≤ m) (d : Bool) :
    spineHeight d (substitution^[m] (.of true)) = if d then m/2 else m-1 := by
  have hp := (spine_interval d (substitution^[m] (.of true))
    (spineHeight d (substitution^[m] (.of true)))).mpr (Nat.le_refl _)
  have hb := (atomic_presence _ m).mp hp
  cases d
  · rw [left_threshold _] at hb
    have he : pathThreshold (List.replicate (m-1) false) ≤ m := by
      rw [left_threshold _]
      split_ifs <;> omega
    have low := (spine_interval false (substitution^[m] (.of true)) (m-1)).mp
      ((atomic_presence _ m).mpr he)
    simp only [Bool.false_eq_true, ite_false]
    split_ifs at hb <;> omega
  · rw [NativeBirthVectorDecoder.pathThreshold_allTrue _] at hb
    have he : pathThreshold (List.replicate (m/2) true) ≤ m := by
      rw [NativeBirthVectorDecoder.pathThreshold_allTrue _]; omega
    have low := (spine_interval true (substitution^[m] (.of true)) (m/2)).mp
      ((atomic_presence _ m).mpr he)
    simp only [ite_true]
    omega

private theorem atomic_fringe (m : Nat) (hm : 4 ≤ m) (d : Bool) :
    2 ≤ spineHeight d (substitution^[m] (.of true)) ∧
    spineHeight d (substitution^[m] (.of true)) ≤ m ∧
    (readout (List.replicate (spineHeight d (substitution^[m] (.of true))-2) d ++
      [!d,d]) (substitution^[m] (.of true)) ≠ .absent ↔ d = true) := by
  rw [atomic_height m (by omega) d]
  rw [atomic_presence, probe_threshold]
  cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true, iff_false, iff_true] <;>
    omega

private theorem semantic_fringe (u : Source) (j : Nat) (hj : 2 ≤ j) (d : Bool) :
    let v := substitution^[2*j] u
    let h := spineHeight d v
    2 ≤ h ∧ h ≤ 2*j+u.length-1 ∧
    (readout (List.replicate (h-2) d ++ [!d,d]) v ≠ .absent ↔ d = true) := by
  induction u with
  | of b =>
    cases b
    · have shift : substitution^[2*j] (.of false) = substitution^[2*j+1] (.of true) := by
        rw [Function.iterate_succ_apply]; rfl
      dsimp only
      rw [shift]
      have h := atomic_fringe (2*j+1) (by omega) d
      have eh := atomic_height (2*j+1) (by omega) d
      refine ⟨h.1, ?_, h.2.2⟩
      rw [eh]
      cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true, FreeMagma.length] <;> omega
    · dsimp only
      have h := atomic_fringe (2*j) (by omega) d
      exact ⟨h.1, by simpa only [FreeMagma.length, Nat.add_sub_cancel] using h.2.1, h.2.2⟩
  | mul l r il ir =>
    dsimp only at il ir ⊢
    have pair : substitution^[2*j] (.mul l r) =
        .mul (substitution^[2*j] l) (substitution^[2*j] r) :=
      Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) (2*j) l r
    rw [pair]
    cases d
    · simp only [spineHeight, Bool.false_eq_true, ite_false]
      have hl := l.length_pos
      have hr := r.length_pos
      refine ⟨by omega, ?_, ?_⟩
      · simp only [FreeMagma.length]; omega
      · have he : 1+spineHeight false (substitution^[2*j] l)-2 =
          (spineHeight false (substitution^[2*j] l)-2)+1 := by omega
        rw [he, List.replicate_succ]
        simpa only [List.cons_append, readout, Bool.false_eq_true] using il.2.2
    · simp only [spineHeight, ite_true]
      have hl := l.length_pos
      have hr := r.length_pos
      refine ⟨by omega, ?_, ?_⟩
      · simp only [FreeMagma.length]; omega
      · have he : 1+spineHeight true (substitution^[2*j] r)-2 =
          (spineHeight true (substitution^[2*j] r)-2)+1 := by omega
        rw [he, List.replicate_succ]
        simpa only [List.cons_append, readout, eq_self_iff_true] using ir.2.2

/-- For every original tree and every even epoch at least four, the actual
maximum physical a-spine exists, satisfies both bounds, and its terminal
side probe has either orientation exactly as prescribed by the global map. -/
theorem global_port_fringe (u : Source) (j : Nat) (hj : 2 ≤ j) (pi : Bool ≃ Bool) :
    let v := substitution^[2*j] u
    let h := physicalHeight pi v
    IsGreatest {s : Nat | physicalPresence pi (List.replicate s false) v = true} h ∧
    (∀ s : Nat, physicalPresence pi (List.replicate s false) v = true ↔ s ≤ h) ∧
    2 ≤ h ∧ h ≤ 2*j+u.length-1 ∧
    (physicalPresence pi (List.replicate (h-2) false ++ [true,false]) v = false ↔
      pi false = false) ∧
    (physicalPresence pi (List.replicate (h-2) false ++ [true,false]) v = true ↔
      pi false = true) := by
  dsimp only
  have other : pi true = !(pi false) := by
    have hn : pi true ≠ pi false := pi.injective.ne (by decide)
    cases h : pi false <;> cases k : pi true <;> simp_all
  have interval (s : Nat) :
      physicalPresence pi (List.replicate s false) (substitution^[2*j] u) = true ↔
        s ≤ physicalHeight pi (substitution^[2*j] u) := by
    simpa only [physicalPresence, List.map_replicate, decide_eq_true_eq, physicalHeight] using
      spine_interval (pi false) (substitution^[2*j] u) s
  have fringe := semantic_fringe u j hj (pi false)
  dsimp only at fringe
  refine ⟨⟨(interval _).mpr (Nat.le_refl _), fun s hs => (interval s).mp hs⟩,
    interval, fringe.1, fringe.2.1, ?_, ?_⟩
  · simp only [physicalPresence, List.map_append, List.map_replicate, List.map_cons,
      List.map_nil, other, decide_eq_false_iff_not, not_not]
    have hp := fringe.2.2
    change (readout (List.replicate (spineHeight (pi false) (substitution^[2*j] u)-2)
      (pi false) ++ [!(pi false),pi false]) (substitution^[2*j] u) = .absent) ↔ _
    cases h : pi false <;> simp_all
  · simpa only [physicalPresence, List.map_append, List.map_replicate, List.map_cons,
      List.map_nil, other, decide_eq_true_eq, physicalHeight] using fringe.2.2

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe

#print axioms D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.GlobalPortFringe.global_port_fringe
