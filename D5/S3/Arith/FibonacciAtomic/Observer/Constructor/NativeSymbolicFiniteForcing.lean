/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicFiniteForcing
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Symbolic finite coordinates of joint native functional solutions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing

open GenealogicalFiberTransport (Source substitution)
open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open ActualTreeReadoutAcquisition (Address)
open NativeFunctionalObstruction

private theorem embed_has_leaf (t : Source) : ∃ p b, LeafAt (embed t) p b := by
  induction t with
  | of b => exact ⟨[], b, (leafAt_leaf _ _ _).mpr ⟨rfl, rfl⟩⟩
  | mul s t ihs _ =>
    obtain ⟨p, b, hp⟩ := ihs
    exact ⟨false :: p, b, (leafAt_node_cons _ _ _ _ _).mpr hp⟩

private theorem finite_below_eq (t : Source) (X : CompletionTree)
    (h : LeafBelow (embed t) X) : X = embed t := by
  induction t generalizing X with
  | of b => exact leafBelow_leaf h
  | mul s t ihs iht =>
    induction X using tree_cases with
    | leaf_case b =>
      obtain ⟨p, c, hp⟩ := embed_has_leaf s
      have bad := h (false :: p) c ((leafAt_node_cons _ _ _ _ _).mpr hp)
      exact ((List.cons_ne_nil _ _) ((leafAt_leaf _ _ _).mp bad).1).elim
    | node_case l r =>
      exact congrArg₂ node (ihs l (leafBelow_children h false))
        (iht r (leafBelow_children h true))

private theorem finite_capture (t : Source) {C : Nat → CompletionTree}
    (inc : Increasing C) (q : Address)
    (h : ∀ p b, LeafAt (embed t) p b → ∃ n, LeafAt (C n) (q ++ p) b) :
    ∃ n, ∀ p b, LeafAt (embed t) p b → LeafAt (C n) (q ++ p) b := by
  induction t generalizing q with
  | of b =>
    obtain ⟨n, hn⟩ := h [] b ((leafAt_leaf _ _ _).mpr ⟨rfl, rfl⟩)
    refine ⟨n, ?_⟩
    intro p c hp
    obtain ⟨rfl, rfl⟩ := (leafAt_leaf _ _ _).mp hp
    exact hn
  | mul s t ihs iht =>
    obtain ⟨n, hn⟩ := ihs (q ++ [false]) (by
      intro p b hp
      simpa only [List.append_assoc, List.singleton_append] using
        h (false :: p) b ((leafAt_node_cons _ _ _ _ _).mpr hp))
    obtain ⟨j, hj⟩ := iht (q ++ [true]) (by
      intro p b hp
      simpa only [List.append_assoc, List.singleton_append] using
        h (true :: p) b ((leafAt_node_cons _ _ _ _ _).mpr hp))
    refine ⟨max n j, ?_⟩
    intro p b hp
    cases p with
    | nil => exact (leafAt_node_nil _ _ _ hp).elim
    | cons c p =>
      cases c
      · have hh := inc n (max n j) (Nat.le_max_left _ _) _ b
          (hn p b ((leafAt_node_cons _ _ _ _ _).mp hp))
        simpa only [List.append_assoc, List.singleton_append] using hh
      · have hh := inc j (max n j) (Nat.le_max_right _ _) _ b
          (hj p b ((leafAt_node_cons _ _ _ _ _).mp hp))
        simpa only [List.append_assoc, List.singleton_append] using hh

private theorem finite_limit_iff {C : Nat → CompletionTree} {X : CompletionTree}
    (inc : Increasing C) (lim : LeafLimit C X) :
    IsFinite X ↔ ∃ n, IsFinite (C n) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨n, hn⟩ := finite_capture t inc [] (by
      intro p b hp
      exact (lim p b).mp (ht ▸ hp))
    exact ⟨n, t, (finite_below_eq t (C n) hn).symm⟩
  · rintro ⟨n, t, ht⟩
    exact ⟨t, (finite_below_eq t X (by
      intro p b hp
      exact (lim p b).mpr ⟨n, ht ▸ hp⟩)).symm⟩

private noncomputable def approximants {m : Nat} (S : System m) :=
  extensionIterate S (fun _ => False) (fun _ => Omega)

private noncomputable def nativeCanonical {m : Nat} (S : System m)
    (i : Fin m) : CompletionTree := nativeLimit (fun n => approximants S n i)

private theorem canonical_limit {m : Nat} (S : System m) (i : Fin m) :
    LeafLimit (fun n => approximants S n i) (nativeCanonical S i) :=
  nativeLimit_leaves _ (fun n k h => extensionIterate_mono S _ _ n k h i)

private theorem canonical_satisfies {m : Nat} (S : System m) :
    Satisfies S (nativeCanonical S) := by
  have shift : ∀ i, LeafLimit
      (fun n => extensionStep S (fun _ => False) (fun _ => Omega) (approximants S n) i)
      (nativeCanonical S i) := by
    intro i p b
    rw [canonical_limit S i p b]
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact (omega_no_leaf _ _ hn).elim
      | succ n => exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n+1, hn⟩
  intro i E eq
  have fixed := leafLimit_unique (shift i)
    (extensionStep_limit S (fun _ => False) (fun _ => Omega) (canonical_limit S) i)
  simpa only [extensionStep, if_false, eq] using fixed

private theorem approximant_below_solution {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) (n : Nat) :
    ∀ i, LeafBelow (approximants S n i) (v i) := by
  induction n with
  | zero => intro i; exact omega_below _
  | succ n ih =>
    intro i
    change LeafBelow (extensionStep S (fun _ => False) (fun _ => Omega)
      (approximants S n) i) (v i)
    simp only [extensionStep, if_false]
    cases eq : S i with
    | none => exact omega_below _
    | some E => rw [sat i E eq]; exact value_leafBelow ih E

private theorem finite_node_iff (X Y : CompletionTree) :
    IsFinite (node X Y) ↔ IsFinite X ∧ IsFinite Y := by
  constructor
  · intro h
    exact ⟨finite_subtree [false] h rfl, finite_subtree [true] h rfl⟩
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact ⟨.mul s t, congrArg₂ node hs ht⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing
