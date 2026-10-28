/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalEffectivePrefix
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Executable finite prefixes of the original canonical native solution. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicFiniteForcing
import Mathlib.Data.Fintype.Pigeonhole

/-! Finite prefix evaluation and its equality to the native canonical leaf limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalEffectivePrefix

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeFunctionalObstruction
open NativeSymbolicFiniteForcing (FunctionalSystem canonicalSolution)
open NativeDepthPatterns (Pattern decompose)

private def leafPrefix : (d : Nat) → Bool → Pattern d
  | 0, _ => ()
  | _ + 1, b => .inl b

private def omegaPrefix : (d : Nat) → Pattern d
  | 0 => ()
  | d + 1 => .inr (omegaPrefix d, omegaPrefix d)

private def trim : (d : Nat) → Pattern (d+1) → Pattern d
  | 0, _ => ()
  | _d + 1, .inl b => .inl b
  | d + 1, .inr (l, r) => .inr (trim d l, trim d r)

private def pairPrefix : (d : Nat) → Pattern d → Pattern d → Pattern d
  | 0, _, _ => ()
  | d + 1, l, r => .inr (trim d l, trim d r)

private def rhoPrefix : (d : Nat) → Pattern d → Pattern d
  | 0, _ => ()
  | _d + 1, .inl true => .inl false
  | d + 1, .inl false => .inr (leafPrefix d false, leafPrefix d true)
  | d + 1, .inr (l, r) => .inr (rhoPrefix d l, rhoPrefix d r)

private def evalPrefix {m : Nat} (d : Nat) (v : Fin m → Pattern d) : Expr m → Pattern d
  | .ground t => (decompose d t).1
  | .token j _ => Fin.elim0 j
  | .var a j => (rhoPrefix d)^[a] (v j)
  | .pair A B => pairPrefix d (evalPrefix d v A) (evalPrefix d v B)

private def stepPrefix {m : Nat} (S : System m) (d : Nat)
    (v : Fin m → Pattern d) (i : Fin m) : Pattern d :=
  match S i with
  | none => omegaPrefix d
  | some E => evalPrefix d v E

private def passPrefix {m : Nat} (S : System m) (d : Nat) : Nat → Fin m → Pattern d
  | 0 => fun _ => omegaPrefix d
  | n + 1 => stepPrefix S d (passPrefix S d n)

private def patternCount : Nat → Nat
  | 0 => 1
  | d + 1 => 2 + patternCount d * patternCount d

/-- The number of simultaneous prefix states, computed without enumerating them. -/
def prefixBound (m d : Nat) : Nat := patternCount d ^ m

private def runPrefix {m : Nat} (S : System m) (d : Nat) :
    Nat → (Fin m → Pattern d) → (Fin m → Pattern d)
  | 0, v => v
  | fuel + 1, v =>
    let w := stepPrefix S d v
    if w = v then v else runPrefix S d fuel w

/-- Evaluate the original reconstruction after a finite number of finite-state passes.
The depth is inclusive, so the returned pattern has cutoff depth h+1. -/
def prefixProgram {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (R : Fin r → CompletionPositiveDriftRegion.Expr k m)
    (h : Nat) (i : Fin r) : Pattern (h+1) :=
  evalPrefix (h+1)
    (runPrefix (NativeSymbolicFiniteForcing.nativeSystem S mode p) (h+1)
      (prefixBound (m+1) (h+1)) (fun _ => omegaPrefix (h+1))) (NativeSymbolicFiniteForcing.specialize mode p (R i))

private theorem pattern_count (d : Nat) : Fintype.card (Pattern d) = patternCount d := by
  induction d with
  | zero => exact Fintype.card_unit
  | succ d ih =>
    change Fintype.card (Bool ⊕ (Pattern d × Pattern d)) = _
    rw [Fintype.card_sum, Fintype.card_bool, Fintype.card_prod, ih]
    rfl

private theorem prefix_bound_card (m d : Nat) :
    prefixBound m d = Fintype.card (Fin m → Pattern d) := by
  rw [Fintype.card_pi_const, pattern_count]
  rfl

private theorem run_iterate {m : Nat} (S : System m) (d fuel : Nat)
    (v : Fin m → Pattern d) :
    runPrefix S d fuel v = (stepPrefix S d)^[fuel] v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    simp only [runPrefix]
    split_ifs with eq
    · exact (Function.iterate_fixed eq (fuel+1)).symm
    · rw [ih, Function.iterate_succ_apply]

private theorem pass_iterate {m : Nat} (S : System m) (d n : Nat) :
    (stepPrefix S d)^[n] (fun _ => omegaPrefix d) = passPrefix S d n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

private theorem cutoff_leaf (d : Nat) (b : Bool) :
    cutoff d (leaf b) = leafPrefix d b := by cases d <;> rfl

private theorem cutoff_omega (d : Nat) : cutoff d Omega = omegaPrefix d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show Omega = node Omega Omega from omega_node]
    change Sum.inr (cutoff d Omega, cutoff d Omega) = _
    rw [ih]; rfl

private theorem trim_cutoff (d : Nat) (X : CompletionTree) :
    trim d (cutoff (d+1) X) = cutoff d X := by
  induction d generalizing X with
  | zero => rfl
  | succ d ih =>
    induction X using tree_cases with
    | leaf_case b => rfl
    | node_case l r => exact congrArg Sum.inr (congrArg₂ Prod.mk (ih l) (ih r))

private theorem pair_cutoff (d : Nat) (X Y : CompletionTree) :
    pairPrefix d (cutoff d X) (cutoff d Y) = cutoff d (node X Y) := by
  cases d with
  | zero => rfl
  | succ d => exact congrArg Sum.inr (congrArg₂ Prod.mk (trim_cutoff d X) (trim_cutoff d Y))

private theorem rho_cutoff (d : Nat) (X : CompletionTree) :
    rhoPrefix d (cutoff d X) = cutoff d (rho X) := by
  induction d generalizing X with
  | zero => rfl
  | succ d ih =>
    induction X using tree_cases with
    | leaf_case b =>
      cases b
      · rw [rho_beta]
        change Sum.inr (leafPrefix d false, leafPrefix d true) =
          (Sum.inr (cutoff d (leaf false), cutoff d (leaf true)) :
            Bool ⊕ (Pattern d × Pattern d))
        rw [cutoff_leaf, cutoff_leaf]
      · rw [rho_alpha]; rfl
    | node_case l r =>
      rw [rho_node]
      exact congrArg Sum.inr (congrArg₂ Prod.mk (ih l) (ih r))

private theorem iterate_cutoff (d a : Nat) (X : CompletionTree) :
    (rhoPrefix d)^[a] (cutoff d X) = cutoff d (rho^[a] X) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, rho_cutoff]

theorem eval_cutoff {m : Nat} (d : Nat) (v : Fin m → CompletionTree) (E : Expr m) :
    evalPrefix d (fun i => cutoff d (v i)) E = cutoff d (value v E) := by
  induction E with
  | ground t => exact (NativeCompletionPrefixLifting.cutoff_embed d t).symm
  | token j _ => exact Fin.elim0 j
  | var a j => exact iterate_cutoff d a (v j)
  | pair A B ihA ihB =>
    simpa only [evalPrefix, value, CompletionPositiveDriftRegion.value, ihA, ihB] using
      (pair_cutoff d (value v A) (value v B))

private theorem pass_cutoff {m : Nat} (S : System m) (d n : Nat) :
    passPrefix S d n = fun i => cutoff d (NativeSymbolicFiniteForcing.approximants S n i) := by
  induction n with
  | zero => funext i; exact (cutoff_omega d).symm
  | succ n ih =>
    funext i
    simp only [passPrefix, ih, NativeSymbolicFiniteForcing.approximants,
      extensionIterate, extensionStep, ite_false, stepPrefix]
    cases hi : S i with
    | none => exact (cutoff_omega d).symm
    | some E => exact eval_cutoff d _ E

private theorem cutoff_leaves (d : Nat) (X Y : CompletionTree) :
    cutoff d X = cutoff d Y ↔
      ∀ q b, q.length < d → (LeafAt X q b ↔ LeafAt Y q b) := by
  induction d generalizing X Y with
  | zero => simp [cutoff]
  | succ d ih =>
    induction X using tree_cases with
    | leaf_case b =>
      induction Y using tree_cases with
      | leaf_case c =>
        change (Sum.inl b : Bool ⊕ (Pattern d × Pattern d)) = Sum.inl c ↔ _
        rw [Sum.inl.injEq]
        constructor
        · rintro rfl q c h; rfl
        · intro h
          exact ((leafAt_leaf c [] b).mp ((h [] b (by simp)).mp
            ((leafAt_leaf b [] b).mpr ⟨rfl, rfl⟩))).2.symm
      | node_case l r =>
        constructor
        · intro h; cases h
        · intro h
          exact (leafAt_node_nil l r b ((h [] b (by simp)).mp
            ((leafAt_leaf b [] b).mpr ⟨rfl, rfl⟩))).elim
    | node_case l r =>
      induction Y using tree_cases with
      | leaf_case b =>
        constructor
        · intro h; cases h
        · intro h
          exact (leafAt_node_nil l r b ((h [] b (by simp)).mpr
            ((leafAt_leaf b [] b).mpr ⟨rfl, rfl⟩))).elim
      | node_case s t =>
        change Sum.inr (cutoff d l, cutoff d r) = (Sum.inr (cutoff d s, cutoff d t) :
          Bool ⊕ (Pattern d × Pattern d)) ↔ _
        rw [Sum.inr.injEq, Prod.mk.injEq, ih, ih]
        constructor
        · rintro ⟨hl, hr⟩ q b hq
          cases q with
          | nil => exact iff_of_false (leafAt_node_nil _ _ _) (leafAt_node_nil _ _ _)
          | cons c q =>
            rw [leafAt_node_cons, leafAt_node_cons]
            cases c
            · exact hl q b (by simpa using hq)
            · exact hr q b (by simpa using hq)
        · intro h
          constructor
          · intro q b hq; simpa only [leafAt_node_cons, Bool.false_eq_true, ite_false] using
              h (false :: q) b (by simpa using hq)
          · intro q b hq; simpa only [leafAt_node_cons, ite_true] using
              h (true :: q) b (by simpa using hq)

private theorem cutoff_sandwich (d : Nat) {X Y Z : CompletionTree}
    (xy : LeafBelow X Y) (yz : LeafBelow Y Z) (eq : cutoff d X = cutoff d Z) :
    cutoff d X = cutoff d Y := by
  apply (cutoff_leaves d X Y).mpr
  intro q b hq
  exact ⟨xy q b, fun h => ((cutoff_leaves d X Z).mp eq q b hq).mpr (yz q b h)⟩

private theorem pass_interval {m : Nat} (S : System m) (d : Nat)
    {a b c : Nat} (ab : a ≤ b) (bc : b ≤ c)
    (eq : passPrefix S d a = passPrefix S d c) : passPrefix S d a = passPrefix S d b := by
  funext i
  rw [pass_cutoff, pass_cutoff] at eq ⊢
  exact cutoff_sandwich d
    (extensionIterate_mono S (fun _ => False) (fun _ => Omega) a b ab i)
    (extensionIterate_mono S (fun _ => False) (fun _ => Omega) b c bc i) (congrFun eq i)

private theorem pass_fixed {m : Nat} (S : System m) (d : Nat) :
    ∃ n, n ≤ prefixBound m d ∧ passPrefix S d n = passPrefix S d (n+1) := by
  let N := prefixBound m d
  obtain ⟨a, b, ne, eq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (N+1) => passPrefix S d n.val) (by simp [N, prefix_bound_card])
  have one {a b : Fin (N+1)} (lt : a < b)
      (eq : passPrefix S d a.val = passPrefix S d b.val) :
      ∃ n, n ≤ N ∧ passPrefix S d n = passPrefix S d (n+1) :=
    ⟨a.val, by omega, pass_interval S d (by omega) (by omega) eq⟩
  rcases lt_or_gt_of_ne ne with lt | lt
  · exact one lt eq
  · exact one lt eq.symm

private theorem pass_stable {m : Nat} (S : System m) (d : Nat)
    {n : Nat} (eq : passPrefix S d n = passPrefix S d (n+1)) :
    ∀ j, n ≤ j → passPrefix S d j = passPrefix S d n := by
  intro j hj
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction a with
  | zero => simp
  | succ a ih =>
    change stepPrefix S d (passPrefix S d (n+a)) = _
    rw [ih]
    exact eq.symm

private theorem limit_cutoff {m : Nat} (S : System m) (d : Nat) (i : Fin m) :
    passPrefix S d (prefixBound m d) i =
      cutoff d (NativeSymbolicFiniteForcing.nativeCanonical S i) := by
  obtain ⟨n, hn, eq⟩ := pass_fixed S d
  have stable := pass_stable S d eq
  rw [pass_cutoff]
  apply (cutoff_leaves d _ _).mpr
  intro q b hq
  rw [NativeSymbolicFiniteForcing.canonical_limit S i q b]
  constructor
  · intro h; exact ⟨prefixBound m d, h⟩
  · rintro ⟨j, hj⟩
    let z := max j (prefixBound m d)
    have hz : passPrefix S d z = passPrefix S d (prefixBound m d) :=
      (stable z (by dsimp [z]; omega)).trans (stable _ hn).symm
    have heq : cutoff d (NativeSymbolicFiniteForcing.approximants S z i) =
        cutoff d (NativeSymbolicFiniteForcing.approximants S (prefixBound m d) i) := by
      simpa only [pass_cutoff] using congrFun hz i
    exact ((cutoff_leaves d _ _).mp heq q b hq).mp
      (extensionIterate_mono S (fun _ => False) (fun _ => Omega) j z
        (Nat.le_max_left _ _) i q b hj)

/-- Every original residual has a terminating executable prefix equal to the same
native canonical completion, for every supplied parameter and inclusive depth. -/
theorem effective_prefix {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (R : Fin r → CompletionPositiveDriftRegion.Expr k m)
    (h : Nat) (i : Fin r) :
    prefixProgram S mode p R h i = cutoff (h+1)
      (CompletionPositiveDriftRegion.value mode p (canonicalSolution S mode p) (R i)) := by
  unfold prefixProgram
  rw [run_iterate, pass_iterate]
  have lim := funext (limit_cutoff (NativeSymbolicFiniteForcing.nativeSystem S mode p) (h+1))
  rw [lim, eval_cutoff, NativeSymbolicFiniteForcing.specialize_value mode p _
    (NativeSymbolicFiniteForcing.canonical_last S mode p)]
  rfl

#print axioms effective_prefix

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalEffectivePrefix
