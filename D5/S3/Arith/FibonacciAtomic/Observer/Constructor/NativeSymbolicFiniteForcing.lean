/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicFiniteForcing
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Symbolic finite coordinates of joint native functional solutions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

/-! Symbolic propagation detects exactly the finite original reconstructions of the
joint native leaf-limit solution and forces their values in every solution. -/

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
    · rintro ⟨n, hn⟩; exact ⟨n + 1, hn⟩
  intro i E eq
  have fixed := leafLimit_unique (shift i)
    (extensionStep_limit S (fun _ => False) (fun _ => Omega) (canonical_limit S) i)
  simpa only [extensionStep, ite_false, eq] using fixed

private theorem approximant_below_solution {m : Nat} {S : System m}
    {v : Fin m → CompletionTree} (sat : Satisfies S v) (n : Nat) :
    ∀ i, LeafBelow (approximants S n i) (v i) := by
  induction n with
  | zero => intro i; exact omega_below _
  | succ n ih =>
    intro i
    change LeafBelow (extensionStep S (fun _ => False) (fun _ => Omega)
      (approximants S n) i) (v i)
    simp only [extensionStep, ite_false]
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



/-- Optional equations and reconstructions share the same native syntax. -/
abbrev FunctionalSystem (k m : Nat) := Fin m → Option (CompletionPositiveDriftRegion.Expr k m)

/-- The finite syntax retains grounds, shared parameter atoms and fixed powers. -/
abbrev FiniteExpression (k : Nat) := NativePrefixIdentityReflection.MixedExpr (Fin k)

def finiteValue {k : Nat} (p : Fin k → Nat) (E : FiniteExpression k) : Source :=
  NativePrefixIdentityReflection.eval (fun j => substitution^[p j] (.of true)) E

def satisfies {k m : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, S i = some E → v i = CompletionPositiveDriftRegion.value mode p v E

private def specialize {k m : Nat} (mode : Fin k → Bool) (p : Fin k → Nat) :
    CompletionPositiveDriftRegion.Expr k m → Expr (m + 1)
  | .ground t => .ground t
  | .token j c => if mode j then .ground (substitution^[p j + c] (.of true))
      else .var 0 (Fin.last m)
  | .var a j => .var a j.castSucc
  | .pair A B => .pair (specialize mode p A) (specialize mode p B)

private def nativeSystem {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) : System (m + 1) :=
  Fin.lastCases none (fun i => (S i).map (specialize mode p))

private theorem specialize_value {k m : Nat} (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin (m + 1) → CompletionTree) (last : v (Fin.last m) = Omega)
    (E : CompletionPositiveDriftRegion.Expr k m) :
    value v (specialize mode p E) =
      CompletionPositiveDriftRegion.value mode p (fun i => v i.castSucc) E := by
  induction E with
  | ground t => rfl
  | token j c =>
    cases h : mode j
    · simp only [specialize, h, Bool.false_eq_true, ite_false,
        value, CompletionPositiveDriftRegion.value, Function.iterate_zero_apply, last]
    · simp only [specialize, h, ite_true, value, CompletionPositiveDriftRegion.value]
      exact (iterate_embed (p j + c) (.of true)).symm
  | var a j => rfl
  | pair A B ihA ihB => exact congrArg₂ node ihA ihB

private theorem approximants_last {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) (n : Nat) :
    approximants (nativeSystem S mode p) n (Fin.last m) = Omega := by
  cases n with
  | zero => rfl
  | succ n => simp [approximants, extensionIterate, extensionStep, nativeSystem]

private theorem canonical_last {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) :
    nativeCanonical (nativeSystem S mode p) (Fin.last m) = Omega := by
  apply leafLimit_unique (canonical_limit _ _)
  intro q b
  simp only [approximants_last]
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

/-- The joint native leaf-limit construction starts every unconstrained state at Omega. -/
noncomputable def canonicalSolution {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) (i : Fin m) : CompletionTree :=
  nativeCanonical (nativeSystem S mode p) i.castSucc

private theorem solution_law {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) : satisfies S mode p (canonicalSolution S mode p) := by
  intro i E eq
  have h := canonical_satisfies (nativeSystem S mode p) i.castSucc
    (specialize mode p E) (by simp [nativeSystem, eq])
  exact h.trans (specialize_value mode p _ (canonical_last S mode p) E)

/-- An unsuccessful finite evaluation records an infinite terminal or an unresolved state. -/
def symbolic {k m : Nat} (mode : Fin k → Bool) (v : Fin m → Option (FiniteExpression k)) :
    CompletionPositiveDriftRegion.Expr k m → Option (FiniteExpression k)
  | .ground t => some (.ground t)
  | .token j c => if mode j then some (.residual c j) else none
  | .var a j => (v j).map (NativeSimultaneousPrefixSeparation.shift a)
  | .pair A B => (symbolic mode v A).bind fun A' =>
      (symbolic mode v B).map fun B' => .pair A' B'

private def symbolicStep {k m : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (v : Fin m → Option (FiniteExpression k)) (i : Fin m) : Option (FiniteExpression k) :=
  (S i).bind (symbolic mode v)

/-- Each pass substitutes all finite expressions obtained in the preceding pass. -/
def finitePass {k m : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool) :
    Nat → Fin m → Option (FiniteExpression k)
  | 0 => fun _ => none
  | n + 1 => symbolicStep S mode (finitePass S mode n)

private def Extends {k m : Nat} (v w : Fin m → Option (FiniteExpression k)) : Prop :=
  ∀ i f, v i = some f → w i = some f

private theorem symbolic_extends {k m : Nat} (mode : Fin k → Bool)
    {v w : Fin m → Option (FiniteExpression k)} (h : Extends v w)
    (E : CompletionPositiveDriftRegion.Expr k m) :
    ∀ f, symbolic mode v E = some f → symbolic mode w E = some f := by
  induction E with
  | ground t => exact fun _ hf => hf
  | token j c => exact fun _ hf => hf
  | var a j =>
    intro f hf
    cases hv : v j with
    | none => simp [symbolic, hv] at hf
    | some g => simpa [symbolic, hv, h j g hv] using hf
  | pair A B ihA ihB =>
    intro f hf
    cases hA : symbolic mode v A with
    | none => simp [symbolic, hA] at hf
    | some A' =>
      cases hB : symbolic mode v B with
      | none => simp [symbolic, hA, hB] at hf
      | some B' => simpa [symbolic, hA, hB, ihA A' hA, ihB B' hB] using hf

private theorem pass_extends_step {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (n : Nat) :
    Extends (finitePass S mode n) (finitePass S mode (n + 1)) := by
  induction n with
  | zero => intro i f h; cases h
  | succ n ih =>
    intro i f hf
    cases eq : S i with
    | none => simp [finitePass, symbolicStep, eq] at hf
    | some E =>
      simpa [finitePass, symbolicStep, eq] using
        symbolic_extends mode ih E f (by simpa [finitePass, symbolicStep, eq] using hf)

private theorem pass_extends {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) {n j : Nat} (h : n ≤ j) :
    Extends (finitePass S mode n) (finitePass S mode j) := by
  induction h with
  | refl => intro i f hf; exact hf
  | step hj ih => intro i f hf; exact pass_extends_step S mode _ i f (ih i f hf)

private def passSupport {k m : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (n : Nat) : Finset (Fin m) := Finset.univ.filter fun i => (finitePass S mode n i).isSome

private theorem support_mono {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (n : Nat) : passSupport S mode n ⊆ passSupport S mode (n + 1) := by
  intro i hi
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Option.isSome_iff_exists.mpr ⟨f, pass_extends_step S mode n i f hf⟩⟩

private theorem support_eq_pass {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (n : Nat) (h : passSupport S mode n = passSupport S mode (n + 1)) :
    finitePass S mode n = finitePass S mode (n + 1) := by
  funext i
  cases hi : finitePass S mode n i with
  | some f => exact (pass_extends_step S mode n i f hi).symm
  | none =>
    cases hj : finitePass S mode (n + 1) i with
    | none => rfl
    | some f =>
      have mem : i ∈ passSupport S mode (n + 1) := by simp [passSupport, hj]
      rw [← h] at mem
      simp [passSupport, hi] at mem

private theorem pass_eventually_fixed {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) : ∃ n ≤ m, finitePass S mode n = finitePass S mode (n + 1) := by
  classical
  by_contra h
  push Not at h
  have grow : ∀ n, n ≤ m + 1 → n ≤ (passSupport S mode n).card := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      have prev := ih (by omega)
      have strict : passSupport S mode n ⊂ passSupport S mode (n + 1) :=
        (support_mono S mode n).ssubset_of_ne
          (fun eq => h n (by omega) (support_eq_pass S mode n eq))
      have card := Finset.card_lt_card strict
      omega
  have large := grow (m + 1) le_rfl
  have small := Finset.card_le_card (Finset.subset_univ (passSupport S mode (m + 1)))
  simp only [Finset.card_univ, Fintype.card_fin] at small
  omega

private theorem pass_fixed_after {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) {n : Nat} (fixed : finitePass S mode n = finitePass S mode (n + 1))
    (j : Nat) : finitePass S mode (n+j) = finitePass S mode n := by
  induction j with
  | zero => simp
  | succ j ih =>
    change symbolicStep S mode (finitePass S mode (n+j)) = finitePass S mode n
    rw [ih]
    exact fixed.symm

private theorem pass_bounded {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (n : Nat) : Extends (finitePass S mode n) (finitePass S mode m) := by
  obtain ⟨j, hj, fixed⟩ := pass_eventually_fixed S mode
  by_cases hn : n ≤ m
  · exact pass_extends S mode hn
  · have eqn := pass_fixed_after S mode fixed (n-j)
    have eqm := pass_fixed_after S mode fixed (m-j)
    rw [Nat.add_sub_of_le (by omega)] at eqn
    rw [Nat.add_sub_of_le hj] at eqm
    rw [eqn, eqm]
    intro i f hf; exact hf



private def Realizes {k : Nat} (p : Fin k → Nat) (X : CompletionTree) :
    Option (FiniteExpression k) → Prop
  | none => ¬ IsFinite X
  | some f => X = embed (finiteValue p f)

private theorem realizes_finite {k : Nat} {p : Fin k → Nat} {X : CompletionTree}
    {q : Option (FiniteExpression k)} (h : Realizes p X q) :
    IsFinite X ↔ q.isSome := by
  cases q with
  | none => exact ⟨fun hx => (h hx).elim, fun hh => by cases hh⟩
  | some f => exact ⟨fun _ => rfl, fun _ => ⟨finiteValue p f, h.symm⟩⟩

private theorem symbolic_realizes {k m : Nat} (mode : Fin k → Bool) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) (q : Fin m → Option (FiniteExpression k))
    (h : ∀ i, Realizes p (v i) (q i)) (E : CompletionPositiveDriftRegion.Expr k m) :
    Realizes p (CompletionPositiveDriftRegion.value mode p v E) (symbolic mode q E) := by
  induction E with
  | ground t => rfl
  | token j c =>
    cases hm : mode j
    · simp only [symbolic, hm, Bool.false_eq_true, ite_false,
        CompletionPositiveDriftRegion.value]
      exact CompletionPositiveDriftRegion.omega_not_finite
    · simp only [symbolic, hm, ite_true, CompletionPositiveDriftRegion.value]
      change atomic (p j + c) = embed (substitution^[c] (substitution^[p j] (.of true)))
      rw [← Function.iterate_add_apply, Nat.add_comm c]
      exact iterate_embed (p j + c) (.of true)
  | var a j =>
    cases hj : q j with
    | none =>
      simp only [symbolic, hj, Option.map_none, Realizes,
        CompletionPositiveDriftRegion.value]
      exact fun hf => (show ¬ IsFinite (v j) from
        (by simpa only [hj, Realizes] using h j)) ((finite_iterate_iff a _).mp hf)
    | some f =>
      simp only [symbolic, hj, Option.map_some, Realizes,
        CompletionPositiveDriftRegion.value]
      rw [show v j = embed (finiteValue p f) from (by simpa only [hj, Realizes] using h j), iterate_embed]
      exact congrArg embed (NativeSimultaneousPrefixSeparation.eval_shift a _ f).symm
  | pair A B ihA ihB =>
    cases hA : symbolic mode q A with
    | none =>
      simp only [symbolic, hA, Option.bind_none, Realizes,
        CompletionPositiveDriftRegion.value]
      exact fun hf => (show ¬ IsFinite (CompletionPositiveDriftRegion.value mode p v A)
        from (by simpa only [hA, Realizes, finiteValue] using ihA)) ((finite_node_iff _ _).mp hf).1
    | some f =>
      cases hB : symbolic mode q B with
      | none =>
        simp only [symbolic, hA, hB, Option.bind_some, Option.map_none, Realizes,
          CompletionPositiveDriftRegion.value]
        exact fun hf => (show ¬ IsFinite (CompletionPositiveDriftRegion.value mode p v B)
          from (by simpa only [hB, Realizes, finiteValue] using ihB)) ((finite_node_iff _ _).mp hf).2
      | some g =>
        simp only [symbolic, hA, hB, Option.bind_some, Option.map_some, Realizes,
          CompletionPositiveDriftRegion.value]
        exact congrArg₂ node
          (by simpa only [hA, Realizes, finiteValue] using ihA)
          (by simpa only [hB, Realizes, finiteValue] using ihB)

private theorem pass_realizes {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) (n : Nat) (i : Fin m) :
    Realizes p (approximants (nativeSystem S mode p) n i.castSucc)
      (finitePass S mode n i) := by
  induction n generalizing i with
  | zero => exact CompletionPositiveDriftRegion.omega_not_finite
  | succ n ih =>
    cases hi : S i with
    | none =>
      simp only [finitePass, symbolicStep, hi, Option.bind_none]
      change ¬ IsFinite (extensionStep (nativeSystem S mode p) (fun _ => False)
        (fun _ => Omega) (approximants (nativeSystem S mode p) n) i.castSucc)
      simpa [extensionStep, nativeSystem, hi] using CompletionPositiveDriftRegion.omega_not_finite
    | some E =>
      simp only [finitePass, symbolicStep, hi, Option.bind_some]
      change Realizes p (extensionStep (nativeSystem S mode p) (fun _ => False)
        (fun _ => Omega) (approximants (nativeSystem S mode p) n) i.castSucc) _
      simp only [extensionStep, ite_false, nativeSystem, Fin.lastCases_castSucc,
        hi, Option.map_some]
      rw [specialize_value mode p _ (approximants_last S mode p n) E]
      exact symbolic_realizes mode p _ _ ih E

private theorem lift_solution {k m : Nat} {S : FunctionalSystem k m}
    {mode : Fin k → Bool} {p : Fin k → Nat} {v : Fin m → CompletionTree}
    (sat : satisfies S mode p v) :
    Satisfies (nativeSystem S mode p) (Fin.lastCases Omega v) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro E he
    simp [nativeSystem] at he
  · intro E he
    cases eq : S j with
    | none => simp [nativeSystem, eq] at he
    | some F =>
      have ef : specialize mode p F = E := by simpa [nativeSystem, eq] using he
      subst E
      rw [specialize_value mode p _ (by simp) F]
      simpa using sat j F eq

private theorem expression_pass_value {k m : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (p : Fin k → Nat) (E : CompletionPositiveDriftRegion.Expr k m)
    (n : Nat) {f : FiniteExpression k} (hf : symbolic mode (finitePass S mode n) E = some f)
    {v : Fin m → CompletionTree} (sat : satisfies S mode p v) :
    CompletionPositiveDriftRegion.value mode p v E = embed (finiteValue p f) := by
  have real := symbolic_realizes mode p
    (fun j => approximants (nativeSystem S mode p) n j.castSucc)
    (finitePass S mode n) (pass_realizes S mode p n) E
  have eq : value (approximants (nativeSystem S mode p) n) (specialize mode p E) =
      embed (finiteValue p f) := by
    rw [specialize_value mode p _ (approximants_last S mode p n) E]
    simpa only [hf, Realizes] using real
  have below := value_leafBelow (approximant_below_solution (lift_solution sat) n)
    (specialize mode p E)
  rw [eq, specialize_value mode p _ (by simp) E] at below
  simpa using finite_below_eq (finiteValue p f) _ below

/-- Exactly the original reconstructions with successful symbolic finite evaluation. -/
def finiteExpressions {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (R : Fin r → CompletionPositiveDriftRegion.Expr k m) (i : Fin r) :
    Option (FiniteExpression k) := symbolic mode (finitePass S mode m) (R i)

def finiteOriginals {k m r : Nat} (S : FunctionalSystem k m) (mode : Fin k → Bool)
    (R : Fin r → CompletionPositiveDriftRegion.Expr k m) : Finset (Fin r) :=
  Finset.univ.filter fun i => (finiteExpressions S mode R i).isSome

/-- Unbounded finite-original classification and same-parameter whole-system rigidity. -/
theorem symbolic_finite_forcing {k m r : Nat} (S : FunctionalSystem k m)
    (mode : Fin k → Bool) (R : Fin r → CompletionPositiveDriftRegion.Expr k m) :
    (∀ p, satisfies S mode p (canonicalSolution S mode p)) ∧
    ∀ (p : Fin k → Nat) (i : Fin r),
      (IsFinite (CompletionPositiveDriftRegion.value mode p (canonicalSolution S mode p) (R i)) ↔
        i ∈ finiteOriginals S mode R) ∧
      ∀ f, finiteExpressions S mode R i = some f →
        CompletionPositiveDriftRegion.value mode p (canonicalSolution S mode p) (R i) =
          embed (finiteValue p f) ∧
        ∀ v, satisfies S mode p v →
          CompletionPositiveDriftRegion.value mode p v (R i) = embed (finiteValue p f) := by
  refine ⟨solution_law S mode, ?_⟩
  intro p i
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro finite
    have hlim := value_leafLimit (canonical_limit (nativeSystem S mode p))
      (specialize mode p (R i))
    rw [specialize_value mode p _ (canonical_last S mode p) (R i)] at hlim
    obtain ⟨n, hn⟩ := (finite_limit_iff
      (fun n j hj => value_leafBelow
        (extensionIterate_mono (nativeSystem S mode p) _ _ n j hj)
        (specialize mode p (R i))) hlim).mp finite
    change IsFinite (value (approximants (nativeSystem S mode p) n)
      (specialize mode p (R i))) at hn
    rw [specialize_value mode p _ (approximants_last S mode p n) (R i)] at hn
    have real := symbolic_realizes mode p _ _ (pass_realizes S mode p n) (R i)
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp ((realizes_finite real).mp hn)
    have bounded := symbolic_extends mode (pass_bounded S mode n) (R i) f hf
    simp only [finiteOriginals, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Option.isSome_iff_exists.mpr ⟨f, bounded⟩
  · intro hi
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
    exact ⟨finiteValue p f,
      (expression_pass_value S mode p (R i) m hf (solution_law S mode p)).symm⟩
  · intro f hf
    exact ⟨expression_pass_value S mode p (R i) m hf (solution_law S mode p),
      fun v sat => expression_pass_value S mode p (R i) m hf sat⟩

#print axioms symbolic_finite_forcing

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing
