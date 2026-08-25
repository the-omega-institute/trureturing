/- GID: D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/CommutingCompletionExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commuting completions share the all-word kernel, including degenerate types. -/
/- Library-search audit trail (2026-08-25):
   * The required `rg` search found `congruenceKernel`, `readoutRelation`, and
     `predictiveProjection` in the inspected completion modules.
   * `minimal_predictive_completion_quotient` and `predictive_completion_monotone`
     were read in full; neither states an exchange law, so neither is reproved.
   * Pinned Mathlib supplies `Function.Commute.iterate_left` and `iterate_iterate`.
     The Lean skill's two local smart searches found no packaged word-normalization theorem.
   * Repository searches for the declaration names and exchange terms found no prior result. -/

import D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange

open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
open D5.S3.Observer.Separation.CongruenceKernel

/-- Two interfaces are equivalent when they identify exactly the same states. -/
def KernelEquivalent {X O P : Type*} (q : X -> O) (r : X -> P) : Prop :=
  readoutRelation q = readoutRelation r

/-- A Boolean word acts by the first or second generator at each letter. -/
def wordAction {X : Type*} (F G : X -> X) : List Bool -> X -> X
  | [], x => x
  | false :: word, x => F (wordAction F G word x)
  | true :: word, x => G (wordAction F G word x)

/-- The canonical word containing all first-generator letters before all second letters. -/
def normalWord (n m : Nat) : List Bool :=
  List.replicate n false ++ List.replicate m true

/-- The interface that records the readout after every generated word. -/
def generatedReadout {X O : Type*} (F G : X -> X) (q : X -> O) :
    X -> List Bool -> O :=
  fun x word => q (wordAction F G word x)

/-- Pulling the quotient projection back to the original states recovers its kernel. -/
theorem predictive_projection_kernel {X O : Type*} (F : X -> X) (q : X -> O) :
    readoutRelation (predictiveProjection F q) =
      congruenceKernel F (readoutRelation q) := by
  ext pair
  constructor
  · intro hpair
    exact Quotient.exact hpair
  · intro hpair
    exact Quotient.sound hpair
#print axioms predictive_projection_kernel

/-- The canonical normal word acts as the corresponding pair of iterates. -/
theorem normal_word_action {X : Type*} (F G : X -> X) (n m : Nat) :
    wordAction F G (normalWord n m) = (F^[n]) ∘ (G^[m]) := by
  have secondBlock : ∀ k : Nat,
      wordAction F G (List.replicate k true) = G^[k] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        funext x
        simp only [List.replicate_succ, wordAction, ih,
          Function.iterate_succ_apply']
  induction n with
  | zero =>
      rw [normalWord, List.replicate_zero, List.nil_append, secondBlock]
      rfl
  | succ n ih =>
      funext x
      change F (wordAction F G (normalWord n m) x) =
        (F^[Nat.succ n]) ((G^[m]) x)
      rw [ih]
      simp only [Function.comp_apply, Function.iterate_succ_apply']
#print axioms normal_word_action

/-- If the generators commute, every word action has a two-block normal form. -/
theorem word_action_normal_form {X : Type*} (F G : X -> X)
    (hcomm : Function.Commute F G) (word : List Bool) :
    ∃ n m : Nat, wordAction F G word = (F^[n]) ∘ (G^[m]) := by
  induction word with
  | nil =>
      exact ⟨0, 0, rfl⟩
  | cons letter word ih =>
      obtain ⟨n, m, hword⟩ := ih
      cases letter with
      | false =>
          refine ⟨n + 1, m, ?_⟩
          funext x
          simp only [wordAction, hword, Function.comp_apply,
            Function.iterate_succ_apply']
      | true =>
          refine ⟨n, m + 1, ?_⟩
          funext x
          simp only [wordAction, hword, Function.comp_apply,
            Function.iterate_succ_apply']
          exact ((hcomm.iterate_left n).eq ((G^[m]) x)).symm
#print axioms word_action_normal_form

/-- Completion by commuting generators exchanges order and equals completion by all words. -/
theorem commuting_completion_exchange {X O : Type*}
    (F G : X -> X) (q : X -> O) (hcomm : Function.Commute F G) :
    KernelEquivalent
        (predictiveProjection F (predictiveProjection G q))
        (predictiveProjection G (predictiveProjection F q)) ∧
      KernelEquivalent
        (predictiveProjection G (predictiveProjection F q))
        (generatedReadout F G q) := by
  unfold KernelEquivalent
  simp only [predictive_projection_kernel]
  constructor
  · ext pair
    constructor
    · intro hpair m n
      change q ((F^[n]) ((G^[m]) pair.1)) =
        q ((F^[n]) ((G^[m]) pair.2))
      have hnm := hpair n m
      change q ((G^[m]) ((F^[n]) pair.1)) =
        q ((G^[m]) ((F^[n]) pair.2)) at hnm
      calc
        q ((F^[n]) ((G^[m]) pair.1)) =
            q ((G^[m]) ((F^[n]) pair.1)) :=
          congrArg q ((hcomm.iterate_iterate n m).eq pair.1)
        _ = q ((G^[m]) ((F^[n]) pair.2)) := hnm
        _ = q ((F^[n]) ((G^[m]) pair.2)) :=
          congrArg q ((hcomm.iterate_iterate n m).eq pair.2).symm
    · intro hpair n m
      change q ((G^[m]) ((F^[n]) pair.1)) =
        q ((G^[m]) ((F^[n]) pair.2))
      have hmn := hpair m n
      change q ((F^[n]) ((G^[m]) pair.1)) =
        q ((F^[n]) ((G^[m]) pair.2)) at hmn
      calc
        q ((G^[m]) ((F^[n]) pair.1)) =
            q ((F^[n]) ((G^[m]) pair.1)) :=
          congrArg q ((hcomm.iterate_iterate n m).eq pair.1).symm
        _ = q ((F^[n]) ((G^[m]) pair.2)) := hmn
        _ = q ((G^[m]) ((F^[n]) pair.2)) :=
          congrArg q ((hcomm.iterate_iterate n m).eq pair.2)
  · ext pair
    constructor
    · intro hpair
      apply funext
      intro word
      obtain ⟨n, m, hword⟩ := word_action_normal_form F G hcomm word
      have hmn := hpair m n
      change q ((F^[n]) ((G^[m]) pair.1)) =
        q ((F^[n]) ((G^[m]) pair.2)) at hmn
      simpa only [generatedReadout, hword, Function.comp_apply] using hmn
    · intro hpair m n
      change q ((F^[n]) ((G^[m]) pair.1)) =
        q ((F^[n]) ((G^[m]) pair.2))
      have hnormal := congrFun hpair (normalWord n m)
      simpa only [generatedReadout, normal_word_action, Function.comp_apply] using hnormal
#print axioms commuting_completion_exchange

/-- Four states suffice to show that the commutativity premise cannot be deleted. -/
inductive FourState
  | a
  | b
  | c
  | d

def counterexampleF : FourState -> FourState
  | .a => .a
  | .b => .a
  | .c => .d
  | .d => .d

def counterexampleG : FourState -> FourState
  | .a => .b
  | .b => .c
  | .c => .c
  | .d => .d

def counterexampleReadout : FourState -> Bool
  | .d => true
  | _ => false

/-- Without commutativity, the two completion orders can have different kernels. -/
theorem commutativity_hypothesis_is_necessary :
    ¬ Function.Commute counterexampleF counterexampleG ∧
      ¬ KernelEquivalent
        (predictiveProjection counterexampleF
          (predictiveProjection counterexampleG counterexampleReadout))
        (predictiveProjection counterexampleG
          (predictiveProjection counterexampleF counterexampleReadout)) := by
  constructor
  · intro hcomm
    have hbad := hcomm FourState.a
    exact FourState.noConfusion hbad
  · unfold KernelEquivalent
    simp only [predictive_projection_kernel]
    intro hequal
    have hFa : ∀ n : Nat, (counterexampleF^[n]) FourState.a = FourState.a := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          rfl
    have hFb : ∀ n : Nat,
        (counterexampleF^[Nat.succ n]) FourState.b = FourState.a := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          rfl
    have hGpreserves : ∀ x : FourState,
        counterexampleReadout x = false ->
          counterexampleReadout (counterexampleG x) = false := by
      intro x hx
      cases x <;> simp [counterexampleReadout, counterexampleG] at hx ⊢
    have hGfalse : ∀ (m : Nat) (x : FourState),
        counterexampleReadout x = false ->
          counterexampleReadout ((counterexampleG^[m]) x) = false := by
      intro m
      induction m with
      | zero =>
          intro x hx
          exact hx
      | succ m ih =>
          intro x hx
          rw [Function.iterate_succ_apply']
          exact hGpreserves _ (ih x hx)
    have hfirst :
        (FourState.a, FourState.b) ∈
          congruenceKernel counterexampleF
            (congruenceKernel counterexampleG
              (readoutRelation counterexampleReadout)) := by
      intro n m
      change counterexampleReadout
          ((counterexampleG^[m]) ((counterexampleF^[n]) FourState.a)) =
        counterexampleReadout
          ((counterexampleG^[m]) ((counterexampleF^[n]) FourState.b))
      cases n with
      | zero =>
          simp only [Function.iterate_zero_apply]
          rw [hGfalse m FourState.a rfl, hGfalse m FourState.b rfl]
      | succ n =>
          rw [hFa (Nat.succ n), hFb n]
    have hsecond :
        (FourState.a, FourState.b) ∈
          congruenceKernel counterexampleG
            (congruenceKernel counterexampleF
              (readoutRelation counterexampleReadout)) := by
      rw [← hequal]
      exact hfirst
    have hbad := hsecond 1 1
    change false = true at hbad
    exact Bool.noConfusion hbad
#print axioms commutativity_hypothesis_is_necessary

example {O : Type*} (q : Empty -> O) :
    KernelEquivalent
        (predictiveProjection id (predictiveProjection id q))
        (predictiveProjection id (predictiveProjection id q)) ∧
      KernelEquivalent
        (predictiveProjection id (predictiveProjection id q))
        (generatedReadout id id q) := by
  exact commuting_completion_exchange id id q (by intro x; exact Empty.elim x)

example (q : PUnit -> Bool) :
    KernelEquivalent
        (predictiveProjection id (predictiveProjection id q))
        (predictiveProjection id (predictiveProjection id q)) ∧
      KernelEquivalent
        (predictiveProjection id (predictiveProjection id q))
        (generatedReadout id id q) := by
  exact commuting_completion_exchange id id q (by intro _; rfl)

example {X O : Type*} (q : X -> O) (c : X) :
    KernelEquivalent
        (predictiveProjection (fun _ => c) (predictiveProjection (fun _ => c) q))
        (predictiveProjection (fun _ => c) (predictiveProjection (fun _ => c) q)) ∧
      KernelEquivalent
        (predictiveProjection (fun _ => c) (predictiveProjection (fun _ => c) q))
        (generatedReadout (fun _ => c) (fun _ => c) q) := by
  exact commuting_completion_exchange (fun _ => c) (fun _ => c) q (by intro _; rfl)

example {X : Type*} (F G : X -> X) :
    wordAction F G (normalWord 0 0) = id := by
  simpa using normal_word_action F G 0 0

end D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
