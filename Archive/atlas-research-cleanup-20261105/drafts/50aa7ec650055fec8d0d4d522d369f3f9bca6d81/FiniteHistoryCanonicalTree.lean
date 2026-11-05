/- Task-private integrable source. Canonical destination:
   D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree.lean
   Reuses PassivePolicyNormalization's dependent histories and actual execution.
   No pruning, query suppression, cost axioms, finite-query assumption, or
   a priori common horizon is used. -/
import D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.FiniteHistoryCanonicalTree

attribute [local instance] Classical.propDecidable

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost (boundedTree)

universe u
variable {W : Type u} {Q : Type} {Y : Q → Type} {L : Type}

/-- Actual terminal runs retain their entire trace in a sufficiently unfolded tree. -/
theorem boundedTree_exact (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L) :
    ∀ n h x t l, execute read policy n h x = some (t,l) →
      runPassiveProtocol read (boundedTree policy n h) x = t := by
  intro n
  induction n with
  | zero => simp [execute]
  | succ n ih =>
    intro h x t l hr
    cases hp : policy h with
    | inr a =>
      have he : ([],a) = (t,l) := by simpa only [execute,hp,Option.some.injEq] using hr
      simpa only [boundedTree,hp,runPassiveProtocol] using congrArg Prod.fst he
    | inl q =>
      simp only [execute, hp] at hr
      obtain ⟨⟨s,a⟩,hs,he⟩ := Option.map_eq_some_iff.mp hr
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      simp only [boundedTree, hp, runPassiveProtocol]
      exact congrArg (List.cons ⟨q,read q x⟩) (ih _ _ _ _ hs)

/-- The unfolding has a uniform realized bound supplied by its construction. -/
theorem boundedTree_length_le (read : (q : Q) → W → Y q)
    (policy : Hist Y → Sum Q L) : ∀ n h x,
      (runPassiveProtocol read (boundedTree policy n h) x).length ≤ n := by
  intro n
  induction n with
  | zero => simp [boundedTree, runPassiveProtocol]
  | succ n ih =>
    intro h x
    cases hp : policy h with
    | inr l => simp [boundedTree, hp, runPassiveProtocol]
    | inl q =>
      simpa only [boundedTree, hp, runPassiveProtocol, List.length_cons,
        Nat.succ_le_succ_iff] using ih (h ++ [⟨q,read q x⟩]) x

/-- The terminal action occurs at the actual full history, not a hidden state. -/
theorem execute_endpoint (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L) :
    ∀ n h x t l, execute read policy n h x = some (t,l) →
      policy (h ++ t) = .inr l := by
  intro n
  induction n with
  | zero => simp [execute]
  | succ n ih =>
    intro h x t l hr
    cases hp : policy h with
    | inr a =>
      simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl,rfl⟩
      simpa using hp
    | inl q =>
      simp only [execute, hp] at hr
      obtain ⟨⟨s,a⟩,hs,he⟩ := Option.map_eq_some_iff.mp hr
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      simpa [List.append_assoc] using ih _ _ _ _ hs

/-- Fuel witnesses cannot change the terminal history or label. Consumed below. -/
theorem execute_unique (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L)
    (n m : Nat) (h : Hist Y) (x : W) (t s : Hist Y) (l k : L)
    (ht : execute read policy n h x = some (t,l))
    (hs : execute read policy m h x = some (s,k)) : (t,l) = (s,k) := by
  have ht' := execute_mono read policy n (max n m) h x t l (le_max_left ..) ht
  have hs' := execute_mono read policy m (max n m) h x s k (le_max_right ..) hs
  exact Option.some.inj (ht'.symm.trans hs')

/-- At a realized terminal history, consistency is exactly realizing that same
complete history and label. No correctness or global termination is assumed. -/
theorem terminal_candidates (read : (q : Q) → W → Y q)
    (policy : Hist Y → Sum Q L) (C : Finset W) (n : Nat) (x : W) (t : Hist Y) (l : L)
    (hr : execute read policy n [] x = some (t,l)) :
    candidates read C t = C.filter (fun y => execute read policy n [] y = some (t,l)) := by
  classical
  ext y
  simp only [candidates, Finset.mem_filter]
  constructor
  · rintro ⟨hy,hc⟩
    exact ⟨hy, (execute_transfer read policy n [] x t l hr).2 y hc⟩
  · rintro ⟨hy,he⟩
    exact ⟨hy, (execute_transfer read policy n [] y t l he).1⟩

/-- Correctness forces a realized stopping consistency set to be a singleton.
This helper is consumed by the general finite bridge below. -/
theorem zero_error_singleton (read : (q : Q) → W → Y q)
    (policy : Hist Y → Sum Q L) (C : Finset W) (decode : L → W)
    (correct : ∀ x ∈ C, ∀ n t l,
      execute read policy n [] x = some (t,l) → decode l = x)
    (x : W) (hx : x ∈ C) (n : Nat) (t : Hist Y) (l : L)
    (hr : execute read policy n [] x = some (t,l)) : candidates read C t = {x} := by
  classical
  rw [terminal_candidates read policy C n x t l hr]
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hy,he⟩
    exact (correct y hy n t l he).symm.trans (correct x hx n t l hr)
  · rintro rfl
    exact ⟨hx,hr⟩

/-- Every pointwise terminating deterministic history policy on finite candidates
has an unpruned canonical tree with every actual query, response, output, and
weighted observation cost preserved. The common fuel is derived, not imposed.
Impossible histories and states outside C need not terminate. -/
theorem finite_history_canonical_tree (read : (q : Q) → W → Y q)
    (policy : Hist Y → Sum Q L) (C : Finset W)
    (terminates : ∀ x ∈ C, ∃ n t l, execute read policy n [] x = some (t,l)) :
    ∃ N : Nat, ∀ n ≥ N,
      let tree := boundedTree policy n []
      (∀ x, (runPassiveProtocol read tree x).length ≤ n) ∧
      (∀ x ∈ C, ∀ m t l, execute read policy m [] x = some (t,l) →
        runPassiveProtocol read tree x = t ∧
        (runPassiveProtocol read tree x).length = t.length ∧
        policy (runPassiveProtocol read tree x) = .inr l ∧
        candidates read C (runPassiveProtocol read tree x) =
          C.filter (fun y => execute read policy m [] y = some (t,l))) ∧
      (∀ (tr : W → Hist Y) (lab : W → L),
        (∀ x ∈ C, ∃ m, execute read policy m [] x = some (tr x,lab x)) →
        ∀ μ : W → ℚ,
          (∑ x ∈ C, μ x * (runPassiveProtocol read tree x).length) =
            ∑ x ∈ C, μ x * (tr x).length) ∧
      (∀ decode : L → W,
        (∀ x ∈ C, ∀ m t l, execute read policy m [] x = some (t,l) → decode l = x) →
        (∀ x ∈ C, candidates read C (runPassiveProtocol read tree x) = {x}) ∧
        (∀ x ∈ C, ∀ y ∈ C,
          runPassiveProtocol read tree x = runPassiveProtocol read tree y → x = y)) := by
  classical
  choose fuel trace label hrun using fun x : C => terminates x.val x.property
  let N := C.attach.sup fuel
  have bounded (x : C) :
      execute read policy N [] x.val = some (trace x,label x) :=
    execute_mono read policy (fuel x) N [] x.val (trace x) (label x)
      (Finset.le_sup (f := fuel) (Finset.mem_attach C x)) (hrun x)
  refine ⟨N, ?_⟩
  intro n hn
  dsimp only
  have exactRun (x : W) (hx : x ∈ C) (m : Nat) (t : Hist Y) (l : L)
      (hr : execute read policy m [] x = some (t,l)) :
      runPassiveProtocol read (boundedTree policy n []) x = t := by
    let a : C := ⟨x,hx⟩
    have eq := execute_unique read policy N m [] x (trace a) t (label a) l (bounded a) hr
    have runN := execute_mono read policy N n [] x (trace a) (label a) hn (bounded a)
    have ht := boundedTree_exact read policy n [] x (trace a) (label a) runN
    exact ht.trans (congrArg Prod.fst eq)
  refine ⟨boundedTree_length_le read policy n [], ?_, ?_, ?_⟩
  · intro x hx m t l hr
    have ht := exactRun x hx m t l hr
    refine ⟨ht, congrArg List.length ht, ?_, ?_⟩
    · rw [ht]
      simpa using execute_endpoint read policy m [] x t l hr
    · rw [ht]
      exact terminal_candidates read policy C m x t l hr
  · intro tr lab runs μ
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨m,hm⟩ := runs x hx
    rw [exactRun x hx m (tr x) (lab x) hm]
  · intro decode correct
    have singleton (x : W) (hx : x ∈ C) :
        candidates read C (runPassiveProtocol read (boundedTree policy n []) x) = {x} := by
      obtain ⟨m,t,l,hr⟩ := terminates x hx
      rw [exactRun x hx m t l hr]
      exact zero_error_singleton read policy C decode correct x hx m t l hr
    refine ⟨singleton, ?_⟩
    intro x hx y hy he
    have eq : ({x} : Finset W) = {y} := by rw [← singleton x hx, ← singleton y hy, he]
    simpa using eq

set_option pp.proofs false in
#print finite_history_canonical_tree
#print axioms boundedTree_exact
#print axioms boundedTree_length_le
#print axioms execute_endpoint
#print axioms execute_unique
#print axioms terminal_candidates
#print axioms zero_error_singleton
#print axioms finite_history_canonical_tree

end D5.S3.ConceptDynamics.Experiment.FiniteHistoryCanonicalTree
