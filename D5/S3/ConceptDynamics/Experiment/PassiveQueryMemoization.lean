/- GID: D5/S3/ConceptDynamics/Experiment/PassiveQueryMemoization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/PassiveQueryMemoization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform dependent query memoization preserves actual supports and completed history kernels. -/

import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization

attribute [local instance] Classical.decEq

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

universe u v w
variable {W : Type u} {Q : Type v} {Y : Q → Type w}

/-- Cache hits select the original response continuation; misses retain the
original query and cache its dependent answer in every continuation. -/
noncomputable def memo (T : PassiveProtocol Q Y) (K : (q : Q) → Option (Y q)) :
    PassiveProtocol Q Y := by
  classical
  exact match T with
  | .stop => .stop
  | .query q next => match K q with
    | some y => memo (next y) K
    | none => .query q (fun y => memo (next y) (Function.update K q (some y)))

/-- Empty-cache memoization is selected from the original tree alone. Actual
paid histories retain exactly its query support, with one charge per address,
and induce exactly the same partition by completed histories. -/
theorem result (T : PassiveProtocol Q Y) (read : (q : Q) → W → Y q) :
    (∀ x : W,
      (runPassiveProtocol read (memo T (fun _ => none)) x).Sublist
        (runPassiveProtocol read T x) ∧
      ((runPassiveProtocol read (memo T (fun _ => none)) x).map Sigma.fst).Nodup ∧
      ((runPassiveProtocol read (memo T (fun _ => none)) x).map Sigma.fst).toFinset =
        ((runPassiveProtocol read T x).map Sigma.fst).toFinset ∧
      (runPassiveProtocol read (memo T (fun _ => none)) x).length =
        ((runPassiveProtocol read T x).map Sigma.fst).toFinset.card) ∧
    (∀ x y : W,
      runPassiveProtocol read (memo T (fun _ => none)) x =
        runPassiveProtocol read (memo T (fun _ => none)) y ↔
      runPassiveProtocol read T x = runPassiveProtocol read T y) := by
  classical
  have simulation : ∀ (p : PassiveProtocol Q Y) (K : (q : Q) → Option (Y q)) (x : W),
      (∀ q y, K q = some y → read q x = y) →
      (runPassiveProtocol read (memo p K) x).Sublist (runPassiveProtocol read p x) ∧
      ((runPassiveProtocol read (memo p K) x).map Sigma.fst).Nodup ∧
      (∀ q ∈ (runPassiveProtocol read (memo p K) x).map Sigma.fst, K q = none) ∧
      (∀ q ∈ (runPassiveProtocol read p x).map Sigma.fst,
        K q ≠ none ∨ q ∈ (runPassiveProtocol read (memo p K) x).map Sigma.fst) := by
    intro p
    induction p with
    | stop => intro K x _; simp [memo, runPassiveProtocol]
    | query q next ih =>
      intro K x coherent
      cases hk : K q with
      | some y =>
        have hy : read q x = y := coherent q y hk
        obtain ⟨hs, hn, hf, hc⟩ := ih y K x coherent
        simp only [memo, hk, runPassiveProtocol, hy, List.map_cons]
        refine ⟨hs.cons _, hn, hf, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Or.inl (by simp [hk])
        · exact hc a ha
      | none =>
        let K' := Function.update K q (some (read q x))
        have coherent' : ∀ a y, K' a = some y → read a x = y := by
          intro a y ha
          by_cases he : a = q
          · subst a; simpa [K'] using ha
          · exact coherent a y (by simpa [K', Function.update_of_ne he] using ha)
        obtain ⟨hs, hn, hf, hc⟩ := ih (read q x) K' x coherent'
        have fresh : q ∉ (runPassiveProtocol read (memo (next (read q x)) K') x).map Sigma.fst := by
          intro hq
          have := hf q hq
          simp [K'] at this
        simp only [memo, hk, runPassiveProtocol, List.map_cons]
        change (Sigma.mk q (read q x) :: runPassiveProtocol read (memo (next (read q x)) K') x).Sublist _ ∧ _
        refine ⟨hs.cons_cons _, List.nodup_cons.mpr ⟨fresh, hn⟩, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hk
          · have he : a ≠ q := by
              intro he
              subst a
              exact fresh ha
            simpa [K', Function.update_of_ne he] using hf a ha
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr (List.mem_cons_self ..)
          · rcases hc a ha with hcache | hpaid
            · by_cases he : a = q
              · exact Or.inr (List.mem_cons.mpr (Or.inl he))
              · exact Or.inl (by simpa [K', Function.update_of_ne he] using hcache)
            · exact Or.inr (List.mem_cons_of_mem _ hpaid)
  have actual : ∀ (p : PassiveProtocol Q Y) (x : W),
      ∀ a ∈ runPassiveProtocol read p x, read a.1 x = a.2 := by
    intro p x
    exact (execute_transfer read (treePolicy p (fun _ => ())) _ _ _ _ _
      (tree_execution read p (fun _ => ()) x)).1
  have replay : ∀ (p : PassiveProtocol Q Y) (x y : W),
      (∀ q ∈ (runPassiveProtocol read p x).map Sigma.fst, read q y = read q x) →
      runPassiveProtocol read p x = runPassiveProtocol read p y := by
    intro p x y agree
    let d : Hist Y → Unit := fun _ => ()
    have ex := tree_execution read p d x
    have ey := tree_execution read p d y
    have moved := (execute_transfer read (treePolicy p d) _ _ _ _ _ ex).2 y (by
      intro a ha
      rw [agree a.1 (List.mem_map.mpr ⟨a, ha, rfl⟩)]
      exact actual p x a ha)
    let nx := (runPassiveProtocol read p x).length + 1
    let ny := (runPassiveProtocol read p y).length + 1
    have mx := execute_mono read (treePolicy p d) nx (max nx ny) _ _ _ _
      (le_max_left _ _) moved
    have my := execute_mono read (treePolicy p d) ny (max nx ny) _ _ _ _
      (le_max_right _ _) ey
    exact congrArg Prod.fst (Option.some.inj (mx.symm.trans my))
  have agreement : ∀ (p : PassiveProtocol Q Y) (x y : W),
      runPassiveProtocol read p x = runPassiveProtocol read p y →
      ∀ q ∈ (runPassiveProtocol read p x).map Sigma.fst, read q y = read q x := by
    intro p x y he q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact (actual p y a (he ▸ ha)).trans (actual p x a ha).symm
  have sim := fun x => simulation T (fun _ => none) x (by simp)
  have supports : ∀ x : W,
      ((runPassiveProtocol read (memo T (fun _ => none)) x).map Sigma.fst).toFinset =
        ((runPassiveProtocol read T x).map Sigma.fst).toFinset := by
    intro x
    ext q
    simp only [List.mem_toFinset]
    constructor
    · intro hq
      exact ((sim x).1.map Sigma.fst).subset hq
    · intro hq
      exact ((sim x).2.2.2 q hq).resolve_left (by simp)
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨(sim x).1, (sim x).2.1, supports x, ?_⟩
    rw [← supports x, List.toFinset_card_of_nodup (sim x).2.1, List.length_map]
  · intro x y
    constructor
    · intro he
      apply replay T x y
      intro q hq
      apply agreement (memo T (fun _ => none)) x y he q
      simpa only [List.mem_toFinset] using
        (show q ∈ ((runPassiveProtocol read (memo T (fun _ => none)) x).map Sigma.fst).toFinset from
          (supports x).symm ▸ (List.mem_toFinset.mpr hq))
    · intro he
      apply replay (memo T (fun _ => none)) x y
      intro q hq
      exact agreement T x y he q (((sim x).1.map Sigma.fst).subset hq)

end D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization
