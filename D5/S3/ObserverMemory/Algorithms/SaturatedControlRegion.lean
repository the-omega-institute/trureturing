/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedControlRegion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedControlRegion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A maximal attained budget gives a silent source-covering successor region. -/

import D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SaturatedControlRegion

open D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol
open D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound
open D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
attribute [local instance] Classical.propDecidable
universe u v w

set_option maxHeartbeats 1000000 in
-- Maximal cost, actual translation reachability and endpoint roots share the same witness.
/-- Uniformly bounded cumulative communication, without finite state sets,
produces an attained actual state whose entire successor region is silent
and covers every current source. A paid rewrite has internal initial roots
and leaf roots throughout that very region. This is the live supplier for
the original per-fiber persistent-state separation argument. -/
theorem saturated_silent_source_region (d : Nat) (hd : 2 ≤ d)
    (A B : Submodule (ZMod 2) (Source d)) (split : IsCompl A B)
    (hA : 0 < Module.finrank (ZMod 2) A) (hB : 0 < Module.finrank (ZMod 2) B)
    {MA : Type u} {MB : Type v} {Root : Type w}
    (C : Controller split MA MB Root) (K : Nat) (hK : UniformCumulativeBudget C K) :
    ∃ (mstar : C.State) (i : Fin d),
      (∃ a b initialWord, runWord C.step initialWord (C.initial a b) = mstar) ∧
      0 < splitCost split i ∧
      (∀ word f, C.cost (runWord C.step word mstar) f = 0) ∧
      (∀ word f, ∃ word', C.step f (runWord C.step word mstar) =
        runWord C.step word' mstar) ∧
      (∀ z : Source d, ∃ word, C.readout (runWord C.step word mstar) = z) ∧
      (∀ (a : A) (b : B), (C.protocol (.rewrite i)
        (C.rootA (.rewrite i) (C.initA a))).node [] ≠ .inr ()) ∧
      (∀ word, (C.protocol (.rewrite i)
        (C.rootA (.rewrite i) (runWord C.step word mstar).val.1)).node [] = .inr ()) := by
  classical
  have runAppend (left right : List (Action d)) (m : C.State) :
      runWord C.step (left ++ right) m = runWord C.step right (runWord C.step left m) := by
    induction left generalizing m with
    | nil => rfl
    | cons f left ih => exact ih (C.step f m)
  have commAppend (left right : List (Action d)) (m : C.State) :
      Comm C.step C.cost m (left ++ right) =
        Comm C.step C.cost m left + Comm C.step C.cost (runWord C.step left m) right := by
    induction left generalizing m with
    | nil => simp [Comm, runWord]
    | cons f left ih =>
      simp only [List.cons_append, Comm, runWord]
      rw [ih, Nat.add_assoc]
  let attained : Nat → Prop := fun k => ∃ a b word, Comm C.step C.cost (C.initial a b) word = k
  let largest := Nat.findGreatest attained K
  have largestAttained : attained largest :=
    Nat.findGreatest_spec (Nat.zero_le K) (show attained 0 from ⟨0, 0, [], rfl⟩)
  have largestBound (a : A) (b : B) (word : List (Action d)) :
      Comm C.step C.cost (C.initial a b) word ≤ largest := by
    by_contra h
    exact Nat.findGreatest_is_greatest (P := attained) (by omega) (hK a b word)
      ⟨a, b, word, rfl⟩
  obtain ⟨a₀, b₀, initialWord, hmax⟩ := largestAttained
  let mstar := runWord C.step initialWord (C.initial a₀ b₀)
  have silent (word : List (Action d)) (f : Action d) :
      C.cost (runWord C.step word mstar) f = 0 := by
    have hb := largestBound a₀ b₀ (initialWord ++ (word ++ [f]))
    rw [commAppend, hmax, commAppend] at hb
    simp only [Comm, Nat.add_zero] at hb
    change largest + (Comm C.step C.cost mstar word +
      C.cost (runWord C.step word mstar) f) ≤ largest at hb
    omega
  have sourceStep (f : Action d) (m : C.State) :
      C.readout (C.step f m) = f.apply (C.readout m) := by
    have hc := C.correct m.val m.property f (C.trace f m)
      (Classical.choose_spec (C.terminates m.val m.property f))
    change (C.readA (C.toControllerData.commit f m.val (C.trace f m)).1 : Source d) +
      (C.readB (C.toControllerData.commit f m.val (C.trace f m)).2 : Source d) = _
    rw [hc.1, hc.2]
    exact Submodule.projection_add_projection_eq_self split _
  let translations : AddSubgroup (Source d) := {
    carrier := {t | ∀ m : C.State, ∃ word,
      C.readout (runWord C.step word m) = C.readout m + t}
    zero_mem' := by
      intro m
      exact ⟨[], (add_zero _).symm⟩
    add_mem' := by
      intro x y hx hy m
      obtain ⟨left, hl⟩ := hx m
      obtain ⟨right, hr⟩ := hy (runWord C.step left m)
      refine ⟨left ++ right, ?_⟩
      rw [runAppend, hr, hl, add_assoc]
    neg_mem' := by
      intro t ht
      simpa only [ZModModule.neg_eq_self] using ht }
  have dataTranslation (i : Fin d) : ((Pi.single i 1, 0) : Source d) ∈ translations := by
    intro m
    refine ⟨[.dataTranslation i], ?_⟩
    exact sourceStep (.dataTranslation i) m
  have controlTranslation : ((0, 1) : Source d) ∈ translations := by
    intro m
    refine ⟨[.controlTranslation], ?_⟩
    exact sourceStep .controlTranslation m
  let stateBasis : Module.Basis (Fin d ⊕ Unit) (ZMod 2) (Source d) :=
    (Pi.basisFun (ZMod 2) (Fin d)).prod (Module.Basis.singleton Unit (ZMod 2))
  let translationSpace := AddSubgroup.toZModSubmodule 2 translations
  have allTranslations : translationSpace = ⊤ :=
    (Submodule.eq_top_iff_forall_basis_mem stateBasis).2 (by
      intro j
      rcases j with i | j
      · change stateBasis (.inl i) ∈ translations
        simpa [stateBasis, Module.Basis.prod_apply, Pi.basisFun_apply] using dataTranslation i
      · have hj : j = () := Subsingleton.elim _ _
        subst j
        change stateBasis (.inr ()) ∈ translations
        simpa [stateBasis, Module.Basis.prod_apply, Module.Basis.singleton_apply]
          using controlTranslation)
  have coverage (z : Source d) : ∃ word, C.readout (runWord C.step word mstar) = z := by
    have ht : z - C.readout mstar ∈ translationSpace := by
      rw [allTranslations]
      exact Submodule.mem_top
    obtain ⟨word, hw⟩ := ht mstar
    exact ⟨word, by rw [hw]; abel⟩
  have suppliers := fixed_split_rewrite_budget d hd A B split hA hB
  obtain ⟨i, hi⟩ := suppliers.2.2.2.1
  have directions := (suppliers.2.2.2.2.2 C K hK).2
  have initialInternal (a : A) (b : B) :
      (C.protocol (.rewrite i) (C.rootA (.rewrite i) (C.initA a))).node [] ≠ .inr () := by
    intro hp
    obtain ⟨n, hn⟩ := Classical.choose_spec (C.terminates
      (C.initial a b).val (C.initial a b).property (.rewrite i))
    change execute answer (C.protocol (.rewrite i) (C.rootA (.rewrite i) (C.initA a))).policy
      n [] (C.initA a, C.initB b) = some (C.trace (.rewrite i) (C.initial a b), ()) at hn
    cases n with
    | zero => simp [execute] at hn
    | succ n =>
      have hp' : (C.protocol (.rewrite i) (C.rootA (.rewrite i) (C.initA a))).policy [] =
          .inr () := hp
      simp only [execute, hp', Option.some.injEq, Prod.mk.injEq] at hn
      have hb := directions a b i
      rw [← hn.1] at hb
      simp only [rightCount, leftCount, List.map_nil, List.sum_nil] at hb
      change 0 < directionDemand (A.projectionOnto B split (Pi.single i 1, 0))
        (controlRestriction B) +
          directionDemand (B.projectionOnto A split.symm (Pi.single i 1, 0))
            (controlRestriction A) at hi
      omega
  have successorLeaf (word : List (Action d)) :
      (C.protocol (.rewrite i) (C.rootA (.rewrite i)
        (runWord C.step word mstar).val.1)).node [] = .inr () := by
    let m := runWord C.step word mstar
    have ht : C.trace (.rewrite i) m = [] := by
      apply List.eq_nil_of_length_eq_zero
      exact silent word (.rewrite i)
    obtain ⟨n, hn⟩ := Classical.choose_spec (C.terminates m.val m.property (.rewrite i))
    change execute answer (C.protocol (.rewrite i) (C.rootA (.rewrite i) m.val.1)).policy
      n [] m.val = some (C.trace (.rewrite i) m, ()) at hn
    rw [ht] at hn
    cases n with
    | zero => simp [execute] at hn
    | succ n =>
      cases hp : (C.protocol (.rewrite i) (C.rootA (.rewrite i) m.val.1)).policy [] with
      | inr l => cases l; exact hp
      | inl q =>
        simp only [execute, hp] at hn
        obtain ⟨⟨s, l⟩, _, he⟩ := Option.map_eq_some_iff.mp hn
        simp at he
  exact ⟨mstar, i, ⟨a₀, b₀, initialWord, rfl⟩, hi, silent,
    fun word f => ⟨word ++ [f], (runAppend word [f] mstar).symm⟩,
    coverage, initialInternal, successorLeaf⟩

#print axioms saturated_silent_source_region

end D5.S3.ObserverMemory.Algorithms.SaturatedControlRegion
