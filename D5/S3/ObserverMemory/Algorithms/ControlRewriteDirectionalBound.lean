/- GID: D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Control rewrites have sharp per-execution directional costs. -/

import D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound

open D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
attribute [local instance] Classical.propDecidable
universe u v w x

/-- A rewrite protocol must produce both prescribed new projections on every
actual original input, using only the old local summary and transmitted bits. -/
def RewriteCorrect {A : Type u} {B : Type v} {MA : Type w} {MB : Type x}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (ellA : A →ₗ[ZMod 2] ZMod 2) (ellB : B →ₗ[ZMod 2] ZMod 2)
    (alpha : A) (beta : B) (initA : A → MA) (initB : B → MB)
    (p : EndpointProtocol MA MB A B) : Prop :=
  (∀ a b, ∃ n t, execute answer p.policy n [] (initA a, initB b) = some (t, ())) ∧
  ∀ a b n t, execute answer p.policy n [] (initA a, initB b) = some (t, ()) →
    p.outA (initA a) (bits t) = (ellA a + ellB b) • alpha ∧
    p.outB (initB b) (bits t) = (ellA a + ellB b) • beta

/-- The source directional indicator has a fixed classical decision instance. -/
noncomputable def directionDemand {T : Type u} {U : Type v} [Zero T] [Zero U]
    (column : T) (control : U) : Nat := by
  classical
  exact if column ≠ 0 ∧ control ≠ 0 then 1 else 0

/-- Required bits in both directions, independently of the current input. -/
noncomputable def rewriteCost {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (ellA : A →ₗ[ZMod 2] ZMod 2) (ellB : B →ₗ[ZMod 2] ZMod 2)
    (alpha : A) (beta : B) : Nat := by
  classical
  exact (directionDemand alpha ellB) +
    (directionDemand beta ellA)

/-- The fixed exchange sends the missing right contribution first and the
missing left contribution second. Both outputs use the old summaries. -/
noncomputable def rewriteProtocol {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (ellA : A →ₗ[ZMod 2] ZMod 2) (ellB : B →ₗ[ZMod 2] ZMod 2)
    (alpha : A) (beta : B) : EndpointProtocol A B A B := by
  classical
  let needR := alpha ≠ 0 ∧ ellB ≠ 0
  let needL := beta ≠ 0 ∧ ellA ≠ 0
  exact {
    node := fun h =>
      if needR ∧ h.length = 0 then .inl (.inr (fun b => decide (ellB b = 1)))
      else if needL ∧ h.length = (if needR then 1 else 0) then
        .inl (.inl (fun a => decide (ellA a = 1)))
      else .inr ()
    outA := fun a h =>
      if alpha = 0 then 0 else
        (ellA a + if ellB = 0 then 0 else if h[0]?.getD false then 1 else 0) • alpha
    outB := fun b h =>
      if beta = 0 then 0 else
        (ellB b + if ellA = 0 then 0 else
          if h[if needR then 1 else 0]?.getD false then 1 else 0) • beta }

set_option maxHeartbeats 1000000 in
-- Fuel induction and the four exact exchange branches share one substantive proof.
/-- On every input, every correct sender-local protocol pays each required
direction on that same execution. The fixed exchange attains both bounds.
The public-label and uniqueness clauses justify using raw evaluator histories
without introducing a free query-label channel or a global tree-depth bound. -/
theorem rewrite_directional_sharpness {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (ellA : A →ₗ[ZMod 2] ZMod 2) (ellB : B →ₗ[ZMod 2] ZMod 2)
    (alpha : A) (beta : B) :
    (∀ {MA : Type w} {MB : Type x} (p : EndpointProtocol MA MB A B) a b n t,
      execute answer p.policy n [] (a, b) = some (t, ()) → PublicTrace p [] t) ∧
    (∀ {MA : Type w} {MB : Type x} (p : EndpointProtocol MA MB A B) a b n m t s,
      execute answer p.policy n [] (a, b) = some (t, ()) →
      execute answer p.policy m [] (a, b) = some (s, ()) → t = s) ∧
    (∀ {MA : Type w} {MB : Type x} (initA : A → MA) (initB : B → MB)
      (p : EndpointProtocol MA MB A B), RewriteCorrect ellA ellB alpha beta initA initB p →
      ∀ a b n t, execute answer p.policy n [] (initA a, initB b) = some (t, ()) →
        (directionDemand alpha ellB) ≤ rightCount t ∧
        (directionDemand beta ellA) ≤ leftCount t ∧
        rewriteCost ellA ellB alpha beta ≤ t.length) ∧
    RewriteCorrect ellA ellB alpha beta id id (rewriteProtocol ellA ellB alpha beta) ∧
    (∀ a b, ∃ n t,
      execute answer (rewriteProtocol ellA ellB alpha beta).policy n [] (a, b) =
        some (t, ()) ∧
      rightCount t = (directionDemand alpha ellB) ∧
      leftCount t = (directionDemand beta ellA) ∧
      t.length = rewriteCost ellA ellB alpha beta) := by
  classical
  have labels {MA : Type w} {MB : Type x} (p : EndpointProtocol MA MB A B) : ∀ n h a b t,
      execute answer p.policy n h (a, b) = some (t, ()) → PublicTrace p (bits h) t := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro h a b t hr
      cases hp : p.policy h with
      | inr l =>
        cases l
        simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, _⟩
        exact hp
      | inl q =>
        simp only [execute, hp] at hr
        obtain ⟨⟨s, l⟩, hs, he⟩ := Option.map_eq_some_iff.mp hr
        cases l
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, _⟩
        refine ⟨hp, ?_⟩
        simpa [bits] using ih _ a b s hs
  have unique {MA : Type w} {MB : Type x} (p : EndpointProtocol MA MB A B) : ∀ n m h a b t s,
      execute answer p.policy n h (a, b) = some (t, ()) →
      execute answer p.policy m h (a, b) = some (s, ()) → t = s := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro m h a b t s ht hs
      cases m with
      | zero => simp [execute] at hs
      | succ m =>
        cases hp : p.policy h with
        | inr l =>
          simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at ht hs
          exact ht.1.symm.trans hs.1
        | inl q =>
          simp only [execute, hp] at ht hs
          obtain ⟨⟨t', l⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
          obtain ⟨⟨s', k⟩, hs', hf⟩ := Option.map_eq_some_iff.mp hs
          cases l
          cases k
          simp only [Prod.mk.injEq] at he hf
          rw [← he.1, ← hf.1, ih m _ a b t' s' ht' hs']
  have uniqueOriginal (p : EndpointProtocol A B A B) : ∀ n m h a b t s,
      execute answer p.policy n h (a, b) = some (t, ()) →
      execute answer p.policy m h (a, b) = some (s, ()) → t = s := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro m h a b t s ht hs
      cases m with
      | zero => simp [execute] at hs
      | succ m =>
        cases hp : p.policy h with
        | inr l =>
          simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at ht hs
          exact ht.1.symm.trans hs.1
        | inl q =>
          simp only [execute, hp] at ht hs
          obtain ⟨⟨t', l⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
          obtain ⟨⟨s', k⟩, hs', hf⟩ := Option.map_eq_some_iff.mp hs
          cases l
          cases k
          simp only [Prod.mk.injEq] at he hf
          rw [← he.1, ← hf.1, ih m _ a b t' s' ht' hs']
  have transfer {MA : Type w} {MB : Type x} (p : EndpointProtocol MA MB A B) : ∀ n h a b t,
      execute answer p.policy n h (a, b) = some (t, ()) →
      (rightCount t = 0 → ∀ b', execute answer p.policy n h (a, b') = some (t, ())) ∧
      (leftCount t = 0 → ∀ a', execute answer p.policy n h (a', b) = some (t, ())) := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro h a b t hr
      cases hp : p.policy h with
      | inr l =>
        cases l
        simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, _⟩
        exact ⟨fun _ _ => by simp [execute, hp], fun _ _ => by simp [execute, hp]⟩
      | inl q =>
        simp only [execute, hp] at hr
        obtain ⟨⟨s, l⟩, hs, he⟩ := Option.map_eq_some_iff.mp hr
        cases l
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, _⟩
        obtain ⟨hR, hL⟩ := ih _ a b s hs
        cases q with
        | inl f =>
          constructor
          · intro hz b'
            have hz' : rightCount s = 0 := by simpa [rightCount] using hz
            simp only [execute, hp, answer]
            rw [show execute answer p.policy n (h ++ [⟨.inl f, f a⟩]) (a, b') =
              some (s, ()) from hR hz' b']
            rfl
          · simp [leftCount]
        | inr f =>
          constructor
          · simp [rightCount]
          · intro hz a'
            have hz' : leftCount s = 0 := by simpa [leftCount] using hz
            simp only [execute, hp, answer]
            rw [show execute answer p.policy n (h ++ [⟨.inr f, f b⟩]) (a', b) =
              some (s, ()) from hL hz' a']
            rfl
  have binary (q : ZMod 2) : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
  have oneA : ellA ≠ 0 → ∃ a, ellA a = 1 := by
    intro hn
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hn
    exact ⟨a, (binary (ellA a)).resolve_left ha⟩
  have oneB : ellB ≠ 0 → ∃ b, ellB b = 1 := by
    intro hn
    obtain ⟨b, hb⟩ := DFunLike.ne_iff.mp hn
    exact ⟨b, (binary (ellB b)).resolve_left hb⟩
  have lower : ∀ {MA : Type w} {MB : Type x} (initA : A → MA) (initB : B → MB)
      (p : EndpointProtocol MA MB A B), RewriteCorrect ellA ellB alpha beta initA initB p →
      ∀ a b n t, execute answer p.policy n [] (initA a, initB b) = some (t, ()) →
        (directionDemand alpha ellB) ≤ rightCount t ∧
        (directionDemand beta ellA) ≤ leftCount t ∧
        rewriteCost ellA ellB alpha beta ≤ t.length := by
    intro MA MB initA initB p hc a b n t hr
    have hR : (directionDemand alpha ellB) ≤ rightCount t := by
      unfold directionDemand
      split_ifs with h
      · by_contra hn
        have hz : rightCount t = 0 := by omega
        obtain ⟨b₀, hb₀⟩ := oneB h.2
        have alt := (transfer p n [] (initA a) (initB b) t hr).1 hz (initB (b + b₀))
        have he := (hc.2 a b n t hr).1.symm.trans (hc.2 a (b + b₀) n t alt).1
        have hz := sub_eq_zero.mpr he
        rw [← sub_smul] at hz
        have hscalar : (ellA a + ellB b) - (ellA a + ellB (b + b₀)) = 1 := by
          rw [map_add, hb₀]
          ring_nf
          exact ZModModule.neg_eq_self 1
        rw [hscalar, one_smul] at hz
        exact h.1 hz
      · exact Nat.zero_le _
    have hL : (directionDemand beta ellA) ≤ leftCount t := by
      unfold directionDemand
      split_ifs with h
      · by_contra hn
        have hz : leftCount t = 0 := by omega
        obtain ⟨a₀, ha₀⟩ := oneA h.2
        have alt := (transfer p n [] (initA a) (initB b) t hr).2 hz (initA (a + a₀))
        have he := (hc.2 a b n t hr).2.symm.trans (hc.2 (a + a₀) b n t alt).2
        have hz := sub_eq_zero.mpr he
        rw [← sub_smul] at hz
        have hscalar : (ellA a + ellB b) - (ellA (a + a₀) + ellB b) = 1 := by
          rw [map_add, ha₀]
          ring_nf
          exact ZModModule.neg_eq_self 1
        rw [hscalar, one_smul] at hz
        exact h.1 hz
      · exact Nat.zero_le _
    have count : rightCount t + leftCount t = t.length := by
      clear hr hR hL
      induction t with
      | nil => rfl
      | cons e t ih =>
        rcases e with ⟨q, y⟩
        cases q <;>
          simp only [rightCount, leftCount, List.map_cons, List.sum_cons,
            List.length_cons] at * <;> omega
    refine ⟨hR, hL, ?_⟩
    change (directionDemand alpha ellB) +
      (directionDemand beta ellA) ≤ t.length
    rw [← count]
    exact Nat.add_le_add hR hL
  have decode (q : ZMod 2) : (if q = 1 then (1 : ZMod 2) else 0) = q := by
    rcases binary q with rfl | rfl <;> norm_num
  have attained : ∀ a b, ∃ n t,
      execute answer (rewriteProtocol ellA ellB alpha beta).policy n [] (a, b) =
        some (t, ()) ∧
      rightCount t = (directionDemand alpha ellB) ∧
      leftCount t = (directionDemand beta ellA) ∧
      t.length = rewriteCost ellA ellB alpha beta ∧
      (rewriteProtocol ellA ellB alpha beta).outA a (bits t) =
        (ellA a + ellB b) • alpha ∧
      (rewriteProtocol ellA ellB alpha beta).outB b (bits t) =
        (ellA a + ellB b) • beta := by
    intro a b
    let qR : Question A B := .inr (fun b => decide (ellB b = 1))
    let qL : Question A B := .inl (fun a => decide (ellA a = 1))
    by_cases hR : alpha ≠ 0 ∧ ellB ≠ 0 <;>
      by_cases hL : beta ≠ 0 ∧ ellA ≠ 0
    · refine ⟨3, [⟨qR, decide (ellB b = 1)⟩, ⟨qL, decide (ellA a = 1)⟩], ?_⟩
      simp [execute, EndpointProtocol.policy, rewriteProtocol, bits, answer,
        qR, qL, hR, hL, rightCount, leftCount,
        rewriteCost, directionDemand, decode, add_comm]
    · refine ⟨3, [⟨qR, decide (ellB b = 1)⟩], ?_⟩
      simp [execute, EndpointProtocol.policy, rewriteProtocol, bits, answer,
        qR, hR, hL, rightCount, leftCount, rewriteCost, directionDemand, decode]
      by_cases hb : beta = 0
      · simp [hb]
      · have hl : ellA = 0 := by tauto
        simp [hb, hl]
    · refine ⟨3, [⟨qL, decide (ellA a = 1)⟩], ?_⟩
      simp [execute, EndpointProtocol.policy, rewriteProtocol, bits, answer,
        qL, hR, hL, rightCount, leftCount,
        rewriteCost, directionDemand, decode, add_comm]
      by_cases ha : alpha = 0
      · simp [ha]
      · have hl : ellB = 0 := by tauto
        simp [ha, hl]
    · refine ⟨3, [], ?_⟩
      simp [execute, EndpointProtocol.policy, rewriteProtocol, bits,
        hR, hL, rightCount, leftCount, rewriteCost, directionDemand]
      constructor
      · by_cases ha : alpha = 0
        · simp [ha]
        · have hl : ellB = 0 := by tauto
          simp [ha, hl]
      · by_cases hb : beta = 0
        · simp [hb]
        · have hl : ellA = 0 := by tauto
          simp [hb, hl]
  refine ⟨fun p a b n t hr => by simpa [bits] using labels p n [] a b t hr,
    fun p a b n m t s => unique p n m [] a b t s, lower, ?_, ?_⟩
  · constructor
    · intro a b
      obtain ⟨n, t, hr, _⟩ := attained a b
      exact ⟨n, t, hr⟩
    · intro a b n t hr
      obtain ⟨m, s, hs, _, _, _, hA, hB⟩ := attained a b
      have he := uniqueOriginal (rewriteProtocol ellA ellB alpha beta) n m [] a b t s hr hs
      simpa [he] using And.intro hA hB
  · intro a b
    obtain ⟨n, t, hr, hR, hL, hcost, _⟩ := attained a b
    exact ⟨n, t, hr, hR, hL, hcost⟩

#print axioms rewrite_directional_sharpness


end D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound
