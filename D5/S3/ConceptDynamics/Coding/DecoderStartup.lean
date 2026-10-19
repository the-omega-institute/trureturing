/- GID: D5/S3/ConceptDynamics/Coding/DecoderStartup
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DecoderStartup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual acquisition and safe live competitors force finite decoder startup. -/
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

variable {C I O : Type*}

/-- A finite actual path that acquires input contains a finite startup path
ending immediately before its first acquisition. -/
theorem initial_drain_of_acquired_run (action : C → Op C I O) (initial : C)
    (r : ℕ → I) (t : Frame C O)
    (hr : Run action (full r) ⟨initial,0,[]⟩ t) (hp : 0 < t.acquired) :
    ∃ u, Drain action ⟨initial,0,[]⟩ u := by
  obtain ⟨vertices,hv⟩ := hr
  induction hv with
  | refl => simp at hp
  | @tail middle finish vertices hv edge ih =>
    by_cases hm : 0 < middle.acquired
    · exact ih hm
    · have zero : middle.acquired = 0 := by omega
      cases edge with
      | internal c d q o batch inst => dsimp only at hp zero; omega
      | acquire c d q o batch f color inst available result =>
        refine ⟨⟨c,q,o⟩,⟨vertices,trace_input_transfer hv ?_⟩,Or.inr ⟨f,inst⟩⟩
        intro k hk hq
        dsimp only at zero hk hq
        omega

/-- Safety on two actual first-label competitors and D liveness force finite
startup. Finite processing is then required only after executed acquisitions. -/
theorem processing_of_safe_live_pair (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
    (safety : ∀ a r, Record a r → ∀ t,
      Run action (full r) ⟨initial,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, Record a r → InD a → ∀ p,
      ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
    (a beta : ℕ → O) (r r' : ℕ → I)
    (ha : Record a r) (hb : Record beta r') (hd : InD a) (different : a 0 ≠ beta 0)
    (postprocessing : ∀ a r, Record a r → ∀ (c d : C) (q : ℕ) (o w : List O)
      (f : I → Option (C × List O)),
      Run action (full r) ⟨initial,0,[]⟩ ⟨c,q,o⟩ →
      action c = .acquire f → f (r q) = some (d,w) →
      ∃ t, Drain action ⟨d,q+1,o++w⟩ t) : Processing action initial Record := by
  refine ⟨?_,postprocessing⟩
  obtain ⟨t,ht,hp⟩ := liveness a r ha hd 0
  have acquired : 0 < t.acquired := by
    by_contra hn
    have zero : t.acquired = 0 := by omega
    obtain ⟨vertices,hv⟩ := ht
    have ht' : Run action (full r') ⟨initial,0,[]⟩ t := by
      refine ⟨vertices,trace_input_transfer hv ?_⟩
      intro k hk hq; dsimp only at hk; omega
    exact different ((safety a r ha t ⟨vertices,hv⟩ 0 hp).symm.trans
      (safety beta r' hb t ht' 0 hp))
  exact initial_drain_of_acquired_run action initial r t ht acquired

end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
