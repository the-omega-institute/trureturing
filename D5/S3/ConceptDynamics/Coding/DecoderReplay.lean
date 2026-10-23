/- GID: D5/S3/ConceptDynamics/Coding/DecoderReplay
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DecoderReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive trace replay identifies safe live source addresses. -/
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

variable {C I O : Type*}

/-- Replay uses the same vertex list and primitive batches, with independent old output. -/
theorem trace_replay {action : C → Op C I O} {r : ℕ → I}
    {s t : Frame C O} {v : List C} (h : Trace action (full r) s t v) :
    ∃ m w, t.acquired = s.acquired + m ∧ t.output = s.output ++ w ∧
      ∀ (r' : ℕ → I) (q' : ℕ) (o' : List O),
        (∀ j, r (s.acquired+j) = r' (q'+j)) →
        Trace action (full r') ⟨s.state,q',o'⟩ ⟨t.state,q'+m,o'++w⟩ v := by
  induction h with
  | refl => refine ⟨0,[],by simp,by simp,?_⟩; intro r' q' o' same; simpa using
      (Trace.refl : Trace action (full r') ⟨s.state,q',o'⟩ ⟨s.state,q',o'⟩ [s.state])
  | @tail middle finish vertices h edge ih =>
    obtain ⟨m,w,hq,ho,replay⟩ := ih
    cases edge with
    | internal c d q o batch inst =>
      dsimp only at hq ho replay
      refine ⟨m,w++batch,hq,by simpa [ho,List.append_assoc],?_⟩
      intro r' q' o' same
      simpa [List.append_assoc] using (replay r' q' o' same).tail
        (Step.internal c d (q'+m) (o'++w) batch inst)
    | acquire c d q o batch f a inst ha hf =>
      dsimp only at hq ho replay
      refine ⟨m+1,w++batch,by simp_all [Nat.add_assoc],by simpa [ho,List.append_assoc],?_⟩
      intro r' q' o' same
      have inputEq : full r' (q'+m) = some a := by
        dsimp only [full]
        rw [← same m,← hq]
        exact ha
      simpa [Nat.add_assoc,List.append_assoc] using (replay r' q' o' same).tail
        (Step.acquire c d (q'+m) (o'++w) batch f a inst inputEq hf)

/-- Comparable actual paths and unread-suffix replay distinguish live source addresses. -/
theorem actual_address_eq (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
    (safe : ∀ a r, Record a r → ∀ t,
      Run action (full r) ⟨initial,0,[]⟩ t → ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (live : ∀ a r, Record a r → InD a → ∀ p,
      ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
    (a b : ℕ → O) (r r' : ℕ → I) (ha : Record a r) (hb : Record b r') (hd : InD a)
    (s s' : Frame C O)
    (hs : Run action (full r) ⟨initial,0,[]⟩ s)
    (hs' : Run action (full r') ⟨initial,0,[]⟩ s')
    (state : s.state = s'.state) (output : s.output = s'.output)
    (same : ∀ j, r (s.acquired+j) = r' (s'.acquired+j)) : a = b := by
  funext p
  obtain ⟨t,ht,hp⟩ := live a r ha hd (max p s.output.length)
  have hp' : p < t.output.length := (le_max_left _ _).trans_lt hp
  have after : Run action (full r) s t := by
    rcases run_comparable hs ht with h | h
    · exact h
    · have hg := (run_mono h).2
      have hh := le_max_right p s.output.length
      omega
  obtain ⟨v,hv⟩ := after
  obtain ⟨m,w,hq,ho,replay⟩ := trace_replay hv
  have newTrace := replay r' s'.acquired s'.output same
  rw [state] at newTrace
  have all := run_trans hs' (show Run action (full r') s'
      ⟨t.state,s'.acquired+m,s'.output++w⟩ from ⟨v,newTrace⟩)
  have hnew : p < (s'.output++w).length := by rw [← output,← ho]; exact hp'
  calc a p = t.output[p] := (safe a r ha t ht p hp').symm
       _ = (s'.output++w)[p] := by simp only [ho,output]
       _ = b p := safe b r' hb _ all p hnew

end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
