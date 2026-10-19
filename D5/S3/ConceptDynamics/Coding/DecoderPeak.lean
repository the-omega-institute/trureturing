/- GID: D5/S3/ConceptDynamics/Coding/DecoderPeak
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DecoderPeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every primitive trace vertex is bounded by the complete horizon peak. -/
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

variable {C I O : Type*}

/-- This supremum includes every actual record and every operation vertex. -/
def ReachThrough (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (H : ℕ) (c : C) : Prop :=
  ∃ a r t, Record a r ∧ Run action (full r) ⟨initial,0,[]⟩ t ∧
    t.acquired ≤ H ∧ t.state = c

noncomputable def Peak (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ) : WithTop ℕ :=
  ⨆ c, ⨆ (_ : ReachThrough action initial Record H c), ((enc c).length : WithTop ℕ)

theorem peak_bound (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ) (c : C)
    (hc : ReachThrough action initial Record H c) :
    ((enc c).length : WithTop ℕ) ≤ Peak action initial Record enc H :=
  le_iSup_of_le c (le_iSup_of_le hc (le_refl _))

private theorem trace_vertex_split {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {v : List C} (h : Trace action input s t v) (c : C) (hc : c ∈ v) :
    ∃ u, Run action input s u ∧ Run action input u t ∧ u.state = c := by
  induction h with
  | refl =>
    have he : c = s.state := by simpa using hc
    exact ⟨s,⟨_,.refl⟩,⟨_,.refl⟩,he.symm⟩
  | @tail middle finish vertices h edge ih =>
    rcases List.mem_append.mp hc with old | last
    · obtain ⟨u,hu,ht,he⟩ := ih old
      exact ⟨u,hu,run_closure.mpr ((run_closure.mp ht).tail edge),he⟩
    · have he : c = finish.state := by simpa using last
      exact ⟨finish,⟨_,h.tail edge⟩,⟨_,.refl⟩,he.symm⟩

/-- No readable intermediate state disappears when costs are bounded at a horizon. -/
theorem peak_trace_bound (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ)
    (a : ℕ → O) (r : ℕ → I) (t : Frame C O) (v : List C)
    (ha : Record a r) (hr : Trace action (full r) ⟨initial,0,[]⟩ t v)
    (hq : t.acquired ≤ H) (c : C) (hc : c ∈ v) :
    ((enc c).length : WithTop ℕ) ≤ Peak action initial Record enc H := by
  obtain ⟨u,hu,ht,he⟩ := trace_vertex_split hr c hc
  exact peak_bound action initial Record enc H c
    ⟨a,r,u,ha,hu,(run_mono ht).1.trans hq,he⟩

theorem peak_monotone (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) :
    Monotone (Peak action initial Record enc) := by
  intro H K hHK
  apply iSup_le
  intro c
  apply iSup_le
  rintro ⟨a,r,t,ha,hr,hq,hc⟩
  exact peak_bound action initial Record enc K c ⟨a,r,t,ha,hr,hq.trans hHK,hc⟩

end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
