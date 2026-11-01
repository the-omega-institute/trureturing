/- GID: D5/S1/Dynamics/Shadowing/BufferedConeExtension
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/BufferedConeExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite buffered mixed old/new graph extension retaining whole paths.
-/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v w

private theorem finite_buffer_transfer_cover
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {I : Type v} [Fintype I]
    (P Q : I → Set X)
    (hP : ∀ i, IsClosed (P i)) (hPQ : ∀ i, P i ⊆ Q i)
    (hQ : ∀ i, IsOpen (Q i)) :
    ∃ T : Finset (Opens X), IsOpenCover (fun U : T => U.1) ∧
      ∀ U : T, ∀ i, (U.1 ∩ P i).Nonempty → U.1 ⊆ Q i := by
  classical
  let O : X → Set X := fun x =>
    {y | ∀ i, y ∈ if x ∈ Q i then Q i else (P i)ᶜ}
  have hOopen : ∀ x, IsOpen (O x) := by
    intro x
    apply isOpen_iInter_of_finite
    intro i
    split_ifs with hi
    · exact hQ i
    · exact (hP i).isOpen_compl
  have hOmem : ∀ x, x ∈ O x := by
    intro x i
    split_ifs with hi
    · exact hi
    · exact by_contra fun hxi => hi ((hPQ i) hxi)
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover
    O hOopen (fun x _ => mem_iUnion.mpr ⟨x, hOmem x⟩)
  let T : Finset (Opens X) := s.image fun x => ⟨O x, hOopen x⟩
  have hTc : IsOpenCover (fun U : T => U.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨O y, hOopen y⟩,
      Finset.mem_image.mpr ⟨y, hy, rfl⟩, hxy⟩
  refine ⟨T, hTc, ?_⟩
  intro U i hUi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp U.property
  intro y hy
  by_contra hyQ
  have hxQ : x ∉ Q i := by
    intro hxQ
    exact hyQ ((hQ i).mem_nhds hxQ)
  have hyc : y ∈ (P i)ᶜ := by
    exact (show y ∈ if x ∈ Q i then Q i else (P i)ᶜ from hy (i := i))
  obtain ⟨z, hzP⟩ := hUi
  exact hyc hzP.2

/-!
The theorem below is the finite retained-cone step in Peng's unrestricted
Question 5.1.  The old graph is retained as a whole-path factor.  Every new
edge is defined by one actual source point, and every complete new path is
traced by one source orbit in the outer buffers.  No global uniform-follower
choice or inverse-limit conclusion is assumed here.
-/
theorem buffered_whole_path_extension
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A : Type v} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    {B : Type w} [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    {V : Type*} [Fintype V]
    (f : X → X) (_hf : Continuous f) (hs : HasShadowing f)
    (K P C : A → Set X) (L D₀ : B → Set X)
    (hK : ∀ a, IsClosed (K a)) (hP : ∀ a, IsClosed (P a))
    (hKP : ∀ a, K a ⊆ interior (P a))
    (hPC : ∀ a, P a ⊆ interior (C a))
    (hL : ∀ b, IsClosed (L b))
    (hLD : ∀ b, L b ⊆ interior (D₀ b))
    (hKcover : ∀ x, ∃ a, x ∈ interior (K a))
    (hLcover : ∀ x, ∃ b, x ∈ interior (L b))
    (e : V → V → Prop) (ell : V → A)
    (hVlive : ∀ v, ∃ p : ℕ → V, p 0 = v ∧ ∀ n, e (p n) (p (n + 1)))
    (hOldP : ∀ w, w ∈ graphLanguage e ell →
      ∃ x, ∀ n, f^[n] x ∈ P (w n))
    (hOldK : ∀ x w, (∀ n, f^[n] x ∈ K (w n)) →
      w ∈ graphLanguage e ell) :
    ∃ (T : Finset (Opens X)) (edge : (V × (T × B)) → (V × (T × B)) → Prop),
      edge = (fun u v =>
        e u.1 v.1 ∧ ∃ t : X,
          t ∈ (u.2.1 : Set X) ∧ t ∈ P (ell u.1) ∧ t ∈ L u.2.2 ∧
          f t ∈ (v.2.1 : Set X) ∧ f t ∈ P (ell v.1) ∧ f t ∈ L v.2.2) ∧
      IsOpenCover (fun U : T => U.1) ∧
      (∀ u v, edge u v → e u.1 v.1) ∧
      (∀ p : ℕ → V, (∀ n, e (p n) (p (n + 1))) →
        ∃ r : ℕ → (V × (T × B)),
          (∀ n, edge (r n) (r (n + 1))) ∧
          (∀ n, (r n).1 = p n)) ∧
      (∀ w, w ∈ graphLanguage edge (fun u => (ell u.1, u.2.2)) →
        ∃ z, ∀ n, f^[n] z ∈ interior (C (w n).1) ∩ interior (D₀ (w n).2)) ∧
      (∀ x w, (∀ n, f^[n] x ∈ K (w n).1 ∧ f^[n] x ∈ L (w n).2) →
        (fun n => (w n).1, fun n => (w n).2) ∈
          graphLanguage edge (fun u => (ell u.1, u.2.2))) := by
  classical
  let I := A ⊕ B
  let P' : I → Set X := fun i => match i with
    | Sum.inl a => P a
    | Sum.inr b => L b
  let Q' : I → Set X := fun i => match i with
    | Sum.inl a => interior (C a)
    | Sum.inr b => interior (D₀ b)
  have hP' : ∀ i, IsClosed (P' i) := by
    intro i
    cases i with
    | inl a => exact hP a
    | inr b => exact hL b
  have hPQ' : ∀ i, P' i ⊆ Q' i := by
    intro i
    cases i with
    | inl a => exact hPC a
    | inr b => exact hLD b
  have hQ' : ∀ i, IsOpen (Q' i) := by
    intro i
    cases i with
    | inl a => exact isOpen_interior
    | inr b => exact isOpen_interior
  obtain ⟨T, hT, hTbuf⟩ := finite_buffer_transfer_cover P' Q' hP' hPQ' hQ'
  obtain ⟨D, hD, htrace⟩ := hs T hT
  let edge : (V × (D × B)) → (V × (D × B)) → Prop := fun u v =>
    e u.1 v.1 ∧ ∃ t : X,
      t ∈ (u.2.1 : Set X) ∧ t ∈ P (ell u.1) ∧ t ∈ L u.2.2 ∧
      f t ∈ (v.2.1 : Set X) ∧ f t ∈ P (ell v.1) ∧ f t ∈ L v.2.2
  refine ⟨D, edge, ?_, hD, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro u v huv
    exact huv.1
  · intro p hp
    have hw : (fun n => ell (p n)) ∈ graphLanguage e ell := by
      exact ⟨p, hp, fun _ => rfl⟩
    obtain ⟨x, hx⟩ := hOldP _ hw
    have hb : ∀ n, ∃ b : B, f^[n] x ∈ L b := by
      intro n
      obtain ⟨b, hb⟩ := hLcover (f^[n] x)
      exact ⟨b, interior_subset hb⟩
    choose b hb using hb
    have hd : ∀ n, ∃ d : D, f^[n] x ∈ (d : Set X) := fun n => hD.exists_mem _
    choose d hd using hd
    refine ⟨fun n => (p n, (d n, b n)), ?_, fun n => rfl⟩
    intro n
    refine ⟨hp n, f^[n] x, hd n, hx n, hb n, ?_, ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply'] using hd (n + 1)
    · exact hx (n + 1)
    · exact hb (n + 1)
  · intro w hw
    obtain ⟨p, hp, hl⟩ := hw
    choose t ht using fun n => (hp n).2
    have hpo : PseudoOrbit f D t := by
      intro n
      refine ⟨(p (n + 1)).2.1, (p (n + 1)).2.1.property, ?_, ?_⟩
      · exact (ht n).2.2.2.1
      · exact (ht (n + 1)).1
    obtain ⟨z, hz⟩ := htrace t hpo
    refine ⟨z, fun n => ?_⟩
    obtain ⟨U, hU, hzn, htn⟩ := hz n
    have hold : (U.1 ∩ P (ell (p n))).Nonempty :=
      ⟨t n, htn, (ht n).2.1⟩
    have hnew : (U.1 ∩ L (p n).2.2).Nonempty :=
      ⟨t n, htn, (ht n).2.2.1⟩
    have hC : U.1 ⊆ interior (C (ell (p n))) := by
      simpa [P', Q'] using hTbuf U (Sum.inl (ell (p n))) hold
    have hD₀ : U.1 ⊆ interior (D₀ (p n).2.2) := by
      simpa [P', Q'] using hTbuf U (Sum.inr (p n).2.2) hnew
    exact ⟨hC hzn, hD₀ hzn⟩
  · intro x w hw
    have hold : (fun n => (w n).1) ∈ graphLanguage e ell := by
      apply hOldK x
      intro n
      exact (hw n).1
    obtain ⟨p, hp, hl⟩ := hold
    have hd : ∀ n, ∃ d : D, f^[n] x ∈ (d : Set X) := fun n => hD.exists_mem _
    choose d hd using hd
    refine ⟨fun n => (p n, (d n, (w n).2)), ?_, ?_⟩
    · intro n
      refine ⟨hp n, f^[n] x, hd n, ?_, (hw n).2, ?_, ?_, (hw (n + 1)).2⟩
      · exact (hw n).1.trans ((hKP (w n).1).trans interior_subset)
      · simpa only [Function.iterate_succ_apply'] using hd (n + 1)
      · exact (hw (n + 1)).1.trans ((hKP (w (n + 1)).1).trans interior_subset)
    · intro n
      apply Prod.ext
      · exact (hl n).trans (rfl)
      · rfl

#print axioms buffered_whole_path_extension

end D5.S1.Dynamics.Shadowing
