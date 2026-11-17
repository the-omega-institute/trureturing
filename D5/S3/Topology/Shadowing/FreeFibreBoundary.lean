/- GID: D5/S3/Topology/Shadowing/FreeFibreBoundary
   generality: G
   mirror-B: D5/B/S3/Topology/Shadowing/FreeFibreBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Topology/Shadowing/FreeFibreBoundary.claim; result=D5/S3/Topology/Shadowing/FreeFibreBoundary.result; claim=D5/S3/Topology/Shadowing/FreeFibreBoundary.claim
   digest: A compact Hausdorff shadowing system admits no zero-dimensional compact Hausdorff shadowing cover. -/

import D5.S1.Dynamics.Shadowing.OpenCoreShadowing
import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

/-! Marked complete graph languages on a convergent section turn every
hypothetical shadowing cover into an impossible open resolution. -/

open TopologicalSpace Set Function Filter UniformSpace
open scoped Topology Uniformity SetRel
open D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
open D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

namespace D5.S1.Dynamics.Shadowing.FreeFibreBoundary

noncomputable section
universe u v w

open scoped OnePoint

/- Restricting the initial marker in the complete joint graph language gives
an exact presentation.  No surjectivity or invariance of the dynamics is
used, and the zeroth coordinate is retained. -/
theorem finite_initial_marked_names
    {Y : Type u} [TopologicalSpace Y]
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {B : Type w} [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    (T : Y → Y) (a : Y → A) (ha : Continuous a)
    (mark : Y → B) (hmark : Continuous mark) (b₀ : B)
    (hs : HasShadowing T) :
    HasFiniteInitialPresentation
      (range (fun y : {y : Y // mark y = b₀} =>
        fun n => a (T^[n] y.val))) := by
  classical
  let obs : Y → A × B := fun y => (a y, mark y)
  have hobs : Continuous obs := ha.prodMk hmark
  obtain ⟨m, edge, label, hlang⟩ :=
    finite_observation_isSofic T obs hobs hs
  refine ⟨m, edge, (fun v => (label v).1),
    {v | (label v).2 = b₀}, ?_⟩
  ext word
  constructor
  · rintro ⟨y, rfl⟩
    have hw : (fun n => obs (T^[n] y.val)) ∈
        range (fun z n => obs (T^[n] z)) := ⟨y.val, rfl⟩
    rw [hlang] at hw
    obtain ⟨path, hpath, hlabel⟩ := hw
    refine ⟨path, ?_, hpath, ?_⟩
    · change (label (path 0)).2 = b₀
      have h₀ := congrArg Prod.snd (hlabel 0)
      change (label (path 0)).2 = mark y.val at h₀
      exact h₀.trans y.property
    · intro n
      exact congrArg Prod.fst (hlabel n)
  · rintro ⟨path, hinitial, hpath, hlabel⟩
    let joint : ℕ → A × B := fun n => label (path n)
    have hw : joint ∈ graphLanguage edge label :=
      ⟨path, hpath, fun _ => rfl⟩
    rw [← hlang] at hw
    obtain ⟨y, hy⟩ := hw
    have hy₀ : mark y = b₀ := by
      have h₀ := congrArg (fun s : ℕ → A × B => (s 0).2) hy
      change mark y = (label (path 0)).2 at h₀
      exact h₀.trans hinitial
    refine ⟨⟨y, hy₀⟩, funext fun n => ?_⟩
    have hn := congrArg (fun s : ℕ → A × B => (s n).1) hy
    change a (T^[n] y) = (label (path n)).1 at hn
    exact hn.trans (hlabel n)

theorem finite_initial_presentation_to_graphLanguage
    {S : Set BinaryName} (hS : HasFiniteInitialPresentation S) :
    ∃ c : FiniteGraphCode, S = finiteGraphLanguage c := by
  classical
  rcases hS with ⟨n, edge, label, initial, hEq⟩
  let c : FiniteGraphCode :=
    ⟨n, (fun v w => decide (edge v w), label, fun v => decide (v ∈ initial))⟩
  refine ⟨c, ?_⟩
  rw [hEq]
  ext word
  constructor
  · rintro ⟨path, hp0, hpath, hlabel⟩
    refine ⟨path, ?_, ?_, hlabel⟩
    · simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hp0
    · intro n
      simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hpath n
  · rintro ⟨path, hp0, hpath, hlabel⟩
    refine ⟨path, ?_, ?_, hlabel⟩
    · simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hp0
    · intro n
      simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hpath n

theorem semiconj_clopen_image_is_finiteGraphLanguage
    {Y : Type*} [TopologicalSpace Y]
    (T : Y → Y) (phi : Y → BinaryName) (hphi : Continuous phi)
    (hsem : Semiconj phi T CoreShift) (hT : HasShadowing T)
    (W : Set Y) (hW : IsClopen W) :
    ∃ c : FiniteGraphCode, phi '' W = finiteGraphLanguage c := by
  let mark : Y → Bool := W.boolIndicator
  have hmark : Continuous mark :=
    (continuous_boolIndicator_iff_isClopen W).2 hW
  have hcoord : Continuous (fun y : Y => phi y 0) :=
    (continuous_apply 0).comp hphi
  obtain ⟨n, edge, label, initial, hpres⟩ := finite_initial_marked_names
    T (fun y => phi y 0) hcoord mark hmark true hT
  have hrange : Set.range (fun y : {y : Y // mark y = true} =>
      fun n => phi (T^[n] y.val) 0) = phi '' W := by
    ext s
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y.val, ?_, ?_⟩
      · exact (Set.mem_iff_boolIndicator W y.val).mpr y.property
      · funext n
        have hn := congrFun (hsem.iterate_right n y.val) 0
        exact (hn.trans (by simpa [CoreShift] using
          shift_one_iterate_apply (phi y.val) n 0)).symm
    · rintro ⟨y, hyW, rfl⟩
      refine ⟨⟨y, ?_⟩, ?_⟩
      · exact (Set.mem_iff_boolIndicator W y).mp hyW
      · funext n
        have hn := congrFun (hsem.iterate_right n y) 0
        exact hn.trans (by simpa [CoreShift] using
          shift_one_iterate_apply (phi y) n 0)
  obtain ⟨c, hc⟩ := finite_initial_presentation_to_graphLanguage
    ⟨n, edge, label, initial, hpres⟩
  exact ⟨c, hrange.symm.trans hc⟩

theorem convergentSection_singleton_isClopen (a : BinaryName) (n : ℕ) :
    IsClopen ({⟨convergentSectionName a n,
      Or.inr ⟨n, rfl⟩⟩} : Set (convergentSectionSet a)) := by
  let g : convergentSectionSet a → OnePoint ℕ := firstDifferenceOnSection a
  have hg : Continuous g := by
    change Continuous (firstDifference a ∘ Subtype.val)
    exact (continuous_firstDifference a).comp continuous_subtype_val
  have hsingle : IsClopen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
    refine ⟨isClosed_singleton, ?_⟩
    simpa using
      (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).2 (isOpen_discrete _)
  have hpre : IsClopen (g ⁻¹' ({(n : OnePoint ℕ)} : Set (OnePoint ℕ))) :=
    hsingle.preimage hg
  have heq : g ⁻¹' ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) =
      ({⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩} : Set (convergentSectionSet a)) := by
    ext s
    constructor
    · intro hs
      have hcan := convergentSectionName_firstDifference a n
      have hsn : firstDifferenceOnSection a s = (n : OnePoint ℕ) := hs
      apply Subtype.ext
      exact congrArg Subtype.val
        ((firstDifferenceOnSection_bijective a).1 (hsn.trans hcan.symm))
    · intro hs
      have hs' : s = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩ := by simpa using hs
      subst s
      exact convergentSectionName_firstDifference a n
  rw [heq] at hpre
  exact hpre

theorem finiteGraphLanguage_section_isClopen
    (a : BinaryName) (c : FiniteGraphCode)
    (hdec : ∃ U : Set BinaryName, IsOpen U ∧ a ∈ U ∧
      (U ⊆ finiteGraphLanguage c ∨ U ⊆ (finiteGraphLanguage c)ᶜ)) :
    IsClopen (((↑) : convergentSectionSet a → BinaryName) ⁻¹'
      finiteGraphLanguage c) := by
  let S₀ := convergentSectionSet a
  let C := finiteGraphLanguage c
  let E : Set S₀ := ((↑) : S₀ → BinaryName) ⁻¹' C
  have hpoint (s : S₀) (hs : s ∈ E) : E ∈ 𝓝 s := by
    by_cases hsa : s.val = a
    · let a₀ : S₀ := ⟨a, Or.inl rfl⟩
      have hsa₀ : s = a₀ := by
        apply Subtype.ext
        exact hsa
      subst s
      obtain ⟨U, hU, haU, hside⟩ := hdec
      have haC : a ∈ C := hs
      rcases hside with hUC | hUcomp
      · apply Filter.mem_of_superset
          ((hU.preimage continuous_subtype_val).mem_nhds (show a₀ ∈
            (Subtype.val : S₀ → BinaryName) ⁻¹' U from haU))
        intro x hx
        exact hUC hx
      · exact False.elim (hUcomp haU haC)
    · obtain ⟨n, hn⟩ := convergentSectionSet_firstDifference_finite a s.val s.property hsa
      let cn : S₀ := ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
      have hsn : s = cn := by
        exact (firstDifferenceOnSection_bijective a).1 (show firstDifferenceOnSection a s =
          firstDifferenceOnSection a cn from hn.trans
            (convergentSectionName_firstDifference a n).symm)
      have hcn := convergentSection_singleton_isClopen a n
      subst s
      apply Filter.mem_of_superset (hcn.2.mem_nhds (by
        change cn = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
        rfl))
      intro x hx
      have hxc : x = cn := by simpa using hx
      simpa [hxc] using hs
  have hpoint_compl (s : S₀) (hs : s ∈ Eᶜ) : Eᶜ ∈ 𝓝 s := by
    by_cases hsa : s.val = a
    · let a₀ : S₀ := ⟨a, Or.inl rfl⟩
      have hsa₀ : s = a₀ := by
        apply Subtype.ext
        exact hsa
      subst s
      obtain ⟨U, hU, haU, hside⟩ := hdec
      have haC : a ∉ C := by
        intro haC
        exact hs haC
      rcases hside with hUC | hUcomp
      · exact False.elim (haC (hUC haU))
      · apply Filter.mem_of_superset
          ((hU.preimage continuous_subtype_val).mem_nhds (show a₀ ∈
            (Subtype.val : S₀ → BinaryName) ⁻¹' U from haU))
        intro x hx hCx
        exact (hUcomp hx) hCx
    · obtain ⟨n, hn⟩ := convergentSectionSet_firstDifference_finite a s.val s.property hsa
      let cn : S₀ := ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
      have hsn : s = cn := by
        exact (firstDifferenceOnSection_bijective a).1 (show firstDifferenceOnSection a s =
          firstDifferenceOnSection a cn from hn.trans
            (convergentSectionName_firstDifference a n).symm)
      have hcn := convergentSection_singleton_isClopen a n
      subst s
      apply Filter.mem_of_superset (hcn.2.mem_nhds (by
        change cn = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
        rfl))
      intro x hx
      have hxc : x = cn := by simpa using hx
      simpa [hxc] using hs
  refine ⟨?_, ?_⟩
  · apply isOpen_compl_iff.mp
    rw [isOpen_iff_mem_nhds]
    exact hpoint_compl
  · rw [isOpen_iff_mem_nhds]
    exact hpoint

theorem clopen_subtype_extension
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [ZeroDimensionalSpace Y] {P K : Set Y} (hP : IsClopen P)
    (hK : IsClosed K) (hKP : K ⊆ P) {E : Set K} (hE : IsClopen E) :
    ∃ W : Set Y, IsClopen W ∧ W ⊆ P ∧
      ((Subtype.val : K → Y) ⁻¹' W = E) := by
  letI : CompactSpace K := hK.isClosedEmbedding_subtypeVal.compactSpace
  let EI : Set Y := Subtype.val '' E
  let FI : Set Y := Subtype.val '' Eᶜ
  have hEI : IsClosed EI := by
    exact (hE.1.isCompact.image continuous_subtype_val).isClosed
  have hFI : IsClosed FI := by
    exact (hE.2.isClosed_compl.isCompact.image continuous_subtype_val).isClosed
  have hdis : Disjoint EI FI := by
    refine Set.disjoint_left.2 ?_
    intro y hyE hyF
    obtain ⟨x, hxE, hxy⟩ := hyE
    obtain ⟨z, hzF, hzy⟩ := hyF
    have hxz : x = z := Subtype.ext (hxy.trans hzy.symm)
    exact hzF (hxz ▸ hxE)
  obtain ⟨W, hW, hEW, hWF⟩ := exists_clopen_of_closed_subset_open
    hEI hFI.isOpen_compl (by
      intro y hy
      intro hyF
      exact Set.disjoint_left.1 hdis hy hyF)
  let W' := W ∩ P
  have hW' : IsClopen W' := hW.inter hP
  refine ⟨W', hW', inter_subset_right, ?_⟩
  ext x
  constructor
  · intro hx
    have hxW : (x : Y) ∈ W := hx.1
    by_contra hxE
    have hxEc : x ∈ Eᶜ := hxE
    exact hWF hxW ⟨(x : K), hxEc, rfl⟩
  · intro hx
    exact ⟨hEW ⟨(x : K), hx, rfl⟩, hKP x.property⟩

theorem freeFibreSource_hasShadowing
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (p : T → OnePoint ℕ) (a : BinaryName) (hp : Continuous p)
    (honto : Function.Surjective p) (hopen : IsOpenMap p) :
    HasShadowing (sourceDynamics p a) := by
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  letI : UniformSpace (FibrePullback p (firstDifference a)) := uniformSpaceOfCompactR1
  have hHcont : Continuous (fibrePullbackSecond p (firstDifference a)) :=
    fibrePullbackSecond_continuous p (firstDifference a)
  have hHopen : IsOpenMap (fibrePullbackSecond p (firstDifference a)) :=
    fibrePullbackSecond_isOpenMap p (firstDifference a) hopen (continuous_firstDifference a)
  let hExt : FibrePullback p (firstDifference a) ⊕ BinaryName → BinaryName :=
    Sum.elim (fibrePullbackSecond p (firstDifference a)) CoreShift
  have hExtcont : Continuous hExt :=
    hHcont.sumElim (SymbolicDynamics.FullShift.continuous_shift 1)
  have hExtopen : IsOpenMap hExt := hHopen.sumElim coreShift_isOpenMap
  have hExtonto : Function.Surjective hExt := by
    intro s
    refine ⟨Sum.inr (prependBinaryName false s), ?_⟩
    simpa [hExt] using (prependBinaryName_shift false s)
  have hcore : HasShadowing CoreShift :=
    (cover_shadowing_iff_uniform CoreShift).mpr coreShift_uniformHasShadowing
  have hs := open_core_extension_hasShadowing
    (h := hExt) (g := CoreShift)
    hExtcont hExtopen hExtonto (by
      intro s
      change CoreShift s = CoreShift s
      rfl)
    (SymbolicDynamics.FullShift.continuous_shift 1) hcore
  have heq : sourceDynamics p a = (fun x => Sum.inr (hExt x)) := by
    funext x
    cases x <;> rfl
  rw [heq]
  exact hs

theorem freeFibre_cover_forces_resolution
    {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (p : T → OnePoint ℕ) (hp : Continuous p) (honto : Function.Surjective p)
    (hopen : IsOpenMap p) (a : BinaryName)
    (hgeneric : ∀ c : FiniteGraphCode, ∃ U : Set BinaryName, IsOpen U ∧ a ∈ U ∧
      (U ⊆ finiteGraphLanguage c ∨ U ⊆ (finiteGraphLanguage c)ᶜ))
    {Y : Type v} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] (τ : Y → Y) (_hτc : Continuous τ)
    (hτs : HasShadowing τ) (q : Y → FreeFibreSource p a)
    (hq : Continuous q) (hqonto : Function.Surjective q)
    (hsemq : Semiconj q τ (sourceDynamics p a)) :
    HasOpenZeroDimensionalResolution.{u, 0, v} p := by
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  let S₀ : Set BinaryName := convergentSectionSet a
  have hS₀closed : IsClosed S₀ := (convergentSectionSet_isCompact a).isClosed
  have hobs : Continuous (sourceObservation p a) :=
    sourceObservation_continuous p a (fibrePullbackSecond_continuous p (firstDifference a))
  let ϕ : Y → BinaryName := sourceObservation p a ∘ q
  have hϕ : Continuous ϕ := hobs.comp hq
  have hsemϕ : Semiconj ϕ τ CoreShift := by
    intro y
    change sourceObservation p a (q (τ y)) = CoreShift (sourceObservation p a (q y))
    rw [hsemq y]
    exact sourceDynamics_semiconj p a (q y)
  let Pset : Set (FreeFibreSource p a) :=
    range (Sum.inl : FibrePullback p (firstDifference a) → FreeFibreSource p a) ∩
      (sourceObservation p a ⁻¹' S₀)
  have hPset : IsClosed Pset := by
    exact isClosed_range_inl.inter (hS₀closed.preimage hobs)
  let YP : Set Y := q ⁻¹' range (Sum.inl : FibrePullback p (firstDifference a) →
    FreeFibreSource p a)
  have hYP : IsClopen YP := by
    exact (isClopen_range_inl.preimage hq)
  let Y₀set : Set Y := q ⁻¹' Pset
  have hY₀closed : IsClosed Y₀set := hPset.preimage hq
  let Y₀ := {y : Y // y ∈ Y₀set}
  let t₀ : T := Classical.choose (honto (∞ : OnePoint ℕ))
  let rBase : FreeFibreSource p a → T :=
    Sum.elim (fun z => z.val.1) (fun _ => t₀)
  have hrBase : Continuous rBase := by
    exact (continuous_fst.comp continuous_subtype_val).sumElim continuous_const
  let r : Y₀ → T := rBase ∘ q ∘ Subtype.val
  have hr : Continuous r := hrBase.comp (hq.comp continuous_subtype_val)
  letI : CompactSpace Y₀ := hY₀closed.isClosedEmbedding_subtypeVal.compactSpace
  have hY₀subYP : Y₀set ⊆ YP := by
    intro y hy
    exact hy.1
  have hronto : Function.Surjective r := by
    obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
    intro t
    obtain ⟨s, hs⟩ := e.surjective (p t)
    have hps : p t = firstDifference a s.val := by
      calc
        p t = e s := (hs).symm
        _ = firstDifferenceOnSection a s := he s
        _ = firstDifference a s.val := rfl
    let z : FibrePullback p (firstDifference a) := ⟨(t, s.val), hps⟩
    obtain ⟨y, hy⟩ := hqonto (Sum.inl z)
    have hyP : q y ∈ Pset := by
      refine ⟨⟨z, hy.symm⟩, ?_⟩
      change sourceObservation p a (q y) ∈ S₀
      rw [hy]
      exact s.property
    refine ⟨⟨y, hyP⟩, ?_⟩
    simp [r, rBase, hy, z]
  have himage : ∀ E : Set Y₀, IsClopen E →
      IsOpen (p '' (r '' E)) := by
    intro E hE
    obtain ⟨W, hW, hWP, htrace⟩ := clopen_subtype_extension hYP hY₀closed
      hY₀subYP hE
    obtain ⟨c, hc⟩ := semiconj_clopen_image_is_finiteGraphLanguage
      τ ϕ hϕ hsemϕ hτs W hW
    obtain ⟨U, hU, haU, hside⟩ := hgeneric c
    have hCsection : IsClopen (((↑) : S₀ → BinaryName) ⁻¹'
        finiteGraphLanguage c) := finiteGraphLanguage_section_isClopen a c
      ⟨U, hU, haU, hside⟩
    let Ebase : Set Y := Subtype.val '' E
    have hEbaseW : Ebase ⊆ W := by
      rintro y ⟨y₀, hy₀, rfl⟩
      change y₀ ∈ (Subtype.val : Y₀ → Y) ⁻¹' W
      rw [htrace]
      exact hy₀
    have hϕE : ϕ '' Ebase = (ϕ '' W) ∩ S₀ := by
      ext s
      constructor
      · rintro ⟨y, hyEbase, hys⟩
        obtain ⟨y₀, hy₀, rfl⟩ := hyEbase
        have hyW : (y₀ : Y) ∈ W := hEbaseW ⟨y₀, hy₀, rfl⟩
        refine ⟨⟨(y₀ : Y), hyW, hys⟩, ?_⟩
        have hsection : sourceObservation p a (q y₀) ∈ S₀ := by
          exact y₀.property.2
        have hϕsection : ϕ (y₀ : Y) ∈ S₀ := by
          change sourceObservation p a (q y₀) ∈ S₀
          exact hsection
        exact hys ▸ hϕsection
      · rintro ⟨⟨y, hyW, hys⟩, hs⟩
        have hyP : q y ∈ Pset := by
          refine ⟨?_, ?_⟩
          · exact hWP hyW
          · change ϕ y ∈ S₀
            simpa [hys] using hs
        have hy₀ : y ∈ Y₀set := hyP
        have hyE : (⟨y, hy₀⟩ : Y₀) ∈ E := by
          have hmem : (⟨y, hy₀⟩ : Y₀) ∈
              (Subtype.val : Y₀ → Y) ⁻¹' W := hyW
          rw [htrace] at hmem
          exact hmem
        exact ⟨y, ⟨⟨y, hy₀⟩, hyE, rfl⟩, hys⟩
    have hEsection : IsClopen (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase)) := by
      have heq : ((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase) =
          ((↑) : S₀ → BinaryName) ⁻¹' finiteGraphLanguage c := by
        ext s
        rw [hϕE, hc]
        simp [s.property]
      rw [heq]
      exact hCsection
    obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
    have himagePR : p '' (r '' E) = e ''
        (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase)) := by
      ext b
      constructor
      · rintro ⟨u, ⟨y₀, hy₀, rfl⟩, rfl⟩
        obtain ⟨z, hz⟩ := y₀.property.1
        have hqz : q y₀.val = Sum.inl z := by
          exact hz.symm
        have hzS : z.val.2 ∈ S₀ := by
          have hsection : sourceObservation p a (q y₀) ∈ S₀ := by
            exact y₀.property.2
          rw [hqz] at hsection
          simpa [sourceObservation] using hsection
        let s : S₀ := ⟨z.val.2, hzS⟩
        have hϕs : ϕ y₀.val = s.val := by
          simp [ϕ, Function.comp_def, hqz, sourceObservation, s]
        have hpr : p (r y₀) = firstDifference a z.val.2 := by
          simp [r, rBase, hqz]
          exact z.property
        refine ⟨s, ?_, ?_⟩
        · exact ⟨y₀.val, ⟨y₀, hy₀, rfl⟩, hϕs⟩
        · rw [he s]
          change firstDifference a z.val.2 = p (r y₀)
          exact hpr.symm
      · rintro ⟨s, hsE, hse⟩
        obtain ⟨y, hyEbase, hϕy⟩ := hsE
        obtain ⟨y₀, hyE, rfl⟩ := hyEbase
        obtain ⟨z, hz⟩ := y₀.property.1
        have hqz : q y₀.val = Sum.inl z := hz.symm
        have hps : p (r y₀) = firstDifference a z.val.2 := by
          simp [r, rBase, hqz]
          exact z.property
        have hsz : s.val = z.val.2 := by
          calc
            s.val = ϕ y₀.val := hϕy.symm
            _ = sourceObservation p a (q y₀.val) := rfl
            _ = z.val.2 := by rw [hqz]; rfl
        refine ⟨r y₀, ⟨y₀, hyE, rfl⟩, ?_⟩
        have hEq : e s = p (r y₀) := by
          calc
            e s = firstDifferenceOnSection a s := he s
            _ = firstDifference a s.val := rfl
            _ = firstDifference a z.val.2 := by rw [hsz]
            _ = p (r y₀) := hps.symm
        exact hEq.symm.trans hse
    have hopenImage : IsOpen (e ''
        (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase))) :=
      e.isOpenMap _ hEsection.2
    rw [himagePR]
    exact hopenImage
  have hopenComp : IsOpenMap (p ∘ r) := by
    apply IsOpenMap.of_nhds_le
    intro y
    apply le_map_iff.2
    intro V hV
    obtain ⟨U, hUV, hUopen, hyU⟩ := mem_nhds_iff.mp hV
    obtain ⟨E, hE, hyE, hEU⟩ := exists_isClopen_mem_of_isOpen hUopen hyU
    have hopenE := himage E hE
    have hsub : p '' (r '' E) ⊆ (p ∘ r) '' V := by
      rintro b ⟨t, ⟨y₀, hy₀, rfl⟩, hpb⟩
      exact ⟨y₀, hUV (hEU hy₀), hpb⟩
    apply Filter.mem_of_superset (hopenE.mem_nhds
      ⟨r y, ⟨y, hyE, rfl⟩, rfl⟩)
    exact hsub
  refine ⟨Y₀, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨r, hr, hronto, ?_⟩
  exact hopenComp

/- The original extension assertion, with compact Hausdorff source and
zero-dimensional compact Hausdorff upstairs systems, retaining the forward
shadowing and time-zero factor quantifiers. -/
def claim : Prop :=
  ∀ (X : Type) (tX : TopologicalSpace X) (cX : @CompactSpace X tX)
    (hX : @T2Space X tX) (f : X → X),
    letI := tX
    letI := cX
    letI := hX
    Continuous f → HasShadowing f →
      ∃ (Y : Type) (tY : TopologicalSpace Y) (cY : @CompactSpace Y tY)
        (hY : @T2Space Y tY) (zY : @ZeroDimensionalSpace Y tY),
        letI := tY
        letI := cY
        letI := hY
        letI := zY
        ∃ (τ : Y → Y), Continuous τ ∧ HasShadowing τ ∧
          ∃ q : Y → X, Continuous q ∧ Function.Surjective q ∧ Semiconj q τ f

theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨A, ell, hAD, hconv, _hclosed, hcompact, hp, hopen, honto, _hU, hnores⟩ :=
    exists_compact_open_map_no_finite_closed_refinement
  obtain ⟨a, hgeneric⟩ := exists_generic_finite_graph_decision
  letI : CompactSpace (Space A natValue ell) := isCompact_iff_compactSpace.mp hcompact
  let p : Space A natValue ell → OnePoint ℕ := projection A natValue ell
  have hp' : Continuous p := by simpa [p] using hp
  have hopen' : IsOpenMap p := by simpa [p] using hopen
  have honto' : Function.Surjective p := by simpa [p] using honto
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp' (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  letI : CompactSpace (FreeFibreSource p a) := inferInstance
  letI : T2Space (FreeFibreSource p a) := inferInstance
  have hsourcec : Continuous (sourceDynamics p a) := sourceDynamics_continuous p a
  have hsources : HasShadowing (sourceDynamics p a) :=
    freeFibreSource_hasShadowing p a hp' honto' hopen'
  obtain ⟨Y, tY, cY, hY, zY, τ, hτc, hτs, q, hq, hqonto, hsem⟩ :=
    hclaim (FreeFibreSource p a) inferInstance inferInstance inferInstance
      (sourceDynamics p a) hsourcec hsources
  letI := tY
  letI := cY
  letI := hY
  letI := zY
  have hres := freeFibre_cover_forces_resolution
    p hp' honto' hopen' a hgeneric τ hτc hτs q hq hqonto hsem
  apply hnores
  simpa [p] using hres

end
end D5.S1.Dynamics.Shadowing.FreeFibreBoundary
