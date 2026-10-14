/- GID: D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/TaggedCompactSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent actual tags form a compact open surjection over OnePoint Nat. -/

import D5.S3.Topology.AlmostDisjoint.ConvergentBranches
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Maps.Basic

open Set Filter Topology
open scoped OnePoint
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches

namespace D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace

-- The family is indexed by its subtype of distinct actual members.

attribute [local instance] Classical.propDecidable

variable (A : Set (Set ℕ))

abbrev Gamma := A ⊕ ℕ
abbrev Ambient := OnePoint ℕ × unitInterval × (Gamma A → Bool)

def zeroVector : Gamma A → Bool := fun _ => false

noncomputable def tagVector (a : A) : Gamma A → Bool := by
  classical
  exact fun γ => decide (γ = Sum.inl a)

noncomputable def natVector (n : ℕ) : Gamma A → Bool := by
  classical
  exact fun γ => match γ with
    | Sum.inl a => decide (n ∈ a.val)
    | Sum.inr m => decide (m = n)

def core (b : OnePoint ℕ) (r : unitInterval) : Ambient A :=
  (b,r,zeroVector A)

noncomputable def naturalPoint (u : ℕ → unitInterval) (n : ℕ) : Ambient A :=
  ((n : OnePoint ℕ),u n,natVector A n)

noncomputable def taggedPoint (ell : A → unitInterval) (a : A)
    (b : OnePoint ℕ) : Ambient A := (b,ell a,tagVector A a)

noncomputable def valueSection (u : ℕ → unitInterval) (ell : A → unitInterval)
    (a : A) (b : OnePoint ℕ) : unitInterval := by
  classical
  exact b.elim (ell a) (fun n => if n ∈ a.val then u n else ell a)

noncomputable def vectorSection (a : A) (b : OnePoint ℕ) : Gamma A → Bool := by
  classical
  exact b.elim (tagVector A a) (fun n =>
    if n ∈ a.val then natVector A n else tagVector A a)

noncomputable def memberSection (u : ℕ → unitInterval) (ell : A → unitInterval)
    (a : A) (b : OnePoint ℕ) : Ambient A :=
  (b,valueSection A u ell a b,vectorSection A a b)

def literalSpace (u : ℕ → unitInterval) (ell : A → unitInterval) : Set (Ambient A) :=
  {x | x.2.2 = zeroVector A} ∪
    (range (naturalPoint A u) ∪
      {x | ∃ a : A, ∃ n : ℕ, n ∉ a.val ∧ x = taggedPoint A ell a (n : OnePoint ℕ)} ∪
      range (fun a : A => taggedPoint A ell a ∞))

private theorem modified_value_tendsto (u : ℕ → unitInterval) (E : Set ℕ)
    (r : unitInterval) (hc : ConvergesOn u E r) :
    Tendsto (fun n => if n ∈ E then u n else r) cofinite (𝓝 r) := by
  classical
  apply Filter.tendsto_def.mpr
  intro V hV
  apply Filter.mem_cofinite.mpr
  apply (hc V hV).subset
  intro n hn
  change (if n ∈ E then u n else r) ∉ V at hn
  by_cases hnE : n ∈ E
  · exact ⟨hnE,by simpa only [if_pos hnE,mem_preimage] using hn⟩
  · rw [if_neg hnE] at hn
    exact False.elim (hn (mem_of_mem_nhds hV))

private theorem valueSection_continuous (u : ℕ → unitInterval) (ell : A → unitInterval)
    (hc : ∀ a : A, ConvergesOn u a.val (ell a)) (a : A) :
    Continuous (valueSection A u ell a) := by
  apply (OnePoint.continuous_iff_from_discrete _).mpr
  simpa only [valueSection,OnePoint.elim_some,OnePoint.elim_infty] using
    modified_value_tendsto u a.val (ell a) (hc a)

private theorem vectorSection_continuous (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (a : A) :
    Continuous (vectorSection A a) := by
  classical
  apply (OnePoint.continuous_iff_from_discrete _).mpr
  apply tendsto_pi_nhds.mpr
  intro γ
  have heq : (fun n : ℕ => vectorSection A a (n : OnePoint ℕ) γ) =ᶠ[cofinite]
      (fun _ => vectorSection A a ∞ γ) := by
    rcases γ with b | m
    · by_cases hba : b = a
      · subst b
        apply Eventually.of_forall
        intro n
        by_cases hn : n ∈ a.val <;>
          simp [vectorSection,tagVector,natVector,hn]
      · have hab : (a.val ∩ b.val).Finite :=
          had a.property b.property (fun h => hba (Subtype.ext h.symm))
        filter_upwards [hab.compl_mem_cofinite] with n hn
        by_cases hna : n ∈ a.val
        · have hnb : n ∉ b.val := fun h => hn ⟨hna,h⟩
          simp [vectorSection,tagVector,natVector,hna,hnb,hba]
        · simp [vectorSection,hna]
    · filter_upwards [(finite_singleton m).compl_mem_cofinite] with n hn
      have hnm : m ≠ n := fun h => hn (by simpa [h])
      by_cases hna : n ∈ a.val
      · simp [vectorSection,tagVector,natVector,hna,hnm]
      · simp [vectorSection,hna]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

private theorem section_continuous (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a)) (a : A) :
    Continuous (memberSection A u ell a) :=
  continuous_id.prodMk
    ((valueSection_continuous A u ell hc a).prodMk (vectorSection_continuous A had a))

private theorem closed_zero_and_tagged {X Γ : Type*} [TopologicalSpace X]
    (tag : X → Γ → Bool) (htag : Continuous tag) (K : Γ → Set X)
    (hK : ∀ γ, IsClosed (K γ))
    (hcoherent : ∀ γ δ x, x ∈ K γ → tag x δ ≠ false → x ∈ K δ) :
    IsClosed ({x | ∀ γ, tag x γ = false} ∪ ⋃ γ, K γ) := by
  classical
  have heq : {x | ∀ γ, tag x γ = false} ∪ ⋃ γ, K γ =
      ⋂ γ, ({x | tag x γ = false} ∪ K γ) := by
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · rintro (hzero | ⟨γ,hγ⟩)
      · exact fun δ => Or.inl (hzero δ)
      · intro δ
        by_cases hδ : tag x δ = false
        · exact Or.inl hδ
        · exact Or.inr (hcoherent γ δ x hγ hδ)
    · intro hx
      by_cases hzero : ∀ γ, tag x γ = false
      · exact Or.inl hzero
      · push Not at hzero
        obtain ⟨γ,hγ⟩ := hzero
        exact Or.inr ⟨γ,(hx γ).resolve_left hγ⟩
  rw [heq]
  apply isClosed_iInter
  intro γ
  have hc : Continuous (fun x => tag x γ) := (continuous_apply γ).comp htag
  exact (isClosed_singleton.preimage hc).union (hK γ)



-- The literal space is an intersection of closed
-- coordinate constraints. The zero-vector core contains every value, including
-- values not in the family limit image.
private noncomputable def coordinatePiece (u : ℕ → unitInterval) (ell : A → unitInterval) :
    Gamma A → Set (Ambient A) := fun γ => match γ with
    | Sum.inl a => range (memberSection A u ell a)
    | Sum.inr n => {naturalPoint A u n}

private theorem section_mem_literal (u : ℕ → unitInterval) (ell : A → unitInterval)
    (a : A) (b : OnePoint ℕ) : memberSection A u ell a b ∈ literalSpace A u ell := by
  classical
  cases b using OnePoint.rec with
  | infty =>
      right
      right
      exact ⟨a,rfl⟩
  | coe n =>
      by_cases hn : n ∈ a.val
      · right
        left
        left
        exact ⟨n,by simp [memberSection,valueSection,vectorSection,naturalPoint,hn]⟩
      · right
        left
        right
        exact ⟨a,n,hn,by simp [memberSection,valueSection,vectorSection,taggedPoint,hn]⟩

private theorem literal_as_coordinate_union (u : ℕ → unitInterval)
    (ell : A → unitInterval) :
    literalSpace A u ell = {x | ∀ γ, x.2.2 γ = false} ∪
      ⋃ γ, coordinatePiece A u ell γ := by
  classical
  ext x
  constructor
  · rintro (hz | ((⟨n,rfl⟩ | ⟨a,n,hn,rfl⟩) | ⟨a,rfl⟩))
    · left
      intro γ
      rw [hz]
      rfl
    · right
      exact mem_iUnion.mpr ⟨Sum.inr n,rfl⟩
    · right
      apply mem_iUnion.mpr
      refine ⟨Sum.inl a,?_⟩
      exact ⟨(n : OnePoint ℕ),by simp [memberSection,valueSection,vectorSection,taggedPoint,hn]⟩
    · right
      exact mem_iUnion.mpr ⟨Sum.inl a,⟨∞,rfl⟩⟩
  · rintro (hz | h)
    · left
      funext γ
      exact hz γ
    · obtain ⟨γ,hγ⟩ := mem_iUnion.mp h
      cases γ with
      | inl a =>
          obtain ⟨b,rfl⟩ := hγ
          exact section_mem_literal A u ell a b
      | inr n =>
          have hx : x = naturalPoint A u n := hγ
          subst x
          exact Or.inr (Or.inl (Or.inl (mem_range_self n)))

private theorem coordinatePiece_closed (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a))
    (γ : Gamma A) : IsClosed (coordinatePiece A u ell γ) := by
  cases γ with
  | inl a =>
      exact (isCompact_range (section_continuous A u ell had hc a)).isClosed
  | inr n =>
      exact isClosed_singleton

private theorem coordinatePiece_coherent (u : ℕ → unitInterval) (ell : A → unitInterval)
    (γ δ : Gamma A) (x : Ambient A)
    (hγ : x ∈ coordinatePiece A u ell γ) (hδ : x.2.2 δ ≠ false) :
    x ∈ coordinatePiece A u ell δ := by
  classical
  cases γ with
  | inl a =>
      obtain ⟨b,rfl⟩ := hγ
      cases b using OnePoint.rec with
      | infty =>
          have heq : δ = Sum.inl a := by
            simpa [memberSection,vectorSection,tagVector] using hδ
          subst δ
          exact mem_range_self ∞
      | coe n =>
          by_cases hn : n ∈ a.val
          · have hs : memberSection A u ell a (n : OnePoint ℕ) = naturalPoint A u n := by
              simp [memberSection,valueSection,vectorSection,naturalPoint,hn]
            rw [hs] at hδ ⊢
            cases δ with
            | inl c =>
                have hnc : n ∈ c.val := by simpa [naturalPoint,natVector] using hδ
                exact ⟨(n : OnePoint ℕ),by simp [memberSection,valueSection,vectorSection,naturalPoint,hnc]⟩
            | inr m =>
                have hmn : m = n := by simpa [naturalPoint,natVector] using hδ
                subst m
                rfl
          · have heq : δ = Sum.inl a := by
              simpa [memberSection,vectorSection,tagVector,hn] using hδ
            subst δ
            exact mem_range_self (n : OnePoint ℕ)
  | inr n =>
      have hx : x = naturalPoint A u n := hγ
      subst x
      cases δ with
      | inl a =>
          have hn : n ∈ a.val := by simpa [naturalPoint,natVector] using hδ
          exact ⟨(n : OnePoint ℕ),by simp [memberSection,valueSection,vectorSection,naturalPoint,hn]⟩
      | inr m =>
          have hmn : m = n := by simpa [naturalPoint,natVector] using hδ
          subst m
          rfl

private theorem literalSpace_isClosed (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a)) :
    IsClosed (literalSpace A u ell) := by
  rw [literal_as_coordinate_union A u ell]
  apply closed_zero_and_tagged (fun x : Ambient A => x.2.2)
    continuous_snd.snd (coordinatePiece A u ell)
  · exact coordinatePiece_closed A u ell had hc
  · exact coordinatePiece_coherent A u ell

-- Reuse IsOpenMap.of_sections: only continuity at the selected base point is
-- required. At finite n every map is continuous at n, because n is isolated.
private theorem continuousAt_finite {X : Type*} [TopologicalSpace X]
    (g : OnePoint ℕ → X) (n : ℕ) : ContinuousAt g (n : OnePoint ℕ) := by
  rw [OnePoint.continuousAt_coe]
  exact continuous_of_discreteTopology.continuousAt

-- Further next step: continuous subtype sections through every infinity point;
-- overwrite a core memberSection at a finite n to pass through any selected fiber point.
-- These sections are then consumed directly by IsOpenMap.of_sections.



abbrev Space (u : ℕ → unitInterval) (ell : A → unitInterval) :=
  ↥(literalSpace A u ell)

def projection (u : ℕ → unitInterval) (ell : A → unitInterval) :
    Space A u ell → OnePoint ℕ := fun x => x.val.1

def coreLift (u : ℕ → unitInterval) (ell : A → unitInterval)
    (r : unitInterval) (b : OnePoint ℕ) : Space A u ell :=
  ⟨core A b r,Or.inl rfl⟩

noncomputable def sectionLift (u : ℕ → unitInterval) (ell : A → unitInterval)
    (a : A) (b : OnePoint ℕ) : Space A u ell :=
  ⟨memberSection A u ell a b,section_mem_literal A u ell a b⟩

noncomputable def naturalLift (u : ℕ → unitInterval) (ell : A → unitInterval)
    (n : ℕ) : Space A u ell :=
  ⟨naturalPoint A u n, Or.inr (Or.inl (Or.inl (mem_range_self n)))⟩

private theorem sectionLift_continuous (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a)) (a : A) :
    Continuous (sectionLift A u ell a) :=
  (section_continuous A u ell had hc a).subtype_mk (section_mem_literal A u ell a)

private theorem coreLift_continuous (u : ℕ → unitInterval) (ell : A → unitInterval)
    (r : unitInterval) : Continuous (coreLift A u ell r) :=
  (continuous_id.prodMk (continuous_const.prodMk continuous_const)).subtype_mk
    (fun _ => Or.inl rfl)

private theorem section_through_infty (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a))
    (x : Space A u ell) (hx : projection A u ell x = ∞) :
    ∃ g : OnePoint ℕ → Space A u ell,
      ContinuousAt g ∞ ∧ g ∞ = x ∧ Function.RightInverse g (projection A u ell) := by
  classical
  rcases x.property with hz | ((hn | htag) | hinf)
  · refine ⟨coreLift A u ell x.val.2.1,(coreLift_continuous A u ell _).continuousAt,?_,fun _ => rfl⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hx.symm
    · exact Prod.ext rfl hz.symm
  · obtain ⟨n,hn⟩ := hn
    have hbase : (n : OnePoint ℕ) = ∞ := (congrArg Prod.fst hn).trans hx
    exact False.elim (OnePoint.coe_ne_infty n hbase)
  · obtain ⟨a,n,hna,heq⟩ := htag
    have hbase : (n : OnePoint ℕ) = ∞ := (congrArg Prod.fst heq).symm.trans hx
    exact False.elim (OnePoint.coe_ne_infty n hbase)
  · obtain ⟨a,ha⟩ := hinf
    refine ⟨sectionLift A u ell a,(sectionLift_continuous A u ell had hc a).continuousAt,?_,fun _ => rfl⟩
    apply Subtype.ext
    exact ha

private theorem projection_open (u : ℕ → unitInterval) (ell : A → unitInterval)
    (had : A.Pairwise (fun E F => (E ∩ F).Finite)) (hc : ∀ a : A, ConvergesOn u a.val (ell a)) :
    IsOpenMap (projection A u ell) := by
  classical
  apply IsOpenMap.of_sections
  intro x
  cases hb : projection A u ell x using OnePoint.rec with
  | infty =>
      simpa only [hb] using section_through_infty A u ell had hc x hb
  | coe n =>
      let g : OnePoint ℕ → Space A u ell := fun b =>
        if b = (n : OnePoint ℕ) then x else coreLift A u ell 0 b
      refine ⟨g,?_,?_,?_⟩
      · exact continuousAt_finite g n
      · simp [g]
      · intro b
        by_cases heq : b = (n : OnePoint ℕ)
        · simp [g,heq,hb]
        · simp only [g,if_neg heq,projection,coreLift,core]


-- Each actual almost-disjoint member has a clopen memberSection range, selected by
-- its own true coordinate. This is the seam consumed by closed-piece extraction.
private theorem section_own_tag (u : ℕ → unitInterval) (ell : A → unitInterval)
    (a : A) (b : OnePoint ℕ) :
    (memberSection A u ell a b).2.2 (Sum.inl a) = true := by
  classical
  cases b using OnePoint.rec with
  | infty => simp [memberSection,vectorSection,tagVector]
  | coe n =>
      by_cases hn : n ∈ a.val <;> simp [memberSection,vectorSection,tagVector,natVector,hn]

private theorem tagged_literal_in_section (u : ℕ → unitInterval)
    (ell : A → unitInterval) (a : A) (x : Space A u ell)
    (hx : x.val.2.2 (Sum.inl a) = true) :
    x ∈ range (sectionLift A u ell a) := by
  have hzero : ¬ ∀ γ, x.val.2.2 γ = false := by
    intro hz
    have hf := hz (Sum.inl a)
    rw [hx] at hf
    exact Bool.noConfusion hf
  have hpiece : x.val ∈ coordinatePiece A u ell (Sum.inl a) := by
    have hmem : x.val ∈ {x | ∀ γ, x.2.2 γ = false} ∪
        ⋃ γ, coordinatePiece A u ell γ := by
      rw [← literal_as_coordinate_union A u ell]
      exact x.property
    obtain ⟨γ,hγ⟩ := mem_iUnion.mp (hmem.resolve_left hzero)
    exact coordinatePiece_coherent A u ell γ (Sum.inl a) x.val hγ (by simpa [hx])
  obtain ⟨b,hb⟩ := hpiece
  exact ⟨b,Subtype.ext hb⟩

private theorem section_range_eq_tag (u : ℕ → unitInterval)
    (ell : A → unitInterval) (a : A) :
    range (sectionLift A u ell a) = {x | x.val.2.2 (Sum.inl a) = true} := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact section_own_tag A u ell a b
  · exact tagged_literal_in_section A u ell a x

private theorem section_range_clopen (u : ℕ → unitInterval)
    (ell : A → unitInterval) (a : A) :
    IsClopen (range (sectionLift A u ell a)) := by
  rw [section_range_eq_tag A u ell a]
  have hc : Continuous (fun x : Space A u ell => x.val.2.2 (Sum.inl a)) :=
    (continuous_apply (Sum.inl a)).comp
      (continuous_snd.snd.comp continuous_subtype_val)
  exact (isClopen_discrete ({true} : Set Bool)).preimage hc

-- The bundled construction consumes all preceding helpers.
-- It does not assert the finite-refinement obstruction or the full base classification.
theorem literal_closed_compact_open_surjection (u : ℕ → unitInterval)
    (ell : A → unitInterval) (had : A.Pairwise (fun E F => (E ∩ F).Finite))
    (hc : ∀ a : A, ConvergesOn u a.val (ell a)) :
    IsClosed (literalSpace A u ell) ∧ IsCompact (literalSpace A u ell) ∧
      Continuous (projection A u ell) ∧ IsOpenMap (projection A u ell) ∧
      Function.Surjective (projection A u ell) ∧
      (∀ a : A, Continuous (sectionLift A u ell a)) ∧
      (∀ a : A, IsClopen (range (sectionLift A u ell a))) := by
  have hclosed := literalSpace_isClosed A u ell had hc
  refine ⟨hclosed,hclosed.isCompact,continuous_fst.comp continuous_subtype_val,
    projection_open A u ell had hc,?_,
    sectionLift_continuous A u ell had hc,section_range_clopen A u ell⟩
  intro b
  exact ⟨coreLift A u ell 0 b,rfl⟩

end D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
