/- GID: D5/S3/Geometry/FiniteAcyclicFaceMatching
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteAcyclicFaceMatching
   mirror-E: none(waiver:finite-face-matching-infrastructure)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Disjoint nonempty face pairs and the directed Hasse graph admit finite source extraction. -/
import D5.S3.Geometry.FiniteVertexDominationCollapse
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Omega

/-! UNCOMPILED source attempt. The ordinary argument is the released CLI
`cli_actual_core_closure_and_free_pair_extraction_proof`. No Morse theorem,
topological conclusion, or free-pair selection is an input. Empty faces are
absent from the native complexes and from all matching endpoints. -/

noncomputable section
open Set Finset

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A positive-length directed walk, with its direction explicit. -/
inductive Walk {α : Type*} (r : α → α → Prop) : α → α → Prop
  | one {a b} : r a b → Walk r a b
  | cons {a b c} : r a b → Walk r b c → Walk r a c

namespace Walk

theorem trans {α : Type*} {r : α → α → Prop} {a b c : α}
    (h : Walk r a b) (k : Walk r b c) : Walk r a c := by
  revert k
  induction h with
  | one h => intro k; exact .cons h k
  | cons h t ih => intro k; exact .cons h (ih k)

theorem map {α β : Type*} {r : α → α → Prop} {q : β → β → Prop}
    (f : α → β) (hf : ∀ a b, r a b → q (f a) (f b))
    {a b : α} (h : Walk r a b) : Walk q (f a) (f b) := by
  induction h with
  | one h => exact .one (hf _ _ h)
  | cons h t ih => exact .cons (hf _ _ h) ih

end Walk

def Acyclic {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ a, ¬ Walk r a a

/-- Every nonempty induced finite subgraph of a DAG has an actual source.
The minimizing statistic is the number of strict ancestors in the finite set.
An incoming edge makes this ancestor set strictly smaller, not merely weakly
smaller. No prechosen topological order is required. -/
theorem finite_source {α : Type*} [DecidableEq α] (F : Finset α)
    (r : α → α → Prop) (ha : Acyclic r) (hne : F.Nonempty) :
    ∃ s ∈ F, ∀ t ∈ F, ¬ r t s := by
  classical
  let ancestors (s : α) := F.filter fun t => Walk r t s
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image F (fun s => (ancestors s).card) hne
  refine ⟨s, hs, ?_⟩
  intro t ht hts
  have hsub : ancestors t ⊆ ancestors s := by
    intro a ha'
    obtain ⟨haF, hat⟩ := Finset.mem_filter.mp ha'
    exact Finset.mem_filter.mpr ⟨haF, hat.trans (.one hts)⟩
  have htS : t ∈ ancestors s := Finset.mem_filter.mpr ⟨ht, .one hts⟩
  have htT : t ∉ ancestors t := by
    intro h
    exact ha t (Finset.mem_filter.mp h).2
  have hlt : (ancestors t).card < (ancestors s).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun he => htT (he.symm ▸ htS)⟩)
  exact (not_lt_of_ge (hmin t ht)) hlt

/-- A cover adds exactly one ORIGINAL vertex. -/
def Cover (a b : Finset V) : Prop := ∃ v ∉ a, b = insert v a

def upper (e : Finset V × V) : Finset V := insert e.2 e.1

def Incident (s : Finset V) (e : Finset V × V) : Prop :=
  s = e.1 ∨ s = upper e

/-- Only finite combinatorial data: disjoint actual codimension-one pairs.
In particular this structure has no collapse, core, map, or SDR field. -/
structure Pairing (K : PreAbstractSimplicialComplex V) where
  pairs : Finset (Finset V × V)
  lower_nonempty : ∀ e ∈ pairs, e.1.Nonempty
  apex_notMem : ∀ e ∈ pairs, e.2 ∉ e.1
  upper_mem : ∀ e ∈ pairs, upper e ∈ K
  disjoint : ∀ e ∈ pairs, ∀ f ∈ pairs, ∀ s,
    Incident s e → Incident s f → e = f

namespace Pairing

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

theorem lower_mem {e : Finset V × V} (he : e ∈ M.pairs) : e.1 ∈ K :=
  (K.isRelLowerSet_faces (M.upper_mem e he)).2
    (Finset.subset_insert _ _) (M.lower_nonempty e he)

theorem lower_ne_upper {e : Finset V × V} (he : e ∈ M.pairs) :
    e.1 ≠ upper e := by
  intro h
  exact M.apex_notMem e he (h.symm ▸ Finset.mem_insert_self _ _)

def Unmatched (s : Finset V) : Prop :=
  ∀ e ∈ M.pairs, ¬ Incident s e

/-- Matched covers point UP; every other cover points DOWN. -/
def Edge (a b : Finset V) : Prop :=
  a ∈ K ∧ b ∈ K ∧
    ((∃ e ∈ M.pairs, a = e.1 ∧ b = upper e) ∨
      (Cover b a ∧ ¬ ∃ e ∈ M.pairs, b = e.1 ∧ a = upper e))

def IsAcyclic : Prop := Acyclic M.Edge

def Saturated (L : PreAbstractSimplicialComplex V) : Prop :=
  ∀ e ∈ M.pairs, e.1 ∈ L ↔ upper e ∈ L

theorem saturated_self : M.Saturated K := by
  intro e he
  exact ⟨fun _ => M.upper_mem e he, fun _ => M.lower_mem he⟩

theorem upper_edge {e : Finset V × V} (he : e ∈ M.pairs) :
    M.Edge e.1 (upper e) :=
  ⟨M.lower_mem he, M.upper_mem e he, Or.inl ⟨e, he, rfl, rfl⟩⟩

/-- A source outside a saturated target must be a LOWER of a matching pair.
The conclusion includes the actual source assertion in the finite difference. -/
theorem source_lower (hacyc : M.IsAcyclic)
    {L T : PreAbstractSimplicialComplex V} (hLK : L ≤ K) (hTL : T ≤ L)
    (hL : M.Saturated L) (hT : M.Saturated T)
    (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T)
    (hne : L ≠ T) :
    ∃ e ∈ M.pairs, e.1 ∈ L ∧ e.1 ∉ T ∧
      ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1 := by
  classical
  let F := (faceSet L).filter fun s => s ∉ T
  have hF : F.Nonempty := by
    by_contra hempty
    apply hne
    apply le_antisymm _ hTL
    intro s hs
    by_contra hsT
    exact hempty ⟨s, Finset.mem_filter.mpr ⟨(mem_faceSet L s).mpr hs, hsT⟩⟩
  obtain ⟨a, ha, hsource⟩ := finite_source F M.Edge hacyc hF
  have haL : a ∈ L := (mem_faceSet L a).mp (Finset.mem_filter.mp ha).1
  have haT : a ∉ T := (Finset.mem_filter.mp ha).2
  have hmatched : ¬ M.Unmatched a := fun hu => haT (hcrit a haL hu)
  obtain ⟨e, he, hae⟩ : ∃ e ∈ M.pairs, Incident a e := by
    simpa only [Unmatched, not_forall, not_imp, not_not] using hmatched
  rcases hae with rfl | rfl
  · exact ⟨e, he, haL, haT, fun s hs hn =>
      hsource s (Finset.mem_filter.mpr ⟨(mem_faceSet L s).mpr hs, hn⟩)⟩
  · have hlL := (hL e he).mpr haL
    have hlT : e.1 ∉ T := fun ht => haT ((hT e he).mp ht)
    exact (hsource e.1 (Finset.mem_filter.mpr
      ⟨(mem_faceSet L e.1).mpr hlL, hlT⟩) (M.upper_edge he)).elim

/-- The source condition proves freeness in the WHOLE current complex.
For every vertex of a strict coface outside the lower, its immediate coface
would point down into the source unless it is the designated upper. This also
rules out every coface of higher codimension. -/
theorem source_free {L T : PreAbstractSimplicialComplex V}
    (hLK : L ≤ K) (hTL : T ≤ L) (e : Finset V × V) (he : e ∈ M.pairs)
    (hlL : e.1 ∈ L) (hlT : e.1 ∉ T)
    (hsource : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) :
    ∀ t ∈ L, e.1 ⊂ t → t = upper e := by
  intro t ht hlt
  have hver : ∀ v ∈ t, v ∉ e.1 → v = e.2 := by
    intro v hvt hvl
    let a := insert v e.1
    have haL : a ∈ L := (L.isRelLowerSet_faces ht).2
      (Finset.insert_subset hvt hlt.subset) ((M.lower_nonempty e he).mono (subset_insert _ _))
    have haT : a ∉ T := fun ha => hlT
      ((T.isRelLowerSet_faces ha).2 (subset_insert _ _) (M.lower_nonempty e he))
    have hp : ∃ f ∈ M.pairs, e.1 = f.1 ∧ a = upper f := by
      by_contra hp
      exact hsource a haL haT ⟨hLK haL, hLK hlL,
        Or.inr ⟨⟨v, hvl, rfl⟩, hp⟩⟩
    obtain ⟨f, hf, hlf, huf⟩ := hp
    have hfe : e = f := M.disjoint e he f hf e.1 (Or.inl rfl) (Or.inl hlf)
    subst f
    have hvu : v ∈ upper e := huf ▸ Finset.mem_insert_self v e.1
    exact (Finset.mem_insert.mp hvu).resolve_right hvl
  have hout : ∃ v ∈ t, v ∉ e.1 := by
    by_contra h
    have hsub : t ⊆ e.1 := by
      intro v hv
      by_contra hvl
      exact h ⟨v, hv, hvl⟩
    exact hlt.ne (Finset.Subset.antisymm hlt.subset hsub)
  obtain ⟨v, hvt, hvl⟩ := hout
  have hapex : e.2 ∈ t := by simpa only [hver v hvt hvl] using hvt
  apply Finset.Subset.antisymm
  · intro w hw
    by_cases hwl : w ∈ e.1
    · exact Finset.mem_insert_of_mem hwl
    · rw [hver w hw hwl]
      exact Finset.mem_insert_self _ _
  · exact Finset.insert_subset hapex hlt.subset

/-- Construct the native owner pair; no new pair or sequence owner is defined. -/
def sourcePair {L T : PreAbstractSimplicialComplex V} (hLK : L ≤ K)
    (hTL : T ≤ L) (hL : M.Saturated L) (e : Finset V × V)
    (he : e ∈ M.pairs) (hlL : e.1 ∈ L) (hlT : e.1 ∉ T)
    (hs : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) : CollapsePair V where
  ambient := L
  lower := e.1
  apex := e.2
  lower_nonempty := M.lower_nonempty e he
  apex_notMem := M.apex_notMem e he
  upper_mem := (hL e he).mp hlL
  free := M.source_free hLK hTL e he hlL hlT hs

end Pairing
end D5.S3.Geometry.FiniteAcyclicFaceMatching
