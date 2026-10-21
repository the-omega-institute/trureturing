/- GID: D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Set.Image]
   utility: none
   digest: Boundary-preserving partial splicing has an exact compatibility domain and image. -/

import D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

/-! Boundary-preserving partial splicing of dependent raw joins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing

open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

universe i u v w
variable {Node : Type i} {Var : Type u}
variable (Value : Var → Type v) (S : Node → Set Var)
variable (Γ : (n : Node) → Set (Assignment Value (S n)))

/-- The common variable carrier seen by two components. -/
def overlapScope (A B : Set Node) : Set Var :=
  componentScope S A ∩ componentScope S B

/-- The left component restricted to the variables shared by two components. -/
def overlapBoundaryLeft (A B : Set Node)
    (a : rawJoin Value S Γ A) : Assignment Value (overlapScope S A B) :=
  restrictAssignment Value Set.inter_subset_left a.val

/-- The right component restricted to the variables shared by two components. -/
def overlapBoundaryRight (A B : Set Node)
    (b : rawJoin Value S Γ B) : Assignment Value (overlapScope S A B) :=
  restrictAssignment Value Set.inter_subset_right b.val

/-- The pointwise union of two records whose overlap values agree. -/
noncomputable def spliceAssignment (A B : Set Node)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B) :
    Assignment Value (componentScope S (A ∪ B)) := by
  classical
  exact fun x => if hx : x.val ∈ componentScope S A then
    a.val ⟨x.val, hx⟩
  else
    b.val ⟨x.val, by
      obtain ⟨n, hn, hnx⟩ := x.property
      exact ⟨n, hn.resolve_left (by
        intro hnA
        exact hx ⟨n, hnA, hnx⟩), hnx⟩⟩

private theorem scope_union (A B : Set Node) :
    componentScope S (A ∪ B) = componentScope S A ∪ componentScope S B := by
  ext x
  constructor
  · rintro ⟨n, hn, hx⟩
    exact Or.imp (fun h => ⟨n, h, hx⟩) (fun h => ⟨n, h, hx⟩) hn
  · rintro (⟨n, hn, hx⟩ | ⟨n, hn, hx⟩)
    · exact ⟨n, Or.inl hn, hx⟩
    · exact ⟨n, Or.inr hn, hx⟩

private theorem splice_left (A B : Set Node)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B)
    (x : componentScope S A) :
    spliceAssignment Value S Γ A B a b
      ⟨x.val, by rw [scope_union]; exact Or.inl x.property⟩ = a.val x := by
  simp only [spliceAssignment, dif_pos x.property]

private theorem splice_right (A B : Set Node)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B)
    (h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b)
    (x : componentScope S B) :
    spliceAssignment Value S Γ A B a b
      ⟨x.val, by rw [scope_union]; exact Or.inr x.property⟩ = b.val x := by
  classical
  by_cases hx : x.val ∈ componentScope S A
  · have hi : x.val ∈ overlapScope S A B := ⟨hx, x.property⟩
    have hv := congrFun h ⟨x.val, hi⟩
    simpa [spliceAssignment, hx, overlapBoundaryLeft, overlapBoundaryRight,
      restrictAssignment, Set.domRestrict₂] using hv
  · simp only [spliceAssignment, dif_neg hx]

/-- A compatible pair of local records has a unique raw join on their union. -/
theorem compatible_splice_unique (A B : Set Node)
    (hdisj : Disjoint A B)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B)
    (h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b) :
    ∃! j : rawJoin Value S Γ (A ∪ B),
      j.val = spliceAssignment Value S Γ A B a b := by
  classical
  have hmem : spliceAssignment Value S Γ A B a b ∈
      rawJoin Value S Γ (A ∪ B) := by
    intro n hn
    rcases hn with hnA | hnB
    · have ha := a.property n hnA
      convert ha using 1
      funext x
      exact splice_left Value S Γ A B a b ⟨x.val, n, hnA, x.property⟩
    · have hb := b.property n hnB
      convert hb using 1
      funext x
      by_cases hx : x.val ∈ componentScope S A
      · have hi : x.val ∈ overlapScope S A B := ⟨hx, ⟨n, hnB, x.property⟩⟩
        have hv := congrFun h ⟨x.val, hi⟩
        simpa [spliceAssignment, hx, overlapBoundaryLeft, overlapBoundaryRight,
          restrictAssignment, Set.domRestrict₂] using hv
      · simpa [spliceAssignment, hx, restrictAssignment, Set.domRestrict₂]
  refine ⟨⟨spliceAssignment Value S Γ A B a b, hmem⟩, rfl, ?_⟩
  intro k hk
  exact Subtype.ext hk

/-- Equal local summaries transport an initially compatible overlap to the
corresponding pair of replacement records. -/
theorem compatible_overlap_transport {A B : Set Node} {QA QB : Type*}
    (qA : rawJoin Value S Γ A → QA)
    (qB : rawJoin Value S Γ B → QB)
    (hA : ∀ a a', qA a = qA a' →
      overlapBoundaryLeft Value S Γ A B a = overlapBoundaryLeft Value S Γ A B a')
    (hB : ∀ b b', qB b = qB b' →
      overlapBoundaryRight Value S Γ A B b = overlapBoundaryRight Value S Γ A B b')
    (a a' : rawJoin Value S Γ A) (b b' : rawJoin Value S Γ B)
    (hab : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b)
    (hqa : qA a = qA a') (hqb : qB b = qB b') :
    overlapBoundaryLeft Value S Γ A B a' = overlapBoundaryRight Value S Γ A B b' := by
  exact (hA a a' hqa).symm.trans (hab.trans (hB b b' hqb))

/-- A partial splice graph records exactly the boundary-compatible summary pairs. -/
def spliceGraph {A B : Set Node} {QA QB QC : Type*}
    (hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA)
    (qB : rawJoin Value S Γ B → QB)
    (qC : rawJoin Value S Γ (A ∪ B) → QC) :
    Set ((QA × QB) × QC) :=
  {p | ∃ (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B),
    ∃ h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b,
      p = ((qA a, qB b), qC (compatible_splice_unique Value S Γ A B hdisj a b h).choose)}

/-- If local summaries preserve the complete overlap and the union summary,
then the splice graph is single-valued on its exact compatibility domain. -/
theorem spliceGraph_single_valued {A B : Set Node} {QA QB QC : Type*}
    (hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA)
    (qB : rawJoin Value S Γ B → QB)
    (qC : rawJoin Value S Γ (A ∪ B) → QC)
    (hA : ∀ a a', qA a = qA a' →
      overlapBoundaryLeft Value S Γ A B a = overlapBoundaryLeft Value S Γ A B a')
    (hB : ∀ b b', qB b = qB b' →
      overlapBoundaryRight Value S Γ A B b = overlapBoundaryRight Value S Γ A B b')
    (hC : ∀ a a' b b' (ha : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b)
      (ha' : overlapBoundaryLeft Value S Γ A B a' = overlapBoundaryRight Value S Γ A B b')
      (hqa : qA a = qA a') (hqb : qB b = qB b'),
      qC (compatible_splice_unique Value S Γ A B hdisj a b ha).choose =
        qC (compatible_splice_unique Value S Γ A B hdisj a' b' ha').choose) :
    ∀ x y : (QA × QB) × QC, x ∈ spliceGraph Value S Γ hdisj qA qB qC →
      y ∈ spliceGraph Value S Γ hdisj qA qB qC → x.1 = y.1 → x.2 = y.2 := by
  intro x y hx hy hxy
  rcases hx with ⟨a, b, hab, rfl⟩
  rcases hy with ⟨a', b', hab', rfl⟩
  simp only at hxy
  have hqa : qA a = qA a' := by
    simpa using congrArg Prod.fst hxy
  have hqb : qB b = qB b' := by
    simpa using congrArg Prod.snd hxy
  have hab' := compatible_overlap_transport Value S Γ qA qB hA hB
    a a' b b' hab hqa hqb
  exact hC a a' b b' hab hab' hqa hqb

/-- The graph's domain is exactly the image of compatible summary pairs. -/
theorem spliceGraph_domain {A B : Set Node} {QA QB QC : Type*}
    (hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA)
    (qB : rawJoin Value S Γ B → QB)
    (qC : rawJoin Value S Γ (A ∪ B) → QC) :
    {z : QA × QB | ∃ a b,
      qA a = z.1 ∧ qB b = z.2 ∧
      overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b} =
      {z | ∃ c : (QA × QB) × QC, c ∈ spliceGraph Value S Γ hdisj qA qB qC ∧ c.1 = z} := by
  ext z
  constructor
  · rintro ⟨a, b, hqa, hqb, hab⟩
    have hz : (qA a, qB b) = z := Prod.ext hqa hqb
    refine ⟨((qA a, qB b), qC (compatible_splice_unique Value S Γ A B hdisj a b hab).choose), ?_, hz⟩
    exact ⟨a, b, hab, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    rcases hc with ⟨a, b, hab, rfl⟩
    exact ⟨a, b, rfl, rfl, hab⟩

/-- The reachable union observations are exactly the observations of compatible
local pairs; no representative choice for a quotient is required. -/
theorem spliceGraph_range {A B : Set Node} {QA QB QC : Type*}
    (hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA)
    (qB : rawJoin Value S Γ B → QB)
    (qC : rawJoin Value S Γ (A ∪ B) → QC) :
    {z : QC | ∃ c : (QA × QB) × QC,
      c ∈ spliceGraph Value S Γ hdisj qA qB qC ∧ c.2 = z} =
      {z : QC | ∃ (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B),
        ∃ h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b,
          qC (compatible_splice_unique Value S Γ A B hdisj a b h).choose = z} := by
  ext z
  constructor
  · rintro ⟨c, ⟨a, b, h, rfl⟩, rfl⟩
    exact ⟨a, b, h, rfl⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨((qA a, qB b), qC (compatible_splice_unique Value S Γ A B hdisj a b h).choose),
      ⟨a, b, h, rfl⟩, rfl⟩


end D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
