/- GID: D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Set.Image]
   utility: none
   digest: Compatible splicing and two complete-context substitutions retain global outputs. -/

import D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

/-! Boundary-preserving partial splicing of dependent raw joins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing

open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords

universe i u v
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

/-- A compatible pair of local records has a unique raw join on their union. -/
theorem compatible_splice_unique (A B : Set Node)
    (hdisj : Disjoint A B)
    (a : rawJoin Value S Γ A) (b : rawJoin Value S Γ B)
    (h : overlapBoundaryLeft Value S Γ A B a = overlapBoundaryRight Value S Γ A B b) :
    ∃! j : rawJoin Value S Γ (A ∪ B),
      j.val = spliceAssignment Value S Γ A B a b := by
  classical
  let N := {n : Node // n ∈ A ∪ B}
  let S' : N → Set Var := fun n => S n.val
  let Γ' : (n : N) → Set (Assignment Value (S' n)) := fun n => Γ n.val
  let P : Set N := {n | n.val ∈ A}
  have outside (n : N) : n ∈ Pᶜ ↔ n.val ∈ B := by
    constructor
    · intro hn
      exact n.property.resolve_left hn
    · intro hn hA
      exact Set.disjoint_left.mp hdisj hA hn
  have scopeA : componentScope S' P = componentScope S A := by
    ext x
    exact ⟨fun ⟨n, hn, hx⟩ => ⟨n.val, hn, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨⟨n, Or.inl hn⟩, hn, hx⟩⟩
  have scopeB : componentScope S' Pᶜ = componentScope S B := by
    ext x
    exact ⟨fun ⟨n, hn, hx⟩ => ⟨n.val, (outside n).mp hn, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨⟨n, Or.inr hn⟩, (outside _).mpr hn, hx⟩⟩
  have scopeU : componentScope S' Set.univ = componentScope S (A ∪ B) := by
    ext x
    exact ⟨fun ⟨n, _, hx⟩ => ⟨n.val, n.property, hx⟩,
      fun ⟨n, hn, hx⟩ => ⟨⟨n, hn⟩, Set.mem_univ _, hx⟩⟩
  let ar : rawJoin Value S' Γ' P :=
    ⟨restrictAssignment Value scopeA.subset a.val, fun n hn => a.property n.val hn⟩
  let br : rawJoin Value S' Γ' Pᶜ :=
    ⟨restrictAssignment Value scopeB.subset b.val,
      fun n hn => b.property n.val ((outside n).mp hn)⟩
  have compatible : br ∈ compatibleCompletions Value S' Γ' P ar := by
    funext x
    exact (congrFun h ⟨x.val, scopeA ▸ x.property.1, scopeB ▸ x.property.2⟩).symm
  obtain ⟨j, hj, _, _⟩ := compatible_union_restrictions Value S' Γ' P ar br compatible
  let k : rawJoin Value S Γ (A ∪ B) :=
    ⟨restrictAssignment Value scopeU.symm.subset j.val,
      fun n hn => j.property ⟨n, hn⟩ (Set.mem_univ _)⟩
  have hk : k.val = spliceAssignment Value S Γ A B a b := by
    funext x
    change j.val _ = _
    rw [hj]
    by_cases hx : x.val ∈ componentScope S A
    · have hx' : x.val ∈ componentScope S' P := scopeA.symm ▸ hx
      simp [unionAssignment, spliceAssignment, hx, hx', ar, restrictAssignment,
        Set.domRestrict₂]
    · have hx' : x.val ∉ componentScope S' P := by simpa only [scopeA] using hx
      simp [unionAssignment, spliceAssignment, hx, hx', br, restrictAssignment,
        Set.domRestrict₂]
  exact ⟨k, hk, fun l hl => Subtype.ext (hl.trans hk.symm)⟩

private theorem self_compatible (D : Set Node)
    (w : rawJoin Value S Γ Set.univ) :
    restrictRecord Value S Γ Dᶜ w ∈ compatibleCompletions Value S Γ D
      (restrictRecord Value S Γ D w) := by
  funext x
  rfl

private theorem reassemble (D : Set Node) (w : rawJoin Value S Γ Set.univ)
    (h : restrictRecord Value S Γ Dᶜ w ∈ compatibleCompletions Value S Γ D
      (restrictRecord Value S Γ D w)) :
    unionRecord Value S Γ D (restrictRecord Value S Γ D w)
      (restrictRecord Value S Γ Dᶜ w) h = w := by
  classical
  apply Subtype.ext
  rw [show (unionRecord Value S Γ D _ _ h).val = _ from
    (compatible_union_restrictions Value S Γ D _ _ h).choose_spec.1]
  funext x
  by_cases hx : x.val ∈ componentScope S D <;>
    simp [unionAssignment, hx, restrictRecord, restrictAssignment, Set.domRestrict₂]

/-- Local summary agreement and agreement outside two disjoint components
preserve every retained global output, by two complete-context substitutions. -/
theorem two_context_output_eq {A B : Set Node} {QA QB Output : Type*}
    (hdisj : Disjoint A B)
    (qA : rawJoin Value S Γ A → QA) (qB : rawJoin Value S Γ B → QB)
    (G : rawJoin Value S Γ Set.univ → Output)
    (hA : BoundaryOutputRetention Value S Γ A qA G)
    (hB : BoundaryOutputRetention Value S Γ B qB G)
    (w w' : rawJoin Value S Γ Set.univ)
    (hqa : qA (restrictRecord Value S Γ A w) = qA (restrictRecord Value S Γ A w'))
    (hqb : qB (restrictRecord Value S Γ B w) = qB (restrictRecord Value S Γ B w'))
    (hout : restrictRecord Value S Γ (A ∪ B)ᶜ w =
      restrictRecord Value S Γ (A ∪ B)ᶜ w') : G w = G w' := by
  classical
  obtain ⟨boundaryA, outputA⟩ := hA _ _ hqa
  have compatibleA : restrictRecord Value S Γ Aᶜ w ∈ compatibleCompletions Value S Γ A
      (restrictRecord Value S Γ A w') :=
    (self_compatible Value S Γ A w).trans boundaryA
  let middle := unionRecord Value S Γ A (restrictRecord Value S Γ A w')
    (restrictRecord Value S Γ Aᶜ w) compatibleA
  have middleA : restrictRecord Value S Γ A middle = restrictRecord Value S Γ A w' :=
    (compatible_union_restrictions Value S Γ A _ _ compatibleA).choose_spec.2.1
  have middleAc : restrictRecord Value S Γ Aᶜ middle = restrictRecord Value S Γ Aᶜ w :=
    (compatible_union_restrictions Value S Γ A _ _ compatibleA).choose_spec.2.2
  have middleB : restrictRecord Value S Γ B middle = restrictRecord Value S Γ B w := by
    apply Subtype.ext
    funext x
    obtain ⟨n, hn, hnx⟩ := x.property
    have hnA : n ∉ A := fun h => Set.disjoint_left.mp hdisj h hn
    exact congrFun (congrArg Subtype.val middleAc) ⟨x.val, n, hnA, hnx⟩
  have middleBc : restrictRecord Value S Γ Bᶜ middle = restrictRecord Value S Γ Bᶜ w' := by
    apply Subtype.ext
    funext x
    obtain ⟨n, hn, hnx⟩ := x.property
    by_cases hnA : n ∈ A
    · exact congrFun (congrArg Subtype.val middleA) ⟨x.val, n, hnA, hnx⟩
    · have hleft := congrFun (congrArg Subtype.val middleAc) ⟨x.val, n, hnA, hnx⟩
      have hright := congrFun (congrArg Subtype.val hout)
        ⟨x.val, n, fun hm => hm.elim hnA hn, hnx⟩
      exact hleft.trans hright
  have first : G w = G middle := by
    have step := outputA (restrictRecord Value S Γ Aᶜ w)
      (self_compatible Value S Γ A w) compatibleA
    rw [reassemble Value S Γ A w] at step
    exact step
  have middleQ : qB (restrictRecord Value S Γ B middle) =
      qB (restrictRecord Value S Γ B w') := (congrArg qB middleB).trans hqb
  have compatibleB : restrictRecord Value S Γ Bᶜ middle ∈
      compatibleCompletions Value S Γ B (restrictRecord Value S Γ B w') := by
    rw [middleBc]
    exact self_compatible Value S Γ B w'
  have second := (hB _ _ middleQ).2 (restrictRecord Value S Γ Bᶜ middle)
    (self_compatible Value S Γ B middle) compatibleB
  rw [reassemble Value S Γ B middle] at second
  have last : unionRecord Value S Γ B (restrictRecord Value S Γ B w')
      (restrictRecord Value S Γ Bᶜ middle) compatibleB = w' := by
    simpa only [middleBc] using
      reassemble Value S Γ B w' (self_compatible Value S Γ B w')
  rw [last] at second
  exact first.trans second

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

end D5.S3.ConceptDynamics.Gluing.BoundaryObservationSplicing
