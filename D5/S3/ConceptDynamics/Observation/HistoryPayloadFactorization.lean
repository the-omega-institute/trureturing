/- GID: D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Observation/HistoryPayloadFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   proof_shape: bind-only; admission_basis: atom-required-bridge
   atom: aea75d31b5b1ebb80a97b4ee9e2de5cdd0e488822c18f8a8f62c717675fb184a
   source_clause: QI-ASSIGN/QI-JOIN/QI-BOUNDARY/QI-ADMISSION-SIGNATURE/QI-P9 complete-complement pointwise tests
   consumer: local_completion_global_tests -> mem_completion_payload_iff -> compatible_union_restrictions -> pinned dependent-function gluing
   anchors: [TopCat.Presheaf.toTypes_isSheaf, TopCat.Sheaf.existsUnique_gluing', Set.domRestrict₂]
   utility: none
   digest: Realized-image factors recover admission and complete local completion sets. -/

import D5.S0.Rewriting.Quotients.SplitSurjectionFactorization
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Restrict
import Mathlib.Topology.Sheaves.SheafOfFunctions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization

open D5.S0.Rewriting.Quotients.SplitSurjectionFactorization
open CategoryTheory Limits TopologicalSpace Opens
open TopCat

universe u v w i

/-- Exact recovery on the realized image, including empty carriers and independent
universes. The split-surjection theorem owns existence and uniqueness. -/
theorem ker_beta_subset_ker_payload_iff_unique_factorization
    {X : Type u} {B : Type v} {Z : Type w} (β : X → B) (P : X → Z) :
    Setoid.ker β ≤ Setoid.ker P ↔
      ∃! φ : Set.range β → Z, P = φ ∘ Set.rangeFactorization β := by
  constructor
  · intro h
    exact split_surjection_factorization (Set.rangeFactorization β) P
      (Set.rangeSplitting β)
      (fun _ _ hxy => h (congrArg Subtype.val hxy))
      (Set.leftInverse_rangeSplitting β)
  · rintro ⟨φ, hφ, _⟩ x y hxy
    rw [hφ]
    exact congrArg φ (Subtype.ext hxy)

/-- The two-valued indicator of K restricted to the raw global join J. -/
noncomputable def admissionIndicator {X : Type u} (J K : Set X) : J → Bool :=
  fun x => @decide (x.val ∈ K) (Classical.propDecidable _)

/-- Global admission is recoverable exactly when every complete summary fiber
inside J has constant K-membership. -/
theorem global_admission_factorization {X : Type u} {B : Type v}
    (J K : Set X) (β : J → B) :
    (∃! k : Set.range β → Bool,
      admissionIndicator J K = k ∘ Set.rangeFactorization β) ↔
      ∀ x y : J, β x = β y → (x.val ∈ K ↔ y.val ∈ K) := by
  rw [← ker_beta_subset_ker_payload_iff_unique_factorization]
  change (∀ x y : J, β x = β y → admissionIndicator J K x = admissionIndicator J K y) ↔ _
  simp only [admissionIndicator, decide_eq_decide]

/-- W = J ∩ K is exactly the union of the entire restricted fibers with an
admitted representative. The union is a set of complete records in J. -/
theorem global_admission_iff_union_fibers {X : Type u} {B : Type v}
    (J K : Set X) (β : J → B) :
    (∃! k : Set.range β → Bool,
      admissionIndicator J K = k ∘ Set.rangeFactorization β) ↔
      J ∩ K = Subtype.val ''
        {x : J | ∃ y : J, y.val ∈ K ∧ β x = β y} := by
  rw [global_admission_factorization]
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨hxJ, hxK⟩
      exact ⟨⟨x, hxJ⟩, ⟨⟨x, hxJ⟩, hxK, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
      exact ⟨x.property, (h x y hxy).mpr hy⟩
  · intro h x y hxy
    have included : ∀ a b : J, β a = β b → b.val ∈ K → a.val ∈ K := by
      intro a b hab hb
      have ha : a.val ∈ Subtype.val ''
          {x : J | ∃ y : J, y.val ∈ K ∧ β x = β y} :=
        ⟨a, ⟨b, hb, hab⟩, rfl⟩
      rw [← h] at ha
      exact ha.2
    exact ⟨included y x hxy.symm, included x y hxy⟩

/-- The factored test still distinguishes admitted and excluded records. -/
theorem admission_factor_test {X : Type u} {B : Type v}
    (J K : Set X) (β : J → B) (k : Set.range β → Bool)
    (hk : admissionIndicator J K = k ∘ Set.rangeFactorization β) (x : J) :
    k (Set.rangeFactorization β x) = true ↔ x.val ∈ J ∩ K := by
  have hx := congrFun hk x
  simpa only [Function.comp_apply, admissionIndicator, decide_eq_true_eq,
    Set.mem_inter_iff, x.property, true_and] using
    (show k (Set.rangeFactorization β x) = true ↔ admissionIndicator J K x = true
      from by rw [hx]; rfl)

section Records

variable {Node : Type i} {Var : Type u} (Value : Var → Type v)

/-- Complete assignments on precisely D; no values outside D are required. -/
abbrev Assignment (D : Set Var) := (x : D) → Value x.val

/-- Restriction along the canonical inclusion of variable scopes. -/
def restrictAssignment {D E : Set Var} (h : D ⊆ E)
    (a : Assignment Value E) : Assignment Value D :=
  Set.domRestrict₂ h a

/-- The union of the scopes of the nodes in A. -/
def componentScope (S : Node → Set Var) (A : Set Node) : Set Var :=
  {x | ∃ n ∈ A, x ∈ S n}

variable (S : Node → Set Var)
variable (Γ : (n : Node) → Set (Assignment Value (S n)))

/-- The empty component has the canonical empty assignment carrier. -/
theorem componentScope_empty : componentScope S (∅ : Set Node) = (∅ : Set Var) := by
  ext x
  constructor
  · rintro ⟨n, hn, _⟩
    exact hn.elim
  · simp

/-- All assignments on the empty scope are the canonical empty assignment. -/
def emptyAssignment : Assignment Value (∅ : Set Var) := fun x => x.property.elim

theorem assignment_eq_empty (a : Assignment Value (∅ : Set Var)) :
    a = emptyAssignment Value := by
  apply Subsingleton.elim

/-- Raw component join: each complete assignment has every node restriction in
the specified local relation. Complement joins also enforce shared variables. -/
def rawJoin (A : Set Node) : Set (Assignment Value (componentScope S A)) :=
  {a | ∀ n (hn : n ∈ A),
    restrictAssignment Value (D := S n) (E := componentScope S A)
      (fun _ hx => ⟨n, hn, hx⟩) a ∈ Γ n}

/-- Specialization from the complete global join to a component join. -/
def restrictRecord (A : Set Node) (a : rawJoin Value S Γ Set.univ) :
    rawJoin Value S Γ A :=
  ⟨restrictAssignment Value (D := componentScope S A) (E := componentScope S Set.univ)
      (fun _ ⟨n, _, hx⟩ => ⟨n, Set.mem_univ n, hx⟩) a.val,
    fun n _hn => a.property n (Set.mem_univ n)⟩

variable (A : Set Node)

/-- The full overlap assignment, retained even when no completion exists. -/
def recordBoundary (a : rawJoin Value S Γ A) :
    Assignment Value (componentScope S A ∩ componentScope S Aᶜ) :=
  restrictAssignment Value Set.inter_subset_left a.val

/-- Restriction of a complete complement record to the same overlap carrier. -/
def completionBoundary (r : rawJoin Value S Γ Aᶜ) :
    Assignment Value (componentScope S A ∩ componentScope S Aᶜ) :=
  restrictAssignment Value Set.inter_subset_right r.val

/-- R_A(rho_A(a)): complete complement records with the same full boundary. -/
def compatibleCompletions (a : rawJoin Value S Γ A) :
    Set (rawJoin Value S Γ Aᶜ) :=
  {r | completionBoundary Value S Γ A r = recordBoundary Value S Γ A a}

private theorem mem_complement_scope (x : componentScope S Set.univ)
    (hx : x.val ∉ componentScope S A) : x.val ∈ componentScope S Aᶜ := by
  obtain ⟨n, _, hn⟩ := x.property
  exact ⟨n, fun hnA => hx ⟨n, hnA, hn⟩, hn⟩

/-- Union of the complete assignments. Only its use with matching boundaries
is a compatible union; it then restricts to both original records. -/
noncomputable def unionAssignment (a : rawJoin Value S Γ A)
    (r : rawJoin Value S Γ Aᶜ) : Assignment Value (componentScope S Set.univ) := by
  classical
  exact fun x => if hx : x.val ∈ componentScope S A then a.val ⟨x.val, hx⟩
    else r.val ⟨x.val, mem_complement_scope S A x hx⟩

private theorem union_left (a : rawJoin Value S Γ A) (r : rawJoin Value S Γ Aᶜ)
    (x : componentScope S A) :
    unionAssignment Value S Γ A a r
      ⟨x.val, by obtain ⟨n, _, hn⟩ := x.property; exact ⟨n, Set.mem_univ n, hn⟩⟩ =
      a.val x := by
  simp only [unionAssignment, dif_pos x.property]

private theorem union_right (a : rawJoin Value S Γ A) (r : rawJoin Value S Γ Aᶜ)
    (h : r ∈ compatibleCompletions Value S Γ A a) (x : componentScope S Aᶜ) :
    unionAssignment Value S Γ A a r
      ⟨x.val, by obtain ⟨n, _, hn⟩ := x.property; exact ⟨n, Set.mem_univ n, hn⟩⟩ =
      r.val x := by
  classical
  by_cases hx : x.val ∈ componentScope S A
  · simpa only [unionAssignment, dif_pos hx, completionBoundary, recordBoundary,
      restrictAssignment, Set.domRestrict₂] using (congrFun h ⟨x.val, hx, x.property⟩).symm
  · simp only [unionAssignment, dif_neg hx]

private theorem sheaf_glue_assignment (a : rawJoin Value S Γ A)
    (r : rawJoin Value S Γ Aᶜ)
    (h : r ∈ compatibleCompletions Value S Γ A a) :
    ∃ g : Assignment Value (componentScope S Set.univ),
      restrictAssignment Value
          (D := componentScope S A) (E := componentScope S Set.univ)
          (fun _ ⟨n, _, hx⟩ => ⟨n, Set.mem_univ n, hx⟩) g = a.val ∧
      restrictAssignment Value
          (D := componentScope S Aᶜ) (E := componentScope S Set.univ)
          (fun _ ⟨n, _, hx⟩ => ⟨n, Set.mem_univ n, hx⟩) g = r.val := by
  change completionBoundary Value S Γ A r = recordBoundary Value S Γ A a at h
  letI : TopologicalSpace Var := ⊥
  letI : DiscreteTopology Var := discreteTopology_bot Var
  let X : TopCat := TopCat.of Var
  let U : Bool → Opens X := fun i => match i with
    | false => ⟨componentScope S A, isOpen_discrete _⟩
    | true => ⟨componentScope S Aᶜ, isOpen_discrete _⟩
  let V : Opens X := ⟨componentScope S Set.univ, isOpen_discrete _⟩
  have hcover : V ≤ iSup U := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := hx
    by_cases hna : n ∈ A
    · exact Opens.mem_iSup.mpr ⟨false, show x ∈ U false from ⟨n, hna, hnx⟩⟩
    · exact Opens.mem_iSup.mpr ⟨true, show x ∈ U true from ⟨n, hna, hnx⟩⟩
  let iUV : ∀ i, U i ⟶ V := fun i => homOfLE (by
    intro x hx
    cases i
    · change x ∈ componentScope S A at hx
      obtain ⟨n, hn, hnx⟩ := hx
      exact ⟨n, Set.mem_univ n, hnx⟩
    · change x ∈ componentScope S Aᶜ at hx
      obtain ⟨n, hn, hnx⟩ := hx
      exact ⟨n, Set.mem_univ n, hnx⟩)
  let F : TopCat.Sheaf (Type (max u v)) X := TopCat.sheafToTypes X Value
  let sf : ∀ i, (F.1.obj (Opposite.op (U i))) := fun i => match i with
    | false => a.val
    | true => r.val
  have hc : TopCat.Presheaf.IsCompatible F.1 U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · funext x
      have hx : x.1 ∈ componentScope S A ∩ componentScope S Aᶜ := by
        have hx' := x.property
        change x.1 ∈ componentScope S A ∩ componentScope S Aᶜ at hx'
        exact hx'
      change a.val ⟨x.1, hx.1⟩ = r.val ⟨x.1, hx.2⟩
      simpa [completionBoundary, recordBoundary, restrictAssignment, Set.domRestrict₂] using (congrFun h ⟨x.1, hx⟩).symm
    · funext x
      have hx : x.1 ∈ componentScope S A ∩ componentScope S Aᶜ := by
        have hx' := x.property
        change x.1 ∈ componentScope S Aᶜ ∩ componentScope S A at hx'
        exact ⟨hx'.2, hx'.1⟩
      change r.val ⟨x.1, hx.2⟩ = a.val ⟨x.1, hx.1⟩
      simpa [completionBoundary, recordBoundary, restrictAssignment, Set.domRestrict₂] using congrFun h ⟨x.1, hx⟩
    · rfl
  obtain ⟨g, hgA, _hgUnique⟩ := F.existsUnique_gluing' U V iUV hcover sf hc
  refine ⟨g, ?_, ?_⟩
  · funext x
    have hx := congrFun (hgA false) x
    change g ⟨x.1, _⟩ = a.val x at hx
    simpa [U, V, iUV, F, sf, TopCat.sheafToTypes, TopCat.presheafToTypes,
      restrictAssignment, Set.domRestrict₂] using hx
  · funext x
    have hx := congrFun (hgA true) x
    change g ⟨x.1, _⟩ = r.val x at hx
    simpa [U, V, iUV, F, sf, TopCat.sheafToTypes, TopCat.presheafToTypes,
      restrictAssignment, Set.domRestrict₂] using hx

/-- Compatible complete component and complement records form a raw global
record, with exactly the original component restrictions. -/
theorem compatible_union_restrictions (a : rawJoin Value S Γ A)
    (r : rawJoin Value S Γ Aᶜ) (h : r ∈ compatibleCompletions Value S Γ A a) :
    ∃ j : rawJoin Value S Γ Set.univ,
      j.val = unionAssignment Value S Γ A a r ∧
      restrictRecord Value S Γ A j = a ∧ restrictRecord Value S Γ Aᶜ j = r := by
  classical
  obtain ⟨g, hga, hgr⟩ := sheaf_glue_assignment Value S Γ A a r h
  have hgu : g = unionAssignment Value S Γ A a r := by
    funext x
    by_cases hx : x.val ∈ componentScope S A
    · have hxg := congrFun hga ⟨x.val, hx⟩
      simpa [unionAssignment, hx, restrictAssignment, Set.domRestrict₂] using hxg
    · have hxg := congrFun hgr ⟨x.val, mem_complement_scope S A x hx⟩
      simpa [unionAssignment, hx, restrictAssignment, Set.domRestrict₂] using hxg
  have hj : unionAssignment Value S Γ A a r ∈ rawJoin Value S Γ Set.univ := by
    intro n _
    by_cases hn : n ∈ A
    · convert a.property n hn using 1
      funext x
      exact union_left Value S Γ A a r ⟨x.val, n, hn, x.property⟩
    · convert r.property n hn using 1
      funext x
      exact union_right Value S Γ A a r h ⟨x.val, n, hn, x.property⟩
  have hjg : g ∈ rawJoin Value S Γ Set.univ := by
    rw [hgu]
    exact hj
  refine ⟨⟨g, hjg⟩, hgu, ?_, ?_⟩
  · apply Subtype.ext
    simpa [restrictRecord] using hga
  · apply Subtype.ext
    simpa [restrictRecord] using hgr

variable (K : Set (Assignment Value (componentScope S Set.univ)))

/-- D_A^K(a), as a subset of the complete complement join. -/
def completionPayload (a : rawJoin Value S Γ A) : Set (rawJoin Value S Γ Aᶜ) :=
  {r | r ∈ compatibleCompletions Value S Γ A a ∧ unionAssignment Value S Γ A a r ∈ K}

/-- Membership is exactly the existence of one admitted complete global record
with these two restrictions. This verifies the union formula's carrier bridge. -/
theorem mem_completion_payload_iff (a : rawJoin Value S Γ A)
    (r : rawJoin Value S Γ Aᶜ) :
    r ∈ completionPayload Value S Γ A K a ↔
      ∃ j : rawJoin Value S Γ Set.univ,
        j.val ∈ K ∧ restrictRecord Value S Γ A j = a ∧
          restrictRecord Value S Γ Aᶜ j = r := by
  constructor
  · rintro ⟨hc, hK⟩
    obtain ⟨j, hj, ha, hr⟩ := compatible_union_restrictions Value S Γ A a r hc
    exact ⟨j, hj.symm ▸ hK, ha, hr⟩
  · rintro ⟨j, hK, rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    have heq : unionAssignment Value S Γ A
        (restrictRecord Value S Γ A j) (restrictRecord Value S Γ Aᶜ j) = j.val := by
      funext x
      classical
      by_cases hx : x.val ∈ componentScope S A <;>
        simp only [unionAssignment, hx, ↓reduceDIte, restrictRecord, restrictAssignment,
          Set.domRestrict₂]
    exact heq.symm ▸ hK

/-- Exact recovery of the entire completion set is fiberwise equality of those
sets. No finiteness or inhabitedness assumptions are imposed. -/
theorem local_completion_factorization {B : Type w} (β : rawJoin Value S Γ A → B) :
    (∃! d : Set.range β → Set (rawJoin Value S Γ Aᶜ),
      completionPayload Value S Γ A K = d ∘ Set.rangeFactorization β) ↔
      ∀ a a' : rawJoin Value S Γ A, β a = β a' →
        completionPayload Value S Γ A K a = completionPayload Value S Γ A K a' :=
  (ker_beta_subset_ker_payload_iff_unique_factorization β
    (completionPayload Value S Γ A K)).symm

/-- The preregistered QI-P9 consumer uses the admitted-global-record carrier
and the membership bridge on a live proof path. -/
theorem local_completion_global_tests {B : Type w} (β : rawJoin Value S Γ A → B) :
    (∃! d : Set.range β → Set (rawJoin Value S Γ Aᶜ),
      completionPayload Value S Γ A K = d ∘ Set.rangeFactorization β) ↔
      ∀ a a' : rawJoin Value S Γ A, β a = β a' →
        ∀ r : rawJoin Value S Γ Aᶜ,
          (∃ j : rawJoin Value S Γ Set.univ,
            j.val ∈ K ∧ restrictRecord Value S Γ A j = a ∧
              restrictRecord Value S Γ Aᶜ j = r) ↔
          (∃ j : rawJoin Value S Γ Set.univ,
            j.val ∈ K ∧ restrictRecord Value S Γ A j = a' ∧
              restrictRecord Value S Γ Aᶜ j = r) := by
  rw [local_completion_factorization]
  constructor
  · intro h a a' hab r
    have hrEq := congrArg (fun s => s r) (h a a' hab)
    have hrIff : completionPayload Value S Γ A K a r ↔
        completionPayload Value S Γ A K a' r := by
      constructor <;> intro hx
      · exact hrEq ▸ hx
      · exact hrEq ▸ hx
    constructor
    · intro hr
      exact (mem_completion_payload_iff Value S Γ A K a' r).mp
        (hrIff.mp ((mem_completion_payload_iff Value S Γ A K a r).mpr hr))
    · intro hr
      exact (mem_completion_payload_iff Value S Γ A K a r).mp
        (hrIff.mpr ((mem_completion_payload_iff Value S Γ A K a' r).mpr hr))
  · intro h a a' hab
    apply Set.ext
    intro r
    have hr := h a a' hab r
    constructor
    · intro hm
      exact (mem_completion_payload_iff Value S Γ A K a' r).mpr
        (hr.mp ((mem_completion_payload_iff Value S Γ A K a r).mp hm))
    · intro hm
      exact (mem_completion_payload_iff Value S Γ A K a r).mpr
        (hr.mpr ((mem_completion_payload_iff Value S Γ A K a' r).mp hm))

/-- The equivalent test condition quantifies over every complete complement
record and retains compatibility as well as K-admission. -/
theorem local_completion_tests {B : Type w} (β : rawJoin Value S Γ A → B) :
    (∃! d : Set.range β → Set (rawJoin Value S Γ Aᶜ),
      completionPayload Value S Γ A K = d ∘ Set.rangeFactorization β) ↔
      ∀ a a' : rawJoin Value S Γ A, β a = β a' →
        ∀ r : rawJoin Value S Γ Aᶜ,
          (r ∈ compatibleCompletions Value S Γ A a ∧ unionAssignment Value S Γ A a r ∈ K) ↔
          (r ∈ compatibleCompletions Value S Γ A a' ∧ unionAssignment Value S Γ A a' r ∈ K) := by
  rw [local_completion_factorization]
  simp only [Set.ext_iff, completionPayload, Set.mem_ofPred_eq]

/-- The compatible union as a member of the complete global join. -/
noncomputable def unionRecord (a : rawJoin Value S Γ A)
    (r : rawJoin Value S Γ Aᶜ) (h : r ∈ compatibleCompletions Value S Γ A a) :
    rawJoin Value S Γ Set.univ :=
  (compatible_union_restrictions Value S Γ A a r h).choose

/-- Additional scope requirement when summaries are to support subsequent
gluing: retain the full boundary and all specified raw result observations.
Payload factorization alone does not prove this requirement or gluing. -/
def BoundaryOutputRetention {B : Type w} {Output : Type*}
    (β : rawJoin Value S Γ A → B)
    (G : rawJoin Value S Γ Set.univ → Output) : Prop :=
  ∀ a a' : rawJoin Value S Γ A, β a = β a' →
    recordBoundary Value S Γ A a = recordBoundary Value S Γ A a' ∧
      ∀ (r : rawJoin Value S Γ Aᶜ)
        (h : r ∈ compatibleCompletions Value S Γ A a)
        (h' : r ∈ compatibleCompletions Value S Γ A a'),
        G (unionRecord Value S Γ A a r h) = G (unionRecord Value S Γ A a' r h')

end Records

#print axioms ker_beta_subset_ker_payload_iff_unique_factorization
#print axioms global_admission_iff_union_fibers
#print axioms mem_completion_payload_iff
#print axioms local_completion_tests

end D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
