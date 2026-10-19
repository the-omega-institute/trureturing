import LeanInformationAuditRegAnalysis.SearchReduction.PresentationSyntax

/-! Statement-level certificates and coverage for the executable syntax lookup.
The kernel verifies conversion terms separately from these retrieval laws. -/
namespace LeanInformationAudit.Tests.SearchReduction.SingleSourceModel
open Lean LeanInformationAudit.SearchReduction

theorem lookup_complete (target : List Name) (entries : List (Name × List Name))
    (b : Name × List Name) :
    b ∈ presentationLookup target entries ↔ b ∈ entries ∧ ∀ a ∈ target, a ∈ b.2 := by
  simp [presentationLookup, supportIncluded, List.all_eq_true]

theorem index_extension (target atoms : List Name) (name : Name)
    (entries : List (Name × List Name)) (h : supportIncluded target atoms = false) :
    presentationLookup target (entries ++ [(name, atoms)]) = presentationLookup target entries := by
  simp [presentationLookup, h]

/-- An unfinished raw dependency analysis retains every candidate. -/
theorem unknown_raw_retained (env : Environment) (target : List PresentationKey)
    (bound : RawOriginBound) (h : bound.unknown = true) :
    rawNecessary env target bound = true := by
  simp [rawNecessary, keyOriginCompatible, h]

/-- A frozen conjunction grammar has an explicit semantic interpretation. -/
inductive Statement where
  | neutral | atom (name : Name) | pack (left right : Statement)
  deriving DecidableEq

def atoms : Statement → Finset Name
  | .neutral => ∅
  | .atom n => {n}
  | .pack p q => atoms p ∪ atoms q

def holds (valuation : Name → Prop) : Statement → Prop
  | .neutral => True
  | .atom n => valuation n
  | .pack p q => holds valuation p ∧ holds valuation q

def normalize : Statement → Statement
  | .neutral => .neutral
  | .atom n => .atom n
  | .pack p q => match normalize p, normalize q with
    | .neutral, q => q
    | p, .neutral => p
    | p, q => .pack p q

theorem normalize_sound (v : Name → Prop) (s : Statement) :
    holds v (normalize s) ↔ holds v s := by
  induction s with
  | neutral => rfl
  | atom n => rfl
  | pack p q hp hq =>
    simp only [normalize, holds]
    cases hnp : normalize p <;> cases hnq : normalize q <;>
      simp_all [holds]

theorem view_sound (v : Name → Prop) (p q : Statement) :
    holds v (.pack p q) → holds v p := And.left

theorem holds_iff_atoms (v : Name → Prop) (s : Statement) :
    holds v s ↔ ∀ a ∈ atoms s, v a := by
  induction s with
  | neutral => simp [holds, atoms]
  | atom n => simp [holds, atoms]
  | pack p q hp hq =>
    simp only [holds, atoms, hp, hq, Finset.mem_union]
    constructor
    · rintro ⟨left, right⟩ a (ha | ha)
      · exact left a ha
      · exact right a ha
    · intro h
      exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩

theorem subset_sound (v : Name → Prop) (source target : Statement)
    (included : atoms target ⊆ atoms source) : holds v source → holds v target := by
  intro h
  exact (holds_iff_atoms v target).mpr fun a ha => (holds_iff_atoms v source).mp h a (included ha)

theorem presentation_sound (v : Name → Prop) (source target : Statement)
    (included : atoms (normalize target) ⊆ atoms (normalize source)) :
    holds v source → holds v target := by
  intro h
  exact (normalize_sound v target).mp
    (subset_sound v (normalize source) (normalize target) included
      ((normalize_sound v source).mpr h))

/-- Two distinct baseline statements are never silently joined into one source. -/
theorem projection_and_pack :
    presentationLookup [`p, `q] [(`left, [`p]), (`right, [`q])] = [] := by decide

/-- Coverage is about keys produced by the actual normalizer, not an assumed
independent normalization function. -/
theorem normalized_lookup_complete (env : Environment) (target : Expr)
    (atoms : List PresentationKey) (hn : normalizedAtoms env target = .ok atoms)
    (entries : List (Name × List PresentationKey)) (b : Name × List PresentationKey) :
    normalizedLookup env target entries = .ok (presentationLookup atoms entries) ∧
      (b ∈ presentationLookup atoms entries ↔
        b ∈ entries ∧ supportIncluded atoms b.2 = true) := by
  constructor
  · simp [normalizedLookup, hn]
  · simp [presentationLookup]

def key (p : Statement) := atoms p

theorem key_meet_hom (p q : Statement) : key (.pack p q) = key p ∪ key q := rfl

theorem filter_not_constant :
    supportIncluded [`p] [`p, `q] = true ∧ supportIncluded [`q] [`p] = false := by decide

/-- Directional inclusion retains a projection that an equality key loses. -/
theorem projection_requires_inclusion :
    presentationLookup [`p] [(`source, [`p, `q])] = [(`source, [`p, `q])] := by decide

def Excluded (old present collection baselineAlias : Prop) : Prop :=
  old ∨ present ∨ collection ∨ baselineAlias

theorem E_old_subset_E_new {o p c b : Prop} : o → Excluded o p c b := Or.inl

theorem P_subset_E {o p c b : Prop} : p → Excluded o p c b := fun h => Or.inr (Or.inl h)

theorem guard_pack_split {o p c b : Prop} : c → Excluded o p c b :=
  fun h => Or.inr (Or.inr (Or.inl h))

theorem guard_arithmetic_alias {o p c b : Prop} : b → Excluded o p c b :=
  fun h => Or.inr (Or.inr (Or.inr h))

theorem single_premise_arithmetic_certificate (x n : Nat) (h : x = n + n + n) :
    x = 3 * n ∧ 0 ≤ n := by omega

theorem syntax_nondegenerate :
    presentationLookup [`p] [(`source, [`p, `q])] ≠ [] ∧
    presentationLookup [`r] [(`source, [`p, `q])] = [] := by decide

run_meta do
  for name in #[``production_lookup_complete, ``scope_necessary_of_normalized_match,
      ``certified_raw_bound_closed, ``unknown_raw_retained, ``raw_necessary_of_normalized_match,
      ``raw_prefilter_preserves_match, ``lookup_complete, ``normalized_lookup_complete,
      ``index_extension,
      ``normalize_sound, ``view_sound, ``holds_iff_atoms, ``subset_sound,
      ``presentation_sound, ``projection_and_pack, ``key_meet_hom,
      ``filter_not_constant, ``projection_requires_inclusion,
      ``E_old_subset_E_new, ``P_subset_E, ``guard_pack_split, ``guard_arithmetic_alias,
      ``single_premise_arithmetic_certificate, ``syntax_nondegenerate] do
    let axioms ← Lean.collectAxioms name
    unless standardAxioms axioms do
      throwError "single-source model has nonstandard axioms: {name}: {axioms}"

#print axioms production_lookup_complete
#print axioms scope_necessary_of_normalized_match
#print axioms raw_necessary_of_normalized_match
#print axioms raw_prefilter_preserves_match
#print axioms normalize_sound
#print axioms view_sound
#print axioms single_premise_arithmetic_certificate
#print axioms lookup_complete
#print axioms index_extension
#print axioms presentation_sound
end LeanInformationAudit.Tests.SearchReduction.SingleSourceModel
