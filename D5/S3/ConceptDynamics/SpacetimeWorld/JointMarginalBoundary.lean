/- GID: D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.FullMarginalsForceJoin; result=D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.diagonal_joint_refutation; claim=D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.FullMarginalsForceJoin
   digest: Full dependent marginals do not force the entire natural join. -/

import D5.S3.ConceptDynamics.SpacetimeWorld.NaturalJoin
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeWorld.JointMarginalBoundary

open WorldDomains NaturalJoin

def Value := {n : Int // n = 1 ∨ n = 2}
def oneValue : Value := ⟨1, Or.inl rfl⟩
def twoValue : Value := ⟨2, Or.inr rfl⟩

def leftNames : Set Bool := {false}
def rightNames : Set Bool := {true}
abbrev JointValuation := LocalValuation (fun _ : Bool => Value) (leftNames ∪ rightNames)

def first (v : JointValuation) : Value := v ⟨false, Or.inl rfl⟩
def second (v : JointValuation) : Value := v ⟨true, Or.inr rfl⟩

/-- Pair notation is faithfully equivalent to the dependent valuation on the union. -/
def pairEquiv : (Value × Value) ≃ JointValuation where
  toFun p s := cond s.val p.2 p.1
  invFun v := (first v, second v)
  left_inv _ := rfl
  right_inv v := by
    funext s
    rcases s with ⟨s, hs⟩
    cases s <;> rfl

def diagonal : Set JointValuation := {v | first v = second v}

theorem diagonal_exact :
    diagonal = {pairEquiv (oneValue, oneValue), pairEquiv (twoValue, twoValue)} := by
  ext v
  obtain ⟨⟨a, b⟩, rfl⟩ := pairEquiv.surjective v
  change a = b ↔ pairEquiv (a, b) = pairEquiv (oneValue, oneValue) ∨
    pairEquiv (a, b) = pairEquiv (twoValue, twoValue)
  rw [pairEquiv.injective.eq_iff, pairEquiv.injective.eq_iff]
  constructor
  · intro hab
    rcases a.property with ha | ha
    · have h : a = oneValue := Subtype.ext ha
      exact Or.inl (Prod.ext h (hab.symm.trans h))
    · have h : a = twoValue := Subtype.ext ha
      exact Or.inr (Prod.ext h (hab.symm.trans h))
  · rintro (h | h) <;>
      exact (congrArg Prod.fst h).trans (congrArg Prod.snd h).symm

def diagonalModel : JointDomain (fun _ : ↥(leftNames ∪ rightNames) => Value) where
  coordinate_nonempty _ := ⟨oneValue⟩
  allowed := diagonal
  nonempty := by
    rw [diagonal_exact]
    exact ⟨_, Or.inl rfl⟩

def fullModel : JointDomain (fun _ : ↥(leftNames ∪ rightNames) => Value) where
  coordinate_nonempty _ := ⟨oneValue⟩
  allowed := Set.univ
  nonempty := ⟨pairEquiv (oneValue, oneValue), Set.mem_univ _⟩

theorem names_disjoint : Disjoint leftNames rightNames := by
  simp [leftNames, rightNames]

theorem diagonal_marginals : first '' diagonal = Set.univ ∧ second '' diagonal = Set.univ := by
  constructor <;> apply Set.eq_univ_iff_forall.mpr <;> intro a
  · exact ⟨pairEquiv (a, a), rfl, rfl⟩
  · exact ⟨pairEquiv (a, a), rfl, rfl⟩

/-- Full coordinate images also give full images in the actual dependent local types. -/
theorem diagonal_local_marginals :
    Set.domRestrict₂ (Set.subset_union_left : leftNames ⊆ leftNames ∪ rightNames) '' diagonal =
        (Set.univ : Set (LocalValuation (fun _ : Bool => Value) leftNames)) ∧
      Set.domRestrict₂ (Set.subset_union_right : rightNames ⊆ leftNames ∪ rightNames) '' diagonal =
        (Set.univ : Set (LocalValuation (fun _ : Bool => Value) rightNames)) := by
  constructor <;> apply Set.eq_univ_iff_forall.mpr <;> intro a
  · obtain ⟨v, hv, ha⟩ := Set.eq_univ_iff_forall.mp diagonal_marginals.1 (a ⟨false, rfl⟩)
    refine ⟨v, hv, ?_⟩
    funext s
    rcases s with ⟨s, hs⟩
    have h : s = false := hs
    subst s
    exact ha
  · obtain ⟨v, hv, ha⟩ := Set.eq_univ_iff_forall.mp diagonal_marginals.2 (a ⟨true, rfl⟩)
    refine ⟨v, hv, ?_⟩
    funext s
    rcases s with ⟨s, hs⟩
    have h : s = true := hs
    subst s
    exact ha

theorem crossed_worlds_excluded :
    pairEquiv (oneValue, twoValue) ∉ diagonal ∧ pairEquiv (twoValue, oneValue) ∉ diagonal := by
  constructor <;> intro h <;> have he := congrArg Subtype.val h <;> contradiction

def join : Set JointValuation := naturalJoin leftNames rightNames Set.univ Set.univ

theorem diagonal_extra_constraint :
    constrainedJoin leftNames rightNames Set.univ Set.univ diagonal = diagonal :=
  constrainedJoin_realizes _ _ _ _ _ (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)

theorem diagonal_strict_join : diagonal ⊂ join := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rw [← diagonal_extra_constraint]
    exact Set.inter_subset_left
  · intro h
    apply crossed_worlds_excluded.1
    rw [h]
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- The stronger assertion is universal over domains and disjoint name sets, independent of
the diagonal witness: full local marginal images would force the entire natural join. -/
def FullMarginalsForceJoin : Prop :=
  ∀ (left right : Set Bool)
    (Γ : Set (LocalValuation (fun _ : Bool => Value) (left ∪ right))),
    Disjoint left right → Γ.Nonempty →
    Set.domRestrict₂ Set.subset_union_left '' Γ = Set.univ →
    Set.domRestrict₂ Set.subset_union_right '' Γ = Set.univ →
    Γ = naturalJoin left right Set.univ Set.univ

theorem diagonal_joint_refutation : ¬ FullMarginalsForceJoin := by
  intro h
  exact (Set.ssubset_iff_subset_ne.mp diagonal_strict_join).2
    (h leftNames rightNames diagonal names_disjoint diagonalModel.nonempty
      diagonal_local_marginals.1 diagonal_local_marginals.2)

end D5.S3.ConceptDynamics.SpacetimeWorld.JointMarginalBoundary
