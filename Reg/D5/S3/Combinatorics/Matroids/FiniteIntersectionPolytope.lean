import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope

namespace Reg.D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := Matroid E
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := Set E → ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M.eRk) (fun e _ => Empty.elim e)

def rejected (i : Bool) : Realization signature.{u} :=
  realize signature (fun j _ M U => if j = i ∧ U.ncard = 2 then 1 else M.eRk U)
    (fun e _ => Empty.elim e)

def observedRegion {E : Type u} [Finite E] (r : Realization signature.{u})
    (M1 M2 : Matroid E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ U : Set E,
    (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((r.readout false E M1 U).toNat : ℝ) ∧
    (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((r.readout true E M2 U).toNat : ℝ)}

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [Finite E] (M1 M2 : Matroid E)
    (_h1 : M1.E = Set.univ) (_h2 : M2.E = Set.univ) (v : E → ℝ),
    v ∈ Set.extremePoints ℝ (observedRegion r M1 M2) →
      ∀ e, v e = 0 ∨ v e = 1

private lemma free_rank {E : Type u} [Finite E] (U : Set E) :
    ((freeOn (Set.univ : Set E)).eRk U).toNat = U.ncard := by
  rw [eRk_freeOn (Set.subset_univ U)]
  rfl

private lemma half_sum {E : Type u} [Finite E] (U : Set E) :
    (∑ _e ∈ U.toFinite.toFinset, (1 / 2 : ℝ)) = (U.ncard : ℝ) / 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card U U.toFinite]
  simp [div_eq_mul_inv]

private lemma half_feasible (i : Bool) :
    (fun _ : ULift.{u} (Fin 3) => (1 / 2 : ℝ)) ∈ observedRegion (rejected i)
      (freeOn Set.univ) (freeOn Set.univ) := by
  classical
  constructor
  · intro e; norm_num
  · intro U
    rw [half_sum]
    have hn : (0 : ℝ) ≤ (U.ncard : ℝ) := Nat.cast_nonneg _
    constructor <;>
      simp only [rejected, realize] <;>
      split_ifs with h <;>
      simp only [ENat.toNat_one, Nat.cast_one, free_rank] <;>
      try { rw [h.2]; norm_num } <;> linarith

private lemma pair_bound (i : Bool) (x : ULift.{u} (Fin 3) → ℝ)
    (hx : x ∈ observedRegion (rejected i) (freeOn Set.univ) (freeOn Set.univ))
    (a b : ULift.{u} (Fin 3)) (hne : a ≠ b) : x a + x b ≤ 1 := by
  classical
  have hp : ({a,b} : Set (ULift.{u} (Fin 3))).ncard = 2 := Set.ncard_pair hne
  cases i with
  | false =>
    have h := (hx.2 ({a,b} : Set (ULift.{u} (Fin 3)))).1
    simpa [rejected, realize, hp, hne] using h
  | true =>
    have h := (hx.2 ({a,b} : Set (ULift.{u} (Fin 3)))).2
    simpa [rejected, realize, hp, hne] using h

private lemma half_extreme (i : Bool) :
    (fun _ : ULift.{u} (Fin 3) => (1 / 2 : ℝ)) ∈ Set.extremePoints ℝ
      (observedRegion (rejected i) (freeOn Set.univ) (freeOn Set.univ)) := by
  classical
  refine ⟨half_feasible i, ?_⟩
  intro x hx y hy hseg
  rcases hseg with ⟨s,t,hs,ht,hst,heq⟩
  have hpair : ∀ a b : ULift.{u} (Fin 3), a ≠ b → x a + x b = 1 := by
    intro a b hab
    have hxp := pair_bound i x hx a b hab
    have hyp := pair_bound i y hy a b hab
    have hea := congrFun heq a
    have heb := congrFun heq b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hea heb
    have hyt : 0 ≤ t * (1 - (y a + y b)) := mul_nonneg ht.le (sub_nonneg.mpr hyp)
    nlinarith
  have h01 := hpair (ULift.up 0) (ULift.up 1) (by decide)
  have h02 := hpair (ULift.up 0) (ULift.up 2) (by decide)
  have h12 := hpair (ULift.up 1) (ULift.up 2) (by decide)
  funext e
  obtain ⟨e⟩ := e
  fin_cases e <;> dsimp <;> linarith

private theorem rejected_law (i : Bool) : ¬ arena.{u}.Law (rejected i) := by
  intro h
  have hh := h (E := ULift.{u} (Fin 3)) (freeOn Set.univ) (freeOn Set.univ)
    rfl rfl _ (half_extreme i) (ULift.up 0)
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  change (loopyOn {ULift.up ()}).eRk {ULift.up ()} =
    (freeOn {ULift.up ()}).eRk {ULift.up ()} at hh
  rw [eRk_loopyOn, eRk_freeOn subset_rfl, encard_singleton] at hh
  exact zero_ne_one hh

def source_registration : Registration arena.{u}
    (type_of% (@extreme_point_zero_one.{u})) where
  actual := realize signature (fun _ _ M => M.eRk) (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@extreme_point_zero_one, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext E M U
      simp [actual, rejected, realize, hji]
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@extreme_point_zero_one.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope.extreme_point_zero_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.eRk) (fun e _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "fn", "arg", "arg", "arg", "body", "arg", "body", "fn", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "fn", "arg", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
