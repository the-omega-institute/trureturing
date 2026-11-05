import D5.S1.Words.Sequenceability.SeparatedPrefixReflection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Sequenceability.SeparatedPrefixReflection
open _root_.D5.S1.Words.Sequenceability.SeparatedPrefixReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
private noncomputable instance {G : Type*} : DecidableEq G := Classical.decEq G

abbrev signature : Signature where
  Params := Σ G : Type u, AddCommGroup G × ℕ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => by letI := p.2.1; exact pref w p.2.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by letI := p.2.1; exact 0)
    (fun e => nomatch e)

abbrev reflectionArena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] (C : Set G) (hc : StrictCone C)
    (w : List G) (hw : Good w) (h k : ℕ) (hgap : 2 ≤ k - h)
    (hk : k ≤ w.length) (lo hi : G) (hs : Separated C w h k lo hi),
    let v := reverseBlock w h k
    v.Perm w ∧ v.length = w.length ∧ v.sum = w.sum ∧
    (∀ j ≤ w.length, (j ≤ h ∨ k ≤ j) → R.readout () ⟨G, inferInstance, j⟩ v = pref w j) ∧
    (∀ j, h ≤ j → j ≤ k → pref v j = pref w h + pref w k - pref w (h + k - j)) ∧
    Good v ∧ Disjoint (reflected w h k lo hi) (inventory w) ∧
    inventory v = (inventory w \ interior w h k) ∪ reflected w h k lo hi ∧
    inventory w \ inventory v = interior w h k ∧
    inventory v \ inventory w = reflected w h k lo hi ∧
    (interior w h k).card = k - h - 1 ∧
    (reflected w h k lo hi).card = k - h - 1 ∧ 0 < k - h - 1

abbrev repairArena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] (C : Set G) (hc : StrictCone C)
    (A : Finset G) (hA : (0 : G) ∉ A) (a b : G) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hr : a + b ∉ insert 0 A)
    (w : List G) (hw : Omega A a b w) (t : ℕ) (ht : t < w.length)
    (hmerge : w[t] = a + b) (h k : ℕ) (hgap : 2 ≤ k - h) (hk : k ≤ w.length)
    (lo hi : G) (hs : Separated C w h k lo hi) (hout : t < h ∨ k ≤ t)
    (hcollision : ∃ i, h < i ∧ i < k ∧ pref w t + a = pref w i),
    let v := reverseBlock w h k
    Omega A a b v ∧ v ≠ w ∧
    R.readout () ⟨G, inferInstance, t⟩ v = pref w t ∧
    (∃ ht' : t < v.length, v[t] = a + b) ∧
    pref v t + a ∉ inventory v ∧ Good (expandAt v t a b) ∧
    (expandAt v t a b).Perm A.toList ∧
    (expandAt v t a b).sum = w.sum ∧
    (∀ x ∈ expandAt v t a b, x ≠ 0)

private def cone : Set (ULift.{u} ℤ) := {x | 0 < x.down}
private theorem cone_strict : StrictCone cone.{u} := by
  constructor
  · intro x y hx hy
    change 0 < x.down + y.down
    change 0 < x.down at hx
    change 0 < y.down at hy
    omega
  · change ¬ 0 < (0 : ℤ)
    omega

private theorem good_two : Good ([⟨2⟩, ⟨-1⟩] : List (ULift.{u} ℤ)) := by
  intro i j hij hj hp
  simp only [List.length_cons, List.length_nil] at hj hp
  have hi : i < 4 := by omega
  interval_cases i <;> interval_cases j <;> simp_all <;>
    intro he <;> have hh := congrArg ULift.down he <;>
    norm_num at hh

private theorem sep_two : Separated cone.{u} [⟨2⟩, ⟨-1⟩] 0 2 ⟨0⟩ ⟨1⟩ := by
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inr ?_, ?_, ?_⟩
  · rfl
  · ext; norm_num [pref]
  · change (0 : ℤ) < 1 - 0; omega
  · intro i hi hk
    have : i = 1 := by omega
    subst i
    change (0 : ℤ) < 2 - 1
    omega
  · intro j hj he
    simp only [List.length_cons, List.length_nil] at hj
    rcases he with he | he
    · have : j = 0 := by omega
      subst j
      exact Or.inl rfl
    · have : j = 2 := by omega
      subst j
      right
      change (0 : ℤ) < 2 + -1 - 0
      omega

private theorem reflection_rejected : ¬ reflectionArena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} ℤ) inferInstance cone cone_strict
    [⟨2⟩,⟨-1⟩] good_two 0 2 (by omega) (by simp) ⟨0⟩ ⟨1⟩ sep_two
  have he := hh.2.2.2.1 2 (by simp) (Or.inr (le_refl _))
  have he' := congrArg ULift.down he
  norm_num [rejected, realize, pref] at he'

private theorem good_three : Good ([⟨2⟩, ⟨-1⟩, ⟨4⟩] : List (ULift.{u} ℤ)) := by
  intro i j hij hj hp
  simp only [List.length_cons, List.length_nil] at hj hp
  have hi : i < 4 := by omega
  interval_cases i <;> interval_cases j <;> simp_all <;>
    intro he <;> have hh := congrArg ULift.down he <;>
    norm_num at hh

private theorem sep_three : Separated cone.{u} [⟨2⟩, ⟨-1⟩, ⟨4⟩] 0 2 ⟨0⟩ ⟨1⟩ := by
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inr ?_, ?_, ?_⟩
  · rfl
  · ext; norm_num [pref]
  · change (0 : ℤ) < 1 - 0; omega
  · intro i hi hk
    have : i = 1 := by omega
    subst i
    change (0 : ℤ) < 2 - 1
    omega
  · intro j hj he
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> first
      | exact Or.inl rfl
      | right; change (0 : ℤ) < _; norm_num [pref]
      | omega

private theorem repair_rejected : ¬ repairArena.{u}.Law rejected := by
  intro h
  let A : Finset (ULift.{u} ℤ) := {⟨2⟩, ⟨-1⟩, ⟨1⟩, ⟨3⟩}
  have hp : ([⟨2⟩,⟨-1⟩,⟨4⟩] : List (ULift.{u} ℤ)).Perm
      (compressed A ⟨1⟩ ⟨3⟩).toList := by
    have hdiff : ∀ m n : ℤ, m ≠ n → (ULift.up.{u} m : ULift ℤ) ≠ ⟨n⟩ := by
      intro m n hne he
      exact hne (congrArg ULift.down he)
    have heq : ∀ x y : ULift.{u} ℤ, x = y ↔ x.down = y.down := by
      intro x y
      exact ⟨congrArg ULift.down, fun h => ULift.ext h⟩
    apply (List.perm_ext_iff_of_nodup (by simp [heq]) (Finset.nodup_toList _)).mpr
    intro x
    simp [compressed, A, heq]
    omega
  have heq : ∀ x y : ULift.{u} ℤ, x = y ↔ x.down = y.down := by
    intro x y
    exact ⟨congrArg ULift.down, fun h => ULift.ext h⟩
  have hh := @h (ULift.{u} ℤ) inferInstance cone cone_strict A (by simp [A, heq])
    ⟨1⟩ ⟨3⟩ (by simp [A]) (by simp [A]) (by simp [heq])
    (by simp [A, heq]) [⟨2⟩,⟨-1⟩,⟨4⟩] ⟨hp,good_three⟩ 2 (by simp)
    (by ext; norm_num) 0 2 (by omega) (by simp) ⟨0⟩ ⟨1⟩ sep_three
    (Or.inr (le_refl _)) ⟨1, by omega, by omega, by ext; norm_num [pref]⟩
  have he := hh.2.2.1
  have he' := congrArg ULift.down he
  norm_num [rejected, realize, pref] at he'

def reflectionFamily : Registration reflectionArena.{u} (type_of% (@separated_prefix_reflection.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separated_prefix_reflection, rejected, reflection_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, reflection_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 1⟩, [0], [1], ?_⟩
    change (0 : ULift.{u} ℤ) ≠ 1
    exact zero_ne_one

def reflectionAudit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@separated_prefix_reflection.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `D5.S1.Words.Sequenceability.SeparatedPrefixReflection.separated_prefix_reflection.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.SeparatedPrefixReflection.reflectionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨reflectionArena.{u}⟩
  objectArena := .source ⟨reflectionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reflectionArena.{u} ⟨reflectionFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def repairFamily : Registration repairArena.{u} (type_of% (@same_pair_repair.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_pair_repair, rejected, repair_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, repair_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 1⟩, [0], [1], ?_⟩
    change (0 : ULift.{u} ℤ) ≠ 1
    exact zero_ne_one

def repairAudit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@same_pair_repair.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `D5.S1.Words.Sequenceability.SeparatedPrefixReflection.same_pair_repair.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.SeparatedPrefixReflection.repairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨repairArena.{u}⟩
  objectArena := .source ⟨repairArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source repairArena.{u} ⟨repairFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.SeparatedPrefixReflection
