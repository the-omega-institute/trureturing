import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostStressTails
import D5.S3.VertexAlgebra.BcGhostStressCurrent
import Reg.Support.DependentFamily

set_option autoImplicit false

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostStressTails
open D5.S3.VertexAlgebra.BcGhostStressCurrent
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.BcGhostStressTails
noncomputable section
universe u

namespace Stress

abbrev signature : Signature where
  Params := Σ K : Type u, Σ R : CommRing K, @Fock K R
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; Fock p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p m => letI := p.2.1; L m p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; vacuum) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law T := ∀ (K : Type u) [R : CommRing K] (m : ℤ) (v : Fock K),
    2 * (((occupied v).sup id : ℕ) : ℤ) + 4 < m → T.readout () ⟨K, R, v⟩ m = 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv := h (ULift.{u} ℚ) 5 0 (by simp [occupied])
  change (vacuum : Fock (ULift.{u} ℚ)) = 0 at hv
  have hscalar := congrArg (fun v : Fock (ULift.{u} ℚ) => (v ∅).down) hv
  norm_num [vacuum] at hscalar

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  have hmode : L (K := ULift.{u} ℚ) (-2) ≠ L 0 := by
    intro heq
    have hcomm := L_b_commutator (K := ULift.{u} ℚ) (-2) 0
    have hzero : L (K := ULift.{u} ℚ) 0 * b 0 - b 0 * L 0 = 0 := by
      simpa using (L_b_commutator (K := ULift.{u} ℚ) 0 0)
    rw [heq, hzero] at hcomm
    have hsmul : (-2 : ULift.{u} ℚ) • b (K := ULift.{u} ℚ) (-2) = 0 := by
      simpa using hcomm.symm
    have hunit : IsUnit (-2 : ULift.{u} ℚ) :=
      isUnit_iff_ne_zero.mpr (by
        intro hscalarZero
        have hrationalZero : (-2 : ℚ) = 0 :=
          congrArg (fun scalar : ULift.{u} ℚ => scalar.down) hscalarZero
        norm_num at hrationalZero)
    have hb : b (K := ULift.{u} ℚ) (-2) = 0 := hunit.smul_eq_zero.mp hsmul
    have hcar := b_c (K := ULift.{u} ℚ) (-2) 2
    have hcontr : (0 : Module.End (ULift.{u} ℚ) (Fock (ULift.{u} ℚ))) = 1 := by
      simpa [hb] using hcar
    exact zero_ne_one hcontr
  obtain ⟨v, hv⟩ : ∃ v : Fock (ULift.{u} ℚ), L (-2) v ≠ L 0 v := by
    apply not_forall.mp
    intro hpointwise
    exact hmode (LinearMap.ext hpointwise)
  refine ⟨⟨ULift.{u} ℚ, inferInstance, v⟩, -2, 0, ?_⟩
  change L (K := ULift.{u} ℚ) (-2) v ≠ L 0 v
  exact hv

def registration : Registration arena.{u} (type_of% (@L_high_mode.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@L_high_mode, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

def audit : Contract.Registration (@L_high_mode.{u})
    (Realization signature.{u}) (Type) (Unit) where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.Stress.audit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.Stress.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => letI := p.2.1; L m p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressTails
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Stress

namespace NormalPair

abbrev signature : Signature where
  Params := Σ K : Type u, Σ R : CommRing K, @Fock K R
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; Fock p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p mk => letI := p.2.1;
    normalPair (mk.1 + mk.2) (-mk.2) p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; vacuum) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law T := ∀ (K : Type u) [R : CommRing K] (m k : ℤ) (v : Fock K),
    2 * (((occupied v).sup id : ℕ) : ℤ) + 4 < m →
      T.readout () ⟨K, R, v⟩ (m, k) = 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv := h (ULift.{u} ℚ) 5 0 0 (by simp [occupied])
  change (vacuum : Fock (ULift.{u} ℚ)) = 0 at hv
  have hscalar := congrArg (fun v : Fock (ULift.{u} ℚ) => (v ∅).down) hv
  norm_num [vacuum] at hscalar

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} ℚ, inferInstance, vacuum⟩, (-1, -1), 0, ?_⟩
  change normalPair (K := ULift.{u} ℚ) (-2) 1 vacuum ≠ normalPair 0 0 vacuum
  intro h
  have hcoord := congrArg (fun v : Fock (ULift.{u} ℚ) => (v {0, 1}).down) h
  norm_num [normalPair, b, c, create, annihilate, vacuum,
    Finsupp.linearCombination_single, createBasis, annihilateBasis, sign,
    Finsupp.smul_apply, Finsupp.single_apply] at hcoord

def registration : Registration arena.{u} (type_of% (@normal_pair_high.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normal_pair_high, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

def audit : Contract.Registration (@normal_pair_high.{u})
    (Realization signature.{u}) (Type) (Unit) where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.NormalPair.audit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.NormalPair.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p mk => letI := p.2.1;
    normalPair (mk.1 + mk.2) (-mk.2) p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℤ × ℤ)
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressTails
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end NormalPair

namespace Outer

abbrev signature : Signature where
  Params := Σ K : Type u, CommRing K
  State p := letI := p.2; Fock p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2; ℤ → Fock p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p v => letI := p.2; fun n => outerNormalPair n v)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2; fun _ => vacuum)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law T := ∀ (K : Type u) [R : CommRing K] (v : Fock K),
    Function.HasFiniteSupport (T.readout () ⟨K, R⟩ v)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hv : (vacuum : Fock (ULift.{u} ℚ)) ≠ 0 := by
    intro hzero
    have hscalar := congrArg (fun v : Fock (ULift.{u} ℚ) => (v ∅).down) hzero
    norm_num [vacuum] at hscalar
  have hs : Function.support (fun _ : ℤ => (vacuum : Fock (ULift.{u} ℚ))) = Set.univ := by
    ext n
    simp [Function.mem_support, hv]
  have hfinite := h (ULift.{u} ℚ) 0
  change (Function.support (fun _ : ℤ => (vacuum : Fock (ULift.{u} ℚ)))).Finite at hfinite
  rw [hs] at hfinite
  exact Set.infinite_univ.not_finite hfinite

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  have hmode : outerNormalPair (K := ULift.{u} ℚ) (-2) ≠ 0 := by
    intro hzero
    have hproduct : L (K := ULift.{u} ℚ) (-2) * c 2 = 0 := by
      simpa only [outerNormalPair, show ¬ (-1 : ℤ) ≤ -2 by norm_num,
        if_false, neg_neg, ← Module.End.mul_eq_comp] using hzero
    have hcomm : L (K := ULift.{u} ℚ) (-2) * b (-2) = b (-2) * L (-2) := by
      apply sub_eq_zero.mp
      simpa using (L_b_commutator (K := ULift.{u} ℚ) (-2) (-2))
    have hcar : b (K := ULift.{u} ℚ) (-2) * c 2 + c 2 * b (-2) = 1 := by
      simpa using (b_c (K := ULift.{u} ℚ) (-2) 2)
    have hL : L (K := ULift.{u} ℚ) (-2) = 0 := by
      calc
        L (K := ULift.{u} ℚ) (-2) =
            L (-2) * (b (-2) * c 2 + c 2 * b (-2)) := by rw [hcar, mul_one]
        _ = (b (-2) * L (-2)) * c 2 + (L (-2) * c 2) * b (-2) := by
          simp only [mul_add, ← mul_assoc, hcomm]
        _ = b (-2) * (L (-2) * c 2) + (L (-2) * c 2) * b (-2) := by
          rw [mul_assoc]
        _ = 0 := by rw [hproduct, mul_zero, zero_mul, add_zero]
    have hcurrent := L_b_commutator (K := ULift.{u} ℚ) (-2) 0
    rw [hL, zero_mul, mul_zero, sub_zero] at hcurrent
    have hsmul : (-2 : ULift.{u} ℚ) • b (K := ULift.{u} ℚ) (-2) = 0 := by
      simpa using hcurrent.symm
    have hunit : IsUnit (-2 : ULift.{u} ℚ) :=
      isUnit_iff_ne_zero.mpr (by
        intro hscalarZero
        have hrationalZero : (-2 : ℚ) = 0 :=
          congrArg (fun scalar : ULift.{u} ℚ => scalar.down) hscalarZero
        norm_num at hrationalZero)
    have hb : b (K := ULift.{u} ℚ) (-2) = 0 := hunit.smul_eq_zero.mp hsmul
    have hcontr : (0 : Module.End (ULift.{u} ℚ) (Fock (ULift.{u} ℚ))) = 1 := by
      simpa only [hb, zero_mul, mul_zero, zero_add] using hcar
    exact zero_ne_one hcontr
  obtain ⟨v, hv⟩ : ∃ v : Fock (ULift.{u} ℚ), outerNormalPair (-2) v ≠ 0 := by
    apply not_forall.mp
    intro hpointwise
    apply hmode
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.zero_apply] using hpointwise v
  refine ⟨⟨ULift.{u} ℚ, inferInstance⟩, v, 0, ?_⟩
  intro heq
  have hvalue := congrFun heq (-2)
  change outerNormalPair (K := ULift.{u} ℚ) (-2) v = outerNormalPair (-2) 0 at hvalue
  exact hv (by simpa only [map_zero] using hvalue)

def registration : Registration arena.{u} (type_of% (@outer_has_finite_support.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@outer_has_finite_support, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

def audit : Contract.Registration (@outer_has_finite_support.{u})
    (Realization signature.{u}) (Type) (Unit) where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.Outer.audit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressTails.Outer.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => letI := p.2;
    fun n => outerNormalPair n v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressTails
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Outer

#print axioms Stress.registration
#print axioms NormalPair.registration
#print axioms Outer.registration
#print axioms Stress.audit
#print axioms NormalPair.audit
#print axioms Outer.audit

end
end Reg.D5.S3.VertexAlgebra.BcGhostStressTails
