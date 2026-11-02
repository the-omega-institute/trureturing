import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! The complete source telescopes with their actual finite-image cardinality observations. -/
namespace Reg.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth

open _root_.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

universe u

/-- Arbitrary group types and all their finite subsets remain in scope.
Only the observation role is finite; no bounded catalog replaces the source. -/
abbrev cardSignature : Signature where
  Params := Type u
  State G := Finset G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actualCard : Realization cardSignature.{u} :=
  realize cardSignature (fun _ _ s => s.card) (fun e => nomatch e)

noncomputable def rejectedCard : Realization cardSignature.{u} :=
  realize cardSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev displacementArena : Arena where
  signature := cardSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {h : ℤ × ℤ} {r : ℕ} (_ : h ≠ 0)
    (_ : f h = 0)
    (_ : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      ∃ k : ℤ, z = k • h),
    let A := (2*(r : ℤ)+1-|h.1+h.2|).toNat
    let B := (2*(r : ℤ)+1-|h.1-h.2|).toNat
    R.readout () G ((leeDiamond r).image f) + (A*B+1)/2 = 2*r^2+2*r+1

private theorem rejected_displacement_law :
    ¬ displacementArena.{u}.Law rejectedCard := by
  intro h
  let G := ULift.{u} (ZMod 1)
  let f : (ℤ × ℤ) →+ G := 0
  have hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(0 : ℤ) → f z = 0 →
      ∃ k : ℤ, z = k • (1,0) := by
    intro z hz _
    refine ⟨0, ?_⟩
    rw [zero_smul]
    apply Prod.ext
    · apply abs_eq_zero.mp
      linarith [abs_nonneg z.1, abs_nonneg z.2]
    · apply abs_eq_zero.mp
      linarith [abs_nonneg z.1, abs_nonneg z.2]
  have hh := h f (h := (1,0)) (r := 0) (by decide)
    (by simp [f]) hshort
  norm_num [rejectedCard, realize] at hh

noncomputable def displacementSource : Registration displacementArena.{u}
    (type_of% (@lee_ball_image_card_of_displacement.{u})) where
  actual := actualCard
  bridge := Iff.rfl
  variation := ⟨lee_ball_image_card_of_displacement, rejectedCard, rejected_displacement_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCard, ?_, rfl, rejected_displacement_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (ZMod 1),
      (∅ : Finset (ULift.{u} (ZMod 1))), ({0} : Finset (ULift.{u} (ZMod 1))), ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def displacementRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@lee_ball_image_card_of_displacement.{u})
      (Realization cardSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.lee_ball_image_card_of_displacement.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.displacementSource
  realizationSource := none
  generated := false
  arena := .source ⟨displacementArena⟩
  objectArena := .source ⟨displacementArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source displacementArena ⟨displacementSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardSignature
    (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev shortKernelArena : Arena where
  signature := cardSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {B r : ℕ} (_ : 0 < B) (_ : r < 2*B)
    (_ : f (0,2*(B : ℤ)) = 0)
    (_ : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      z = 0 ∨ z = (0,2*(B : ℤ)) ∨ z = (0,-2*(B : ℤ))),
    R.readout () G ((leeDiamond r).image f) =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1)

private theorem rejected_shortKernel_law : ¬ shortKernelArena.{u}.Law rejectedCard := by
  intro h
  let G := ULift.{u} (ZMod 1)
  let f : (ℤ × ℤ) →+ G := 0
  have hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(0 : ℤ) → f z = 0 →
      z = 0 ∨ z = (0,2*(1 : ℤ)) ∨ z = (0,-2*(1 : ℤ)) := by
    intro z hz _
    left
    apply Prod.ext
    · apply abs_eq_zero.mp
      linarith [abs_nonneg z.1,abs_nonneg z.2]
    · apply abs_eq_zero.mp
      linarith [abs_nonneg z.1,abs_nonneg z.2]
  have hh := h f (B := 1) (r := 0) (by norm_num) (by norm_num)
    (by simp [f]) hshort
  norm_num [rejectedCard,realize] at hh

noncomputable def shortKernelSource : Registration shortKernelArena.{u}
    (type_of% (@lee_ball_image_card_of_short_kernel.{u})) where
  actual := actualCard
  bridge := Iff.rfl
  variation := ⟨lee_ball_image_card_of_short_kernel,rejectedCard,rejected_shortKernel_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCard,?_,rfl,rejected_shortKernel_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (ZMod 1),
      (∅ : Finset (ULift.{u} (ZMod 1))), ({0} : Finset (ULift.{u} (ZMod 1))), ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def shortKernelRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@lee_ball_image_card_of_short_kernel.{u})
      (Realization cardSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.shortKernelSource
  realizationSource := none
  generated := false
  arena := .source ⟨shortKernelArena⟩
  objectArena := .source ⟨shortKernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shortKernelArena ⟨shortKernelSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardSignature
    (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

open _root_.D5.S3.FiniteGroups

abbrev sharpArena : Arena where
  signature := cardSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G]
    {s : ℕ} (_ : 3 ≤ s) (_ : ¬ Nat.Prime (2*s+1))
    (_ : ¬ IsAddCyclic G) (a b : G) (_ : a ≠ b)
    (_ : ∀ g : G, ∃ x y : ℤ,
      |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g)
    (_ : Nat.card G = BajnokBeattySharpMaximum.MaximumOrder s)
    (r : ℕ) (_ : r ≤ s),
    let B := (2*s+1-Nat.minFac (2*s+1))/2
    R.readout () G ((leeDiamond r).image (fun z => z.1 • a+z.2 • b)) =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1)

private theorem rejected_sharp_law : ¬ sharpArena.{u}.Law rejectedCard := by
  intro h
  obtain ⟨c,k,_,_,a,b,hab,hnoncyclic,hcover,hfinite,horder⟩ :=
    (BajnokBeattySharpMaximum.sharp_maximum.{0} 4 (by norm_num)).2
  letI := hfinite
  let G := ULift.{u} (ZMod c × ZMod (c*k))
  let e : G ≃+ (ZMod c × ZMod (c*k)) := AddEquiv.ulift
  have hnon : ¬ IsAddCyclic G := fun hh => hnoncyclic (e.isAddCyclic.mp hh)
  have hdistinct : e.symm a ≠ e.symm b := fun he => hab (e.symm.injective he)
  have hcov : ∀ g : G, ∃ x y : ℤ, |x|+|y| ≤ (4 : ℤ) ∧
      x • e.symm a+y • e.symm b = g := by
    intro g
    obtain ⟨x,y,hxy,he⟩ := hcover (e g)
    refine ⟨x,y,hxy,?_⟩
    apply e.injective
    simpa only [map_add, map_zsmul, AddEquiv.apply_symm_apply] using he
  have hord : Nat.card G = BajnokBeattySharpMaximum.MaximumOrder 4 :=
    (Nat.card_congr e.toEquiv).trans horder
  have hh := h (s := 4) (by norm_num) (by norm_num) hnon
    (e.symm a) (e.symm b) hdistinct hcov hord 0 (by norm_num)
  norm_num [rejectedCard,realize] at hh

noncomputable def sharpSource : Registration sharpArena.{u}
    (type_of% (@sharp_pair_growth.{u})) where
  actual := actualCard
  bridge := Iff.rfl
  variation := ⟨sharp_pair_growth,rejectedCard,rejected_sharp_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCard,?_,rfl,rejected_sharp_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (ZMod 1),
      (∅ : Finset (ULift.{u} (ZMod 1))), ({0} : Finset (ULift.{u} (ZMod 1))), ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def sharpRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@sharp_pair_growth.{u})
      (Realization cardSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.sharp_pair_growth.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth.sharpSource
  realizationSource := none
  generated := false
  arena := .source ⟨sharpArena⟩
  objectArena := .source ⟨sharpArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sharpArena ⟨sharpSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardSignature
    (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
