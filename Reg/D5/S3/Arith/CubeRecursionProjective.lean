import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.CubeRecursionProjective

/-! # Cubic rational-map readouts

These source families preserve the full parameter, complex projective point,
and matrix domains. Source occurrence binding remains unspecified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.CubeRecursionProjective

open _root_.D5.S3.Arith.CubeRecursionProjective
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Degree

noncomputable abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => RatFunc ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual := DependentFamily.realize signature
  (fun _ _ t => rationalMap t) (fun e => nomatch e)

noncomputable abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ t : ℕ,
    (r.readout () () t).num.natDegree = 1 ∧
    (r.readout () () t).denom.natDegree = 3 ∧ mapDegree (r.readout () () t) = 3

abbrev sourceScope := type_of% (@map_degree_three)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

noncomputable def erased := DependentFamily.realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := (h 0).1
  norm_num [erased, DependentFamily.realize] at hh

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp map_degree_three, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    change rationalMap 0 = rationalMap 1 at he
    have h0 := (rational_map_semantics 0).2 0
    have h1 := (rational_map_semantics 1).2 0
    rw [he] at h0
    have hh := h0.trans h1.symm
    norm_num [projectiveMap, q] at hh

end Degree

noncomputable abbrev mapSignature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => OnePoint ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => OnePoint ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def mapActual := DependentFamily.realize mapSignature
  (fun _ t p => projectiveMap t p) (fun e => nomatch e)

noncomputable def mapErased := DependentFamily.realize mapSignature
  (fun _ _ _ => ∞) (fun e => nomatch e)

theorem map_dependence : DependentFamily.ObservationalDependence mapSignature mapActual := by
  intro i
  refine ⟨0, (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [mapActual, DependentFamily.realize, projectiveMap, q]
  intro he
  have hh := OnePoint.coe_injective he
  norm_num at hh

namespace Homogeneous

noncomputable abbrev arena : DependentFamily.Arena where
  signature := mapSignature
  Law := fun r => ∀ t : ℕ, ∀ x y : ℂ, ∀ h : x ≠ 0 ∨ y ≠ 0,
    r.readout () t (projectivePoint x y h) = homogeneousImage t x y h

abbrev sourceScope := type_of% (@homogeneous_coordinates)

theorem source_bridge : sourceScope ↔ arena.Law mapActual := Iff.rfl

theorem erased_fails : ¬ arena.Law mapErased := by
  intro h
  have hh := h 0 0 1 (Or.inr (by norm_num))
  simpa [mapErased, DependentFamily.realize, homogeneousImage, homogeneousA,
    homogeneousB, OnePoint.equivProjectivization_symm_apply_mk] using hh

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := mapActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp homogeneous_coordinates, mapErased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mapErased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := map_dependence

end Homogeneous

namespace Semantics

noncomputable abbrev arena : DependentFamily.Arena where
  signature := mapSignature
  Law := fun r => ∀ t : ℕ,
    r.readout () t ∞ = (0 : ℂ) ∧
    ∀ z : ℂ, r.readout () t z =
      if (rationalMap t).denom.eval z = 0 then ∞
      else (RatFunc.eval (RingHom.id ℂ) z (rationalMap t) : ℂ)

abbrev sourceScope := type_of% (@rational_map_semantics)

theorem source_bridge : sourceScope ↔ arena.Law mapActual := Iff.rfl

theorem erased_fails : ¬ arena.Law mapErased := by
  intro h
  have hh := (h 0).1
  simpa [mapErased, DependentFamily.realize] using hh

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := mapActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp rational_map_semantics, mapErased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mapErased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := map_dependence

end Semantics

namespace Conjugacy

noncomputable abbrev arena : DependentFamily.Arena where
  signature := mapSignature
  Law := fun r => ∀ t : ℕ, ∀ g : PGL(2, ℂ), ¬ ∀ p : OnePoint ℂ,
    mobius g (r.readout () t (mobius g⁻¹ p)) = powerMap p

abbrev sourceScope := type_of% (@not_conjugate)

theorem source_bridge : sourceScope ↔ arena.Law mapActual := Iff.rfl

noncomputable def powerReadout := DependentFamily.realize mapSignature
  (fun _ _ p => powerMap p) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law powerReadout := by
  intro h
  apply h 0 1
  intro p
  simp [powerReadout, DependentFamily.realize, mobius]

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := mapActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp not_conjugate, powerReadout, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨powerReadout, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := map_dependence

end Conjugacy

namespace Mobius

noncomputable abbrev signature : DependentFamily.Signature where
  Params := GL (Fin 2) ℂ
  State := fun _ => OnePoint ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => OnePoint ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual := DependentFamily.realize signature
  (fun _ g p => mobius (Matrix.ProjGenLinGroup.mk g) p) (fun e => nomatch e)

noncomputable abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ g : GL (Fin 2) ℂ,
    r.readout () g ∞ =
      (if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ)) ∧
    ∀ z : ℂ, r.readout () g z =
      (if g 1 0 * z + g 1 1 = 0 then ∞
       else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ))

abbrev sourceScope := type_of% (@mobius_coordinates)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

noncomputable def erased := DependentFamily.realize signature
  (fun _ _ _ => ∞) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := (h 1).2 0
  simpa [erased, DependentFamily.realize] using hh

noncomputable def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp mobius_coordinates, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, (0 : ℂ), (1 : ℂ), ?_⟩
    simp [actual, DependentFamily.realize, mobius]

end Mobius

noncomputable def Degree.registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@map_degree_three) (DependentFamily.Realization Degree.signature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionProjective.map_degree_three.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionProjective.Degree.family
  realizationSource := none
  generated := false
  arena := .source ⟨Degree.arena⟩
  objectArena := .source ⟨Degree.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Degree.arena ⟨Degree.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := Option.some (DependentFamily.realize Degree.signature (fun _ _ t => rationalMap t) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := Option.some (ℕ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


noncomputable def Homogeneous.registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@homogeneous_coordinates) (DependentFamily.Realization mapSignature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionProjective.homogeneous_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionProjective.Homogeneous.family
  realizationSource := none
  generated := false
  arena := .source ⟨Homogeneous.arena⟩
  objectArena := .source ⟨Homogeneous.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Homogeneous.arena ⟨Homogeneous.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := Option.some (DependentFamily.realize mapSignature (fun _ t p => projectiveMap t p) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := Option.some (OnePoint ℂ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


noncomputable def Semantics.registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@rational_map_semantics) (DependentFamily.Realization mapSignature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionProjective.rational_map_semantics.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionProjective.Semantics.family
  realizationSource := none
  generated := false
  arena := .source ⟨Semantics.arena⟩
  objectArena := .source ⟨Semantics.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Semantics.arena ⟨Semantics.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := Option.some (DependentFamily.realize mapSignature (fun _ t p => projectiveMap t p) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := Option.some (OnePoint ℂ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


noncomputable def Conjugacy.registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@not_conjugate) (DependentFamily.Realization mapSignature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionProjective.not_conjugate.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionProjective.Conjugacy.family
  realizationSource := none
  generated := false
  arena := .source ⟨Conjugacy.arena⟩
  objectArena := .source ⟨Conjugacy.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Conjugacy.arena ⟨Conjugacy.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := Option.some (DependentFamily.realize mapSignature (fun _ t p => projectiveMap t p) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := Option.some (OnePoint ℂ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


noncomputable def Mobius.registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@mobius_coordinates) (DependentFamily.Realization Mobius.signature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionProjective.mobius_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionProjective.Mobius.family
  realizationSource := none
  generated := false
  arena := .source ⟨Mobius.arena⟩
  objectArena := .source ⟨Mobius.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Mobius.arena ⟨Mobius.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := Option.some (DependentFamily.realize Mobius.signature (fun _ g p => mobius (Matrix.ProjGenLinGroup.mk g) p) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := Option.some (OnePoint ℂ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CubeRecursionProjective
