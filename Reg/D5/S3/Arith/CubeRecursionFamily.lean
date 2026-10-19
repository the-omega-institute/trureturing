import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.CubeRecursionFamily

/-!
# Reduced-pair and orbit readouts

The source telescope is retained without a finite restriction on parameters,
rational states or iterate indices. The selected readout is the actual rational
step or orbit. Source occurrence binding remains unspecified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.CubeRecursionFamily

open _root_.D5.S3.Arith.CubeRecursionFamily
open _root_.D5.S3.Arith.CubeRecursionProjective
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace ReducedStep

abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := DependentFamily.realize signature (fun _ t x => step t x) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ t a b : ℕ, 0 < a → 0 < b → a.Coprime b →
    0 < r.readout () t ((a : ℚ) / b) ∧
    (r.readout () t ((a : ℚ) / b)).num = (nextA t a b : ℤ) ∧
    (r.readout () t ((a : ℚ) / b)).den = nextB t a b ∧
    (nextA t a b).Coprime (nextB t a b) ∧
    nextA t a b + nextB t a b = (a + (t + 1) * b) ^ 3

abbrev sourceScope := type_of% (@reduced_step)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased := DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := (h 0 1 1 (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [erased, DependentFamily.realize] at hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp reduced_step, erased, erased_fails⟩
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
    refine ⟨0, 1, 2, ?_⟩
    norm_num [actual, DependentFamily.realize, step]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@reduced_step) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionFamily.reduced_step.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionFamily.ReducedStep.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ t x => step t x) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℚ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end ReducedStep

namespace PositiveOrbit

structure Params where
  t : ℕ
  x : ℚ
  positive : 0 < x

abbrev signature : DependentFamily.Signature where
  Params := Params
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := DependentFamily.realize signature
  (fun _ p n => orbit p.t p.x n) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ p : Params,
    (∀ n, 0 < r.readout () p n) ∧
    ∀ n, (r.readout () p (n + 1)).num + ((r.readout () p (n + 1)).den : ℤ) =
      ((r.readout () p n).num + ((p.t + 1 : ℕ) : ℤ) * (r.readout () p n).den) ^ 3

abbrev sourceScope := type_of% (@positive_orbit_cube)

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  exact ⟨fun h p => h p.t p.x p.positive, fun h t x hx => h ⟨t,x,hx⟩⟩

def erased := DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := (h ⟨0,1,by norm_num⟩).1 0
  norm_num [erased, DependentFamily.realize] at hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp positive_orbit_cube, erased, erased_fails⟩
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
    refine ⟨⟨0,1,by norm_num⟩, 0, 1, ?_⟩
    norm_num [actual, DependentFamily.realize, orbit, step]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@positive_orbit_cube) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionFamily.positive_orbit_cube.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionFamily.PositiveOrbit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ p n => orbit p.t p.x n) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℕ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveOrbit

namespace WholeFamily

open scoped MatrixGroups

abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℚ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := DependentFamily.realize signature
  (fun _ t p => orbit t p.1 p.2) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r =>
    ∀ t : ℕ,
    mapDegree (rationalMap t) = 3 ∧
    (∀ x y : ℂ, ∀ h : x ≠ 0 ∨ y ≠ 0,
      projectiveMap t (projectivePoint x y h) = homogeneousImage t x y h) ∧
    ((∀ g : PGL(2, ℂ), ∃ m : GL (Fin 2) ℂ, Matrix.ProjGenLinGroup.mk m = g) ∧
      ∀ m : GL (Fin 2) ℂ,
        mobius (Matrix.ProjGenLinGroup.mk m) OnePoint.infty =
          (if m 1 0 = 0 then OnePoint.infty else (m 0 0 / m 1 0 : ℂ)) ∧
        ∀ z : ℂ, mobius (Matrix.ProjGenLinGroup.mk m) z =
          (if m 1 0 * z + m 1 1 = 0 then OnePoint.infty
           else ((m 0 0 * z + m 0 1) / (m 1 0 * z + m 1 1) : ℂ))) ∧
        (projectiveMap t OnePoint.infty = (0 : ℂ) ∧
          ∀ z : ℂ, projectiveMap t z =
            if (rationalMap t).denom.eval z = 0 then OnePoint.infty
            else (RatFunc.eval (RingHom.id ℂ) z (rationalMap t) : ℂ)) ∧
        (∀ g : PGL(2, ℂ), ¬ ∀ p : OnePoint ℂ,
          mobius g (projectiveMap t (mobius g⁻¹ p)) = powerMap p) ∧
        ∀ x : ℚ, 0 < x →
          (∀ n : ℕ, 0 < r.readout () t (x, n) ∧ 0 < (r.readout () t (x, n)).num ∧
            0 < (r.readout () t (x, n)).den ∧
            (r.readout () t (x, n)).num.natAbs.Coprime (r.readout () t (x, n)).den ∧
            (r.readout () t (x, n)).num / ((r.readout () t (x, n)).den : ℚ) = r.readout () t (x, n)) ∧
          (∀ n : ℕ, 1 ≤ n →
            (r.readout () t (x, n)).num + ((r.readout () t (x, n)).den : ℤ) =
              ((r.readout () t (x, n - 1)).num +
                ((t + 1 : ℕ) : ℤ) * (r.readout () t (x, n - 1)).den) ^ 3) ∧
          (∀ n : ℕ, projectiveMap t (((r.readout () t (x, n)) : ℂ) : OnePoint ℂ) =
            (((r.readout () t (x, n + 1)) : ℂ) : OnePoint ℂ))

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased := DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := ((h 0).2.2.2.2.2 1 (by norm_num)).1 0
  norm_num [erased, DependentFamily.realize] at hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, erased, erased_fails⟩
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
    refine ⟨0, (1,0), (1,1), ?_⟩
    norm_num [actual, DependentFamily.realize, orbit, step]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Arith.CubeRecursionFamily.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.CubeRecursionFamily.WholeFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ t p => orbit t p.1 p.2) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ((ℚ × ℕ) : Type)
  sourceSelection := some {
    owner := `D5.S3.Arith.CubeRecursionFamily
    definition := some {
      owner := `D5.S3.Arith.CubeRecursionFamily
      name := `D5.S3.Arith.CubeRecursionFamily.originalClaim
      path := #[] }
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WholeFamily

end Reg.D5.S3.Arith.CubeRecursionFamily
