import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
import Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
import Reg.Support.DependentFamily

/-! The uniform construction reads the prescribed marginals on the copies of the tables. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

open _root_.D5.S3.ConceptDynamics.Attribution
open _root_.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
open _root_.D5.S3.ConceptDynamics.Attribution.FixedKernelMass (seedFixedMass)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Matrix

universe u v w s

noncomputable section

attribute [local instance 2000] FiniteTableCalibration.tableSMul FiniteTableCalibration.tableAction

local instance {G : Type*} {T : Type*} [Group G] [MulAction G T] [Fintype T] :
    Fintype (Orbit G T) := Fintype.ofFinite _

open Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (signature actual rejected)

open Classical in
abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w}
      [Group G] [MulAction G X] [MulAction G Y] [Fintype X] [Fintype Y]
    (H : Subgroup G) (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
        (normalized : ∀ x, ∑ y, P x y = 1)
        (cov : ∀ (g : G) x y, P (g • x) (g • y) = P x y)
        (m : ℕ) (hm : 0 < m) (z : X × Y → ℤ)
        (hz : ∀ x y, P x y = (z (x, y) : ℝ) / m),
        let cell (xy : X × Y) := univ.filter (fun t : X → Y => t xy.1 = xy.2)
        let A : Matrix (Option (X × Y)) (Orbit G (X → Y)) ℤ :=
          fun i o => orbitCount (i.elim univ cell) o
        ∃ x : Orbit G (X → Y) → ℝ,
          ∃ rows : {o // 0 < x o} → Option (X × Y), Function.Injective rows ∧
            let N := m * (A.submatrix rows Subtype.val).det.natAbs
            0 < N ∧ ∃ (U : Type (max v w)) (_ : Fintype U) (_ : MulAction G U) (f : X → U → Y),
              Fintype.card U = N ∧
              (∀ x y, (∑ t : U, if f x t = y then (N : ℝ)⁻¹ else 0) = R.readout () ⟨X, Y⟩ P x y) ∧
              (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
              (∀ t : X → Y, FiniteTableCalibration.tableLaw (fun _ : U => (N : ℝ)⁻¹) f t =
                x (orbit t)) ∧
              ∀ (S : Type s) (_ : Fintype S) (_ : MulAction G S) (a : S → ℝ) (read : X → S → Y),
                (∀ t, 0 ≤ a t) → (∑ t, a t) = 1 → (∀ (g : G) t, a (g • t) = a t) →
                (∀ x y, (∑ t, if read x t = y then a t else 0) = P x y) →
                (∀ (g : G) x t, read (g • x) (g • t) = g • read x t) →
                seedFixedMass (G := H) a ≤ seedFixedMass (G := H) (fun _ : U => (N : ℝ)⁻¹)

private theorem rejected_law : ¬ arena.{u,v,w,s}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let X := PUnit.{v+1}
  let Y := PUnit.{w+1}
  let P (_ : X) (_ : Y) : ℝ := 1
  obtain ⟨_, _, _, hN, U, _, _, f, card, marginal, _, _, _⟩ :=
    altered (G := G) (X := X) (Y := Y) ⊤ P (fun _ _ => zero_le_one)
      (fun _ => by simp [P]) (fun _ _ _ => rfl) 1 Nat.one_pos (fun _ => 1)
      (fun _ _ => by norm_num [P])
  have post := marginal PUnit.unit PUnit.unit
  have identical (u : U) : f PUnit.unit u = PUnit.unit := Subsingleton.elim _ _
  simp only [identical, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card] at post
  have contradiction : (1 : ℝ) = 0 := by
    change _ = (0 : ℝ) at post
    rwa [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')] at post
  exact one_ne_zero contradiction

def family : Registration arena.{u,v,w,s} (type_of% (@uniform_kernel_optimum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_kernel_optimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨PUnit.{v+1}, PUnit.{w+1}⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun (congrFun equal PUnit.unit) PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_kernel_optimum) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.rationalKernel
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,s}⟩
  objectArena := .source ⟨arena.{u,v,w,s}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,s} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
        "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev copyEventSignature : Signature where
  Params := Type v
  State T := T → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def copyEventActual : Realization copyEventSignature.{v} :=
  realize copyEventSignature (fun _ _ event => event) (fun e => nomatch e)

def copyEventEmpty : Realization copyEventSignature.{v} :=
  realize copyEventSignature (fun _ _ _ _ => False) (fun e => nomatch e)

open Classical in
abbrev copyEventArena : Arena where
  signature := copyEventSignature.{v}
  Law R :=
    ∀ {G : Type u} {T : Type v} [Group G] [MulAction G T] [Fintype T] (n : T → ℕ),
      (∀ (g : G) t, n (g • t) = n t) →
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ A : T → Prop,
          (∑ s : S, if R.readout () T A (f s) then 1 else (0 : ℕ)) =
            ∑ t : T, if A t then n t else 0

private theorem empty_copy_event_fails : ¬ copyEventArena.{u,v}.Law copyEventEmpty := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let _ : Group G := inferInstanceAs (Group PUnit)
  let _ : Fintype T := inferInstanceAs (Fintype PUnit)
  let _ : MulAction G T :=
    { smul := fun _ t => t
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  obtain ⟨S, _, _, f, _, _, counts⟩ :=
    law (G := G) (T := T) (fun _ => 1) (fun _ _ => rfl)
  have impossible := counts (fun _ => True)
  have empty (s : S) : copyEventEmpty.readout () T (fun _ => True) (f s) = False := rfl
  simp only [empty, ite_false, ite_true, Finset.sum_const_zero] at impossible
  simp [T] at impossible

def copyEventFamily : Registration copyEventArena.{u,v}
    (type_of% (@SeedCopies.exact_card_count)) where
  actual := copyEventActual
  bridge := Iff.rfl
  variation := ⟨@SeedCopies.exact_card_count, copyEventEmpty, empty_copy_event_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨copyEventEmpty, ?_, rfl, empty_copy_event_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{v+1}, fun _ => False, fun _ => True, ?_⟩
    intro equal
    exact (Eq.mp (congrFun equal PUnit.unit).symm trivial)

def copyEventRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@SeedCopies.exact_card_count) (Realization copyEventSignature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.copyEventCounts
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.copyEventFamily
  realizationSource := none
  generated := false
  arena := .source ⟨copyEventArena.{u,v}⟩
  objectArena := .source ⟨copyEventArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source copyEventArena.{u,v} ⟨copyEventFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize copyEventSignature (fun _ _ event => event) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
    definition := none
    coordinates := #[1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
          "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg",
          "arg", "body", "fn", "fn", "fn", "arg", "fn"]
        stateBinder := 11
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
          "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg",
          "arg", "body", "fn", "fn", "arg", "arg", "fn"]
        stateBinder := 11
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
