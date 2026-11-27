import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection

/-! The original first-residue observation is the cast of the source
coordinate from the product modulus to the first modulus. The Law below
retains the full source telescope, including the single D preceding both
moduli and the equivalence of the exact dependent fibres. -/

namespace Reg.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection

open _root_.D5.S3.Combinatorics.Geometry.HyperplaneArrangements
open _root_.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

open _root_.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection (result)

abbrev sourceScope := type_of% (@result.{u})

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State P := ZMod (P.1 * P.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := ZMod P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => ZMod.cast x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} {n : ℕ} [Finite ι]
    (a : ι → Fin n → ℤ) (b : ι → ℤ),
    ∃ D : ℕ, 0 < D ∧
      ∀ p q : ℕ, 1 < p → 1 < q → p.Coprime q → p.Coprime D → q.Coprime D →
        ∃ e : Complement a b (p * q) ≃
          (Σ V : RationalFlat a,
            {x : Fin n → ZMod p // ∀ i : ι,
              (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod p) a i x ≠ (b i : ZMod p)} ×
            {y : Fin n → ZMod q //
              (∀ i : ι, (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod q) a i y = 0) ∧
              (∀ i : ι, ¬ (∀ v ∈ V.val, row ℚ a i v = 0) → row (ZMod q) a i y ≠ 0)}),
          ∀ z j, (e z).2.1.val j = r.readout () ⟨p, q⟩ (z.val j)

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_positive : arena.{u}.Law actual :=
  @result.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Empty → Fin 1 → ℤ := fun _ _ => 0
  let b : ULift.{u} Empty → ℤ := fun _ => 0
  obtain ⟨D, hD, hDlaw⟩ := h a b
  let p := D + 1
  let q := D * p + 1
  have hp : 1 < p := by dsimp [p]; omega
  have hq : 1 < q := by
    have hmul := Nat.mul_pos hD (by omega : 0 < p)
    dsimp [q]
    omega
  have hpD : p.Coprime D := by simp [p]
  have hqD : q.Coprime D := by simp [q, Nat.add_comm]
  have hpq : p.Coprime q := by simp [q, Nat.add_comm]
  obtain ⟨e, he⟩ := hDlaw p q hp hq hpq hpD hqD
  let V : RationalFlat a := ⟨commonKernel a ∅, ∅, rfl⟩
  let target : type_of% (e (⟨fun _ => 0, fun i => nomatch i.down⟩ : Complement a b (p * q))) :=
    ⟨V, ⟨(⟨fun _ => 1, fun i => nomatch i.down⟩),
      ⟨fun _ => 0, ⟨(fun i => nomatch i.down), (fun i => nomatch i.down)⟩⟩⟩⟩
  obtain ⟨z, hz⟩ := e.surjective target
  have hbad := he z (0 : Fin 1)
  rw [hz] at hbad
  change (1 : ZMod p) = 0 at hbad
  let : Fact (1 < p) := ⟨hp⟩
  exact one_ne_zero hbad

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 3⟩, 0, 1, ?_⟩
  change (ZMod.cast (0 : ZMod 6) : ZMod 2) ≠ ZMod.cast (1 : ZMod 6)
  rw [ZMod.cast_zero, ZMod.cast_one (by decide : 2 ∣ 6)]
  decide

def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := actual_dependence

set_option linter.style.longLine false in
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result.{u})
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ZMod.cast x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection
    definition := none
    coordinates := #[6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Combinatorics.Geometry.HyperplaneArrangements.CentralizationBijection
