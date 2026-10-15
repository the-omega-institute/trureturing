import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization

open _root_.D5.S3.StatisticalMechanics.CellularAutomata
open KleinFourInvariant KleinFourFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev LawfulCA := {T : Function.End Config // LazyInvertibleGeneration.IsCA T}
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => LawfulCA) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ T => T.1 ∈ Submonoid.closure
    ({F | LazyInvertibleGeneration.IsInvertibleCA F} ∪ {F | LazyInvertibleGeneration.IsLazy F}))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def condition (T : Function.End Config) : Prop :=
  ((∃ b : Bool, T '' weightSet 1 = weightSet (if b then 3 else 1) ∧
      T '' weightSet 3 = weightSet (if b then 3 else 1)) →
    ∃ (x : Config) (b : Bool), (orbitFinset x).card = 2 ∧
      T '' (constants ∪ orbit x) = {fun _ => b})

abbrev arena : Arena where
  signature := signature
  Law R := ∀ T : LawfulCA, R.readout () () T ↔ condition T.1

def identityCA : LawfulCA := ⟨1, by rw [← lift.map_one]; exact isca_lift 1⟩

theorem identity_condition : condition identityCA.1 :=
  (membership_iff 1 identityCA.2).mp (Submonoid.one_mem _)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h identityCA).mpr identity_condition

def merger : CA :=
  ({ lower := { c := id, p := fun _ => (true, false) },
     free := fun _ => .f false e } : Table).ca

theorem merger_not_generated : lift merger ∉ generated := by
  intro h
  have hm : Merges merger := ⟨false, rfl, rfl⟩
  have hn : ¬ Witness merger := by
    rintro ⟨_, b, h0, h1, _, _⟩
    change X.c false = .c b at h0
    change X.c true = .c b at h1
    exact (by decide : X.c false ≠ .c true) (h0.trans h1.symm)
  exact hn (membership_implies_criterion merger ((lift_membership_iff merger).mp h) hm)

def mergerCA : LawfulCA := ⟨lift merger, isca_lift merger⟩

def source_registration : Registration arena
    (∀ (T : Function.End Config), LazyInvertibleGeneration.IsCA T →
      (T ∈ Submonoid.closure ({F | LazyInvertibleGeneration.IsInvertibleCA F} ∪
        {F | LazyInvertibleGeneration.IsLazy F}) ↔ condition T)) where
  actual := actual
  bridge := by
    constructor
    · intro h T; exact h T.1 T.2
    · intro h T hT; exact h ⟨T, hT⟩
  variation := ⟨fun T => membership_iff T.1 T.2, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨(), identityCA, mergerCA, ?_⟩
    intro h
    change ((1 : Function.End Config) ∈ generated) = (lift merger ∈ generated) at h
    exact merger_not_generated (Eq.mp h (Submonoid.one_mem generated))

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization.membership_iff)
      (type_of% (realize signature
        (fun _ _ T => T.1 ∈ Submonoid.closure
          ({F | LazyInvertibleGeneration.IsInvertibleCA F} ∪
            {F | LazyInvertibleGeneration.IsLazy F})) (fun e => nomatch e)))
      Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization.membership_iff
    "Reg.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization/\
    Reg.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization.arena/[anonymous]")
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ T => T.1 ∈ Submonoid.closure
      ({F | LazyInvertibleGeneration.IsInvertibleCA F} ∪
        {F | LazyInvertibleGeneration.IsLazy F})) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.KleinFourFactorization
