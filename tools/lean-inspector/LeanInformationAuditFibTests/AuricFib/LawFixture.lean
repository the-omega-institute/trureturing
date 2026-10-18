import LeanInformationAuditInterface.Contract.AuricFib
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Typed law-family fixtures and kernel rejection boundaries. -/

namespace LeanInformationAuditFibTests.AuricFib.LawFixture
open LeanInformationAudit.Analysis LeanInformationAudit.AuricFib.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)

def starMasses : Masses := ⟨4, 1, 1, 1, 1, 8, by decide, by decide⟩

noncomputable def mass (_ : ℝ) (w : Window) : ℝ := starMasses.value w

theorem target : ∀ θ : ℝ, ∀ w : Window, mass θ w = mass θ w := fun _ _ => rfl

abbrev signature : DependentFamily.Signature where
  Params := ℝ
  State _ := Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : DependentFamily.Realization signature where
  readout _ := mass
  anchor e := nomatch e

noncomputable abbrev source : Source target where
  signature := signature
  actual := actual
  rebuild r := ∀ θ : ℝ, ∀ w : Window, r.readout () θ w = r.readout () θ w
  reconstruction := .exact
  selection := {
    owner := `LeanInformationAuditFibTests.AuricFib.LawFixture
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }

noncomputable abbrev client : Client.{0,0,0,0,0,0,0} target where
  source := source
  plan := { task := (), initial := [], additions := [[()]] }
  acquisition := .unavailable "parameter family; no finite parameter presentation"

noncomputable abbrev family : LawFamily client where
  Mode := Window
  state_eq _ := rfl
  role := ()
  output_eq _ := rfl
  atoms := [(.middle, .middle), (.ends, .ends), (.zero, .zero), (.high, .high), (.low, .low)]
  identify := id
  bijective := Function.bijective_id
  atoms_correct := by intro m w; cases m <;> cases w <;> simp
  law := mass
  law_eq _ _ := rfl
  domain θ := 0 ≤ θ ∧ θ ≤ 1
  nonnegative := by intro θ _ w; cases w <;> norm_num [mass, starMasses, Masses.value]
  normalized := by intro θ _; norm_num [mass, starMasses, Masses.value]

noncomputable def point : LawPoint family where
  parameter := (1 / 2 : ℝ)
  in_domain := by constructor <;> norm_num
  masses := starMasses
  law_eq _ := rfl

noncomputable def star : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) [] none

noncomputable def collapsed : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point)
    [.identifiable (by intro θ φ _ _ _; rfl)] none

private theorem targetDependentFact (θ φ : ℝ) (_ : family.domain θ) (_ : family.domain φ)
    (_ : Pyramid.CoarseEq (family.law θ) (family.law φ)) :
    Pyramid.delta (family.law θ) = Pyramid.delta (family.law φ) :=
  congrArg (fun _ : ℝ => Pyramid.delta (family.law θ)) (target θ .zero)

noncomputable def usesTarget : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) [.identifiable targetDependentFact] none

private opaque targetDependentOpaque (θ φ : ℝ) (hθ : family.domain θ) (hφ : family.domain φ)
    (h : Pyramid.CoarseEq (family.law θ) (family.law φ)) :
    Pyramid.delta (family.law θ) = Pyramid.delta (family.law φ) :=
  targetDependentFact θ φ hθ hφ h

noncomputable def usesOpaqueTarget : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) [.identifiable targetDependentOpaque] none

noncomputable def noPoint : Application.{0,0,0,0,0,0} target where
  evidence := .law client family none [] none

noncomputable def computedPoint : LawPoint family where
  parameter := (1 / 2 : ℝ)
  in_domain := by constructor <;> norm_num
  masses := { starMasses with nullMass := Nat.add 0 4 }
  law_eq _ := rfl

noncomputable def unavailablePoint : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some computedPoint)
    [.identifiable (by intro θ φ _ _ _; rfl)] none

noncomputable def taskSigned : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) []
    (some ⟨-1, 2, -3, 4, 5, 2, by decide⟩)

noncomputable def taskZero : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) []
    (some ⟨0, 0, 0, 0, 0, 1, by decide⟩)

noncomputable abbrev infiniteFamily : LawFamily client := {
  family with
  domain := fun _ => True
  simplex := none
  nonnegative := by intro θ _ w; cases w <;> norm_num [mass, starMasses, Masses.value]
  normalized := by intro θ _; norm_num [mass, starMasses, Masses.value]
  infinite := some ⟨Infinite.of_injective (fun θ : ℝ => (⟨θ, trivial⟩ : {θ : ℝ // True}))
    (fun _ _ h => congrArg Subtype.val h)⟩ }

noncomputable def infinite : Application.{0,0,0,0,0,0} target where
  evidence := .law client infiniteFamily none [] none

noncomputable def signed : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point)
    [.deltaSign .positive (by
       intro θ _
       norm_num [DeltaSign.Holds, Pyramid.delta, Pyramid.r, Pyramid.kappa,
         Pyramid.X, Pyramid.Y, Pyramid.Z,
         mass, starMasses, Masses.value]),
     .positiveWidth (by
       intro θ _
       norm_num [Pyramid.width, Pyramid.r, Pyramid.X, Pyramid.Y, Pyramid.Z,
         mass, starMasses, Masses.value])] none

namespace Separation
noncomputable def law (θ : Bool) (w : Window) : ℝ :=
  if θ then match w with | .low | .high => 1/2 | _ => 0
  else match w with | .zero | .ends => 1/2 | _ => 0

theorem target : ∀ θ w, law θ w = law θ w := fun _ _ => rfl
abbrev signature : DependentFamily.Signature where
  Params := Bool
  State _ := Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : DependentFamily.Realization signature where
  readout _ := law
  anchor e := nomatch e
noncomputable abbrev source : Source target where
  signature := signature
  actual := actual
  rebuild r := ∀ θ w, r.readout () θ w = r.readout () θ w
  reconstruction := .exact
  selection := { LawFixture.source.selection with
    owner := `LeanInformationAuditFibTests.AuricFib.LawFixture }
noncomputable abbrev client : Client.{0,0,0,0,0,0,0} target where
  source := source
  plan := { task := (), initial := [], additions := [[()]] }
  acquisition := .unavailable "no parameter-domain presentation"
noncomputable abbrev family : LawFamily client where
  Mode := Window
  state_eq _ := rfl
  role := ()
  output_eq _ := rfl
  atoms := LawFixture.family.atoms
  identify := id
  bijective := Function.bijective_id
  atoms_correct := LawFixture.family.atoms_correct
  law := law
  law_eq _ _ := rfl
  domain _ := True
  nonnegative := by intro θ _ w; cases θ <;> cases w <;> norm_num [law]
  normalized := by intro θ _; cases θ <;> norm_num [law]
noncomputable def strict : Application.{0,0,0,0,0,0} target where
  evidence := .law client family none
    [.separated (by
      refine ⟨false, true, trivial, trivial, ?_, ?_⟩
      · norm_num [Pyramid.CoarseEq, Pyramid.X, Pyramid.Y, Pyramid.Z, law]
      · norm_num [DeltaSign.Holds, Pyramid.delta, Pyramid.r, Pyramid.kappa,
         Pyramid.X, Pyramid.Y, Pyramid.Z, law])]
    (some ⟨0, 0, 0, 1, 0, 1, by decide⟩)
end Separation

namespace Simplex

theorem target : ∀ p : Window → ℝ, ∀ w, p w = p w := fun _ _ => rfl
abbrev signature : DependentFamily.Signature where
  Params := Window → ℝ
  State _ := Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : DependentFamily.Realization signature where
  readout _ p := p
  anchor e := nomatch e
noncomputable abbrev source : Source target where
  signature := signature
  actual := actual
  rebuild r := ∀ p w, r.readout () p w = r.readout () p w
  reconstruction := .exact
  selection := LawFixture.source.selection
noncomputable abbrev client : Client.{0,0,0,0,0,0,0} target where
  source := source
  plan := { task := (), initial := [], additions := [[()]] }
  acquisition := .unavailable "no finite simplex presentation"
noncomputable abbrev family : LawFamily client where
  Mode := Window
  state_eq _ := rfl
  role := ()
  output_eq _ := rfl
  atoms := LawFixture.family.atoms
  identify := id
  bijective := Function.bijective_id
  atoms_correct := LawFixture.family.atoms_correct
  law := id
  law_eq _ _ := rfl
  domain p := (∀ w, 0 ≤ p w) ∧ p .zero + p .low + p .high + p .ends + p .middle = 1
  nonnegative _ h := h.1
  normalized _ h := h.2
  simplex := some ⟨fun p hp hn => ⟨p, ⟨hp, hn⟩, fun _ => rfl⟩⟩
noncomputable def strict : Application.{0,0,0,0,0,0} target where
  evidence := .law client family none
    [.separated (by
      refine ⟨Separation.law false, Separation.law true, ?_, ?_, ?_, ?_⟩
      · constructor
        · intro w; cases w <;> norm_num [Separation.law]
        · norm_num [Separation.law]
      · constructor
        · intro w; cases w <;> norm_num [Separation.law]
        · norm_num [Separation.law]
      · norm_num [Pyramid.CoarseEq, Pyramid.X, Pyramid.Y, Pyramid.Z, Separation.law]
      · norm_num [Pyramid.delta, Pyramid.r, Pyramid.kappa, Pyramid.X, Pyramid.Y, Pyramid.Z,
          Separation.law])] none
end Simplex

namespace Star

inductive Mode where
  | separate | ab | bc | all | ac
  deriving DecidableEq

def identify : Mode → Window
  | .separate => .zero | .ab => .low | .bc => .high | .all => .ends | .ac => .middle
def fromWindow : Window → Mode
  | .zero => .separate | .low => .ab | .high => .bc | .ends => .all | .middle => .ac

/-- Independent star bonds, with zero or one open bond giving separate terminals. -/
noncomputable def mass (θ : ℝ × ℝ × ℝ) (m : Mode) : ℝ :=
  let A := θ.1
  let B := θ.2.1
  let C := θ.2.2
  match m with
  | .separate => (1-A)*(1-B)*(1-C) + A*(1-B)*(1-C) +
      (1-A)*B*(1-C) + (1-A)*(1-B)*C
  | .ab => A*B*(1-C)
  | .bc => (1-A)*B*C
  | .all => A*B*C
  | .ac => A*(1-B)*C

theorem target : ∀ θ m, mass θ m = mass θ m := fun _ _ => rfl
abbrev signature : DependentFamily.Signature where
  Params := ℝ × ℝ × ℝ
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def actual : DependentFamily.Realization signature where
  readout _ := mass
  anchor e := nomatch e
noncomputable abbrev source : Source target where
  signature := signature
  actual := actual
  rebuild r := ∀ θ m, r.readout () θ m = r.readout () θ m
  reconstruction := .exact
  selection := LawFixture.source.selection
noncomputable abbrev client : Client.{0,0,0,0,0,0,0} target where
  source := source
  plan := { task := (), initial := [], additions := [[()]] }
  acquisition := .unavailable "continuous three-bond parameter domain"
noncomputable abbrev family : LawFamily client where
  Mode := Mode
  state_eq _ := rfl
  role := ()
  output_eq _ := rfl
  atoms := [(.ac, .middle), (.separate, .zero), (.bc, .high), (.all, .ends), (.ab, .low)]
  identify := identify
  bijective := by
    constructor
    · intro a b h; cases a <;> cases b <;> cases h <;> rfl
    · intro w; refine ⟨fromWindow w, ?_⟩; cases w <;> rfl
  atoms_correct := by intro m w; cases m <;> cases w <;> simp [identify]
  law θ w := mass θ (fromWindow w)
  law_eq := by intro θ m; cases m <;> rfl
  domain θ := θ.1 ∈ Set.Icc 0 1 ∧ θ.2.1 ∈ Set.Icc 0 1 ∧ θ.2.2 ∈ Set.Icc 0 1
  nonnegative := by
    intro θ h w
    rcases h with ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩
    have hA : 0 ≤ 1 - θ.1 := sub_nonneg.mpr ha'
    have hB : 0 ≤ 1 - θ.2.1 := sub_nonneg.mpr hb'
    have hC : 0 ≤ 1 - θ.2.2 := sub_nonneg.mpr hc'
    cases w <;> dsimp [mass, fromWindow] <;> positivity
  normalized := by intro θ _; dsimp [mass, fromWindow]; ring
noncomputable def point : LawPoint family where
  parameter := (1/2, 1/2, 1/2)
  in_domain := by norm_num [family]
  masses := starMasses
  law_eq := by intro w; cases w <;> norm_num [family, mass, fromWindow, starMasses, Masses.value]
noncomputable def analysis : Application.{0,0,0,0,0,0} target where
  evidence := .law client family (some point) [] none

end Star

/-- A constant identification cannot acquire the required bijection. -/
theorem rejectsNonbijectiveIdentification : True := by
  fail_if_success
    have : LawFamily client := { family with
      identify := fun _ => Window.zero, bijective := Function.bijective_id }
  trivial

/-- An unrelated law cannot acquire equality to the actual source readout. -/
theorem rejectsFalseLawEquality : True := by
  fail_if_success
    have : LawFamily client := { family with
      law := fun _ _ => 0, law_eq := fun _ _ => rfl }
  trivial

/-- An arbitrary proposition is not an allowed family-fact certificate. -/
theorem rejectsFactOutsideAllowlist : True := by
  fail_if_success
    have : LawFact family := .positiveWidth (show True from trivial)
  trivial

/-- The requested negative rational point cannot acquire a domain certificate. -/
theorem rejectsPointOutsideDomain : ¬ family.domain (-1) := by norm_num [family]

end LeanInformationAuditFibTests.AuricFib.LawFixture
