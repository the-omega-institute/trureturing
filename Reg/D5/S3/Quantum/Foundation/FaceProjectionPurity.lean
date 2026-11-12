import D5.S3.Quantum.Foundation.FaceProjectionPurity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Normalized original projection outputs on arbitrary finite dimensional carriers. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FaceProjectionPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Inputs where
  A : Type u
  [add : NormedAddCommGroup A]
  [space : NormedSpace ℝ A]
  [finite : FiniteDimensional ℝ A]
  cone : PointedCone ℝ A
  unit : A →ₗ[ℝ] ℝ
  pairing : A →ₗ[ℝ] A →ₗ[ℝ] ℝ
  face : PointedCone.Face cone
  projection : A →ₗ[ℝ] A

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => (P.unit (P.projection x))⁻¹ • P.projection x)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    let B := P.pairing
    let F := P.face
    let Q := P.projection
    IsClosed (C : Set P.A) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    (∃ x ∈ C, x ≠ (0 : P.A)) →
    (∀ x y, B x y = B y x) →
    (∀ x : P.A, x ≠ 0 → 0 < B x x) →
    (∀ x, x ∈ C ↔ ∀ y ∈ C, 0 ≤ B x y) →
    (∀ p : pure C u, confirms C u p (B p)) →
    (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, B p x ≤ f x) →
    (∀ x, Q (Q x) = Q x) →
    (∀ x y, B (Q x) y = B x (Q y)) →
    (∀ x ∈ C, Q x ∈ F) →
    (∀ x ∈ F, Q x = x) →
    pure C u = {x | x ∈ base C u ∧ B x x = 1} ∧
      IsCompact (pure C u) ∧ (pure C u).Nonempty ∧
      ∀ p : pure C u, Q p = 0 ∨
        (0 < u (Q p) ∧ O.readout () P p ∈ pure C u ∧
          Q p = u (Q p) • O.readout () P p)

abbrev sourceScope : Prop := type_of% (@least_confirmation_face_purity.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    dsimp only
    intro hclosed hu hne hsym hpos hdual hc hleast hid hadj hface hfix
    exact @h P.A P.add P.space P.finite P.cone P.unit hclosed hu hne P.pairing
      hsym hpos hdual hc hleast P.face P.projection hid hadj hface hfix
  · intro h A add space finite C u hclosed hu hne B hsym hpos hdual hc hleast F Q
    exact h (@Inputs.mk A add space finite C u B F Q) hclosed hu hne hsym hpos hdual hc hleast

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@least_confirmation_face_purity.{u})

private abbrev Line := ULift.{u} ℝ

private instance lineFinite : FiniteDimensional ℝ Line.{u} :=
  FiniteDimensional.of_injective (ULift.moduleEquiv : Line.{u} ≃ₗ[ℝ] ℝ).toLinearMap
    ULift.down_injective

private def lineUnit : Line.{u} →ₗ[ℝ] ℝ := ULift.moduleEquiv.toLinearMap

private def lineCone : PointedCone ℝ Line.{u} :=
  (PointedCone.positive ℝ ℝ).comap lineUnit

private def linePairing : Line.{u} →ₗ[ℝ] Line.{u} →ₗ[ℝ] ℝ :=
  (LinearMap.mul ℝ ℝ).compl₁₂ lineUnit lineUnit

private theorem lineBase : base lineCone.{u} lineUnit = {ULift.up 1} := by
  ext x
  constructor
  · intro hx
    exact ULift.ext hx.2
  · intro hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨show (0 : ℝ) ≤ 1 by norm_num, rfl⟩

private theorem linePure : pure lineCone.{u} lineUnit = {ULift.up 1} := by
  rw [_root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.pure,
    lineBase, extremePoints_singleton]

private def linePoint : pure lineCone.{u} lineUnit :=
  ⟨ULift.up 1, (Set.ext_iff.mp linePure _).mpr (Set.mem_singleton _)⟩

private def lineInputs : Inputs.{u} where
  A := Line.{u}
  cone := lineCone
  unit := lineUnit
  pairing := linePairing
  face := ⊤
  projection := LinearMap.id

private theorem line_closed : IsClosed (lineCone.{u} : Set Line) :=
  isClosed_le continuous_const lineUnit.continuous_of_finiteDimensional

private theorem line_strict : ∀ x ∈ lineCone.{u}, x ≠ 0 → 0 < lineUnit x := by
  intro x hx hx0
  have hx' : x.down ≠ 0 := fun hh => hx0 (ULift.ext hh)
  exact lt_of_le_of_ne hx (Ne.symm hx')

private theorem line_positive : ∀ x : Line.{u}, x ≠ 0 → 0 < linePairing x x := by
  intro x hx
  exact mul_self_pos.mpr (fun hh => hx (ULift.ext hh))

private theorem line_dual : ∀ x : Line.{u},
    x ∈ lineCone ↔ ∀ y ∈ lineCone, 0 ≤ linePairing x y := by
  intro x
  constructor
  · exact fun hx y hy => mul_nonneg hx hy
  · intro hh
    have hx := hh (ULift.up 1) (show (0 : ℝ) ≤ 1 by norm_num)
    change 0 ≤ x.down * 1 at hx
    change 0 ≤ x.down
    simpa only [mul_one] using hx

private theorem line_confirms :
    ∀ p : pure lineCone.{u} lineUnit, confirms lineCone lineUnit p (linePairing p) := by
  intro p
  have hp : (p : Line) = ULift.up 1 := by
    exact (Set.ext_iff.mp linePure _).mp p.property
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hp]
    change 0 ≤ 1 * x.down ∧ 1 * x.down ≤ x.down
    simpa only [one_mul] using And.intro (show 0 ≤ x.down from hx) (le_refl x.down)
  · rw [hp]
    change (1 : ℝ) * 1 = 1
    norm_num

private theorem line_least : ∀ (p : pure lineCone.{u} lineUnit) f,
    confirms lineCone lineUnit p f → ∀ x ∈ lineCone, linePairing p x ≤ f x := by
  intro p f hf x _
  have hp : (p : Line) = ULift.up 1 := by
    exact (Set.ext_iff.mp linePure _).mp p.property
  have hf1 : f (ULift.up 1) = 1 := by simpa [hp] using hf.2
  have hx : x = x.down • (ULift.up 1 : Line) := by ext; simp
  have hfx : f x = x.down := by
    conv_lhs => rw [hx, map_smul, smul_eq_mul, hf1, mul_one]
  rw [hp, hfx]
  change 1 * x.down ≤ x.down
  simp

private theorem line_evaluation (O : Realization signature.{u}) (h : arena.Law O) :
    O.readout () lineInputs linePoint = ULift.up 1 := by
  have hh := h lineInputs line_closed line_strict
    ⟨ULift.up 1, (show (0 : ℝ) ≤ 1 by norm_num), by
      intro hzero
      have := congrArg ULift.down hzero
      change (1 : ℝ) = 0 at this
      norm_num at this⟩
    (fun x y => mul_comm x.down y.down) line_positive line_dual line_confirms line_least
    (fun _ => rfl) (fun _ _ => rfl) (fun x hx => hx) (fun _ _ => rfl)
  rcases hh.2.2.2 linePoint with hz | ⟨_, _, he⟩
  · have := congrArg ULift.down hz
    change (1 : ℝ) = 0 at this
    norm_num at this
  · change (ULift.up 1 : Line.{u}) = (1 : ℝ) • O.readout () lineInputs linePoint at he
    rw [one_smul] at he
    exact he.symm

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  have he := line_evaluation rejected hh
  have hh' := congrArg ULift.down he
  change (0 : ℝ) = 1 at hh'
  norm_num at hh'

private abbrev Plane := ULift.{u} (ℝ × ℝ)

private instance planeFinite : FiniteDimensional ℝ Plane.{u} :=
  FiniteDimensional.of_injective (ULift.moduleEquiv : Plane.{u} ≃ₗ[ℝ] ℝ × ℝ).toLinearMap
    ULift.down_injective

private def planeUnit : Plane.{u} →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).comp ULift.moduleEquiv.toLinearMap

private def planeCone : PointedCone ℝ Plane.{u} :=
  ((PointedCone.positive ℝ ℝ).prod (PointedCone.positive ℝ ℝ)).comap
    ULift.moduleEquiv.toLinearMap

private def planeInputs : Inputs.{u} where
  A := Plane.{u}
  cone := planeCone
  unit := planeUnit
  pairing := 0
  face := ⊤
  projection := LinearMap.id

private theorem planeLeft : ULift.up (1, 0) ∈ pure planeCone.{u} planeUnit := by
  refine ⟨⟨show (0 : ℝ × ℝ) ≤ (1, 0) by constructor <;> norm_num,
    by change (1 + 0 : ℝ) = 1; norm_num⟩, ?_⟩
  intro y hy z hz hseg
  change (0 ≤ y.down.1 ∧ 0 ≤ y.down.2) ∧ y.down.1 + y.down.2 = 1 at hy
  change (0 ≤ z.down.1 ∧ 0 ≤ z.down.2) ∧ z.down.1 + z.down.2 = 1 at hz
  obtain ⟨a, b, ha, hb, _, he⟩ := hseg
  have he2 := congrArg (fun x : Plane => x.down.2) he
  change a * y.down.2 + b * z.down.2 = 0 at he2
  have hy2 : y.down.2 = 0 := by nlinarith [hy.1.2, hz.1.2]
  apply ULift.ext
  exact Prod.ext (by linarith [hy.2]) hy2

private theorem planeRight : ULift.up (0, 1) ∈ pure planeCone.{u} planeUnit := by
  refine ⟨⟨show (0 : ℝ × ℝ) ≤ (0, 1) by constructor <;> norm_num,
    by change (0 + 1 : ℝ) = 1; norm_num⟩, ?_⟩
  intro y hy z hz hseg
  change (0 ≤ y.down.1 ∧ 0 ≤ y.down.2) ∧ y.down.1 + y.down.2 = 1 at hy
  change (0 ≤ z.down.1 ∧ 0 ≤ z.down.2) ∧ z.down.1 + z.down.2 = 1 at hz
  obtain ⟨a, b, ha, hb, _, he⟩ := hseg
  have he1 := congrArg (fun x : Plane => x.down.1) he
  change a * y.down.1 + b * z.down.1 = 0 at he1
  have hy1 : y.down.1 = 0 := by nlinarith [hy.1.1, hz.1.1]
  apply ULift.ext
  exact Prod.ext hy1 (by linarith [hy.2])

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨planeInputs, ⟨ULift.up (1, 0), planeLeft⟩,
    ⟨ULift.up (0, 1), planeRight⟩, ?_⟩
  intro he
  have hh := congrArg (fun x : Plane => x.down.1) he
  change (1 + 0 : ℝ)⁻¹ * 1 = (0 + 1 : ℝ)⁻¹ * 0 at hh
  norm_num at hh

def family : Registration arena.{u} (type_of% @least_confirmation_face_purity.{u}) where
  actual := realize signature (fun _ P x => (P.unit (P.projection x))⁻¹ • P.projection x)
    (fun e => nomatch e)
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@least_confirmation_face_purity.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P x => (P.unit (P.projection x))⁻¹ • P.projection x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FaceProjectionPurity
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 9, 15, 16]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_bridge
#print axioms actual_positive
#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Foundation.FaceProjectionPurity
