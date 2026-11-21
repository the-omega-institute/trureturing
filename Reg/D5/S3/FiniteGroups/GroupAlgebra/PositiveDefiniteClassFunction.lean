import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
import Reg.Support.DependentFamily

/-! # Source registrations for the character expansion of a positive semidefinite class function

The first readout is the dimension of the span of the sections `x ↦ φ (x * y⁻¹)`, as a function
of `φ`. On the trivial group the constant function `1` satisfies every hypothesis, and a
dimension of zero would force the empty family and hence `φ = 0`, which refutes the varied law.
The second readout is the weighted sum of characters `x ↦ ∑ i, c i * χ_i x` of the expansion
clause, as a function of the group element; the zero function refutes the varied law at `φ = 1`. -/

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
open _root_.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe u
noncomputable section

/-- The group and its group structure. -/
abbrev Params := Σ G : Type u, Group G

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The dimension of the span of the sections `x ↦ φ (x * y⁻¹)`. -/
def observe (p : Params.{u}) (φ : p.1 → ℂ) : ℕ := by
  obtain ⟨G, gG⟩ := p
  exact Module.finrank ℂ (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)))

def actual : Realization signature.{u} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original telescope is retained; only the dimension of the span varies. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [gG : Group G] (φ : G → ℂ)
    (_hpsd : (Matrix.of fun x y : G => φ (x * y⁻¹)).PosSemidef)
    (_hclass : ∀ g x, φ (g * x * g⁻¹) = φ x)
    (_hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)))),
    ∃ (m : ℕ) (n : Fin m → ℕ)
      (ρ : ∀ i, Representation ℂ G (EuclideanSpace ℂ (Fin (n i)))) (c : Fin m → ℝ),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) ∧
      (∀ i g v, ‖ρ i g v‖ = ‖v‖) ∧ (∀ i, 0 < c i) ∧
      (∀ x, φ x = ∑ i, (c i : ℂ) * (ρ i).character x) ∧
      (∀ i (v w : EuclideanSpace ℂ (Fin (n i))), (fun g => ⟪w, ρ i g v⟫_ℂ) ∈
        Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹))) ∧
      R.readout () ⟨G, gG⟩ φ = ∑ i, n i ^ 2

/-- On the trivial group the constant function `1` has a positive semidefinite kernel. -/
theorem one_posSemidef :
    (Matrix.of fun x y : PUnit.{u + 1} => (fun _ : PUnit.{u + 1} => (1 : ℂ)) (x * y⁻¹)).PosSemidef := by
  have : (Matrix.of fun x y : PUnit.{u + 1} => (fun _ : PUnit.{u + 1} => (1 : ℂ)) (x * y⁻¹)) = 1 := by
    ext x y
    simp [Subsingleton.elim x y]
  rw [this]
  exact Matrix.PosSemidef.one

/-- A dimension of zero forces every degree to vanish, irreducibility forces positive degrees, so
the family is empty and the expansion gives `1 = 0`. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨m, n, ρ, c, hirr, -, -, -, hφ, -, hrank⟩ :=
    @h PUnit.{u + 1} _ (fun _ => 1) one_posSemidef (fun _ _ => rfl) inferInstance
  have hrank' : (0 : ℕ) = ∑ i, n i ^ 2 := hrank
  have hn : ∀ i, n i = 0 := fun i =>
    pow_eq_zero_iff two_ne_zero |>.1 ((Finset.sum_eq_zero_iff.1 hrank'.symm) i (Finset.mem_univ _))
  have hpos : ∀ i, 0 < n i := fun i => by
    have := hirr i
    have : Nontrivial (ρ i).asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ PUnit.{u + 1}) _
    have : Nontrivial (EuclideanSpace ℂ (Fin (n i))) := (ρ i).asModuleEquiv.symm.toEquiv.nontrivial
    simpa using Module.finrank_pos (R := ℂ) (M := EuclideanSpace ℂ (Fin (n i)))
  have : IsEmpty (Fin m) := ⟨fun i => (hpos i).ne' (hn i)⟩
  have h1 := hφ PUnit.unit
  simp at h1

theorem observe_zero : observe ⟨PUnit.{u + 1}, inferInstance⟩ (fun _ => 0) = 0 := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range fun y : PUnit.{u + 1} =>
    fun x : PUnit.{u + 1} => (fun _ : PUnit.{u + 1} => (0 : ℂ)) (x * y⁻¹))) = 0
  simp
  rfl

theorem observe_one : observe ⟨PUnit.{u + 1}, inferInstance⟩ (fun _ => 1) = 1 := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range fun y : PUnit.{u + 1} =>
    fun x : PUnit.{u + 1} => (fun _ : PUnit.{u + 1} => (1 : ℂ)) (x * y⁻¹))) = 1
  rw [Set.range_unique]
  exact finrank_span_singleton (fun h => one_ne_zero (congrFun h PUnit.unit))

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, inferInstance⟩, fun _ => 0, fun _ => 1, fun h => ?_⟩
  change observe ⟨PUnit.{u + 1}, inferInstance⟩ (fun _ => (0 : ℂ)) =
    observe ⟨PUnit.{u + 1}, inferInstance⟩ (fun _ => (1 : ℂ)) at h
  rw [observe_zero, observe_one] at h
  exact zero_ne_one h

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_sum_character_of_finiteDimensional.{u}

def source : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_sum_character_of_finiteDimensional.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_sum_character_of_finiteDimensional.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction.exists_sum_character_of_finiteDimensional_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ => observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## The expansion clause: the weighted sum of characters as a function on the group -/
namespace Expansion

/-- The group, the degrees, the representations and the weights. -/
abbrev Params := Σ G : Type u, Σ _ : Group G, Σ m : ℕ, Σ n : Fin m → ℕ,
  Σ _ : (∀ i, Representation ℂ G (EuclideanSpace ℂ (Fin (n i)))), Fin m → ℝ

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The value at `x` of the weighted sum of characters `∑ i, c i * χ_i`. -/
def observe (p : Params.{u}) (x : p.1) : ℂ := by
  obtain ⟨G, gG, m, n, ρ, c⟩ := p
  exact ∑ i, (c i : ℂ) * (ρ i).character x

def actual : Realization signature.{u} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original telescope is retained; only the weighted sum of characters in the
expansion clause varies. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [gG : Group G] (φ : G → ℂ)
    (_hpsd : (Matrix.of fun x y : G => φ (x * y⁻¹)).PosSemidef)
    (_hclass : ∀ g x, φ (g * x * g⁻¹) = φ x)
    (_hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)))),
    ∃ (m : ℕ) (n : Fin m → ℕ)
      (ρ : ∀ i, Representation ℂ G (EuclideanSpace ℂ (Fin (n i)))) (c : Fin m → ℝ),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) ∧
      (∀ i g v, ‖ρ i g v‖ = ‖v‖) ∧ (∀ i, 0 < c i) ∧
      (∀ x, φ x = R.readout () ⟨G, gG, m, n, ρ, c⟩ x) ∧
      (∀ i (v w : EuclideanSpace ℂ (Fin (n i))), (fun g => ⟪w, ρ i g v⟫_ℂ) ∈
        Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹))) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹))) =
        ∑ i, n i ^ 2

/-- On the trivial group the constant function `1` satisfies the hypotheses, and the rejected
readout would make it the zero function. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨m, n, ρ, c, -, -, -, -, hφ, -, -⟩ :=
    @h PUnit.{u + 1} _ (fun _ => 1) one_posSemidef (fun _ _ => rfl) inferInstance
  exact one_ne_zero (hφ PUnit.unit)

/-- The integers, written multiplicatively, in universe `u`. -/
abbrev Ints := ULift.{u} (Multiplicative ℤ)

/-- The generator of the integers. -/
abbrev gen : Ints.{u} := ULift.up (Multiplicative.ofAdd 1)

/-- The line `EuclideanSpace ℂ (Fin 1)`. -/
abbrev Line := EuclideanSpace ℂ (Fin 1)

/-- The integers acting on the line by `n ↦ (-1) ^ n`. -/
def sign : Representation ℂ Ints.{u} Line :=
  (Units.coeHom _).comp ((zpowersHom _ (-1 : (Module.End ℂ Line)ˣ)).comp MulEquiv.ulift.toMonoidHom)

theorem sign_gen : sign.{u} gen = -1 := by
  change (((-1 : (Module.End ℂ Line)ˣ) ^ (1 : ℤ) : (Module.End ℂ Line)ˣ) : Module.End ℂ Line) = _
  rw [zpow_one, Units.val_neg, Units.val_one]

/-- One summand with weight one: the sign representation of the integers on a line. -/
abbrev testParams : Params.{u} :=
  ⟨Ints, inferInstance, 1, fun _ => 1, fun _ => sign, fun _ => 1⟩

theorem observe_one : observe testParams.{u} 1 = 1 := by
  change ∑ _i : Fin 1, ((1 : ℝ) : ℂ) * (sign.{u}).character 1 = 1
  rw [Fintype.sum_unique, Complex.ofReal_one, one_mul, Representation.character, map_one,
    LinearMap.trace_one, finrank_euclideanSpace_fin]
  norm_num

theorem observe_gen : observe testParams.{u} gen = -1 := by
  change ∑ _i : Fin 1, ((1 : ℝ) : ℂ) * (sign.{u}).character gen = -1
  rw [Fintype.sum_unique, Complex.ofReal_one, one_mul, Representation.character, sign_gen,
    map_neg, LinearMap.trace_one, finrank_euclideanSpace_fin]
  norm_num

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParams, 1, gen, fun h => ?_⟩
  change observe testParams.{u} 1 = observe testParams.{u} gen at h
  rw [observe_one, observe_gen] at h
  norm_num at h

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_sum_character_of_finiteDimensional.{u}

def source : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_sum_character_of_finiteDimensional.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

end Expansion

def expansion_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_sum_character_of_finiteDimensional.{u})
    (Realization Expansion.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction.exists_sum_character_of_finiteDimensional_expansion_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction.Expansion.source
  realizationSource := none
  generated := false
  arena := .source ⟨Expansion.arena⟩
  objectArena := .source ⟨Expansion.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Expansion.arena ⟨Expansion.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Expansion.signature (fun _ => Expansion.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
    definition := none
    coordinates := #[0, 6, 7, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
