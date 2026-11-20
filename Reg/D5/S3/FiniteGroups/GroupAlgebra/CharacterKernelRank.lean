import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Source registration for the rank of a character kernel

The readout is the dimension of the span of the sections, as a function of the weight family.
For the span of the operator families `(ρ i g)_i` the readout is the span of a set of families;
for the nondegeneracy of the weighted trace pairing it is the family in the conclusion.
The two theorems after the registrations show that irreducibility and pairwise inequivalence
cannot be dropped from the rank formula. -/

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
open _root_.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe uk uG uι uW
noncomputable section

/-! ## The registration -/

/-- Carrier field, group, index type, spaces, their dictionaries and the representations. -/
abbrev Params := Σ k : Type uk, Σ G : Type uG, Σ _ : Field k, Σ _ : Group G,
  Σ ι : Type uι, Σ _ : Fintype ι, Σ W : ι → Type uW, Σ _ : (∀ i, AddCommGroup (W i)),
  Σ _ : (∀ i, Module k (W i)), ∀ i, Representation k G (W i)

abbrev signature : Signature where
  Params := Params.{uk, uG, uι, uW}
  State p := p.2.2.2.2.1 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The dimension of the span of the sections `x ↦ ∑ i, c i * χ_i (x * y⁻¹)`. -/
def observe (p : Params.{uk, uG, uι, uW}) (c : p.2.2.2.2.1 → p.1) : ℕ := by
  obtain ⟨k, G, fk, gG, ι, fι, W, aW, mW, ρ⟩ := p
  exact Module.finrank k (Submodule.span k
    (Set.range fun y : G => fun x : G => ∑ i, c i * (ρ i).character (x * y⁻¹)))

def actual : Realization signature.{uk, uG, uι, uW} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{uk, uG, uι, uW} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original telescope is retained; only the dimension of the span varies. -/
abbrev arena : Arena where
  signature := signature.{uk, uG, uι, uW}
  Law R := ∀ {k : Type uk} {G : Type uG} [fk : Field k] [IsAlgClosed k] [gG : Group G]
    {ι : Type uι} [fι : Fintype ι] {W : ι → Type uW} [aW : ∀ i, AddCommGroup (W i)]
    [mW : ∀ i, Module k (W i)] [∀ i, FiniteDimensional k (W i)]
    (ρ : ∀ i, Representation k G (W i)) [∀ i, (ρ i).IsIrreducible]
    (_hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) (c : ι → k) (_hc : ∀ i, c i ≠ 0),
    R.readout () ⟨k, G, fk, gG, ι, fι, W, aW, mW, ρ⟩ c = ∑ i, Module.finrank k (W i) ^ 2

/-! A one-summand model in arbitrary universes: the trivial group acting trivially on a line
over the algebraic closure of the rationals. -/

private abbrev K0 := AlgebraicClosure ℚ
private abbrev testK := ULift.{uk} K0
private abbrev testG := PUnit.{uG + 1}
private abbrev testI := PUnit.{uι + 1}
private abbrev testW : testI.{uι} → Type uW := fun _ => ULift.{uW} K0

/-- Algebraic closedness transported along a ring isomorphism between universes. -/
private theorem isAlgClosed_of_ringEquiv {k : Type*} {k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  refine ⟨e x, ?_⟩
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

private instance testK_isAlgClosed : IsAlgClosed testK.{uk} :=
  isAlgClosed_of_ringEquiv (k := K0) ULift.ringEquiv.symm

/-- The line `ULift K0` as a space over `ULift K0` in another universe. -/
private def lineEquiv : ULift.{uW} K0 ≃ₗ[testK.{uk}] testK.{uk} where
  toFun x := ⟨x.down⟩
  invFun y := ⟨y.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem finrank_line : Module.finrank testK.{uk} (ULift.{uW} K0) = 1 :=
  lineEquiv.{uk, uW}.finrank_eq.trans (Module.finrank_self _)

private instance testW_finite (i : testI.{uι}) :
    FiniteDimensional testK.{uk} (testW.{uι, uW} i) :=
  Module.Finite.equiv lineEquiv.{uk, uW}.symm

private abbrev testρ : ∀ i : testI.{uι},
    Representation testK.{uk} testG.{uG} (testW.{uι, uW} i) :=
  fun _ => Representation.trivial _ _ _

private instance testρ_irreducible (i : testI.{uι}) :
    (testρ.{uk, uG, uι, uW} i).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one _ finrank_line

private theorem test_hne : ∀ i j : testI.{uι}, i ≠ j →
    IsEmpty ((testρ.{uk, uG, uι, uW} i).Equiv (testρ.{uk, uG, uι, uW} j)) :=
  fun i j h => absurd (Subsingleton.elim i j) h

private abbrev testParams : Params.{uk, uG, uι, uW} :=
  ⟨testK, testG, inferInstance, inferInstance, testI, inferInstance, testW, inferInstance,
    inferInstance, testρ⟩

private theorem test_sum :
    ∑ i : testI.{uι}, Module.finrank testK.{uk} (testW.{uι, uW} i) ^ 2 = 1 := by
  rw [Fintype.sum_unique]
  change Module.finrank testK.{uk} (ULift.{uW} K0) ^ 2 = 1
  rw [finrank_line, one_pow]

private theorem rejected_law : ¬ arena.{uk, uG, uι, uW}.Law rejected := by
  intro h
  have he := h (k := testK.{uk}) (G := testG.{uG}) (W := testW.{uι, uW})
    testρ test_hne (fun _ => 1) (fun _ => one_ne_zero)
  rw [test_sum] at he
  exact zero_ne_one he

private theorem observe_zero : observe testParams.{uk, uG, uι, uW} (fun _ => 0) = 0 := by
  change Module.finrank testK.{uk} (Submodule.span testK.{uk}
    (Set.range fun y : testG.{uG} => fun x : testG.{uG} =>
      ∑ i : testI.{uι}, (0 : testK.{uk}) * (testρ.{uk, uG, uι, uW} i).character (x * y⁻¹))) = 0
  have h0 : (fun y : testG.{uG} => fun x : testG.{uG} =>
      ∑ i : testI.{uι}, (0 : testK.{uk}) * (testρ.{uk, uG, uι, uW} i).character (x * y⁻¹)) =
      fun _ => (0 : testG.{uG} → testK.{uk}) := by
    funext y x
    simp
  rw [h0]
  simp

private theorem observe_one : observe testParams.{uk, uG, uι, uW} (fun _ => 1) = 1 := by
  change Module.finrank testK.{uk} (Submodule.span testK.{uk}
    (Set.range fun y : testG.{uG} => fun x : testG.{uG} =>
      ∑ i : testI.{uι}, (1 : testK.{uk}) * (testρ.{uk, uG, uι, uW} i).character (x * y⁻¹))) = 1
  have h := finrank_span_sum_character_kernel testρ.{uk, uG, uι, uW} test_hne (fun _ => 1)
    (fun _ => one_ne_zero)
  rw [test_sum] at h
  convert h using 3

private theorem dependence : ObservationalDependence signature.{uk, uG, uι, uW} actual := by
  intro i
  refine ⟨testParams, fun _ => 0, fun _ => 1, ?_⟩
  intro h
  change observe testParams (fun _ => 0) = observe testParams (fun _ => 1) at h
  rw [observe_zero, observe_one] at h
  exact zero_ne_one h

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @finrank_span_sum_character_kernel.{uk, uG, uι, uW}

def source : Registration arena.{uk, uG, uι, uW} sourceStatement.{uk, uG, uι, uW} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finrank_span_sum_character_kernel.{uk, uG, uι, uW}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finrank_span_sum_character_kernel.{uk, uG, uι, uW})
    (Realization signature.{uk, uG, uι, uW}) Unit Unit := {
  unitName :=
    .str `D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.finrank_span_sum_character_kernel
      "__information_unit"
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.source
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
    definition := none
    coordinates := #[0, 1, 5, 7, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## The operator span and the trace pairing

Scalar field, index type, spaces and their dictionaries, shared by the registrations of
`span_range_pi_eq_top` and `eq_zero_of_tracePairing`. -/

set_option linter.checkUnivs false in
/-- The scalar field, index type, spaces and dictionaries. -/
abbrev EndParams := Σ k : Type uk, Σ _ : Field k, Σ ι : Type uι, Σ W : ι → Type uW,
  Σ _ : (∀ i, AddCommGroup (W i)), ∀ i, Module k (W i)

/-- The product of the endomorphism algebras of the test line has `1 ≠ 0`. -/
private theorem test_one_ne_zero :
    (1 : ∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : (∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i)) =>
    (f PUnit.unit (⟨1⟩ : ULift.{uW} K0)).down) h
  simp at h1

private theorem test_bot_ne_top :
    (⊥ : Submodule testK.{uk} (∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i))) ≠ ⊤ := by
  intro h
  have hm : (1 : ∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i)) ∈
      (⊤ : Submodule testK.{uk} (∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i))) :=
    Submodule.mem_top
  rw [← h] at hm
  have h0 : (1 : ∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i)) = 0 :=
    (Submodule.mem_bot testK.{uk}).mp hm
  exact test_one_ne_zero.{uk, uι, uW} h0

private abbrev testEndParams : EndParams.{uk, uι, uW} :=
  ⟨testK, inferInstance, testI, testW, inferInstance, inferInstance⟩

/-! ### `span_range_pi_eq_top`: the span of a set of operator families -/
namespace Span

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := EndParams.{uk, uι, uW}
  State p := letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    Set (∀ i, Module.End p.1 (p.2.2.2.1 i))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    Submodule p.1 (∀ i, Module.End p.1 (p.2.2.2.1 i))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uk, uι, uW} :=
  realize signature (fun _ p s => letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    Submodule.span p.1 s) (fun e => nomatch e)

def rejected : Realization signature.{uk, uι, uW} :=
  realize signature (fun _ p _ => letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    (⊥ : Submodule p.1 (∀ i, Module.End p.1 (p.2.2.2.1 i)))) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- The complete original telescope is retained; only the span of the operator families varies. -/
abbrev arena : Arena where
  signature := signature.{uk, uι, uW}
  Law R := ∀ {k : Type uk} {G : Type uG} [fk : Field k] [IsAlgClosed k] [Group G]
    {ι : Type uι} [Fintype ι] {W : ι → Type uW} [aW : ∀ i, AddCommGroup (W i)]
    [mW : ∀ i, Module k (W i)] [∀ i, FiniteDimensional k (W i)]
    (ρ : ∀ i, Representation k G (W i)) [∀ i, (ρ i).IsIrreducible]
    (_hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))),
    R.readout () ⟨k, fk, ι, W, aW, mW⟩
      (Set.range fun g : G => (fun i => ρ i g : ∀ i, Module.End k (W i))) = ⊤

/-- On the trivial representation of the trivial group on a line the zero submodule is not
everything. -/
theorem rejected_law : ¬ arena.{uk, uG, uι, uW}.Law rejected := by
  intro h
  exact test_bot_ne_top (h (k := testK.{uk}) (G := testG.{uG}) (W := testW.{uι, uW}) testρ test_hne)

theorem dependence : ObservationalDependence signature.{uk, uι, uW} actual := by
  intro i
  refine ⟨testEndParams, ∅, Set.univ, fun h => test_bot_ne_top ?_⟩
  have h' : Submodule.span testK.{uk}
      (∅ : Set (∀ i : testI.{uι}, Module.End testK.{uk} (testW.{uι, uW} i))) =
      Submodule.span testK.{uk} Set.univ := h
  rwa [Submodule.span_empty, Submodule.span_univ] at h'

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @span_range_pi_eq_top.{uk, uG, uι, uW}

def source : Registration arena.{uk, uG, uι, uW} sourceStatement.{uk, uG, uι, uW} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@span_range_pi_eq_top.{uk, uG, uι, uW}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

end Span

def span_range_pi_eq_top_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@span_range_pi_eq_top.{uk, uG, uι, uW})
    (Realization Span.signature.{uk, uι, uW}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.span_range_pi_eq_top_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.Span.source
  realizationSource := none
  generated := false
  arena := .source ⟨Span.arena⟩
  objectArena := .source ⟨Span.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Span.arena ⟨Span.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Span.signature (fun _ p s => letI := p.2.1; letI := p.2.2.2.2.1;
    letI := p.2.2.2.2.2; Submodule.span p.1 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
    definition := none
    coordinates := #[0, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ### `eq_zero_of_tracePairing`: the operator family paired against every family -/
namespace Pairing

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := EndParams.{uk, uι, uW}
  State p := letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    ∀ i, Module.End p.1 (p.2.2.2.1 i)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    ∀ i, Module.End p.1 (p.2.2.2.1 i)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uk, uι, uW} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature.{uk, uι, uW} :=
  realize signature (fun _ p _ => letI := p.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2
    (1 : ∀ i, Module.End p.1 (p.2.2.2.1 i))) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- The complete original telescope is retained; only the family in the conclusion varies. -/
abbrev arena : Arena where
  signature := signature.{uk, uι, uW}
  Law R := ∀ {k : Type uk} [fk : Field k] {ι : Type uι} [Fintype ι] {W : ι → Type uW}
    [aW : ∀ i, AddCommGroup (W i)] [mW : ∀ i, Module k (W i)] [∀ i, FiniteDimensional k (W i)]
    (c : ι → k) (_hc : ∀ i, c i ≠ 0) (A : ∀ i, Module.End k (W i))
    (_h : ∀ B, tracePairing c B A = 0), R.readout () ⟨k, fk, ι, W, aW, mW⟩ A = 0

/-- The zero family pairs to zero with every family, but the identity family is not zero. -/
theorem rejected_law : ¬ arena.{uk, uι, uW}.Law rejected := by
  intro h
  exact test_one_ne_zero (h (k := testK.{uk}) (ι := testI.{uι}) (W := testW.{uι, uW})
    (fun _ => 1) (fun _ => one_ne_zero) 0 (fun B => map_zero _))

theorem dependence : ObservationalDependence signature.{uk, uι, uW} actual := by
  intro i
  exact ⟨testEndParams, 1, 0, test_one_ne_zero⟩

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @eq_zero_of_tracePairing.{uk, uι, uW}

def source : Registration arena.{uk, uι, uW} sourceStatement.{uk, uι, uW} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_zero_of_tracePairing.{uk, uι, uW}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

end Pairing

def eq_zero_of_tracePairing_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eq_zero_of_tracePairing.{uk, uι, uW})
    (Realization Pairing.signature.{uk, uι, uW}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.eq_zero_of_tracePairing_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank.Pairing.source
  realizationSource := none
  generated := false
  arena := .source ⟨Pairing.arena⟩
  objectArena := .source ⟨Pairing.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Pairing.arena ⟨Pairing.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Pairing.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## The hypotheses cannot be dropped -/

/-- Irreducibility cannot be dropped: the trivial group acting trivially on the plane `K × K`
has character kernel of rank at most one, while the formula would give four. -/
private theorem reducible_plane_rank_le_one (K : Type*) [Field K] (c : K) :
    Module.finrank K (Submodule.span K (Set.range fun y : Unit => fun x : Unit =>
      c * (Representation.trivial K Unit (K × K)).character (x * y⁻¹))) ≤ 1 ∧
    Module.finrank K (K × K) ^ 2 = 4 := by
  refine ⟨?_, ?_⟩
  · exact (finrank_range_le_card _).trans (by simp)
  · simp [Module.finrank_prod]

/-- Pairwise inequivalence cannot be dropped: two copies of the trivial representation of the
trivial group on the irreducible line `K`, with weights `1` and `-1`, have zero character kernel,
while the formula would give two. -/
private theorem duplicate_trivial_zero_kernel (K : Type*) [Field K] :
    (Representation.trivial K Unit K).IsIrreducible ∧
    Module.finrank K (Submodule.span K (Set.range fun y : Unit => fun x : Unit =>
      ∑ i : Bool, (if i then (1 : K) else -1) *
        (Representation.trivial K Unit K).character (x * y⁻¹))) = 0 ∧
    ∑ _i : Bool, Module.finrank K K ^ 2 = 2 := by
  refine ⟨_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one _
    (Module.finrank_self K), ?_, ?_⟩
  · have h0 : (fun y : Unit => fun x : Unit => ∑ i : Bool, (if i then (1 : K) else -1) *
        (Representation.trivial K Unit K).character (x * y⁻¹)) =
        fun _ => (0 : Unit → K) := by
      funext y x
      simp
    rw [h0]
    simp
  · simp

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
