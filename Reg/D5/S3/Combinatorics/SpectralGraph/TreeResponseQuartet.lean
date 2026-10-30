import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
import Mathlib.Combinatorics.SimpleGraph.Star

/-! The two source families observe full absolute block determinants. -/

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet

open _root_.D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix

universe u

/-- Only the carrier and common fibre dimension parameterize the observation. -/
abbrev InverseParams := Σ _ : Type u, ℕ

abbrev inverseSignature : Signature where
  Params := InverseParams.{u}
  State p := Matrix (p.1 × Fin p.2) (p.1 × Fin p.2) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → p.1 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def inverseActual : Realization inverseSignature.{u} :=
  realize inverseSignature (fun _ _ M => weight M) (fun e => nomatch e)

open Classical in
def inverseRejected : Realization inverseSignature.{u} :=
  realize inverseSignature (fun _ _ _ x y => if x = y then 0 else 1)
    (fun e => nomatch e)

abbrev inverseArena : Arena where
  signature := inverseSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (G : SimpleGraph V) (Q : Matrix (V × Fin r) (V × Fin r) ℝ),
    G.IsTree → Q.PosDef → Supported G Q → ∀ a b c e,
      Quartet (R.readout () ⟨V, r⟩ Q⁻¹) a b c e

abbrev inverseSource := type_of% (@inverse_tree_quartet.{u})

theorem inverse_source_bridge : inverseSource.{u} ↔ inverseArena.{u}.Law inverseActual.{u} := Iff.rfl

theorem inverse_actual_positive : inverseArena.{u}.Law inverseActual.{u} :=
  @inverse_tree_quartet.{u}

theorem inverse_rejected_law : ¬ inverseArena.{u}.Law inverseRejected.{u} := by
  classical
  intro h
  let V := ULift.{u} Bool
  let a : V := ⟨false⟩
  let b : V := ⟨true⟩
  have hs : Supported (SimpleGraph.starGraph a) (1 : Matrix (V × Fin 1) (V × Fin 1) ℝ) := by
    intro x y hxy _
    ext i j
    have hn : (x, i) ≠ (y, j) := fun he => hxy (congrArg Prod.fst he)
    simp [block, Matrix.one_apply, hn]
  have hh := h (SimpleGraph.starGraph a) (1 : Matrix (V × Fin 1) (V × Fin 1) ℝ)
    (SimpleGraph.isTree_starGraph a) Matrix.PosDef.one hs a a b b
  have hab : a ≠ b := by
    intro he
    have hb : false = true := congrArg ULift.down he
    cases hb
  norm_num [inverseRejected, realize, Quartet, RepeatedMin, hab] at hh

def inverseFamily : Registration inverseArena.{u} inverseSource.{u} where
  actual := inverseActual
  bridge := inverse_source_bridge
  variation := ⟨inverse_actual_positive, inverseRejected, inverse_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨inverseRejected, ?_, rfl, inverse_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let p : InverseParams.{u} := ⟨ULift.{u} (Fin 4), 1⟩
    refine ⟨p, (1 : Matrix (ULift.{u} (Fin 4) × Fin 1) (ULift.{u} (Fin 4) × Fin 1) ℝ),
      (2 : ℝ) • (1 : Matrix (ULift.{u} (Fin 4) × Fin 1)
        (ULift.{u} (Fin 4) × Fin 1) ℝ), ?_⟩
    intro he
    have hh := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
    norm_num [inverseActual, realize, weight, block, p, Matrix.det_fin_one,
      Matrix.submatrix_apply, Matrix.one_apply, Function.Embedding.coeFn_mk] at hh

/-- The response observation retains the entire retained set. -/
abbrev ResponseParams := Σ V : Type u, Σ _ : ℕ, Set V

abbrev responseSignature : Signature where
  Params := ResponseParams.{u}
  State p := Matrix (p.2.2 × Fin p.2.1) (p.2.2 × Fin p.2.1) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2 → p.2.2 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def responseActual : Realization responseSignature.{u} :=
  realize responseSignature (fun _ _ M => weight M) (fun e => nomatch e)

def responseRejected : Realization responseSignature.{u} :=
  realize responseSignature (fun _ _ M x y => |weight M x y - weight M x x|)
    (fun e => nomatch e)

abbrev responseArena : Arena where
  signature := responseSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (T : SimpleGraph V) (H : Matrix (V × Fin r) (V × Fin r) ℝ),
    T.IsTree → H.IsSymm → Supported T H → ∀ (z : ℝ)
    (B : Set V) [DecidablePred (· ∈ B)],
    (cut (H - z • 1) Bᶜ Bᶜ).PosDef → ∀ P : Fin 4 ↪ B,
      Quartet (R.readout () ⟨V, r, B⟩ (response (H - z • 1) B))
        (P 0) (P 1) (P 2) (P 3)

abbrev responseSource := type_of% (@complete263_2.{u})

theorem response_source_bridge : responseSource.{u} ↔ responseArena.{u}.Law responseActual.{u} := Iff.rfl

theorem response_actual_positive : responseArena.{u}.Law responseActual.{u} := @complete263_2.{u}

private def sampleDiagonal (x : ULift.{u} (Fin 4)) : ℝ :=
  ![-1, -3, -2, -4] x.down

private def sampleMatrix : Matrix (ULift.{u} (Fin 4) × Fin 1) (ULift.{u} (Fin 4) × Fin 1) ℝ :=
  diagonal (fun p => sampleDiagonal p.1)

private abbrev samplePorts : Fin 4 ↪ (Set.univ : Set (ULift.{u} (Fin 4))) where
  toFun i := ⟨ULift.up i, Set.mem_univ _⟩
  inj' := by intro i j he; exact congrArg (fun p => p.val.down) he

theorem response_rejected_law : ¬ responseArena.{u}.Law responseRejected.{u} := by
  classical
  intro h
  let V := ULift.{u} (Fin 4)
  have hs : Supported (SimpleGraph.starGraph (ULift.up 0 : V)) sampleMatrix.{u} := by
    intro x y hxy _
    ext i j
    have hn : (x, i) ≠ (y, j) := fun he => hxy (congrArg Prod.fst he)
    simp [sampleMatrix, block, diagonal_apply, hn]
  have hK : (cut (sampleMatrix.{u} - (0 : ℝ) • 1) Set.univᶜ Set.univᶜ).PosDef := by
    simp only [zero_smul, sub_zero]
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨(isHermitian_diagonal_iff.mpr (fun _ => IsSelfAdjoint.all _)).submatrix _, ?_⟩
    intro x hx
    exact (hx (funext fun y => (y.1.property (Set.mem_univ _)).elim)).elim
  have hh := h (SimpleGraph.starGraph (ULift.up 0 : V)) sampleMatrix
    (SimpleGraph.isTree_starGraph _) (by exact (isHermitian_diagonal_iff.mpr
      (fun _ => IsSelfAdjoint.all _)).isSymm) hs 0 Set.univ hK samplePorts
  have hp (i : Fin 4) : samplePorts.{u} i =
      (⟨ULift.up i, Set.mem_univ _⟩ : (Set.univ : Set V)) := rfl
  simp only [hp] at hh
  norm_num [responseRejected, realize, Quartet, RepeatedMin, weight, block, response,
    cut, sampleMatrix, sampleDiagonal, samplePorts, Matrix.det_fin_one, diagonal_apply,
    Matrix.mul_apply, Matrix.submatrix_apply, Function.Embedding.coeFn_mk, ULift.ext_iff] at hh

def responseFamily : Registration responseArena.{u} responseSource.{u} where
  actual := responseActual
  bridge := response_source_bridge
  variation := ⟨response_actual_positive, responseRejected, response_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨responseRejected, ?_, rfl, response_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let p : ResponseParams.{u} := ⟨ULift.{u} (Fin 4), 1, Set.univ⟩
    let x : (Set.univ : Set (ULift.{u} (Fin 4))) := ⟨ULift.up 0, Set.mem_univ _⟩
    refine ⟨p, (1 : Matrix (↥(Set.univ : Set (ULift.{u} (Fin 4))) × Fin 1)
      (↥(Set.univ : Set (ULift.{u} (Fin 4))) × Fin 1) ℝ),
      (2 : ℝ) • (1 : Matrix (↥(Set.univ : Set (ULift.{u} (Fin 4))) × Fin 1)
      (↥(Set.univ : Set (ULift.{u} (Fin 4))) × Fin 1) ℝ), ?_⟩
    intro he
    have hh := congrFun (congrFun he x) x
    norm_num [responseActual, realize, weight, block, p, x, Matrix.det_fin_one,
      Matrix.submatrix_apply, Matrix.one_apply, Function.Embedding.coeFn_mk] at hh

noncomputable def inverseRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@inverse_tree_quartet.{u}) (Realization inverseSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet.inverse_tree_quartet.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet.inverseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena.{u}⟩
  objectArena := .source ⟨inverseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverseFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize inverseSignature.{u} (fun _ _ M => weight M) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def responseRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@complete263_2.{u}) (Realization responseSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet.complete263_2.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet.responseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨responseArena.{u}⟩
  objectArena := .source ⟨responseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source responseArena ⟨responseFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize responseSignature.{u} (fun _ _ M => weight M) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
    definition := none
    coordinates := #[0, 3, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
