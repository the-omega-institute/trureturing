import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Reg.Support.DependentFamily
import D5.S3.Quantum.Schatten.CompoundMatrices

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open LeanInformationAudit
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation

universe u

abbrev signature : Signature where
  Params := Type u
  State p := CStarMatrix p p ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize.{u + 1, u, 0, u, 0} signature
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)

noncomputable def negativeIdentity (p : Type u) : Matrix p p ℂ := by
  classical
  exact fun i j => if i = j then -1 else 0

noncomputable def rejected : Realization signature.{u} :=
  realize.{u + 1, u, 0, u, 0} signature
    (fun _ (p : Type u) _ => negativeIdentity p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (rho : DensityState n), (R.readout () n rho.1).PosSemidef

theorem actual_law : arena.{u}.Law actual := by
  intro n _ _ rho
  exact density_posSemidef rho

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  let rho : DensityState n :=
    ⟨1, by
      constructor
      · exact zero_le_one
      · change Matrix.trace (1 : Matrix n n ℂ) = 1
        rw [Matrix.trace_one]
        norm_num
    ⟩
  have hp := h rho
  have hq := hp.2 (Finsupp.single (ULift.up ()) (1 : ℂ))
  norm_num [rejected, negativeIdentity, realize,
    dotProduct, Matrix.mulVec, Finsupp.sum_single_index] at hq

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  let n : signature.{u}.Params := ULift.{u} Unit
  refine ⟨n, 0, 1, ?_⟩
  intro h
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up ()) (ULift.up ())) h
  change (0 : Matrix n n ℂ) (ULift.up ()) (ULift.up ()) =
    (1 : Matrix n n ℂ) (ULift.up ()) (ULift.up ()) at he
  simpa using he

noncomputable def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef.{u_1})
    (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
      (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "PartialTraceMutualInformation") "density_posSemidef") "Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation/Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u_1}⟩,
  objectArena := .source ⟨arena.{u_1}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨registration.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.PartialTraceMutualInformation, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration_1

namespace EntropySpectral
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open Matrix
open scoped BigOperators
noncomputable section

abbrev signature : Signature where
  Params := Σ n : Type u, Σ _ : Fintype n, DecidableEq n
  State p := @DensityState p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p rho => @vonNeumannEntropy p.1 p.2.1 p.2.2 rho)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p rho => @vonNeumannEntropy p.1 p.2.1 p.2.2 rho + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (rho : DensityState n),
    R.readout () ⟨n, inferInstance, inferInstance⟩ rho =
      spectralEntropy (density_posSemidef rho).isHermitian

theorem bridge : (type_of% @entropy_eq_spectral.{u}) ↔ arena.{u}.Law actual := Iff.rfl

def singletonDensity : DensityState (ULift.{u} Unit) :=
  ⟨1, zero_le_one, by
    change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
    simp [Matrix.trace]⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance singletonDensity
  change vonNeumannEntropy singletonDensity + 1 =
    spectralEntropy (density_posSemidef singletonDensity).isHermitian at he
  rw [entropy_eq_spectral] at he
  linarith

def diagonalDensity {n : Type u} [Fintype n] [DecidableEq n] (f : n → ℝ)
    (hf : ∀ i, 0 ≤ f i) (ht : ∑ i, f i = 1) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal (fun i => (f i : ℂ))), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr (hf i))).nonneg)
  · change (Matrix.diagonal (fun i => (f i : ℂ))).trace = 1
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, ht, Complex.ofReal_one]

theorem diagonalEntropy {n : Type u} [Fintype n] [DecidableEq n] (f : n → ℝ)
    (hf : ∀ i, 0 ≤ f i) (ht : ∑ i, f i = 1) :
    vonNeumannEntropy (diagonalDensity f hf ht) = ∑ i, Real.negMulLog (f i) := by
  rw [entropy_eq_spectral]
  let rho := diagonalDensity f hf ht
  have hh := (density_posSemidef rho).isHermitian
  have hm : CStarMatrix.ofMatrix.symm rho.1 = Matrix.diagonal (fun i => (f i : ℂ)) := rfl
  obtain ⟨s, hs⟩ := hh.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := 1) (f := f) (by simp) (by simpa using hm)
  unfold spectralEntropy
  rw [← s.sum_comp]
  change (∑ i, Real.negMulLog ((hh.eigenvalues ∘ s) i)) = _
  rw [hs]

def pureProfile (i : ULift.{u} (Fin 2)) : ℝ := if i.down = 0 then 1 else 0

theorem pureProfile_nonneg : ∀ i : ULift.{u} (Fin 2), 0 ≤ pureProfile i := by
  intro i
  unfold pureProfile
  split_ifs <;> norm_num

theorem sum_lift (f : ULift.{u} (Fin 2) → ℝ) :
    ∑ i, f i = f ⟨0⟩ + f ⟨1⟩ := by
  rw [← (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2).symm.sum_comp f]
  exact Fin.sum_univ_two _

theorem pureProfile_mass : ∑ i : ULift.{u} (Fin 2), pureProfile i = 1 := by
  rw [sum_lift]
  norm_num [pureProfile]

theorem half_mass : ∑ _i : ULift.{u} (Fin 2), (1/2 : ℝ) = 1 := by norm_num

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : signature.Params := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩
  refine ⟨p, diagonalDensity pureProfile pureProfile_nonneg pureProfile_mass,
    diagonalDensity (fun _ => (1/2 : ℝ)) (by intros; norm_num) half_mass, ?_⟩
  change vonNeumannEntropy (diagonalDensity pureProfile pureProfile_nonneg pureProfile_mass) ≠
    vonNeumannEntropy (diagonalDensity (fun _ : ULift.{u} (Fin 2) => (1/2 : ℝ))
      (by intros; norm_num) half_mass)
  rw [diagonalEntropy, diagonalEntropy]
  simp only [pureProfile, sum_lift]
  norm_num only [Fin.zero_eta, Fin.isValue, ite_true, Fin.reduceEq, ite_false,
    Real.negMulLog_one, Real.negMulLog_zero, add_zero]
  have hp := Real.binEntropy_pos (p := (1/2 : ℝ)) (by norm_num) (by norm_num)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at hp
  norm_num at hp
  linarith

def source_registration : Registration arena.{u} (type_of% @entropy_eq_spectral.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @entropy_eq_spectral.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entropy_eq_spectral.{u}) (Realization signature.{u}) (type_of% @DensityState.{u}) Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral.unit
  realizationName := `Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p rho => @vonNeumannEntropy p.1 p.2.1 p.2.2 rho)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.PartialTraceMutualInformation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end EntropySpectral

end Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation
