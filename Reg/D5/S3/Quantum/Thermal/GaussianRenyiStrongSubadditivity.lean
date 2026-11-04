import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

/-! Source-bound registration for bosonic Gaussian Rényi strong subadditivity. -/

namespace Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity

open _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
open _root_.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Σ _ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ, Finset (Fin n))
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p α => gaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)))
    (reducedCovariance (symplecticForm (Sigma.fst p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance V → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α ≤ 2 → α ≠ 1 →
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B))
              (reducedCovariance (symplecticForm n) (A ∪ B)) +
            gaussianRenyiEntropy α (reducedCovariance V (B ∪ C))
              (reducedCovariance (symplecticForm n) (B ∪ C)) ≥
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B ∪ C))
              (reducedCovariance (symplecticForm n) (A ∪ B ∪ C)) +
            R.readout () ⟨n, V, B⟩ α

lemma empty_entropy {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (α : ℝ) :
    gaussianRenyiEntropy α (reducedCovariance V ∅)
      (reducedCovariance (symplecticForm n) ∅) = 0 := by
  have : IsEmpty {p : Fin n × Fin 2 // p.1 ∈ (∅ : Finset (Fin n))} :=
    ⟨fun p => by simpa using p.property⟩
  unfold gaussianRenyiEntropy
  split_ifs <;> simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hV : physicalCovariance (n := 0) 0 := by
    unfold physicalCovariance
      _root_.D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
    constructor
    · ext i; exact Fin.elim0 i
    · convert (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0) (Fin 0) ℂ).PosSemidef) using 1
      ext i; exact Fin.elim0 i
  have hh := h 0 0 hV ∅ ∅ ∅ (by simp) (by simp) (by simp)
    2 (by norm_num) (by norm_num) (by norm_num)
  let E := gaussianRenyiEntropy 2 (reducedCovariance (n := 0) 0 ∅)
    (reducedCovariance (symplecticForm 0) ∅)
  change E + 1 ≤ E + E at hh
  have he : E = 0 := empty_entropy 0 2
  rw [he] at hh
  norm_num at hh

lemma zero_entropy {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : Matrix ι ι ℝ) (α : ℝ) :
    gaussianRenyiEntropy α 0 Ω =
      (1 / 2 : ℝ) * ((Fintype.card ι : ℝ) * renyiFunction α 0) := by
  have hmap : (0 : Matrix ι ι ℝ).map Complex.ofReal = 0 := by ext; simp
  have hz : symplecticOperator 0 Ω = 0 := by simp [symplecticOperator, hmap]
  have hH : (symplecticOperator 0 Ω).IsHermitian := hz ▸ Matrix.isHermitian_zero
  have he : hH.eigenvalues = 0 := hH.eigenvalues_eq_zero_iff.mpr hz
  rw [gaussianRenyiEntropy, dite_eq_left hH]
  simp [he]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, Finset.univ⟩, 1, 3, ?_⟩
  change gaussianRenyiEntropy 1 (reducedCovariance 0 Finset.univ) _ ≠
    gaussianRenyiEntropy 3 (reducedCovariance 0 Finset.univ) _
  have hr : reducedCovariance (n := 1) 0 Finset.univ = 0 := rfl
  rw [hr, zero_entropy, zero_entropy]
  have hc : Fintype.card {p : Fin 1 × Fin 2 //
      p.1 ∈ (Finset.univ : Finset (Fin 1))} = 2 := by decide
  rw [hc]
  norm_num [renyiFunction, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.unit
  realizationName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p α => gaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)))
    (reducedCovariance (symplecticForm (Sigma.fst p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
    definition := some {
      owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
      name := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.claim
      path := #[] }
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

namespace ReducedCard

#print _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reduced_card

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    ℕ (fun n => Finset (Fin n)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature
    (fun _ n X => Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X})
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ n X => Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (X : Finset (Fin n)),
    R.readout () n X = 2 * X.card

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 ∅
  norm_num [rejected, realize] at hh

lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, ∅, {0}, ?_⟩
  change Fintype.card {p : Fin 1 × Fin 2 // p.1 ∈ (∅ : Finset (Fin 1))} ≠
    Fintype.card {p : Fin 1 × Fin 2 // p.1 ∈ ({0} : Finset (Fin 1))}
  decide

def source_registration : Registration arena (type_of% @reduced_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reduced_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reduced_card) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.ReducedCard.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.ReducedCard.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n X => Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X})
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ReducedCard

namespace ShiftedPosDef

open scoped ComplexOrder

#print _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.shifted_posDef

universe u

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ ι : Type u, Σ _ : Fintype ι, DecidableEq ι)
    (fun p => Matrix (Sigma.fst p) (Sigma.fst p) ℝ)
    (fun p => Matrix (Sigma.fst p) (Sigma.fst p) ℂ)

def actual : Realization signature.{u} :=
  realize signature (fun _ _ V => V.map Complex.ofReal) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (_hV : physicalOn V ω)
    (_hpos : (V.map Complex.ofReal).PosDef) {x : ℝ}
    (_hx0 : 0 ≤ x) (_hx1 : x < 1),
    ((R.readout () ⟨ι, inferInstance, inferInstance⟩ V) +
      (x : ℂ) • (Complex.I • ω.map Complex.ofReal)).PosDef

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let ι := ULift.{u} Unit
  have hm : (1 : Matrix ι ι ℝ).map Complex.ofReal = 1 :=
    Matrix.map_one Complex.ofReal rfl rfl
  have hz : (0 : Matrix ι ι ℝ).map Complex.ofReal = 0 := by ext; simp
  have hV : physicalOn (1 : Matrix ι ι ℝ) 0 := by
    exact ⟨Matrix.isSymm_one, by simpa [hm, hz] using
      (Matrix.PosSemidef.one : (1 : Matrix ι ι ℂ).PosSemidef)⟩
  have hp : ((1 : Matrix ι ι ℝ).map Complex.ofReal).PosDef := by
    simpa [hm] using (Matrix.PosDef.one : (1 : Matrix ι ι ℂ).PosDef)
  have hh := @h ι inferInstance inferInstance 1 0 hV hp 0 (by norm_num) (by norm_num)
  have hh' : (0 : Matrix ι ι ℂ).PosDef := by simpa [rejected, realize] using hh
  have hdet := hh'.det_pos.1
  norm_num at hdet

lemma dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} Unit
  refine ⟨⟨ι, inferInstance, inferInstance⟩, 0, 1, ?_⟩
  intro h
  have hh := congrArg (fun M : Matrix ι ι ℂ => M ⟨()⟩ ⟨()⟩) h
  simp only [actual, realize, Matrix.map_apply] at hh
  exact zero_ne_one hh

def source_registration : Registration arena.{u} (type_of% @shifted_posDef.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shifted_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shifted_posDef) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.ShiftedPosDef.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.ShiftedPosDef.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ V => V.map Complex.ofReal)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ShiftedPosDef

namespace LogKoteljanskii

open scoped ComplexOrder

universe u

#print _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.log_koteljanskii

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ ι : Type u, Σ _ : DecidableEq ι, Matrix ι ι ℂ)
    (fun p => Finset (Sigma.fst p)) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p B =>
    letI := Sigma.fst (Sigma.snd p)
    Real.log ((Sigma.snd (Sigma.snd p)).submatrix (Subtype.val : ↥B → Sigma.fst p)
      Subtype.val).det.re) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (_hH : H.PosDef) (A B C : Finset ι),
    Disjoint A B → Disjoint A C → Disjoint B C →
    Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
        R.readout () ⟨ι, inferInstance, H⟩ B ≤
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let ι := ULift.{u} Unit
  have hblock (Z : Finset ι) :
      (1 : Matrix ι ι ℂ).submatrix (Subtype.val : ↥Z → ι) Subtype.val = 1 :=
    Matrix.submatrix_one _ Subtype.val_injective
  have hh := @h ι inferInstance 1 Matrix.PosDef.one ∅ ∅ ∅
    (by simp) (by simp) (by simp)
  norm_num [rejected, realize, hblock] at hh

lemma dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} Unit
  refine ⟨⟨ι, inferInstance, 2⟩, ∅, {⟨()⟩}, ?_⟩
  change Real.log ((2 : Matrix ι ι ℂ).submatrix
    (Subtype.val : ↥(∅ : Finset ι) → ι) Subtype.val).det.re ≠
    Real.log ((2 : Matrix ι ι ℂ).submatrix
      (Subtype.val : ↥({⟨()⟩} : Finset ι) → ι) Subtype.val).det.re
  simpa [Matrix.det_unique, Matrix.submatrix_apply, Matrix.ofNat_apply]
    using (ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

def source_registration : Registration arena.{u} (type_of% @log_koteljanskii.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_koteljanskii, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@log_koteljanskii) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.LogKoteljanskii.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.LogKoteljanskii.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p B =>
    letI := Sigma.fst (Sigma.snd p)
    Real.log ((Sigma.snd (Sigma.snd p)).submatrix (Subtype.val : ↥B → Sigma.fst p)
      Subtype.val).det.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end LogKoteljanskii

end
end Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
