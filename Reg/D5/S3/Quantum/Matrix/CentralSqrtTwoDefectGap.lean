import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

universe u
noncomputable section
open Finset Matrix
open scoped BigOperators
open _root_.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def oneReadout : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

private def sourceFamily (law : Realization signature → Prop) (statement : Prop)
    (bridge : statement ↔ law actual) (good : law actual)
    (bad : Realization signature) (hbad : ¬ law bad) :
    Registration ⟨signature, law⟩ statement where
  actual := actual
  bridge := bridge
  variation := ⟨good, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actual bad hbad
  dependence := dependence

namespace ScalarGap
abbrev law (R : Realization signature) : Prop :=
  ∀ {c K lam mu x y z : ℝ}, 0 < c → 0 < K →
    (lam - mu) * z = c * x * y → 1 ≤ K * x ^ 2 → 1 ≤ K * y ^ 2 → |z| ≤ 1 →
      c / K ≤ R.readout () () |lam - mu|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have hh := @h 1 1 1 0 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at hh

def family : Registration ⟨signature, law⟩ (type_of% @rank_one_gap_from_identity) :=
  sourceFamily law _ Iff.rfl (@rank_one_gap_from_identity) zeroReadout bad
end ScalarGap

namespace CrossIdentity
abbrev law (R : Realization signature) : Prop :=
  ∀ {d : Type u} [Fintype d] [DecidableEq d] {A B : Matrix d d ℝ} {q : d} {c : ℝ},
    A.IsSymm → B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1) →
    ∀ (u v : d → ℝ) (lam mu : ℝ), A *ᵥ u = lam • u → B *ᵥ v = mu • v →
    R.readout () () ((mu - lam) * (u ⬝ᵥ v)) = c * u q * v q
private theorem bad : ¬ law oneReadout := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance 0 0 ⟨()⟩ 0 (by simp) (by simp)
    0 0 0 0 (by simp) (by simp)
  norm_num [oneReadout, realize] at hh

def family : Registration ⟨signature, law⟩ (type_of% @rank_one_cross_identity.{u}) :=
  sourceFamily law _ Iff.rfl (@rank_one_cross_identity.{u}) oneReadout bad
end CrossIdentity

namespace MatrixGap
abbrev law (R : Realization signature) : Prop :=
  ∀ {d : Type u} [Fintype d] [DecidableEq d] {A B : Matrix d d ℝ} {q : d} {c K : ℝ},
    0 < c → 0 < K → A.IsSymm →
    B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1) →
    ∀ (u v : d → ℝ) (lam mu : ℝ), A *ᵥ u = lam • u → B *ᵥ v = mu • v →
    1 ≤ K * (u q) ^ 2 → 1 ≤ K * (v q) ^ 2 → |u ⬝ᵥ v| ≤ 1 →
    c / K ≤ R.readout () () |lam - mu|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance 0 1 ⟨()⟩ 1 1 (by norm_num) (by norm_num)
    (by simp) (by ext i j; rcases i with ⟨⟨⟩⟩; rcases j with ⟨⟨⟩⟩; simp [Matrix.vecMulVec])
    1 1 0 1 (by simp) (by simp) (by norm_num) (by norm_num) (by simp [dotProduct])
  norm_num [zeroReadout, realize] at hh

def family : Registration ⟨signature, law⟩ (type_of% @rank_one_gap_of_matrices.{u}) :=
  sourceFamily law _ Iff.rfl (@rank_one_gap_of_matrices.{u}) zeroReadout bad
end MatrixGap

namespace RecurrenceEndpoint
abbrev law (R : Realization signature) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t b : ℝ) (y : ℕ → ℝ), y 0 = 0 →
    (∀ j, j + 2 ≤ n + 1 → y (j + 2) = t * y (j + 1) - y j) →
    y (n + 1) = b * y n →
    R.readout () () (∑ j ∈ Finset.range n, y (j + 1) ^ 2) ≤
      (1 + |b|) ^ 2 * (n : ℝ) ^ 3 * y n ^ 2
private theorem bad : ¬ law oneReadout := by
  intro h
  have hh := h 1 (by omega) 0 0 0 (by simp) (by simp) (by simp)
  norm_num [oneReadout, realize] at hh

def family : Registration ⟨signature, law⟩ (type_of% @recurrence_endpoint_observability) :=
  sourceFamily law _ Iff.rfl (@recurrence_endpoint_observability) oneReadout bad
end RecurrenceEndpoint

namespace SectorEndpoint
abbrev law (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (b t : ℝ) (v : Fin (n + 1) → ℝ),
    sectorMatrix n b *ᵥ v = t • v →
    R.readout () () (∑ i, v i ^ 2) ≤
      (1 + |b|) ^ 2 * (n + 1 : ℝ) ^ 3 * v (Fin.last n) ^ 2
private theorem bad : ¬ law oneReadout := by
  intro h
  have hh := h 0 0 0 0 (by simp)
  norm_num [oneReadout, realize] at hh

def family : Registration ⟨signature, law⟩ (type_of% @sector_endpoint_observability) :=
  sourceFamily law _ Iff.rfl (@sector_endpoint_observability) oneReadout bad
end SectorEndpoint

namespace SectorCrossGap
abbrev law (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (u v : Fin (n + 1) → ℝ) (lam mu : ℝ),
    sectorMatrix n (-Real.sqrt 2) *ᵥ u = lam • u →
    sectorMatrix n (Real.sqrt 2) *ᵥ v = mu • v →
    (∑ i, u i ^ 2) = 1 → (∑ i, v i ^ 2) = 1 →
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤
      R.readout () () |lam - mu|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have he (c : ℝ) : sectorMatrix 0 c *ᵥ (1 : Fin 1 → ℝ) = c • (1 : Fin 1 → ℝ) := by
    ext i
    fin_cases i
    simp [sectorMatrix, _root_.D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
      _root_.D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, Matrix.mulVec, dotProduct]
  have hh := h 0 1 1 (-Real.sqrt 2) (Real.sqrt 2) (he _) (he _)
    (by simp) (by simp)
  have hp : 0 < 2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2 := by positivity
  norm_num [zeroReadout, realize] at hh
  linarith

def family : Registration ⟨signature, law⟩ (type_of% @sector_inverse_cubic_gap) :=
  sourceFamily law _ Iff.rfl (@sector_inverse_cubic_gap) zeroReadout bad
end SectorCrossGap

namespace SectorGap
abbrev law (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (i j : Fin (n + 1) ⊕ Fin (n + 1)), i ≠ j →
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤
      R.readout () () |sectorSpectrum n i - sectorSpectrum n j|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have hh := h 0 (Sum.inl 0) (Sum.inr 0) (by simp)
  have hp : 0 < 2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2 := by positivity
  norm_num [zeroReadout, realize] at hh
  linarith

def family : Registration ⟨signature, law⟩ (type_of% @sector_spectral_gap) :=
  sourceFamily law _ Iff.rfl (@sector_spectral_gap) zeroReadout bad
end SectorGap

namespace CentralGap
abbrev law (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (lambda : Fin (2 * (n + 1) - 1 + 1) → ℝ),
    Finset.univ.val.map lambda = (centralDefect (n + 1) (by omega)).charpoly.roots →
    ∀ (i j : Fin (2 * (n + 1) - 1 + 1)), i ≠ j →
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤
      R.readout () () |lambda i - lambda j|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have hH : (centralDefect 1 (by omega)).IsHermitian := by
    unfold centralDefect _root_.D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
    simpa only [add_assoc, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_diagonal (0 : Fin 2 → ℝ)).add
        (Matrix.isHermitian_add_transpose_self
          (_root_.D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand 1 (centralEdges 1 (by omega))))
  have hr : Finset.univ.val.map hH.eigenvalues = (centralDefect 1 (by omega)).charpoly.roots := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hH.roots_charpoly_eq_eigenvalues.symm
  have hh := h 0 hH.eigenvalues hr 0 1 (by decide)
  have hp : 0 < 2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2 := by positivity
  norm_num [zeroReadout, realize] at hh
  linarith

def family : Registration ⟨signature, law⟩ (type_of% @central_spectral_gap) :=
  sourceFamily law _ Iff.rfl (@central_spectral_gap) zeroReadout bad
end CentralGap

namespace UniformGap
abbrev law (R : Realization signature) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → (centralDefect n hn).IsHermitian ∧
      ∀ (lambda : Fin (2 * n - 1 + 1) → ℝ),
        Finset.univ.val.map lambda = (centralDefect n hn).charpoly.roots →
        ∀ i j, i ≠ j → c / (n : ℝ) ^ 3 ≤ R.readout () () |lambda i - lambda j|
private theorem bad : ¬ law zeroReadout := by
  rintro ⟨c, hc, N, hN, h⟩
  obtain ⟨hH, hh⟩ := h N hN le_rfl
  have hr : Finset.univ.val.map hH.eigenvalues = (centralDefect N hN).charpoly.roots := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hH.roots_charpoly_eq_eigenvalues.symm
  let i : Fin (2 * N - 1 + 1) := ⟨0, by omega⟩
  let j : Fin (2 * N - 1 + 1) := ⟨1, by omega⟩
  have hg := hh hH.eigenvalues hr i j (by intro he; have := congrArg Fin.val he; dsimp [i, j] at this; omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < c / (N : ℝ) ^ 3 := by positivity
  norm_num [zeroReadout, realize] at hg
  linarith

def family : Registration ⟨signature, law⟩ (type_of% @uniform_inverse_cubic_gap) :=
  sourceFamily law _ Iff.rfl (@uniform_inverse_cubic_gap) zeroReadout bad
end UniformGap

namespace ScalarGap
def audit : Contract.Registration (@rank_one_gap_from_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.ScalarGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.ScalarGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ScalarGap

namespace CrossIdentity
def audit : Contract.Registration (@rank_one_cross_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.CrossIdentity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.CrossIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CrossIdentity

namespace MatrixGap
def audit : Contract.Registration (@rank_one_gap_of_matrices) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.MatrixGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.MatrixGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MatrixGap

namespace RecurrenceEndpoint
def audit : Contract.Registration (@recurrence_endpoint_observability) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.RecurrenceEndpoint.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.RecurrenceEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RecurrenceEndpoint

namespace SectorEndpoint
def audit : Contract.Registration (@sector_endpoint_observability) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorEndpoint.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SectorEndpoint

namespace SectorCrossGap
def audit : Contract.Registration (@sector_inverse_cubic_gap) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorCrossGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorCrossGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SectorCrossGap

namespace SectorGap
def audit : Contract.Registration (@sector_spectral_gap) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.SectorGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SectorGap

namespace CentralGap
def audit : Contract.Registration (@central_spectral_gap) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.CentralGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.CentralGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some { owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CentralGap

namespace UniformGap
def audit : Contract.Registration (@uniform_inverse_cubic_gap) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.UniformGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.UniformGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some { owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end UniformGap

end Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
