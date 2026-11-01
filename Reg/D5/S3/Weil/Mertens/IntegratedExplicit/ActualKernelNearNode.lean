import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode

structure WindowParams where
  n : ℕ
  x : Fin n → ℝ
  j : Fin n
  g : ℝ
  d : ℝ
  N : ℕ

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature WindowParams (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ p h => S p.x p.j h) (fun e => nomatch e)

private def nodes : Fin 1 → ℝ := fun _ => 0

private theorem singleton_posDef : (H nodes).PosDef := by
  have hM : 0 < firstLiMass := by
    rw [firstLiMass]
    linarith [_root_.D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity.first_li_coefficient_pos]
  have he : H nodes = Matrix.diagonal (fun _ : Fin 1 => firstLiMass) := by
    ext i k
    fin_cases i
    fin_cases k
    simp [H, nodes, K_zero]
  rw [he]
  exact Matrix.posDef_diagonal_iff.mpr (fun _ => hM)

private theorem S_zero {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (hp : (H x).PosDef) :
    S x j 0 = 0 := by
  letI := hp.isUnit.invertible
  have hb : b x j 0 = H x *ᵥ Pi.single j 1 := by
    ext i
    simp [b, H, Matrix.mulVec_single_one]
  dsimp only [S]
  rw [hb, ← Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec,
    Matrix.dotProduct_single_one, Matrix.mulVec_single_one]
  simp [H, K_zero]

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨g, d, N, hg, hgd, hgap, hwindow, hN, hrho, hcert⟩ :=
    explicit_near_node_posDef nodes (Function.injective_of_subsingleton nodes) (0 : Fin 1) singleton_posDef
  let h := rho nodes g (L (g / 2) d N) / 2
  have hh : 0 < h := half_pos hrho
  have hle : |h| ≤ rho nodes g (L (g / 2) d N) := by rw [abs_of_pos hh]; dsimp [h]; linarith
  have hp := hcert h (by simpa only [abs_of_pos hh] using hh) hle
  refine ⟨⟨1, nodes, 0, g, d, N⟩, 0, h, ?_⟩
  change S nodes 0 0 ≠ S nodes 0 h
  rw [S_zero nodes 0 singleton_posDef]
  exact ne_of_lt (hp.1.2.trans_le hp.1.1)

private def testN : ℕ := ⌈Real.exp 1⌉₊ + 1
private def testParams : WindowParams := ⟨1, nodes, 0, 1, 1, testN⟩

private lemma testN_bound : Real.exp 1 < (testN : ℝ) := by
  have hh := Nat.le_ceil (Real.exp 1)
  dsimp only [testN]
  push_cast
  linarith

private lemma test_gap : ∀ i : Fin 1, i ≠ (0 : Fin 1) → (1 : ℝ) ≤ |nodes i - nodes 0| := by
  intro i hi
  exact (hi (Subsingleton.elim _ _)).elim

private lemma test_window : ∀ i : Fin 1, |nodes i - nodes 0| + (1 : ℝ) / 2 ≤ 1 := by
  intro i
  norm_num [nodes]

namespace Remainder

def error (p : WindowParams) (h : ℝ) : ℝ := |h| ^ 2 *
  (4 + q p.x * (scale |h| / 2 + |c| + L (p.g / 2) p.d p.N + 2 * |h|) ^ 2)

def arena : Arena where
  signature := signature
  Law F := ∀ {n : ℕ} (x : Fin n → ℝ) (j : Fin n), (H x).PosDef →
    ∀ {g d : ℝ} {N : ℕ}, 0 < g → g / 2 ≤ d →
    (∀ i, i ≠ j → g ≤ |x i - x j|) →
    (∀ i, |x i - x j| + g / 2 ≤ d) → Real.exp d < N →
    ∀ {h : ℝ}, 0 < |h| → |h| ≤ 1 / 2 → |h| ≤ g / 2 →
    |F.readout () ⟨n, x, j, g, d, N⟩ h - (|h| * scale |h| - 2 * c * |h|)| ≤
      |h| ^ 2 * (4 + q x * (scale |h| / 2 + |c| + L (g / 2) d N + 2 * |h|) ^ 2)

def rejected : Realization signature := realize signature
  (fun _ p h => S p.x p.j h + 2 * error p h + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh nodes 0 singleton_posDef (g := 1) (d := 1) (N := testN)
    (by norm_num) (by norm_num) test_gap test_window testN_bound
    (h := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have ha := near_node_remainder nodes 0 singleton_posDef (g := 1) (d := 1) (N := testN)
    (by norm_num) (by norm_num) test_gap test_window testN_bound
    (h := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  change |S nodes 0 (1 / 2) + 2 * error testParams (1 / 2) + 1 -
      (|1 / 2| * scale |1 / 2| - 2 * c * |1 / 2|)| ≤ error testParams (1 / 2) at hb
  change |S nodes 0 (1 / 2) - (|1 / 2| * scale |1 / 2| - 2 * c * |1 / 2|)| ≤
    error testParams (1 / 2) at ha
  linarith [(abs_le.mp ha).1, (abs_le.mp hb).2]

def evidence : Registration arena (type_of% @near_node_remainder) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@near_node_remainder, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@near_node_remainder) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.near_node_remainder.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.Remainder.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h => S p.x p.j h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 12
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Remainder

namespace Positive

def arena : Arena where
  signature := signature
  Law F := ∀ {n : ℕ} (x : Fin n → ℝ) (j : Fin n), (H x).PosDef →
    ∀ {g d : ℝ} {N : ℕ}, 0 < g → g / 2 ≤ d →
    (∀ i, i ≠ j → g ≤ |x i - x j|) →
    (∀ i, |x i - x j| + g / 2 ≤ d) → Real.exp d < N →
    ∀ {h : ℝ}, 0 < |h| → |h| ≤ rho x g (L (g / 2) d N) →
    |h| * scale |h| / 4 ≤ F.readout () ⟨n, x, j, g, d, N⟩ h ∧
      0 < |h| * scale |h| / 4

def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  obtain ⟨g, d, N, hg, hgd, hgap, hwindow, hN, hrho, _⟩ :=
    explicit_near_node_posDef nodes (Function.injective_of_subsingleton nodes) (0 : Fin 1) singleton_posDef
  let h := rho nodes g (L (g / 2) d N) / 2
  have hp : 0 < |h| := abs_pos.mpr (ne_of_gt (half_pos hrho))
  have hle : |h| ≤ rho nodes g (L (g / 2) d N) := by
    rw [abs_of_pos (half_pos hrho)]
    dsimp [h]
    linarith
  have hb := hh nodes 0 singleton_posDef hg hgd hgap hwindow hN hp hle
  change |h| * scale |h| / 4 ≤ -1 ∧ 0 < |h| * scale |h| / 4 at hb
  linarith [hb.1, hb.2]

def evidence : Registration arena (type_of% @near_node_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@near_node_positive, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@near_node_positive) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.near_node_positive.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.Positive.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p h => S p.x p.j h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 12
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Positive

namespace Insertion

structure Params where
  n : ℕ
  x : Fin n → ℝ
  j : Fin n

abbrev pairSignature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Params
  (fun _ => ℝ) (fun p => ℝ × Matrix (Sum (Fin p.n) Unit) (Sum (Fin p.n) Unit) ℝ)

def actualPair : Realization pairSignature := realize pairSignature
  (fun _ p h => (S p.x p.j h, augmented p.x p.j h)) (fun e => nomatch e)

def arena : Arena where
  signature := pairSignature
  Law F := ∀ {n : ℕ} (x : Fin n → ℝ), Function.Injective x →
    ∀ j : Fin n, (H x).PosDef →
    ∃ g d : ℝ, ∃ N : ℕ, 0 < g ∧ g / 2 ≤ d ∧
      (∀ i, i ≠ j → g ≤ |x i - x j|) ∧
      (∀ i, |x i - x j| + g / 2 ≤ d) ∧ Real.exp d < N ∧
      0 < rho x g (L (g / 2) d N) ∧
      ∀ h : ℝ, 0 < |h| → |h| ≤ rho x g (L (g / 2) d N) →
        (|h| * scale |h| / 4 ≤ (F.readout () ⟨n, x, j⟩ h).1 ∧ 0 < |h| * scale |h| / 4) ∧
        (F.readout () ⟨n, x, j⟩ h).2.PosDef

def rejected : Realization pairSignature := realize pairSignature
  (fun _ p h => (-1, augmented p.x p.j h)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  obtain ⟨g, d, N, hg, hgd, hgap, hwindow, hN, hrho, hcert⟩ :=
    hh nodes (Function.injective_of_subsingleton nodes) (0 : Fin 1) singleton_posDef
  let h := rho nodes g (L (g / 2) d N) / 2
  have hp : 0 < |h| := abs_pos.mpr (ne_of_gt (half_pos hrho))
  have hle : |h| ≤ rho nodes g (L (g / 2) d N) := by
    rw [abs_of_pos (half_pos hrho)]
    dsimp [h]
    linarith
  have hb := (hcert h hp hle).1
  change |h| * scale |h| / 4 ≤ -1 ∧ 0 < |h| * scale |h| / 4 at hb
  linarith [hb.1, hb.2]

private theorem pair_dependence : ObservationalDependence pairSignature actualPair := by
  intro role
  obtain ⟨p, h, k, hne⟩ := dependence ()
  refine ⟨⟨p.n, p.x, p.j⟩, h, k, ?_⟩
  intro he
  exact hne (congrArg Prod.fst he)

def evidence : Registration arena (type_of% @explicit_near_node_posDef) where
  actual := actualPair
  bridge := Iff.rfl
  variation := ⟨@explicit_near_node_posDef, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actualPair rejected rejected_law
  dependence := pair_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@explicit_near_node_posDef) (Realization pairSignature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.explicit_near_node_posDef.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode.Insertion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ p h => (S p.x p.j h, augmented p.x p.j h)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Insertion

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelNearNode
