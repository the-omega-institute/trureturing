import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The original spectral count with all cutoffs and its inclusive count observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (G b)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (C)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping (G0)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (K Sigma)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator (boundaryOperator)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter
open scoped Topology

abbrev signature : Signature where
  Params := ℕ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ mu lam => positiveCount mu lam) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := 
    B = 2 * Real.goldenRatio^3 ∧
    ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
      (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
      Monotone (fun i => (mu i)⁻¹) ∧ Tendsto (fun i => (mu i)⁻¹) atTop atTop ∧
      (∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
      (∀ lam : ℝ, ∃ s q : Finset ℕ,
        (∀ i, i ∈ s ↔ (mu i)⁻¹ ≤ lam) ∧
        (∀ i, i ∈ q ↔ (mu i)⁻¹ < lam) ∧
        (modeProjection e s).range = modeSpace e s ∧
        (modeProjection e q).range = modeSpace e q ∧
        (modeProjection k s).range = modeSpace k s ∧
        (modeProjection k q).range = modeSpace k q ∧
        (∀ u : G0, u ∈ modeSpace e s ↔ ∀ i, i ∉ s → e.repr u i = 0) ∧
        (∀ u : G0, u ∈ modeSpace e q ↔ ∀ i, i ∉ q → e.repr u i = 0) ∧
        (∀ x : K, x ∈ modeSpace k s ↔ ∀ i, i ∉ s → k.repr x i = 0) ∧
        (∀ x : K, x ∈ modeSpace k q ↔ ∀ i, i ∉ q → k.repr x i = 0) ∧
        Module.finrank ℝ (modeSpace e s) = obs.readout () mu lam ∧
        Module.finrank ℝ (modeSpace e q) = strictCount mu lam ∧
        Module.finrank ℝ (modeSpace k s) = obs.readout () mu lam ∧
        Module.finrank ℝ (modeSpace k q) = strictCount mu lam ∧
        Module.finrank ℝ (fullModeSpace e s (0 ≤ lam)) =
          (if 0 ≤ lam then 1 else 0) + obs.readout () mu lam ∧
        Module.finrank ℝ (fullModeSpace e q (0 < lam)) =
          (if 0 < lam then 1 else 0) + strictCount mu lam) ∧
      obs.readout () mu 0 = 0 ∧ strictCount mu 0 = 0 ∧
      (∀ lam : ℝ, 0 ≤ lam → lam < Real.goldenRatio⁻¹ → obs.readout () mu lam = 0) ∧
      (∀ lam : ℝ, 0 ≤ lam → (obs.readout () mu lam : ℝ) ≤ B * lam) ∧
      (∀ lam : ℝ, b⁻¹ < lam → b * lam - 1 ≤ (strictCount mu lam : ℝ) ∧
        b * lam - 1 ≤ (obs.readout () mu lam : ℝ)) ∧
      (∀ lam : ℝ, 2 / b ≤ lam →
        (b/2) * lam ≤ (obs.readout () mu lam : ℝ) ∧
        (obs.readout () mu lam : ℝ) ≤ B * lam) ∧
      (∀ j : ℕ, 1 ≤ j → (j : ℝ) / B ≤ positiveEigenvalue mu j ∧
        positiveEigenvalue mu j ≤ (j : ℝ) / b)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℕ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_,e,k,mu,_,_,_,_,_,_,_,_,_,hz,_⟩
  change (1 : ℕ) = 0 at hz
  norm_num at hz

def familyRegistration : Registration arena (type_of% actual_spectral_counting) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_spectral_counting,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    classical
    obtain ⟨_,e,k,mu,_,_,_,_,_,_,_,_,hcut,hzero,_⟩ := actual_spectral_counting
    refine ⟨mu,0,(mu 0)⁻¹,?_⟩
    change positiveCount mu 0 ≠ positiveCount mu (mu 0)⁻¹
    rw [hzero]
    obtain ⟨s,q,hs,_⟩ := hcut (mu 0)⁻¹
    have hset : {n : ℕ | (mu n)⁻¹ ≤ (mu 0)⁻¹} = (s : Set ℕ) := by
      ext n
      exact (hs n).symm
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨0,(hs 0).mpr le_rfl⟩
    have hcount : 0 < positiveCount mu (mu 0)⁻¹ := by
      simpa [positiveCount,hset] using hpos
    exact ne_of_lt hcount

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_spectral_counting)
    (type_of% (realize signature (fun _ mu lam => positiveCount mu lam) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ mu lam => positiveCount mu lam) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["arg","arg","body","arg","body","arg","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","body","body","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
