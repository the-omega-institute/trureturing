import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
open _root_.D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
noncomputable section
set_option autoImplicit false

namespace continuous_F
abbrev signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun M => Fin M → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ c => F c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ c => deriv (fun x : ℝ => x * Real.log x) (∑ i, c i))
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ}, Continuous (R.readout () M)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := @h 1
  have hh : Continuous (deriv (fun x : ℝ => x * Real.log x)) := by
    simpa [rejected, realize, Function.comp_def, Fin.sum_univ_one] using
      hc.comp (show Continuous (fun x : ℝ => (fun _ : Fin 1 => x)) by fun_prop)
  exact Real.not_continuousAt_deriv_mul_log_zero hh.continuousAt
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (fun _ => 0), (fun _ => 1/2), ?_⟩
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hps : ({1} : Finset (Fin 2)).powerset = {∅, {1}} := by decide
  have hsdiff : ({0, 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  have hs (f : Finset (Fin 2) → ℝ) :
      ∑ a ∈ {{0}, ∅, {1}, {0, 1}}, f a =
        f {0} + (f ∅ + (f {1} + f {0, 1})) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  have hlog : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  change F (fun _ : Fin 2 => (0:ℝ)) ≠ F (fun _ => 1/2)
  norm_num [F, pb, hu, Finset.powerset_insert, hps, Finset.sum_range_succ,
    Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton,
    Finset.compl_eq_univ_sdiff, Real.negMulLog, Real.binEntropy, Real.log_div, hlog,
    hs, hsdiff]
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  linarith

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.continuous_F)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.continuous_F, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.continuous_F) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.continuous_F.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep.continuous_F.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => F c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end continuous_F

abbrev orderSignature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def orderActual : Realization orderSignature :=
  realize orderSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
theorem order_dependence : ObservationalDependence orderSignature orderActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1:ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh
namespace F_le_interiorT
abbrev signature := orderSignature
def actual : Realization signature := orderActual
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {M : ℕ} (x y : Fin M → ℝ) (ht : InteriorT x y),
    R.readout () () (F x) (F y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x : Fin 1 → ℝ := fun _ => 1/2
  have ht : InteriorT x x := by
    refine ⟨⟨0, 0, 0, le_rfl, zero_le_one, ?_⟩, ?_, ?_⟩
    · simp
    · intro i; norm_num [x]
    · intro i; norm_num [x]
  exact h x x ht

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.F_le_interiorT)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.F_le_interiorT, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := order_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.F_le_interiorT) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy.F_le_interiorT.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep.F_le_interiorT.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end F_le_interiorT
end
end Reg.D5.S3.Entropy.PoissonBinomial.ConfigurationalEntropyStep
