import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
open _root_.D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal BigOperators
noncomputable section

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℕ × ℕ
  State p := PrefixSampler (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => ENNReal.ofReal (DyadicSupportLines.residual (law s) p.2 / (2 : ℝ)^p.2))
  (fun e => nomatch e)

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ),
    R.readout () (m,d) s ≤ fairTape (active s d)

private def point : PrefixSampler (Fin 2) where
  observe _ _ := some 0
  persistent _ _ _ _ _ h := h
  terminates := Filter.Eventually.of_forall (fun _ => ⟨0,0,rfl⟩)

private def halfPath : Path :=
  ⟨fun d => if d = 0 then ⟨1,2⟩ else ⟨0,2⟩,
   fun d => if d = 0 then ⟨0,2,0⟩ else ⟨0,0,0⟩⟩

private theorem half_legal : IsRootPath 2 halfPath := by
  constructor
  · rfl
  · intro d
    cases d <;> norm_num [halfPath, IsState, Legal, successor, ones]

private theorem half_law (i : Fin 2) :
    law (Paths.fromPath 2 halfPath (by decide) half_legal) i = 1/2 := by
  rw [Paths.path_law, Real.ofDigits_eq_sum_add_ofDigits _ 1]
  have tail : (fun d => CarryGraphRealization.labelDigit halfPath i (d+1)) = fun _ => 0 := by
    funext d
    simp [CarryGraphRealization.labelDigit, labelSet, halfPath]
  rw [tail]
  fin_cases i <;>
    simp [Real.ofDigits, Real.ofDigitsTerm, Finset.sum_range_succ,
      CarryGraphRealization.labelDigit, labelSet, halfPath]

private theorem point_law (i : Fin 2) : law point i = if i=0 then 1 else 0 := by
  unfold law emitted point
  fin_cases i <;> simp

def rejected : Realization signature := realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h point 0
  simpa [rejected, realize, active, point] using bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(2,0), point, Paths.fromPath 2 halfPath (by decide) half_legal, ?_⟩
  simp [actual, realize, DyadicSupportLines.residual, point_law, half_law, Fin.sum_univ_succ]

def proof_record : Registration arena
    (∀ {m : ℕ} (s : PrefixSampler (Fin m)) (d : ℕ),
      ENNReal.ofReal (DyadicSupportLines.residual (law s) d / (2 : ℝ)^d) ≤ fairTape (active s d)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cylinder_tail_lower, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.cylinder_tail_lower)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.cylinder_tail_lower "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => ENNReal.ofReal (DyadicSupportLines.residual (law s) p.2 / (2 : ℝ)^p.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
    coordinates := #[0,2]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1 }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
