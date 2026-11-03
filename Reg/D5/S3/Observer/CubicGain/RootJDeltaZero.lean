import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.RootJDeltaZero
import Reg.Support.SingleDependentReadout

/-! Source-bound audit evidence and a complete native-kernel satisfiability witness. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace Reg.D5.S3.Observer.CubicGain.RootJDeltaZero
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.Observer.CubicGain.RootJDeltaZero
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- A complete source tuple; repeated sources are intentional. -/
def witnessSources (q : Slot) : Mat :=
  if q.val = 9 then sourceChart 3 (5/3)
  else if q.val = 13 then sourceChart (1/2) (8/5)
  else if 8 ≤ q.val ∧ q.val < 16 then sourceChart (3/2) (4/3)
  else sourceChart 1 1

private theorem witness_legal (q : Slot) : LegalSource (witnessSources q) := by
  unfold witnessSources
  split_ifs
  · exact source_chart_legal _ _ (by norm_num) (by norm_num)
  · exact source_chart_legal _ _ (by norm_num) (by norm_num)
  · exact source_chart_legal _ _ (by norm_num) (by norm_num)
  · exact source_chart_legal _ _ (by norm_num) (by norm_num)

private theorem witness_trace_one (q : Slot) :
    witnessSources q 0 0 + witnessSources q 1 1 = 1 := by
  simpa [Matrix.trace, Fin.sum_univ_two] using (witness_legal q).2.2

private theorem witness_default (q : Slot) (h : q.val < 8 ∨ 16 ≤ q.val) :
    witnessSources q = sourceChart 1 1 := by
  have hn : q.val ≠ 9 := by omega
  have hn13 : q.val ≠ 13 := by omega
  have hm : ¬ (8 ≤ q.val ∧ q.val < 16) := by omega
  simp [witnessSources, hn, hn13, hm]

private theorem witness_middle (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 16)
    (hne : q.val ≠ 9) (hne13 : q.val ≠ 13) :
    witnessSources q = sourceChart (3/2) (4/3) := by
  simp [witnessSources, hne, hne13, hlo, hhi]

private theorem witness_m_trace (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 16) :
    witnessSources q 1 0 + (witnessSources q 0 1 + witnessSources q 1 1) = 29/18 := by
  by_cases he : q.val = 9
  · norm_num [witnessSources, he, sourceChart]
  · by_cases he13 : q.val = 13
    · norm_num [witnessSources, he, he13, sourceChart]
    · rw [witness_middle q hlo hhi he he13]
      norm_num [sourceChart]

private theorem witness_jm_trace (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 12) :
    witnessSources q 0 0 + witnessSources q 1 0 + witnessSources q 1 1 = 3/2 := by
  by_cases he : q.val = 9
  · norm_num [witnessSources, he, sourceChart]
  · rw [witness_middle q hlo (by omega) he (by omega)]
    norm_num [sourceChart]

private theorem witness_mm_trace (q : Slot) (hlo : 12 ≤ q.val) (hhi : q.val < 16) :
    witnessSources q 0 0 + witnessSources q 1 0 +
      (witnessSources q 0 1 + 2 * witnessSources q 1 1) = 47/18 := by
  by_cases he13 : q.val = 13
  · norm_num [witnessSources, show q.val ≠ 9 by omega, he13, sourceChart]
  · rw [witness_middle q (by omega) hhi (by omega) he13]
    norm_num [sourceChart]

def witnessCoefficients (a b : ℝ) : Blocks :=
  fun _ => ![3*a + 12*b, -4*a - 13*b, a, b]

private theorem witness_kernel (a b : ℝ) :
    witnessCoefficients a b ∈ V witnessSources := by
  apply LinearMap.mem_ker.mpr
  ext r
  change normalized (prefixWord (r.1.val + 1) r.2.1.val)
      (witnessSources (descendant r)) (witnessCoefficients a b (descendant r)) -
    normalized (prefixWord (r.1.val + 1) r.2.1.val)
      (witnessSources (reference r)) (witnessCoefficients a b (reference r)) = 0
  rw [normalized_eval, normalized_eval]
  rw [show (prefixWord (r.1.val + 1) r.2.1.val).length = r.1.val + 1 from List.length_ofFn]
  rcases r with ⟨n, p, j⟩
  fin_cases n
  all_goals norm_num only [witnessCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk, Fin.val_natCast, Nat.reduceAdd, Nat.cast_ofNat]
  all_goals first | (ring; done) | skip
  · by_cases hp : p.val = 0
    · have he : p = 0 := Fin.ext hp
      subst p
      norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, witness_trace_one] <;> ring
    · have hr : (reference ⟨⟨1, by decide⟩,p,j⟩).val ≥ 16 := by dsimp [reference]; norm_num; omega
      have hq : (descendant ⟨⟨1, by decide⟩,p,j⟩).val ≥ 16 := by dsimp [descendant]; norm_num; omega
      rw [witness_default _ (Or.inr hq), witness_default _ (Or.inr hr)]
      ring
  · by_cases hp : p.val = 0
    · have he : p = 0 := Fin.ext hp
      subst p
      norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, witness_trace_one] <;> ring
    · have hr : (reference ⟨⟨3, by decide⟩,p,j⟩).val ≥ 16 := by dsimp [reference]; norm_num; omega
      have hq : (descendant ⟨⟨3, by decide⟩,p,j⟩).val ≥ 16 := by dsimp [descendant]; norm_num; omega
      rw [witness_default _ (Or.inr hq), witness_default _ (Or.inr hr)]
      ring
  · by_cases hp : p.val = 1
    · have he : p = 1 := Fin.ext hp
      subst p
      have hq0 : 8 ≤ (descendant ⟨⟨4, by decide⟩,1,j⟩).val := by dsimp [descendant]; norm_num; omega
      have hq1 : (descendant ⟨⟨4, by decide⟩,1,j⟩).val < 16 := by have hj := j.isLt; dsimp [descendant]; norm_num at hj ⊢; omega
      norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
      rw [witness_m_trace _ hq0 hq1]
      norm_num [reference, witnessSources, sourceChart] <;> ring
    · have hr : (reference ⟨⟨4, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (reference ⟨⟨4, by decide⟩,p,j⟩).val := by dsimp [reference]; norm_num; omega
      have hq : (descendant ⟨⟨4, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (descendant ⟨⟨4, by decide⟩,p,j⟩).val := by
        have hj := j.isLt; dsimp [descendant]; norm_num at hj ⊢; omega
      rw [witness_default _ hq, witness_default _ hr]
      ring
  · by_cases hp : p.val = 2
    · have he : p = 2 := Fin.ext hp
      subst p
      have hq0 : 8 ≤ (descendant ⟨⟨5, by decide⟩,2,j⟩).val := by dsimp [descendant]; norm_num; omega
      have hq1 : (descendant ⟨⟨5, by decide⟩,2,j⟩).val < 12 := by
        have hj := j.isLt
        change j.val < 3 at hj
        dsimp [descendant]
        norm_num
        omega
      norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
      rw [witness_jm_trace _ hq0 hq1]
      norm_num [reference, witnessSources, sourceChart] <;> ring
    · by_cases hp3 : p.val = 3
      · have he : p = 3 := Fin.ext hp3
        subst p
        have hq0 : 12 ≤ (descendant ⟨⟨5, by decide⟩,3,j⟩).val := by dsimp [descendant]; norm_num; omega
        have hq1 : (descendant ⟨⟨5, by decide⟩,3,j⟩).val < 16 := by have hj := j.isLt; dsimp [descendant]; norm_num at hj ⊢; omega
        norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
          _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
          _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
          _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
          Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
        rw [witness_mm_trace _ hq0 hq1]
        norm_num [reference, witnessSources, sourceChart] <;> ring
      · have hr : (reference ⟨⟨5, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (reference ⟨⟨5, by decide⟩,p,j⟩).val := by dsimp [reference]; norm_num; omega
        have hq : (descendant ⟨⟨5, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (descendant ⟨⟨5, by decide⟩,p,j⟩).val := by
          have hj := j.isLt; dsimp [descendant]; norm_num at hj ⊢; omega
        rw [witness_default _ hq, witness_default _ hr]
        ring
  · by_cases hp : p.val = 4
    · have he : p = 4 := Fin.ext hp
      subst p
      have hj0 : j.val = 0 := by
        have hj := j.isLt
        change j.val < 1 at hj
        omega
      have heq : j = ⟨0, by norm_num⟩ := Fin.ext hj0
      subst j
      norm_num [prefixWord, List.ofFn_succ, acquisition, Raw, reference, descendant,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, witnessSources, sourceChart]
    · by_cases hp6 : p.val = 6
      · have he : p = 6 := Fin.ext hp6
        subst p
        have hj0 : j.val = 0 := by
          have hj := j.isLt
          change j.val < 1 at hj
          omega
        have heq : j = ⟨0, by norm_num⟩ := Fin.ext hj0
        subst j
        norm_num [prefixWord, List.ofFn_succ, acquisition, Raw, reference, descendant,
          _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
          _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
          _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
          Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, witnessSources, sourceChart]
      · by_cases hm : 4 < p.val ∧ p.val < 8
        · have hq0 : 8 ≤ (descendant ⟨⟨6, by decide⟩,p,j⟩).val := by dsimp [descendant]; norm_num; omega
          have hq1 : (descendant ⟨⟨6, by decide⟩,p,j⟩).val < 16 := by
            have hj := j.isLt
            change j.val < 1 at hj
            dsimp [descendant]
            norm_num
            omega
          have hn : (descendant ⟨⟨6, by decide⟩,p,j⟩).val ≠ 9 := by dsimp [descendant]; norm_num; omega
          have hr0 : 8 ≤ (reference ⟨⟨6, by decide⟩,p,j⟩).val := by dsimp [reference]; norm_num; omega
          have hr1 : (reference ⟨⟨6, by decide⟩,p,j⟩).val < 16 := by dsimp [reference]; norm_num; omega
          have hrn : (reference ⟨⟨6, by decide⟩,p,j⟩).val ≠ 9 := by dsimp [reference]; norm_num; omega
          have hn13 : (descendant ⟨⟨6, by decide⟩,p,j⟩).val ≠ 13 := by
            have hj := j.isLt
            change j.val < 1 at hj
            dsimp [descendant]
            norm_num
            omega
          have hrn13 : (reference ⟨⟨6, by decide⟩,p,j⟩).val ≠ 13 := by
            dsimp [reference]
            norm_num
            omega
          rw [witness_middle _ hq0 hq1 hn hn13, witness_middle _ hr0 hr1 hrn hrn13]
          ring
        · have hr : (reference ⟨⟨6, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (reference ⟨⟨6, by decide⟩,p,j⟩).val := by dsimp [reference]; norm_num; omega
          have hq : (descendant ⟨⟨6, by decide⟩,p,j⟩).val < 8 ∨ 16 ≤ (descendant ⟨⟨6, by decide⟩,p,j⟩).val := by
            have hj := j.isLt; dsimp [descendant]; norm_num at hj ⊢; omega
          rw [witness_default _ hq, witness_default _ hr]
          ring

set_option maxHeartbeats 1000000 in
-- Ten native response rows are normalized simultaneously before exact elimination.
private theorem witness_delta : Delta witnessSources = 0 := by
  ext x
  have h18 := congrFun x.property (⟨⟨0, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩⟩ : Row)
  have h19 := congrFun x.property (⟨⟨0, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩⟩ : Row)
  have h28 := congrFun x.property (⟨⟨1, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩⟩ : Row)
  have h29 := congrFun x.property (⟨⟨1, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩⟩ : Row)
  have h38 := congrFun x.property (⟨⟨2, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩⟩ : Row)
  have h39 := congrFun x.property (⟨⟨2, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩⟩ : Row)
  have h48 := congrFun x.property (⟨⟨3, by decide⟩,⟨0, by decide⟩,⟨7, by decide⟩⟩ : Row)
  have h49 := congrFun x.property (⟨⟨3, by decide⟩,⟨0, by decide⟩,⟨8, by decide⟩⟩ : Row)
  have h5 := congrFun x.property (⟨⟨4, by decide⟩,⟨1, by decide⟩,⟨0, by decide⟩⟩ : Row)
  have h7 := congrFun x.property (⟨⟨6, by decide⟩,⟨4, by decide⟩,⟨0, by decide⟩⟩ : Row)
  change normalized _ _ _ - normalized _ _ _ = 0 at h18 h19 h28 h29 h38 h39 h48 h49 h5 h7
  simp only [normalized_eval] at h18 h19 h28 h29 h38 h39 h48 h49 h5 h7
  norm_num [prefixWord, List.ofFn_succ, reference, descendant, acquisition, Raw,
    _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, witnessSources, sourceChart]
      at h18 h19 h28 h29 h38 h39 h48 h49 h5 h7
  have hd : 2*x.val 0 1 + 8*x.val 0 2 + 26*x.val 0 3 = 0 := by
    linarith
  simp [Delta, history, H, sample, block, evaluate, evaluation, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  linarith

private theorem witness_rank : Module.finrank ℝ (LinearMap.range (H witnessSources)) = 2 := by
  let u : Coeff 3 := ![0,-4,1,0]
  let v : Coeff 3 := ![0,-13,0,1]
  have hu : u ∈ LinearMap.range (H witnessSources) := by
    refine ⟨⟨witnessCoefficients 1 0, witness_kernel 1 0⟩, ?_⟩
    ext i
    fin_cases i <;> norm_num [H, sample, block, evaluate, evaluation,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, witnessCoefficients, u]
  have hv : v ∈ LinearMap.range (H witnessSources) := by
    refine ⟨⟨witnessCoefficients 0 1, witness_kernel 0 1⟩, ?_⟩
    ext i
    fin_cases i <;> norm_num [H, sample, block, evaluate, evaluation,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, witnessCoefficients, v]
  have heq : Submodule.span ℝ (Set.range ![u,v]) = LinearMap.range (H witnessSources) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      fin_cases i <;> assumption
    · rintro _ ⟨x,rfl⟩
      have hd := congrArg (fun f : V witnessSources →ₗ[ℝ] ℝ => f x) witness_delta
      simp [Delta, history, H, sample, block, evaluate, evaluation,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hd
      have hsplit : H witnessSources x = x.val 0 2 • u + x.val 0 3 • v := by
        ext i
        fin_cases i <;> simp [H, sample, block, evaluate, evaluation,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ, u, v] <;> linarith
      rw [hsplit]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩)
  have li : LinearIndependent ℝ ![u,v] := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have h2 := congrFun ha 2
    have h3 := congrFun ha 3
    norm_num [Fin.sum_univ_two, u, v] at h2 h3
    fin_cases i <;> assumption
  have hr := finrank_span_eq_card li
  rw [heq] at hr
  simpa using hr

private theorem witness_nonzero_e : E witnessSources ≠ 0 := by
  intro hz
  let x : V witnessSources := ⟨witnessCoefficients 1 0, witness_kernel 1 0⟩
  have he := congrArg (fun f : V witnessSources →ₗ[ℝ] ℝ => f x) hz
  norm_num [x, E, history, H, sample, block, evaluate, evaluation,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, witnessCoefficients, Pi.single_apply,
    Matrix.vecHead, Matrix.vecTail] at he

namespace NormalizedResponse
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Bool) (P : Mat) (b : Coeff 3),
    R.readout () () (normalized w P b)
      (Matrix.trace (acquisition w * P) *
        (b 0 + (w.length : ℝ) * b 1 + (w.length : ℝ)^2 * b 2 +
          (w.length : ℝ)^3 * b 3) - b 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h [] 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hn : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hn

def source_registration : Registration arena (type_of% @normalized_eval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_eval, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normalized_eval) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.RootJDeltaZero.normalized_eval.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.RootJDeltaZero.NormalizedResponse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.RootJDeltaZero
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end NormalizedResponse

namespace FixedLeaf
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coeff 3) (fun _ => Coeff 3 → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Slot → Mat), (∀ q, LegalSource (P q)) →
    P 0 0 1 + P 0 1 0 = 1 → P 1 0 1 + P 1 1 0 = 1 →
    Module.finrank ℝ (LinearMap.range (H P)) = 2 → E P ≠ 0 → Delta P = 0 →
    (P 8 = P 9 ∧ ∀ x : V P, x.val 8 = x.val 9) ∨
    (P 12 = P 13 ∧ ∀ x : V P, x.val 12 = x.val 13) ∨
    (P 10 = P 11 ∧ ∀ x : V P, R.readout () () (x.val 10) (x.val 11))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : witnessSources 0 0 1 + witnessSources 0 1 0 = 1 := by
    norm_num [witnessSources, sourceChart]
  have h1 : witnessSources 1 0 1 + witnessSources 1 1 0 = 1 := by
    norm_num [witnessSources, sourceChart]
  have hh := h witnessSources witness_legal h0 h1 witness_rank witness_nonzero_e witness_delta
  rcases hh with ⟨hs,_⟩ | ⟨hs,_⟩ | ⟨_,hh⟩
  · have he := congrArg (fun Q : Mat => Q 0 0) hs
    norm_num [witnessSources, sourceChart] at he
  · have he := congrArg (fun Q : Mat => Q 0 0) hs
    norm_num [witnessSources, sourceChart] at he
  · exact hh 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Coeff 3), (1 : Coeff 3), ?_⟩
  intro he
  have hn : (1 : Coeff 3) = 0 := Eq.mp (congrFun he 0) rfl
  have hz := congrFun hn 0
  norm_num at hz

def source_registration : Registration arena (type_of% @fixed_original_leaf) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_original_leaf, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_original_leaf) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.RootJDeltaZero.fixed_original_leaf.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.RootJDeltaZero.FixedLeaf.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.RootJDeltaZero
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end FixedLeaf

end Reg.D5.S3.Observer.CubicGain.RootJDeltaZero
