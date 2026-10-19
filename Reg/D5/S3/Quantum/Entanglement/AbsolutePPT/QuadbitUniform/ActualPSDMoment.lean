import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators Matrix
noncomputable section

namespace actual_psd_zero_jump_moment
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 5 → ℝ) (fun _ => Fin 9 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ h d =>
    (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (4 : ℝ)) (fun e => nomatch e)
/-- Every binder of the literal PSD theorem is retained, including all six premises. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4)
    (hK : (!![2 * (1 - d 8), -(h 0 + d 7), -(h 1 + d 5);
                -(h 0 + d 7), 2 * (1 - d 6), -(h 2 + d 4);
                -(h 1 + d 5), -(h 2 + d 4), 2 * (1 - d 3)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () h d ≤ (7 / 2 : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hK : (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · change (!![2, 0, 0; 0, 2, 0; 0, 0, 2] : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = _
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
    · intro x
      simp [dotProduct, mulVec, Fin.sum_univ_succ, star_trivial]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hf := h 0 0 (by intro i j hij; simp) (by intro i; simp)
    (by intro i j hij; simp) (by intro i; norm_num) (by norm_num)
    (by simpa using hK)
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ, Pi.zero_apply]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_zero_jump_moment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_zero_jump_moment.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_zero_jump_moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h d => (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_psd_zero_jump_moment

namespace actual_psd_flat_tail_middle_energy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => Fin 5 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ w h => w * (∑ i, h i) + (∑ i, (h i) ^ 2))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ w _ => 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 + 1)
    (fun e => nomatch e)
/-- The law retains the complete original w,h telescope and every premise. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (w : ℝ) (h : Fin 5 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (hH : (∑ i, h i) ≤ 4 - 6 * w) (hlarge : 1 ≤ h 0)
    (hw : 1 / 4 ≤ w) (hrho : w ≤ (5 - Real.sqrt 17) / 2)
    (hK : (!![2, -(w + h 0), -(w + h 1);
                -(w + h 0), 2, -(w + h 2);
                -(w + h 1), -(w + h 2), 2] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () w h ≤ 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : Fin 5 → ℝ := ![1, 0, 0, 0, 0]
  have hK : (!![2, -((1 / 4 : ℝ) + v 0), -((1 / 4 : ℝ) + v 1);
                -((1 / 4 : ℝ) + v 0), 2, -((1 / 4 : ℝ) + v 2);
                -((1 / 4 : ℝ) + v 1), -((1 / 4 : ℝ) + v 2), 2] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
    norm_num [v]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · change (!![2, -(5 / 4), -(1 / 4);
                  -(5 / 4), 2, -(1 / 4);
                  -(1 / 4), -(1 / 4), 2] : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = _
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
    · intro x
      simp [dotProduct, mulVec, Fin.sum_univ_succ, star_trivial]
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2),
        sq_nonneg (x 1 - x 2), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hrho : (1 / 4 : ℝ) ≤ (5 - Real.sqrt 17) / 2 := by
    have hsqrt : Real.sqrt 17 ≤ 9 / 2 := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
      have hn := Real.sqrt_nonneg (17 : ℝ)
      by_contra h
      have hp := mul_pos (by linarith : 0 < Real.sqrt 17 - 9 / 2)
        (by linarith : 0 < Real.sqrt 17 + 9 / 2)
      nlinarith only [hs, hp]
    linarith only [hsqrt]
  have hf := h (1 / 4) v
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [v])
    (by intro i; fin_cases i <;> norm_num [v])
    (by norm_num [v, Fin.sum_univ_succ]) (by norm_num [v])
    (by norm_num) hrho hK
  norm_num [rejected, realize] at hf
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_flat_tail_middle_energy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_flat_tail_middle_energy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_flat_tail_middle_energy)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_flat_tail_middle_energy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_flat_tail_middle_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ w h => w * (∑ i, h i) + (∑ i, (h i) ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_psd_flat_tail_middle_energy

-- UNCOMPILED source-only additions below; existing registrations above are preserved.
private theorem zero_defect_psd (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1 / 4) :
    (!![2, -w, -w; -w, 2, -w; -w, -w, 2] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (!![2, -w, -w; -w, 2, -w; -w, -w, 2] :
      Matrix (Fin 3) (Fin 3) ℝ)ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro x
    have hform : star x ⬝ᵥ
        ((!![2, -w, -w; -w, 2, -w; -w, -w, 2] :
          Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) =
        w * ((x 0 - x 1)^2 + (x 0 - x 2)^2 + (x 1 - x 2)^2) +
          (2 - 2*w) * ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
      simp [dotProduct, mulVec, Fin.sum_univ_succ, star_trivial]
      ring
    rw [hform]
    exact add_nonneg (mul_nonneg hw (by positivity))
      (mul_nonneg (by linarith) (by positivity))

namespace actual_psd_nonflat_middle_energy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _w : ℝ, Fin 5 → ℝ)
    (fun _ => Fin 9 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p d => p.1 * ((∑ i, p.2 i) + (∑ i, d i)) + (∑ i, (p.2 i) ^ 2) + (∑ i, (d i) ^ 2)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ => (if p.1 ≤ (5 - Real.sqrt 17) / 2 then
        4 - 2 * p.1 - 4 * p.1 ^ 2 + p.1 ^ 3 + p.1 ^ 4
      else (4 - 6 * p.1) * (4 - 5 * p.1)) + 1) (fun e => nomatch e)
/-- Every original real parameter and every original premise is retained. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4 - 6 * w)
    (hw : 1 / 4 ≤ w) (hw1 : w ≤ 1 / 2)
    (hK : (!![2 * (1 - d 8), -(w + h 0 + d 7), -(w + h 1 + d 5);
                -(w + h 0 + d 7), 2 * (1 - d 6), -(w + h 2 + d 4);
                -(w + h 1 + d 5), -(w + h 2 + d 4), 2 * (1 - d 3)] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () ⟨w,h⟩ d ≤
      if w ≤ (5 - Real.sqrt 17) / 2 then
        4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4
      else (4 - 6 * w) * (4 - 5 * w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hf := hall (1 / 4) 0 0
    (by intro i j hij; simp) (by intro i; simp)
    (by intro i j hij; simp) (by intro i; norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using zero_defect_psd (1 / 4) (by norm_num) (by norm_num))
  change (if (1 / 4 : ℝ) ≤ (5 - Real.sqrt 17) / 2 then
      4 - 2 * (1 / 4) - 4 * (1 / 4)^2 + (1 / 4)^3 + (1 / 4)^4
      else (4 - 6 * (1 / 4)) * (4 - 5 * (1 / 4))) + 1 ≤
    (if (1 / 4 : ℝ) ≤ (5 - Real.sqrt 17) / 2 then
      4 - 2 * (1 / 4) - 4 * (1 / 4)^2 + (1 / 4)^3 + (1 / 4)^4
      else (4 - 6 * (1 / 4)) * (4 - 5 * (1 / 4))) at hf
  linarith only [hf]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1 / 4, (fun _ => 0)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_nonflat_middle_energy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_nonflat_middle_energy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_nonflat_middle_energy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_nonflat_middle_energy.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_nonflat_middle_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => p.1 * ((∑ i, p.2 i) + (∑ i, d i)) + (∑ i, (p.2 i) ^ 2) + (∑ i, (d i) ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_psd_nonflat_middle_energy

namespace actual_psd_small_jump_defect_bound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _N : ℕ, Σ _j : ℝ, Σ _w : ℝ, Fin 5 → ℝ)
    (fun _ => Fin 9 → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p d => (2 + p.2.2.1) * ((p.1 : ℝ) + p.2.2.1 * p.2.1 + (∑ i, p.2.2.2 i) - (∑ i, d i)) - (1 + p.2.2.1) * p.1 +
      (p.2.2.1 * ((∑ i, p.2.2.2 i) + (∑ i, d i)) + (∑ i, (p.2.2.2 i) ^ 2) + (∑ i, (d i) ^ 2))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p d => target p.1 * ((p.1 : ℝ) + p.2.2.1 * p.2.1 + (∑ i, p.2.2.2 i) - (∑ i, d i)) ^ 2 + 1) (fun e => nomatch e)
/-- The natural dimension, real j,w, fourteen real defects and all hypotheses are unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (hN : 56 ≤ N) (j w : ℝ)
    (hj : 6 ≤ j) (hw : 0 ≤ w) (hw1 : w ≤ 1 / 4)
    (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4 - 6 * w)
    (hK : (!![2 * (1 - d 8), -(w + h 0 + d 7), -(w + h 1 + d 5);
                -(w + h 0 + d 7), 2 * (1 - d 6), -(w + h 2 + d 4);
                -(w + h 1 + d 5), -(w + h 2 + d 4), 2 * (1 - d 3)] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef),
    O.readout () ⟨N,j,w,h⟩ d ≤
      target N * ((N : ℝ) + w * j + (∑ i, h i) - (∑ i, d i)) ^ 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hf := hall 56 (by norm_num) 6 0 (by norm_num) (by norm_num) (by norm_num)
    0 0 (by intro i j hij; simp) (by intro i; simp)
    (by intro i j hij; simp) (by intro i; norm_num) (by norm_num)
    (by simpa using zero_defect_psd 0 (by norm_num) (by norm_num))
  change target 56 * ((56 : ℝ) + 0 * 6 + (∑ _i : Fin 5, (0 : ℝ)) -
      (∑ _i : Fin 9, (0 : ℝ))) ^ 2 + 1 ≤
    target 56 * ((56 : ℝ) + 0 * 6 + (∑ _i : Fin 5, (0 : ℝ)) -
      (∑ _i : Fin 9, (0 : ℝ))) ^ 2 at hf
  linarith only [hf]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨56,6,0,(fun _ => 0)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_small_jump_defect_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_small_jump_defect_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.actual_psd_small_jump_defect_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_small_jump_defect_bound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment.actual_psd_small_jump_defect_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => (2 + p.2.2.1) * ((p.1 : ℝ) + p.2.2.1 * p.2.1 + (∑ i, p.2.2.2 i) - (∑ i, d i)) - (1 + p.2.2.1) * p.1 +
      (p.2.2.1 * ((∑ i, p.2.2.2 i) + (∑ i, d i)) + (∑ i, (p.2.2.2 i) ^ 2) + (∑ i, (d i) ^ 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
    definition := none
    coordinates := #[0, 2, 3, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end actual_psd_small_jump_defect_bound

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
