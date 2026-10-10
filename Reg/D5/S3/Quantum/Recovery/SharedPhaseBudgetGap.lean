import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.SharedPhaseBudgetGap
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.SharedPhaseBudgetGap
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix Complex Finset
open scoped ComplexOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap

namespace Compressed

abbrev signature : Signature where
  Params := ℕ
  State m := Fin m → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => ∑ j, p j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4/(3-2*Real.sqrt 2)) (fun e => nomatch e)

def sourceStatement : Prop := ∃ gamma : ℝ, 0<gamma ∧
    ∀ (m : ℕ) (_ : 1≤m) (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
      (∀ j, 0≤p j) → (∀ j k, ‖z j k‖=1) →
      (M-∑ j, p j • Matrix.vecMulVec (B.mulVec (z j)) (star (B.mulVec (z j)))).PosSemidef →
      (∑ j, p j) ≤ 4/(3-2*Real.sqrt 2)-gamma

def arena : Arena where
  signature := signature
  Law R := ∃ gamma : ℝ, 0<gamma ∧
    ∀ (m : ℕ) (_ : 1≤m) (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
      (∀ j, 0≤p j) → (∀ j k, ‖z j k‖=1) →
      (M-∑ j, p j • Matrix.vecMulVec (B.mulVec (z j)) (star (B.mulVec (z j)))).PosSemidef →
      R.readout () m p ≤ 4/(3-2*Real.sqrt 2)-gamma

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨g,hg,h⟩
  have hm : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose B
  have hb := h 1 (by omega) (fun _ => 0) (fun _ _ => 1)
    (by simp) (by simp) (by simpa using hm)
  change 4/(3-2*Real.sqrt 2) ≤ 4/(3-2*Real.sqrt 2)-g at hb
  linarith

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_hop_original,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ),(fun _ => 0),(fun _ => 1),?_⟩
    change (∑ _ : Fin 1, (0 : ℝ)) ≠ ∑ _ : Fin 1, (1 : ℝ)
    norm_num

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.first_hop_original)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ p => ∑ j, p j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.first_hop_original.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.Compressed.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ p => ∑ j, p j) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.SharedPhaseBudgetGap,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Compressed

namespace PhaseCone

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 4) (Fin 4) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ C => eta C) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def sourceStatement : Prop := ∃ gamma : ℝ, 0 < gamma ∧
    ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      0 ∈ phaseMasses (noisyCorrelation epsilon) ∧
      BddAbove (phaseMasses (noisyCorrelation epsilon)) ∧
      IsLUB (phaseMasses (noisyCorrelation epsilon)) (eta (noisyCorrelation epsilon)) ∧
      0 ≤ eta (noisyCorrelation epsilon) ∧
      eta (noisyCorrelation epsilon) ≤ (4/(3-2*Real.sqrt 2)-gamma)*epsilon

def arena : Arena where
  signature := signature
  Law R := ∃ gamma : ℝ, 0 < gamma ∧
    ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      0 ∈ phaseMasses (noisyCorrelation epsilon) ∧
      BddAbove (phaseMasses (noisyCorrelation epsilon)) ∧
      IsLUB (phaseMasses (noisyCorrelation epsilon)) (eta (noisyCorrelation epsilon)) ∧
      0 ≤ eta (noisyCorrelation epsilon) ∧
      R.readout () () (noisyCorrelation epsilon) ≤ (4/(3-2*Real.sqrt 2)-gamma)*epsilon

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨g,_,h⟩
  have hb := (h 0 (by norm_num) (by norm_num)).2.2.2.2
  change (1 : ℝ) ≤ (4/(3-2*Real.sqrt 2)-g)*0 at hb
  norm_num at hb

private theorem mass_le_diag (C : Matrix (Fin 4) (Fin 4) ℂ) {t : ℝ}
    (ht : t ∈ phaseMasses C) : t ≤ (C 0 0).re := by
  rcases ht with ⟨m,_,p,z,_,hz,hP,rfl⟩
  have hd := (Complex.nonneg_iff.mp (hP.diag_nonneg (i := 0))).1
  have hterm (j : Fin m) : (p j • Matrix.vecMulVec (z j) (star (z j))) 0 0 = (p j : ℂ) := by
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.star_def, Complex.real_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hz, one_pow, Complex.ofReal_one, mul_one]
  simp only [Matrix.sub_apply, Matrix.sum_apply, hterm, Complex.sub_re,
    Complex.re_sum, Complex.ofReal_re] at hd
  linarith only [hd]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let J : Matrix (Fin 4) (Fin 4) ℂ := Matrix.vecMulVec (fun _ => 1) (fun _ => 1)
  obtain ⟨_,_,h⟩ := eta_strict_improvement
  have hzero := h 0 (by norm_num) (by norm_num)
  have hz : eta (noisyCorrelation 0) = 0 := by
    have hu := hzero.2.2.2.2
    simp only [mul_zero] at hu
    exact le_antisymm hu hzero.2.2.2.1
  have hone : (1 : ℝ) ∈ phaseMasses J := by
    refine ⟨1,le_rfl,(fun _ => 1),(fun _ _ => 1),?_,?_,?_,?_⟩
    · simp
    · simp
    · simpa [J, Pi.star_def] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef)
    · simp
  have hbounded : BddAbove (phaseMasses J) := ⟨(J 0 0).re,fun _ ht => mass_le_diag J ht⟩
  have hlow : 1 ≤ eta J := le_csSup hbounded hone
  refine ⟨(),noisyCorrelation 0,J,?_⟩
  change eta (noisyCorrelation 0) ≠ eta J
  rw [hz]
  linarith only [hlow]

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eta_strict_improvement,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.eta_strict_improvement)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ C => eta C) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.eta_strict_improvement.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap.PhaseCone.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ C => eta C) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.SharedPhaseBudgetGap,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end PhaseCone
end Reg.D5.S3.Quantum.Recovery.SharedPhaseBudgetGap
