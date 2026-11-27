import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Stieltjes.NoisyFirstAtom
import Reg.Support.SingleDependentReadout

/-! The lower enclosure depends on the supplied absolute normalization. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Stieltjes.NoisyFirstAtom
open LeanInformationAudit
namespace Reg.D5.S3.Analytic.Stieltjes.NoisyFirstAtom
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (p b y : ℕ → ℝ) (h S ε : ℝ)
    (_ : 0 < h) (_ : 0 < S) (_ : 0 < b 0) (_ : ∀ i, b 0 ≤ b i)
    (_ : ∀ i, 0 ≤ p i) (_ : HasSum p 1) (_ : 1 ≤ S * b 0 * p 0)
    (_ : y 0 = 1) (_ : ∀ j, 0 < j → j ≤ k →
      |y j - ∑' i, p i * b i / (b i + j * h)| ≤ ε),
    let D := difference k y / (k.factorial * h^k)
    let η := (2^k - 1) * ε / (k.factorial * h^k)
    1 ≤ R.readout () () S * b 0 * poleProduct k (b 0) h * (D + η) ∧
      poleProduct k (b 0) h * (D - η) ≤ 1

private theorem discarded_fails : ¬arena.Law discarded := by
  intro law
  have h := law 0 (fun i => if i = 0 then 1 else 0) (fun _ => 1) (fun _ => 1)
    1 1 0 zero_lt_one zero_lt_one zero_lt_one (fun _ => le_rfl) (fun i => by split <;> norm_num)
    (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) (by norm_num) rfl (fun _ hpos hle => by omega)
  have hfalse : (1 : ℝ) ≤ 0 := by simpa [discarded, realize] using h.1
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hfalse

def family : Registration arena (type_of% @noisy_first_atom_enclosure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨noisy_first_atom_enclosure, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), by change (0 : ℝ) ≠ 1; norm_num⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Stieltjes.NoisyFirstAtom.noisy_first_atom_enclosure) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Stieltjes.NoisyFirstAtom.unit
  realizationName := `Reg.D5.S3.Analytic.Stieltjes.NoisyFirstAtom.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Stieltjes.NoisyFirstAtom
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Analytic.Stieltjes.NoisyFirstAtom
