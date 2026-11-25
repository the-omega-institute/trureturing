import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicParityLimit

/-! The coefficient of the parity limit depends on its normalizer. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicParityLimit

open Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityLimit
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ Z => 2 / Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lam : ℝ), 0 < lam →
    let factor := R.readout () ()
    let m := lam / (8 * Real.pi ^ 2)
    ∃ (n : ℕ) (t Z : ℝ) (w : ℤ → ℝ), 0 < n ∧
      ((n : ℝ) ^ 2 - 1) / 5 ≤ m ∧ m < (n : ℝ) * (n + 2) / 5 ∧
      Activation m n t Z w ∧
      ∀ odd : Bool, ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        let q := 2 * k + if odd then 1 else 2
        letI : NeZero q := ⟨by cases odd <;> simp [q]⟩
        let a := 1 - lam / (q : ℝ) ^ 2
        let d : ℝ := if odd then 1 / 2 else 0
        let L := ∑' j : ℤ, w j ^ 2
        let m₄ := ∑' j : ℤ, (j : ℝ) ^ 4 * w j
        let coefficient := factor Z * ((t - d ^ 2) * (3 * lam / 8) + (4 * Real.pi ^ 2 / 3) * m₄)
        (∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v) ∧
        ∀ v ∈ feasible q a, IsMinOn energy (feasible q a) v →
          |(q : ℝ) ^ 2 * (L - energy v) - coefficient| < ε

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  obtain ⟨n, t, Z, w, hn, hlo, hhi, act, hlim⟩ := H 1 (by norm_num)
  let m := (1 : ℝ) / (8 * Real.pi ^ 2)
  let m₄ := ∑' j : ℤ, (j : ℝ) ^ 4 * w j
  let c := t * (3 / 8) + (4 * Real.pi ^ 2 / 3) * m₄
  have ht : 0 < t := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (sq_pos_of_pos hn').trans_le act.radius_lower
  have hm₄ : 0 ≤ m₄ := tsum_nonneg fun j => mul_nonneg (by positivity) (act.nonneg j)
  have hc : 0 < c := by
    unfold c
    exact add_pos_of_pos_of_nonneg (mul_pos ht (by norm_num)) (mul_nonneg (by positivity) hm₄)
  obtain ⟨k, hk, h⟩ := ((eventually_ge_atTop n).and
    (hlim false (c / 2) (half_pos hc))).exists
  let q := 2 * k + 2
  have hfit : 2 * latticeSupportRadius n m < q := by
    unfold latticeSupportRadius q
    split <;> omega
  obtain ⟨t', Z', w', act', _, v, hv, hmin, hgap, _, _⟩ :=
    cyclic_to_lattice_comparison q n hn 1 hfit hlo hhi.le
  obtain ⟨a, _, hu⟩ :=
    (exists_lattice_square_moment_minimizer_on_interval n hn m).mp ⟨hlo, hhi.le⟩
  have he : (t', Z', w') = (t, Z, w) := (hu _ act').trans (hu _ act).symm
  have hw : w' = w := congrArg (fun p : ℝ × ℝ × (ℤ → ℝ) => p.2.2) he
  rw [hw] at hgap
  have hx : |(q : ℝ) ^ 2 * ((∑' j, w j ^ 2) - energy v) + c| < c / 2 := by
    have hh := h.2 v hv hmin
    change |(q : ℝ) ^ 2 * ((∑' j, w j ^ 2) - energy v) -
      rejected.readout () () Z * ((t - (if false = true then 1 / 2 else 0 : ℝ) ^ 2) *
        (3 * 1 / 8) + (4 * Real.pi ^ 2 / 3) * m₄)| < c / 2 at hh
    have he : rejected.readout () () Z * ((t - (if false = true then 1 / 2 else 0 : ℝ) ^ 2) *
        (3 * 1 / 8) + (4 * Real.pi ^ 2 / 3) * m₄) = -c := by
      simp [c, rejected, realize]
    rwa [he, sub_neg_eq_add] at hh
  linarith only [(abs_lt.mp hx).2, mul_nonneg (sq_nonneg (q : ℝ)) hgap, hc]

def evidence : Registration arena (type_of% @cyclic_parity_correction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_parity_correction, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_parity_correction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityLimit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityLimit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicParityLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicParityLimit
