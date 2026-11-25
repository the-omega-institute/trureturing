import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicSupportCertificate

/-! The support readout records strict positivity of the indicated weights. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => max 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace Boundary

universe u

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ) (j : ι)
    (_hmax : ∀ i, x i ≤ x j)
    (a b g : ℝ) (_hg : 0 ≤ g)
    (_hmass : ∑ i, (a + b * x i + g * x i ^ 2) = 0)
    (_hmoment : 0 < ∑ i, x i * (a + b * x i + g * x i ^ 2)),
    let clip := R.readout () ()
    0 < clip (a + b * x j + g * x j ^ 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let x : ULift.{u} (Fin 2) → ℝ := fun i => i.down.val
  let last : ULift.{u} (Fin 2) := ⟨1⟩
  have hmax (i : ULift.{u} (Fin 2)) : x i ≤ x last := by
    rcases i with ⟨i⟩
    fin_cases i <;> norm_num [x, last]
  have hsum (f : ℝ → ℝ) : (∑ i, f (x i)) = f 0 + f 1 := by
    rw [Fintype.sum_equiv Equiv.ulift (fun i => f (x i)) (fun i : Fin 2 => f i.val)
      (fun _ => rfl), Fin.sum_univ_two]
    norm_num
  have hmass : ∑ i, (-1 + 2 * x i + 0 * x i ^ 2) = 0 := by
    rw [hsum (fun z => -1 + 2 * z + 0 * z ^ 2)]
    norm_num
  have hmoment : 0 < ∑ i, x i * (-1 + 2 * x i + 0 * x i ^ 2) := by
    rw [hsum (fun z => z * (-1 + 2 * z + 0 * z ^ 2))]
    norm_num
  exact (lt_irrefl _) (h (ι := ULift.{u} (Fin 2)) x last hmax
    (-1) 2 0 le_rfl hmass hmoment)

def evidence : Registration arena.{u} (type_of% @boundary_variation_pos.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_variation_pos.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@boundary_variation_pos.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate.Boundary.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate.Boundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Boundary

namespace Dual

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] {threshold s a b g lo hi : ℝ}
    {sites : Finset (ZMod q)} (_hs : 0 < s) (_hb : b ≤ 0) (_hg : g ≤ 0)
    (_hlo : a + b * (1 - lo) + g * ((1 - lo ^ 2) / s) ≤ 0)
    (_hhi : a + b * (1 - hi) + g * ((1 - hi ^ 2) / s) ≤ 0)
    (_hbetween : ∀ i ∉ sites, lo ≤ sample i ∧ sample i ≤ hi),
    let clip := R.readout () ()
    let p := fun i : ZMod q => a + b * (1 - sample i) + g * ((1 - sample i ^ 2) / s)
    let v := fun i : ZMod q => if i ∈ sites then p i else 0
    (∀ i ∈ sites, 0 < p i) →
    (∑ i, v i) = 1 →
    cosineMoment 1 v = threshold →
    cosineMoment 2 v = threshold →
    v ∈ feasible q threshold ∧
      (∀ w ∈ feasible q threshold, w ≠ v → energy v < energy w) ∧
      (∀ w ∈ feasible q threshold, energy v + (∑ i, (w i - v i) ^ 2) ≤ energy w) ∧
      ∀ w ∈ feasible q threshold, IsMinOn energy (feasible q threshold) w →
        ∀ i, 0 < clip (w i) ↔ i ∈ sites

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let q := 1
  have : NeZero q := ⟨by decide⟩
  let sites : Finset (ZMod q) := univ
  let v : ZMod q → ℝ := fun _ => 1
  have hone (i : ZMod q) : i = 0 := Subsingleton.elim _ _
  have hc (i : ZMod q) : sample i = 1 := by
    rw [hone i]
    simp [sample, centeredAngle]
  have hM (r : ℕ) : cosineMoment r v = 1 := by
    rw [cosineMoment_eq_centered]
    have hzero (i : ZMod q) : centeredAngle i = 0 := by rw [hone i]; simp [centeredAngle]
    simp only [v, hzero, mul_zero, Real.cos_zero, sum_const, nsmul_eq_mul,
      card_univ, ZMod.card, Nat.cast_one, q, mul_one]
  let p : ZMod q → ℝ := fun i => 1 + 0 * (1 - sample i) + (-2) * ((1 - sample i ^ 2) / 1)
  have hp (i : ZMod q) : p i = 1 := by simp [p, hc]
  have hv : (fun i : ZMod q => if i ∈ sites then p i else 0) = v := by
    funext i
    simpa only [sites, mem_univ, ite_true, v] using hp i
  have hraw := h (q := q) (threshold := 1) (s := 1) (a := 1) (b := 0) (g := -2)
    (lo := 0) (hi := 0) (sites := sites) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun i hi => (hi (mem_univ i)).elim)
    (fun i _ => by change 0 < p i; rw [hp]; exact zero_lt_one)
    (by rw [hv]; simp only [v, sum_const, nsmul_eq_mul, card_univ, ZMod.card, q,
      Nat.cast_one, mul_one]) (by rw [hv]; exact hM 1) (by rw [hv]; exact hM 2)
  have hfit : v ∈ feasible q 1 := by
    rw [← hv]
    exact hraw.1
  have hmin : IsMinOn energy (feasible q 1) v := by
    intro w hw
    by_cases he : w = v
    · subst w
      change energy v ≤ energy v
      exact le_rfl
    · have hlt := hraw.2.1 w hw (by rwa [hv])
      rw [hv] at hlt
      exact hlt.le
  exact (lt_irrefl _) ((hraw.2.2.2 v hfit hmin 0).mpr (mem_univ _))

def evidence : Registration arena (type_of% @exact_support_of_dual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_support_of_dual, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exact_support_of_dual) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate.Dual.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate.Dual.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dual

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
