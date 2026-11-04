import D5.S3.Combinatorics.Probability.CdsoCapacityCertificate
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Registration of the full same-law capacity statement. -/

open _root_.D5.S3.Combinatorics.Probability.CdsoCapacityCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped BigOperators
noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Probability.CdsoCapacityCertificate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun a => Atom a → ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ mass => energy mass)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (mass : Atom a → ℝ)
    (hnonneg : ∀ T, 0 ≤ mass T) (htotal : ∑ T, mass T = 1)
    (hmean : ∑ T, mass T * (T.val.card : ℝ) = (a + 1 : ℝ) - δ)
    (hdense : ∀ i, threshold a δ ≤ marginal mass i)
    (hsort : Antitone (marginal mass)),
    let y := marginal mass
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    let u := (y z + y o) / 2
    let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
    (∀ T : Finset (Fin (a + 2)), T.Nonempty →
      0 ≤ residual (weight y) (weight y t) T ∧
        (residual (weight y) (weight y t) T = 0 ↔
          (T.card = a + 1 ∧ ∃ i, univ \ T = {i} ∧ y i ≤ y t) ∨
          (T.card = a ∧ ∃ i j, i ≠ j ∧ univ \ T = {i, j} ∧ y t ≤ y i ∧ y t ≤ y j))) ∧
      v = groupedV a δ u (y t) ∧ Omega a δ u (y t) ∧
      max (F0 a δ u (y t)) (F1 a δ u (y t)) ≤ energy mass ∧
      (energy mass = F1 a δ u (y t) →
        y z = u ∧ y o = u ∧ (∀ i ∈ tailSet a, y i = v) ∧
          ∀ T : Atom a, 0 < mass T → residual (weight y) (weight y t) T.val = 0) ∧
      R.readout () a mass = linearPart δ y (weight y t) +
        ∑ T : Atom a, mass T * residual (weight y) (weight y t) T.val

private def fullAtom (a : ℕ) : Atom a :=
  ⟨univ, ⟨⟨0, by omega⟩, Finset.mem_univ _⟩⟩
private def shortAtom : Atom 4096 :=
  ⟨univ \ {⟨4096, by decide⟩, ⟨4097, by decide⟩}, by
    refine ⟨⟨0, by decide⟩, ?_⟩
    simp [Fin.ext_iff]⟩
private def dirac {a : ℕ} (A : Atom a) (p : ℝ) : Atom a → ℝ :=
  fun T => if T = A then p else 0
private def p : ℝ := 4095 / 8192
private def trialMass : Atom 4096 → ℝ :=
  fun T => dirac (fullAtom 4096) p T + dirac shortAtom (1 - p) T

private lemma dirac_total {a : ℕ} (A : Atom a) (p : ℝ) :
    (∑ T, dirac A p T) = p := by simp [dirac]
private lemma dirac_mean {a : ℕ} (A : Atom a) (p : ℝ) :
    (∑ T, dirac A p T * (T.val.card : ℝ)) = p * A.val.card := by
  simp [dirac, ite_mul]
private lemma dirac_marginal {a : ℕ} (A : Atom a) (p : ℝ) (i : Fin (a + 2)) :
    marginal (dirac A p) i = if i ∈ A.val then p else 0 := by
  unfold marginal
  have he (T : Atom a) : (if i ∈ T.val then dirac A p T else 0) =
      if T = A then (if i ∈ A.val then p else 0) else 0 := by
    by_cases h : T = A
    · subst T; simp [dirac]
    · simp [dirac, h]
  simp_rw [he]
  simp
private lemma marginal_add {a : ℕ} (x z : Atom a → ℝ) (i : Fin (a + 2)) :
    marginal (fun T => x T + z T) i = marginal x i + marginal z i := by
  unfold marginal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> ring
private lemma trial_marginal (i : Fin 4098) :
    marginal trialMass i = if i ∈ shortAtom.val then 1 else p := by
  unfold trialMass
  rw [marginal_add, dirac_marginal, dirac_marginal]
  simp only [fullAtom, Finset.mem_univ, ite_true]
  split_ifs <;> ring
private lemma short_mem (i : Fin 4098) : i ∈ shortAtom.val ↔ i.val < 4096 := by
  simp only [shortAtom, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have := i.isLt
  omega
private lemma trial_nonneg (T : Atom 4096) : 0 ≤ trialMass T := by
  unfold trialMass dirac
  split_ifs <;> norm_num [p]
private lemma trial_total : (∑ T, trialMass T) = 1 := by
  simp only [trialMass, Finset.sum_add_distrib, dirac_total]
  ring
private lemma trial_mean : (∑ T, trialMass T * (T.val.card : ℝ)) =
    (4096 + 1 : ℝ) - 1 / 4096 := by
  simp only [trialMass, add_mul, Finset.sum_add_distrib, dirac_mean]
  norm_num [fullAtom, shortAtom, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Fin.ext_iff, p]
private lemma trial_dense (i : Fin 4098) :
    threshold 4096 (1 / 4096) ≤ marginal trialMass i := by
  rw [trial_marginal]
  split_ifs <;> norm_num [threshold, p]
private lemma trial_sorted : Antitone (marginal trialMass) := by
  intro i j hij
  simp only [trial_marginal, short_mem]
  have hv : i.val ≤ j.val := hij
  by_cases hj : j.val < 4096
  · have hi : i.val < 4096 := lt_of_le_of_lt hv hj
    simp [hi, hj]
  · by_cases hi : i.val < 4096 <;> norm_num [hi, hj, p]
private lemma energy_nonneg {a : ℕ} (mass : Atom a → ℝ) (h : ∀ T, 0 ≤ mass T) :
    0 ≤ energy mass := by
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (mul_nonneg (h T) (sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (a := 4096) (by decide) (δ := 1 / 4096) (by norm_num)
    (by norm_num) trialMass trial_nonneg trial_total trial_mean trial_dense trial_sorted
  have hg := capacity_lemma (a := 4096) (by decide) (δ := 1 / 4096) (by norm_num)
    (by norm_num) trialMass trial_nonneg trial_total trial_mean trial_dense trial_sorted
  have hb' := hb.2.2.2.2.2
  have hg' := hg.2.2.2.2.2
  change (-1 : ℝ) = _ at hb'
  linarith [energy_nonneg trialMass trial_nonneg]

private lemma energy_zero (a : ℕ) : energy (fun _ : Atom a => (0 : ℝ)) = 0 := by
  simp [energy]
private lemma energy_full (a : ℕ) : energy (dirac (fullAtom a) 1) = (a + 2 : ℝ) ^ 3 := by
  have hm (i : Fin (a + 2)) : marginal (dirac (fullAtom a) 1) i = 1 := by
    rw [dirac_marginal]; simp [fullAtom]
  unfold energy weight
  simp_rw [hm]
  simp only [inv_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [dirac, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [fullAtom]
  ring
private lemma actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, (fun _ => 0), dirac (fullAtom 0) 1, ?_⟩
  change energy (fun _ : Atom 0 => (0 : ℝ)) ≠ energy (dirac (fullAtom 0) 1)
  rw [energy_zero, energy_full]
  norm_num

def evidence : Registration arena (type_of% @capacity_lemma) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@capacity_lemma, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    @capacity_lemma (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Probability.CdsoCapacityCertificate.capacity_lemma.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Probability.CdsoCapacityCertificate.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ mass => energy mass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Probability.CdsoCapacityCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg",
        "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 5
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
end Reg.D5.S3.Combinatorics.Probability.CdsoCapacityCertificate
