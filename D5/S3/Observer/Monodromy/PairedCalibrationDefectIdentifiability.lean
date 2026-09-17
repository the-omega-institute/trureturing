/- GID: D5/S3/Observer/Monodromy/PairedCalibrationDefectIdentifiability
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/PairedCalibrationDefectIdentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A sharp calibration-ratio defect exactly characterizes uniform decoding of the complete paired record matrix. -/

import D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
import Mathlib.Tactic

/-!
# Sharp identification with imperfectly paired calibration

Both copies use the existing actual two-pulse records, but their detector gains,
offsets and pulse gains may differ. The paired matrix retains weighted products
of records from the same acquisition block. The error budget is imposed on an
explicit weighted sum of squared cross-ratio defects, not on a desired decoder.

A single decoder of the complete 4-by-4 matrix works for all finite admissible
ensembles exactly when cLo^2 < (1-eta)cHi^2. Sufficiency constructs that decoder.
Necessity constructs a four-block ensemble and a one-block ensemble with the
same complete matrix at the critical defect. It excludes every deterministic
nonlinear matrix decoder, not merely a fixed quadratic statistic.

Gaussian output measures, conditional independence of physical replicas and
finite-sample probability bounds are not formalized in this algebraic source.
The collision is for the paired second-moment matrix, not for the full paired
probability law. No claim of global novelty is made.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.PairedCalibrationDefectIdentifiability

open D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
open D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography
open D5.S3.Observer.Monodromy.TransvectionLieFiltration

/-- Primitive calibration parameters of one independently prepared copy. -/
structure Calibration where
  gain : ℝ
  offset : ℝ
  first : ℝ
  second : ℝ

/-- Positivity needed for physical variance records. -/
def Positive (p : Calibration) : Prop :=
  0 < p.gain ∧ 0 ≤ p.offset ∧ 0 < p.first ∧ 0 < p.second

/-- Actual cross-setting second moments under a finite acquisition ensemble. -/
def pairedMatrix {n : ℕ} (c : ℝ) (w : Fin n → ℝ)
    (left right : Fin n → Calibration) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ∑ r, w r *
    records c (left r).gain (left r).offset (left r).first (left r).second i *
    records c (right r).gain (right r).offset (right r).first (right r).second j

/-- Signal weight of a paired ensemble. It is positive on admissible ensembles. -/
def pairMass {n : ℕ} (w : Fin n → ℝ) (left right : Fin n → Calibration) : ℝ :=
  ∑ r, w r * (left r).gain * (right r).gain *
    (((left r).first * (right r).second)^2 +
      ((right r).first * (left r).second)^2)

/-- Only relative pulse-ratio mismatch contributes to the exact pairing defect. -/
def pairDefect {n : ℕ} (w : Fin n → ℝ) (left right : Fin n → Calibration) : ℝ :=
  ∑ r, w r * (left r).gain * (right r).gain *
    ((left r).first * (right r).second - (right r).first * (left r).second)^2

/-- An independently specified weighted defect budget, not a claim about outputs. -/
def AdmissiblePair {n : ℕ} (eta : ℝ) (w : Fin n → ℝ)
    (left right : Fin n → Calibration) : Prop :=
  (∀ r, 0 ≤ w r ∧ Positive (left r) ∧ Positive (right r)) ∧
    0 < ∑ r, w r ∧ pairDefect w left right ≤ eta * pairMass w left right

/-- d-transpose M d, where d=(1,-1,-1,1). -/
def pairNumerator (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (M 3 3-M 1 3-M 2 3+M 0 3) - (M 3 1-M 1 1-M 2 1+M 0 1) -
    (M 3 2-M 1 2-M 2 2+M 0 2) + (M 3 0-M 1 0-M 2 0+M 0 0)

/-- a-transpose M b + b-transpose M a, with a=(-1,1,0,0), b=(-1,0,1,0). -/
def pairDenominator (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (M 1 2-M 1 0-M 0 2+M 0 0) + (M 2 1-M 2 0-M 0 1+M 0 0)

def pairedContrast (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  pairNumerator M / pairDenominator M

/-- Sharp all-decoder identification, with an actual complete-matrix collision
when the budget is too large. No coordinate box, identical detector gains or
identical offsets between the copies is assumed. -/
theorem uniform_paired_decoder_iff (cLo cHi eta : ℝ)
    (hLo : 0 < cLo) (hLH : cLo < cHi) (hEta : 0 ≤ eta) (hEta1 : eta < 1) :
    (∃ decoder : Matrix (Fin 4) (Fin 4) ℝ → Bool,
      ∀ (n : ℕ) (w : Fin n → ℝ) (left right : Fin n → Calibration),
        AdmissiblePair eta w left right →
        decoder (pairedMatrix cLo w left right) = false ∧
        decoder (pairedMatrix cHi w left right) = true) ↔
      cLo^2 < (1-eta)*cHi^2 := by
  classical
  have hHi : 0 < cHi := hLo.trans hLH
  have ray (s t : ℝ) : controlledDirection s t = ![1, s, 0, t] := by
    ext i
    fin_cases i <;>
      norm_num [controlledDirection, dualPulse, increment, pairing,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
  have variance (c s t : ℝ) : outputVariance c s t =
      1+s^2+2*c*s*t+2*t^2 := by
    simp [outputVariance, ray, covariance, Fin.sum_univ_succ] <;> ring
  have rec (c g o s t : ℝ) : records c g o s t =
      ![o+g, o+g+g*s^2, o+g+2*g*t^2,
        o+g+g*s^2+2*c*g*s*t+2*g*t^2] := by
    ext k
    fin_cases k <;> simp [records, variance] <;> ring

  have read_mass (n : ℕ) (c : ℝ) (w : Fin n → ℝ)
      (left right : Fin n → Calibration) :
      pairDenominator (pairedMatrix c w left right) = 2*pairMass w left right := by
    simp only [pairDenominator, pairedMatrix, pairMass, rec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have read_defect (n : ℕ) (c : ℝ) (w : Fin n → ℝ)
      (left right : Fin n → Calibration) :
      pairNumerator (pairedMatrix c w left right) =
        2*c^2*(pairMass w left right-pairDefect w left right) := by
    simp only [pairNumerator, pairedMatrix, pairMass, pairDefect, rec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

  have bounds (n : ℕ) (c : ℝ) (w : Fin n → ℝ)
      (left right : Fin n → Calibration) (ha : AdmissiblePair eta w left right) :
      (1-eta)*c^2 ≤ pairedContrast (pairedMatrix c w left right) ∧
        pairedContrast (pairedMatrix c w left right) ≤ c^2 := by
    rcases ha with ⟨hpos, htotal, hbudget⟩
    have hterm (r : Fin n) : 0 ≤ w r*(left r).gain*(right r).gain *
        (((left r).first*(right r).second)^2 +
          ((right r).first*(left r).second)^2) := by
      rcases hpos r with ⟨hw, ⟨hgL, hoL, hsL, htL⟩, ⟨hgR, hoR, hsR, htR⟩⟩
      positivity
    have hsome : ∃ r, 0 < w r := by
      by_contra h
      push_neg at h
      have hz : (∑ r, w r) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        exact le_antisymm (h r) (hpos r).1
      linarith
    obtain ⟨r, hr⟩ := hsome
    have hstrict : 0 < w r*(left r).gain*(right r).gain *
        (((left r).first*(right r).second)^2 +
          ((right r).first*(left r).second)^2) := by
      rcases hpos r with ⟨hw, ⟨hgL, hoL, hsL, htL⟩, ⟨hgR, hoR, hsR, htR⟩⟩
      positivity
    have hmass : 0 < pairMass w left right :=
      lt_of_lt_of_le hstrict
        (Finset.single_le_sum (fun r _ => hterm r) (Finset.mem_univ r))
    have hdefect : 0 ≤ pairDefect w left right := by
      apply Finset.sum_nonneg
      intro r _
      rcases hpos r with ⟨hw, ⟨hgL, hoL, hsL, htL⟩, ⟨hgR, hoR, hsR, htR⟩⟩
      positivity
    unfold pairedContrast
    rw [read_mass, read_defect]
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 2*pairMass w left right)).mpr
      have he := mul_le_mul_of_nonneg_left hbudget (sq_nonneg c)
      nlinarith
    · apply (div_le_iff₀ (by positivity : 0 < 2*pairMass w left right)).mpr
      have he := mul_nonneg (sq_nonneg c) hdefect
      nlinarith

  constructor
  · rintro ⟨decoder, hdecoder⟩
    by_contra hfail
    have hfail' : (1-eta)*cHi^2 ≤ cLo^2 := le_of_not_gt hfail
    let x := (cHi-cLo)/(cHi+cLo)
    have hsum : 0 < cHi+cLo := add_pos hHi hLo
    have hx0 : 0 < x := div_pos (sub_pos.mpr hLH) hsum
    have hx1 : x < 1 := by
      apply (div_lt_one hsum).mpr
      linarith
    let d := Real.sqrt x
    let a := Real.sqrt (1+x)
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hd2 : d^2 = x := Real.sq_sqrt hx0.le
    have hd1 : d < 1 := by nlinarith
    have ha2 : a^2 = 1+x := Real.sq_sqrt (by linarith : 0 ≤ 1+x)
    have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith : 0 < 1+x)
    have hminus : 0 < 1-d := by linarith
    have hplus : 0 < 1+d := by linarith
    have hx : (cHi+cLo)*x = cHi-cLo := by
      dsimp [x]
      field_simp [ne_of_gt hsum]
    have hbridge : cHi*(1-x) = cLo*(1+x) := by nlinarith
    have hbridge2 : cHi^2*(1-x)^2 = cLo^2*(1+x)^2 := by
      calc
        _ = (cHi*(1-x))^2 := by ring
        _ = (cLo*(1+x))^2 := by rw [hbridge]
        _ = _ := by ring
    have hscaled := mul_le_mul_of_nonneg_right hfail' (sq_nonneg (1+x))
    have hbudget : 8*x ≤ eta*(2*(1+x)^2) := by
      apply (mul_le_mul_left (sq_pos_of_pos hHi)).mp
      nlinarith [hscaled, hbridge2]

    let p : Calibration := ⟨1, 0, 1-d, 1+d⟩
    let q : Calibration := ⟨1, 0, 1+d, 1-d⟩
    let z : Calibration := ⟨1, 0, a, a⟩
    let wH : Fin 4 → ℝ := ![1/4, 1/4, 1/4, 1/4]
    let lH : Fin 4 → Calibration := ![p, p, q, q]
    let rH : Fin 4 → Calibration := ![p, q, p, q]
    let wL : Fin 1 → ℝ := fun _ => 1
    let lL : Fin 1 → Calibration := fun _ => z
    let rL : Fin 1 → Calibration := fun _ => z
    have hmH : pairMass wH lH rH = 2*(1+x)^2 := by
      calc
        _ = 2*(1+d^2)^2 := by
          norm_num [pairMass, wH, lH, rH, p, q, Fin.sum_univ_succ] <;> ring
        _ = _ := by rw [hd2]
    have heH : pairDefect wH lH rH = 8*x := by
      calc
        _ = 8*d^2 := by
          norm_num [pairDefect, wH, lH, rH, p, q, Fin.sum_univ_succ] <;> ring
        _ = _ := by rw [hd2]
    have hadmH : AdmissiblePair eta wH lH rH := by
      refine ⟨?_, ?_, ?_⟩
      · intro r
        fin_cases r <;>
          simp [wH, lH, rH, p, q, Positive, hminus, hplus]
      · norm_num [wH, Fin.sum_univ_succ]
      · rw [hmH, heH]
        exact hbudget
    have hadmL : AdmissiblePair eta wL lL rL := by
      refine ⟨?_, ?_, ?_⟩
      · intro r
        simp [wL, lL, rL, z, Positive, ha0]
      · norm_num [wL, Fin.sum_univ_succ]
      · simp [pairDefect, pairMass, wL, lL, rL, z, Fin.sum_univ_succ]
        <;> positivity

    have avg (k : Fin 4) :
        (records cHi 1 0 (1-d) (1+d) k +
          records cHi 1 0 (1+d) (1-d) k)/2 = records cLo 1 0 a a k := by
      have he : (records cHi 1 0 (1-d) (1+d) k +
          records cHi 1 0 (1+d) (1-d) k)/2 =
          ![1, 2+d^2, 3+2*d^2, 4+3*d^2+2*cHi*(1-d^2)] k := by
        fin_cases k <;> simp [rec] <;> ring
      rw [he, hd2, rec]
      fin_cases k <;> norm_num <;> ring_nf <;> simp only [ha2] <;>
        nlinarith [hbridge]
    have hcollision : pairedMatrix cHi wH lH rH = pairedMatrix cLo wL lL rL := by
      ext i j
      calc
        _ = ((records cHi 1 0 (1-d) (1+d) i +
              records cHi 1 0 (1+d) (1-d) i)/2) *
            ((records cHi 1 0 (1-d) (1+d) j +
              records cHi 1 0 (1+d) (1-d) j)/2) := by
          norm_num [pairedMatrix, wH, lH, rH, p, q, Fin.sum_univ_succ] <;> ring
        _ = records cLo 1 0 a a i * records cLo 1 0 a a j := by rw [avg, avg]
        _ = _ := by
          simp [pairedMatrix, wL, lL, rL, z, Fin.sum_univ_succ]
    have hH := (hdecoder 4 wH lH rH hadmH).2
    have hL := (hdecoder 1 wL lL rL hadmL).1
    rw [hcollision, hL] at hH
    exact Bool.false_ne_true hH
  · intro hgap
    let tau := (cLo^2+(1-eta)*cHi^2)/2
    let decoder : Matrix (Fin 4) (Fin 4) ℝ → Bool :=
      fun M => if tau < pairedContrast M then true else false
    refine ⟨decoder, ?_⟩
    intro n w left right ha
    have hlo := (bounds n cLo w left right ha).2
    have hhi := (bounds n cHi w left right ha).1
    have hl : ¬ tau < pairedContrast (pairedMatrix cLo w left right) := by
      dsimp [tau]
      linarith
    have hh : tau < pairedContrast (pairedMatrix cHi w left right) := by
      dsimp [tau]
      linarith
    constructor
    · simp [decoder, hl]
    · simp [decoder, hh]

#print axioms uniform_paired_decoder_iff

end D5.S3.Observer.Monodromy.PairedCalibrationDefectIdentifiability
