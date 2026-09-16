/- GID: D5/S3/Observer/Monodromy/DriftMixtureMomentIdentifiability
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/DriftMixtureMomentIdentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced drift mixtures admit one four-moment decoder exactly below a sharp bound, with an actual full-record collision beyond it. -/

import D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
import Mathlib.Tactic

/-!
# Sharp identifiability from four pooled moments under balanced calibration drift

Reuse the actual four experimental records from GainRobustGaussianDiscrimination.
A finite sum allows arbitrary calibration variation across acquisition slots.
Exposure weights are absorbed into `gain` and `offset`; all four setting classes
use the same weighted calibration ensemble. Randomized setting assignment
independent of exogenous calibration gives this model at the expectation level.
This equality of ensembles is an explicit assumption of the observational model,
not a statement about every finite randomized realization or setting-dependent drift.

The main theorem quantifies over every decoder of the complete four-real record,
not just threshold rules. Sufficiency constructs a normalized-moment threshold.
Necessity constructs a two-point high-correlation mixture and a constant
low-correlation calibration with identical complete four-moment records.

The reverse Cauchy--Schwarz estimate used inside the proof is classical
Polya--Szego/Cassels prior art. No separate novelty claim is made for it.
The application is a sharp observer-fiber classification for the specified
quantum-control candidate family. A moment collision is not equality of full
Gaussian-mixture laws, and no Gaussian measure or quantum state is formalized here.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.DriftMixtureMomentIdentifiability

open D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
open D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography
open D5.S3.Observer.Monodromy.TransvectionLieFiltration

/-- Pooled actual records; gain includes the nonnegative exposure weight. -/
def pooledRecords {n : ℕ} (c : ℝ) (gain offset s t : Fin n → ℝ) : Fin 4 → ℝ :=
  fun k => ∑ r, records c (gain r) (offset r) (s r) (t r) k

/-- The pulse gains stay positive in the common box; effective mass is nonzero.
Offsets are arbitrary and need not be constant across slots. -/
def Admissible {n : ℕ} (δ : ℝ) (gain s t : Fin n → ℝ) : Prop :=
  (∀ r, 0 ≤ gain r) ∧ (0 < ∑ r, gain r) ∧ (∀ r, GainBox δ (s r) (t r))

/-- Scale-free statistic of four observed second moments. Its denominator is
proved positive on every admissible record in the theorem below. -/
def normalizedContrast (z : Fin 4 → ℝ) : ℝ :=
  (z 3-z 1-z 2+z 0)^2 / (2*(z 1-z 0)*(z 2-z 0))

/-- One decoder of the full four-moment record works for every finite balanced
calibration mixture iff the displayed sharp inequality holds. Failure excludes
all deterministic nonlinear decoders as well, through an explicit record collision.
`false` denotes cLo and `true` denotes cHi; no entanglement predicate is assumed. -/
theorem uniform_mixture_decoder_iff (cLo cHi δ : ℝ)
    (hLo : 0 < cLo) (hLH : cLo < cHi) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∃ decoder : (Fin 4 → ℝ) → Bool,
      ∀ (n : ℕ) (gain offset s t : Fin n → ℝ), Admissible δ gain s t →
        decoder (pooledRecords cLo gain offset s t) = false ∧
        decoder (pooledRecords cHi gain offset s t) = true) ↔
      (cLo+cHi)*δ^2 < cHi-cLo := by
  classical
  have hHi : 0 < cHi := hLo.trans hLH
  have hsum : 0 < cLo+cHi := add_pos hLo hHi
  have hp : 0 < 1-δ^2 := by nlinarith
  have hq : 0 < 1+δ^2 := by positivity
  have hl : 0 < 1-δ := by linarith
  have hu : 0 < 1+δ := by positivity
  let q := (1-δ^2)/(1+δ^2)
  have hqpos : 0 < q := div_pos hp hq
  have ray (s t : ℝ) : controlledDirection s t = ![1, s, 0, t] := by
    ext i
    fin_cases i <;>
      norm_num [controlledDirection, dualPulse, increment, pairing,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
  have formula (c s t : ℝ) : outputVariance c s t = 1+s^2+2*c*s*t+2*t^2 := by
    simp [outputVariance, ray, covariance, Fin.sum_univ_succ]
    <;> ring
  have rec_formula (c g o s t : ℝ) : records c g o s t =
      ![o+g, o+g+g*s^2, o+g+2*g*t^2,
        o+g+g*s^2+2*c*g*s*t+2*g*t^2] := by
    ext k
    fin_cases k <;> simp [records, formula] <;> ring

  -- Moment bounds are derived from the actual pooled records for every finite size.
  have bounds (n : ℕ) (gain offset s t : Fin n → ℝ)
      (ha : Admissible δ gain s t) (c : ℝ) :
      q^2*c^2 ≤ normalizedContrast (pooledRecords c gain offset s t) ∧
        normalizedContrast (pooledRecords c gain offset s t) ≤ c^2 := by
    rcases ha with ⟨hg, hm, hbox⟩
    let A := ∑ r, gain r * (s r)^2
    let B := ∑ r, gain r * (t r)^2
    let C := ∑ r, gain r * s r * t r
    have hspos (r : Fin n) : 0 < s r := lt_of_lt_of_le hl (hbox r).1.1
    have htpos (r : Fin n) : 0 < t r := lt_of_lt_of_le hl (hbox r).2.1
    have hsome : ∃ r, 0 < gain r := by
      by_contra hn
      push_neg at hn
      have hz : (∑ r, gain r) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        exact le_antisymm (hn r) (hg r)
      linarith
    obtain ⟨r, hr⟩ := hsome
    have hA : 0 < A := lt_of_lt_of_le
      (mul_pos hr (sq_pos_of_pos (hspos r)))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hg i) (sq_nonneg _))
        (Finset.mem_univ r))
    have hB : 0 < B := lt_of_lt_of_le
      (mul_pos hr (sq_pos_of_pos (htpos r)))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hg i) (sq_nonneg _))
        (Finset.mem_univ r))
    have hC : 0 < C := lt_of_lt_of_le
      (mul_pos (mul_pos hr (hspos r)) (htpos r))
      (Finset.single_le_sum
        (fun i _ => mul_nonneg (mul_nonneg (hg i) (hspos i).le) (htpos i).le)
        (Finset.mem_univ r))
    have hAB : 0 < A*B := mul_pos hA hB
    have haRead : pooledRecords c gain offset s t 1 -
        pooledRecords c gain offset s t 0 = A := by
      simp only [pooledRecords, rec_formula, Matrix.cons_val_zero,
        Matrix.cons_val_one, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hbRead : pooledRecords c gain offset s t 2 -
        pooledRecords c gain offset s t 0 = 2*B := by
      simp only [pooledRecords, rec_formula]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hdRead : pooledRecords c gain offset s t 3 -
        pooledRecords c gain offset s t 1 - pooledRecords c gain offset s t 2 +
        pooledRecords c gain offset s t 0 = 2*c*C := by
      simp only [pooledRecords, rec_formula]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hcontrast : normalizedContrast (pooledRecords c gain offset s t) =
        c^2*C^2/(A*B) := by
      unfold normalizedContrast
      rw [haRead, hbRead, hdRead]
      field_simp [ne_of_gt hA, ne_of_gt hB]
      <;> ring

    -- Weighted Cauchy--Schwarz, via a nonnegative actual square sum.
    have hcs : C^2 ≤ A*B := by
      have hz : 0 ≤ ∑ i, gain i * (B*s i-C*t i)^2 := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (hg i) (sq_nonneg _)
      have he : (∑ i, gain i * (B*s i-C*t i)^2) = B*(A*B-C^2) := by
        calc
          _ = B^2*(∑ i, gain i*(s i)^2) - (2*B*C)*(∑ i, gain i*s i*t i) +
              C^2*(∑ i, gain i*(t i)^2) := by
            simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
              ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = B*(A*B-C^2) := by change B^2*A-(2*B*C)*C+C^2*B = _; ring
      rw [he] at hz
      by_contra hn
      have hneg := mul_pos hB (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith

    -- Classical sharp reverse estimate, retaining both box endpoints.
    have hpoint (i : Fin n) :
        (1-δ^2)*((s i)^2+(t i)^2) ≤ 2*(1+δ^2)*(s i*t i) := by
      have hx : 0 ≤ (1+δ)*s i-(1-δ)*t i := by
        have h1 := mul_nonneg hu.le (sub_nonneg.mpr (hbox i).1.1)
        have h2 := mul_nonneg hl.le (sub_nonneg.mpr (hbox i).2.2)
        nlinarith
      have hy : 0 ≤ (1+δ)*t i-(1-δ)*s i := by
        have h1 := mul_nonneg hu.le (sub_nonneg.mpr (hbox i).2.1)
        have h2 := mul_nonneg hl.le (sub_nonneg.mpr (hbox i).1.2)
        nlinarith
      have hprod := mul_nonneg hx hy
      have he : ((1+δ)*s i-(1-δ)*t i)*((1+δ)*t i-(1-δ)*s i) =
          2*(1+δ^2)*(s i*t i)-(1-δ^2)*((s i)^2+(t i)^2) := by ring
      rw [he] at hprod
      linarith
    have hsumineq : (1-δ^2)*(A+B) ≤ 2*(1+δ^2)*C := by
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hg i))
      calc
        _ = ∑ i, gain i*((1-δ^2)*((s i)^2+(t i)^2)) := by
          dsimp [A, B]
          simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i, gain i*(2*(1+δ^2)*(s i*t i)) := h
        _ = 2*(1+δ^2)*C := by
          dsimp [C]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    have hsq : ((1-δ^2)*(A+B))^2 ≤ (2*(1+δ^2)*C)^2 := by
      have hminus : 0 ≤ 2*(1+δ^2)*C-(1-δ^2)*(A+B) := sub_nonneg.mpr hsumineq
      have hplus : 0 ≤ 2*(1+δ^2)*C+(1-δ^2)*(A+B) := by positivity
      nlinarith [mul_nonneg hminus hplus]
    have hrev : (1-δ^2)^2*(A*B) ≤ (1+δ^2)^2*C^2 := by
      have ham := mul_nonneg (sq_nonneg (1-δ^2)) (sq_nonneg (A-B))
      nlinarith
    have hratio : q^2*(A*B) ≤ C^2 := by
      apply (mul_le_mul_left (sq_pos_of_pos hq)).mp
      calc
        (1+δ^2)^2*(q^2*(A*B)) = (1-δ^2)^2*(A*B) := by
          dsimp [q]
          field_simp [ne_of_gt hq]
          <;> ring
        _ ≤ (1+δ^2)^2*C^2 := hrev
    rw [hcontrast]
    constructor
    · apply (le_div_iff₀ hAB).mpr
      have h := mul_le_mul_of_nonneg_left hratio (sq_nonneg c)
      nlinarith
    · apply (div_le_iff₀ hAB).mpr
      exact mul_le_mul_of_nonneg_left hcs (sq_nonneg c)

  constructor
  · rintro ⟨decoder, hdecode⟩
    by_contra hfail
    have hfailure : cHi-cLo ≤ (cLo+cHi)*δ^2 := le_of_not_gt hfail
    let x := (cHi-cLo)/(cLo+cHi)
    let d := Real.sqrt x
    let a := Real.sqrt (1+x)
    have hx : 0 < x := div_pos (sub_pos.mpr hLH) hsum
    have hxd : x ≤ δ^2 := by
      apply (div_le_iff₀ hsum).mpr
      nlinarith [hfailure]
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hd2 : d^2 = x := Real.sq_sqrt hx.le
    have hdd : d ≤ δ := by nlinarith
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a^2 = 1+x := Real.sq_sqrt (by positivity)
    have ha1 : 1 ≤ a := by nlinarith
    have had : a ≤ 1+d := by nlinarith
    have harelation : (cLo+cHi)*x = cHi-cLo := by
      dsimp [x]
      field_simp [ne_of_gt hsum]
      <;> ring
    let gHi : Fin 2 → ℝ := ![1/2, 1/2]
    let oHi : Fin 2 → ℝ := ![0, 0]
    let sHi : Fin 2 → ℝ := ![1-d, 1+d]
    let tHi : Fin 2 → ℝ := ![1+d, 1-d]
    let gLo : Fin 1 → ℝ := ![1]
    let oLo : Fin 1 → ℝ := ![0]
    let sLo : Fin 1 → ℝ := ![a]
    let tLo : Fin 1 → ℝ := ![a]
    have hHiAdm : Admissible δ gHi sHi tHi := by
      refine ⟨?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num [gHi]
      · norm_num [gHi, Fin.sum_univ_succ]
      · intro i; fin_cases i <;>
          simp only [GainBox, sHi, tHi, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
          constructor <;> constructor <;> linarith
    have hLoAdm : Admissible δ gLo sLo tLo := by
      refine ⟨?_, ?_, ?_⟩
      · intro i; fin_cases i; norm_num [gLo]
      · norm_num [gLo, Fin.sum_univ_succ]
      · intro i; fin_cases i
        simp only [GainBox, sLo, tLo, Matrix.cons_val_zero]
        constructor <;> constructor <;> linarith
    have hHighRecords : pooledRecords cHi gHi oHi sHi tHi =
        ![1, 2+d^2, 3+2*d^2, 4+3*d^2+2*cHi*(1-d^2)] := by
      ext k
      fin_cases k <;>
        norm_num [pooledRecords, gHi, oHi, sHi, tHi, rec_formula,
          Fin.sum_univ_succ] <;> ring
    have hLowRecords : pooledRecords cLo gLo oLo sLo tLo =
        ![1, 1+a^2, 1+2*a^2, 1+(3+2*cLo)*a^2] := by
      ext k
      fin_cases k <;>
        norm_num [pooledRecords, gLo, oLo, sLo, tLo, rec_formula,
          Fin.sum_univ_succ] <;> ring
    have hcollision : pooledRecords cHi gHi oHi sHi tHi =
        pooledRecords cLo gLo oLo sLo tLo := by
      rw [hHighRecords, hLowRecords, hd2, ha2]
      ext k
      fin_cases k <;> simp <;> nlinarith [harelation]
    have hhigh := (hdecode 2 gHi oHi sHi tHi hHiAdm).2
    have hlow := (hdecode 1 gLo oLo sLo tLo hLoAdm).1
    rw [hcollision, hlow] at hhigh
    cases hhigh
  · intro hsep
    have hqsep : cLo < cHi*q := by
      change cLo < cHi*((1-δ^2)/(1+δ^2))
      rw [← mul_div_assoc]
      apply (lt_div_iff₀ hq).mpr
      nlinarith [hsep]
    have hsqsep : cLo^2 < q^2*cHi^2 := by
      have hprod := mul_pos (sub_pos.mpr hqsep) (add_pos (mul_pos hHi hqpos) hLo)
      nlinarith
    let τ := (cLo^2+q^2*cHi^2)/2
    refine ⟨fun z => decide (τ < normalizedContrast z), ?_⟩
    intro n gain offset s t hadm
    have hlo := (bounds n gain offset s t hadm cLo).2
    have hhi := (bounds n gain offset s t hadm cHi).1
    have hlow : ¬ τ < normalizedContrast (pooledRecords cLo gain offset s t) := by
      dsimp [τ]
      linarith
    have hhigh : τ < normalizedContrast (pooledRecords cHi gain offset s t) := by
      dsimp [τ]
      linarith
    simp [hlow, hhigh]

#print axioms uniform_mixture_decoder_iff

end D5.S3.Observer.Monodromy.DriftMixtureMomentIdentifiability
