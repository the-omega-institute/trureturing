/- GID: D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim; result=D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result; claim=D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim
   digest: A finite complex witness refutes the reverse Mittag-Leffler characterization. -/

/-
result
proof_shape: bind-only (Gamma identities, rational bounds and geometric-series estimates).
escape_witness: none
admission_basis: open-problem-resolution (#22376; Refuted)
Direct frozen dependencies (declaration statement_id):
  D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs sha256:7779f326a10cb0e250db2bbc5f0665a27b7ade7372d03e5a9d9c5e09c85d973f
  D5.S3.Analytic.ExpRatioCM.Defs.CompletelyMonotoneOn sha256:f25bdc23dc3c3d7bb2a8e428111edb1df2af60971e1fe8d8bb2e2ab069581ea0
  D5.S3.Analytic.KilbasSaigo.Series.tendsto_inv_phi sha256:436b65354c91edb4d68046ee98b7908f63798e7e947243d30fdda75c7a1ca6b6
  D5.S3.Analytic.KilbasSaigo.Series.phi sha256:48f40d9fffa359115ae3e097c1dc944669272f609e0a351f61dcfa5c7d2fc422

The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source conventions are literal; CompletelyMonotoneOn is reused from its existing owner.
Only the endpoint pair (3/2,1/2) is certified; no all-alpha or interior-beta family is asserted.
-/

import D5.S3.Analytic.Asymptotics.MittagLefflerBarnesKernel
import D5.S3.Analytic.Asymptotics.MellinBarnesSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import D5.S3.Analytic.KilbasSaigo.Series
import D5.S3.Analytic.ExpRatioCM.Defs
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianAnalyticEndpoints
import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity

/-! Binding definitions for GGPS, arXiv:2410.11852v4, Conjecture 25.
The source defines the series for alpha > 0 and every real beta; its
inequality conjectures use beta >= 0. Real inputs are embedded into C.
The real part below reads the real-valued series on real inputs.
HasSum specifies actual convergence, and claim asserts existence.
-/

namespace D5.S3.Analytic.Asymptotics.MittagLefflerModulusRefutation

/-- Equation (1.1), including convergence, for the entire source family.
At Gamma poles, Mathlib's inverse of its totalized Gamma is zero. -/
def IsSourceSeries (E : ℝ → ℝ → ℂ → ℂ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ β : ℝ, ∀ z : ℂ,
    HasSum (fun k : ℕ => z ^ k / (Real.Gamma (α * (k : ℝ) + β) : ℂ))
      (E α β z)

/-- The reciprocal real function in Conjecture 25. -/
noncomputable def reciprocal (E : ℝ → ℝ → ℂ → ℂ) (α β x : ℝ) : ℝ :=
  1 / (E α β (x : ℂ)).re

/-- Conjecture 25: A iff B iff C, with every source object required to exist.
The existing D5 CM owner supplies smoothness and every signed derivative;
the extra positivity clause preserves the source's positive codomain. -/
def claim : Prop :=
  (∃ E : ℝ → ℝ → ℂ → ℂ, IsSourceSeries E) ∧
    ∀ E : ℝ → ℝ → ℂ → ℂ, IsSourceSeries E →
      ∀ α : ℝ, ∀ β : ℝ, 1 < α → α < 2 → 0 ≤ β →
        (((∀ z : ℂ, (E α β (z.re : ℂ)).re ≤ ‖E α β z‖) ↔
            (α - 1 ≤ β ∧ β ≤ α)) ∧
          ((α - 1 ≤ β ∧ β ≤ α) ↔
            ((∀ x : ℝ, 0 < x → 0 < reciprocal E α β x) ∧
              D5.S3.Analytic.ExpRatioCM.Defs.CompletelyMonotoneOn
                (reciprocal E α β))))

end D5.S3.Analytic.Asymptotics.MittagLefflerModulusRefutation

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open scoped BigOperators
open Filter Topology MeasureTheory
namespace D5.S3.Analytic.Asymptotics.MittagLefflerModulusRefutation
private noncomputable def rho : ℝ := (Real.sqrt Real.pi)⁻¹
private noncomputable def term (z : ℂ) (k : ℕ) : ℂ :=
  z ^ k / (Real.Gamma ((3 / 2 : ℝ) * k + 1 / 2) : ℂ)
private noncomputable def ec (n : ℕ) : ℝ := (2 : ℝ)^(3*n) / ((6*n-1).doubleFactorial : ℝ)
private noncomputable def oc (n : ℕ) : ℝ := 1 / ((3*n+1).factorial : ℝ)

private theorem rho_bounds :
    (56418958354775628694 / 10^20 : ℝ) ≤ rho ∧
      rho ≤ (56418958354775628696 / 10^20 : ℝ) := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlo : (8862269254527580136487/5000000000000000000000:ℝ) ≤ Real.sqrt Real.pi := by
    exact (by norm_num [RHFiniteGaussian.AnalyticEndpoints.sqrtPiLower250] :
      (8862269254527580136487/5000000000000000000000:ℝ) ≤
        (RHFiniteGaussian.AnalyticEndpoints.sqrtPiLower250 : ℝ)).trans
      RHFiniteGaussian.AnalyticEndpoints.sqrt_pi_250_bounds.1
  have hhi : Real.sqrt Real.pi ≤ (17724538509055160273003/10000000000000000000000:ℝ) := by
    exact RHFiniteGaussian.AnalyticEndpoints.sqrt_pi_250_bounds.2.trans
      (by norm_num [RHFiniteGaussian.AnalyticEndpoints.sqrtPiUpper250])
  unfold rho
  rw [inv_eq_one_div]
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith
  · apply (div_le_iff₀ hs).2
    nlinarith

private theorem term_even (z : ℂ) (n : ℕ) :
    term z (2*n) = z^(2*n) * ((ec n * rho : ℝ) : ℂ) := by
  unfold term ec rho
  rw [show (3/2:ℝ) * (2*n:ℕ) + 1/2 = (3*n:ℕ) + 1/2 by push_cast; ring,
    Real.Gamma_nat_add_half]
  push_cast
  rw [show 2 * (3*n) - 1 = 6*n-1 by omega]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem term_odd (z : ℂ) (n : ℕ) :
    term z (2*n+1) = z^(2*n+1) * (oc n : ℂ) := by
  unfold term oc
  rw [show (3/2:ℝ) * (2*n+1:ℕ) + 1/2 = (3*n+1:ℕ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  push_cast
  ring

private theorem gamma_step_three (s : ℝ) (hs : 0 < s) :
    Real.Gamma (s+3) = s*(s+1)*(s+2)*Real.Gamma s := by
  rw [show s+3 = (s+1+1)+1 by ring, Real.Gamma_add_one (by linarith),
    Real.Gamma_add_one (by linarith), Real.Gamma_add_one hs.ne']
  ring

private theorem term_two_step (z : ℂ) (k : ℕ) :
    term z (k+2) = term z k * z^2 /
      (((3/2:ℝ)*k+1/2) * ((3/2:ℝ)*k+3/2) * ((3/2:ℝ)*k+5/2) : ℝ) := by
  unfold term
  rw [show (3/2:ℝ)*(k+2:ℕ)+1/2 = ((3/2:ℝ)*k+1/2)+3 by push_cast; ring,
    gamma_step_three _ (by positivity), pow_add]
  rw [show (3/2:ℝ)*k+1/2+1 = (3/2:ℝ)*k+3/2 by ring,
    show (3/2:ℝ)*k+1/2+2 = (3/2:ℝ)*k+5/2 by ring]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring



private noncomputable def pa (z : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, z^(2*j) * (ec j : ℂ)
private noncomputable def pb (z : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, z^(2*j+1) * (oc j : ℂ)
private noncomputable def partialSum (z : ℂ) : ℂ := ∑ k ∈ Finset.range 64, term z k

private theorem partial_pairs (z : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), term z k) = pa z n * (rho : ℂ) + pb z n := by
  rw [D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs]
  simp_rw [term_even, term_odd]
  simp only [pa, pb, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

private noncomputable def witness : ℂ := ⟨-115,10⟩

private theorem pa_axis : pa (-115 : ℂ) 32 = (⟨(2148289600656950580065354273655857058363946679653641908249253259174732417590131319749329005443211021692437722213532796393975074916650086449953116225300368602697 / 40127857252329676858044595283454864762797684538681937239373205704247913473902871234279621953515696158643893475951398128959461971146071107063706184657 : ℝ), (0 / 1 : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [pa, ec, Finset.sum_range_succ, pow_succ,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Nat.doubleFactorial, Nat.factorial]

private theorem pb_axis : pb (-115 : ℂ) 32 = (⟨(-60474444447573108249228527854762405950784864186380861228067826612820803016987490720590951350944893233714112758408673449935233096810145 / 2002165471662582547671223329081567122870785368860677009623872617214676837300120642969100528695116584549735025665727369576448 : ℝ), (0 / 1 : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [pb, oc, Finset.sum_range_succ, pow_succ,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Nat.doubleFactorial, Nat.factorial]

private theorem pa_point : pa witness 32 = (⟨(2690449949284682654097143306851647817620926638363360084801351775521662447626943479270584564947103811172401402684799504497116306855029835950921856233845558170328783 / 287933838496133053888001476633776738720155559974084410230857365576472829601293676642872915053686818685411943441120902661696020447884299606969605190271783 : ℝ), (-2023270017724676564841343462172575800153408228635959396380517601061942092980092501676651641364030946038538702911507824731319490387493354105507033888426722662045280 / 37556587629930398333217583908753487659150725214011010030111830292583412556690479562113858485263498089401557840146204695003828754071865166126470242209363 : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [pa, ec, witness, Finset.sum_range_succ, pow_succ,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Nat.doubleFactorial, Nat.factorial]

private theorem pb_point : pb witness 32 = (⟨(-1112083253171965234159128811429887598607377917849818193698903146026231167518311397529439765132274533321868319715659740263163708031568322915 / 210950241458372068851253619525291890720751492601098678099364231072254171134643428090277739914506974001620570325763538225406672896 : ℝ), (182395831239618487109687266451185234609894794424410761512321290851084906434973235310989745296885552175813587415140610857570832203947774664145 / 6000979237276321221794872702811592996556114828994412395405598257608072605172356467515532548620579970940837803214483811096437194752 : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;>
    norm_num [pb, oc, witness, Finset.sum_range_succ, pow_succ,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Nat.doubleFactorial, Nat.factorial]

private theorem partial_axis : (3 / 100000 : ℝ) < (partialSum (-115)).re := by
  have h := partial_pairs (-115) 32
  norm_num only [show 2*32=64 by norm_num] at h
  unfold partialSum
  rw [h, pa_axis, pb_axis]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  linarith [rho_bounds.1, rho_bounds.2]

private theorem partial_point : |(partialSum witness).re| ≤ (1 / 1000000 : ℝ) ∧ |(partialSum witness).im| ≤ (1 / 100000 : ℝ) := by
  have h := partial_pairs witness 32
  norm_num only [show 2*32=64 by norm_num] at h
  unfold partialSum
  rw [h, pa_point, pb_point]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, mul_zero, sub_zero, zero_add]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [rho_bounds.1, rho_bounds.2]

private theorem ec_nonneg (n : ℕ) : 0 ≤ ec n := by unfold ec; positivity
private theorem oc_nonneg (n : ℕ) : 0 ≤ oc n := by unfold oc; positivity
private theorem rho_nonneg : 0 ≤ rho := (by norm_num : (0:ℝ) ≤ 56418958354775628694 / 10^20).trans rho_bounds.1

private theorem tail_initial {z : ℂ} (hz : ‖z‖ ≤ 125) :
    ‖term z 64‖ ≤ (1 / 10^13 : ℝ) ∧
      ‖term z 65‖ ≤ (1 / 10^13 : ℝ) * (3/4) := by
  have hec := ec_nonneg 32
  have hecrho : 0 ≤ ec 32 * rho := mul_nonneg hec rho_nonneg
  have hoc := oc_nonneg 32
  have hr : rho ≤ 1 := rho_bounds.2.trans (by norm_num)
  constructor
  · calc
      ‖term z 64‖ = ‖z‖^64 * (ec 32 * rho) := by
        rw [show 64=2*32 by norm_num, term_even, norm_mul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ec_nonneg _) rho_nonneg)]
      _ ≤ (125:ℝ)^64 * ec 32 := by
        calc
          _ ≤ (125:ℝ)^64 * (ec 32 * 1) := by gcongr
          _ = _ := by ring
      _ ≤ _ := by norm_num [ec, Nat.doubleFactorial]
  · calc
      ‖term z 65‖ = ‖z‖^65 * oc 32 := by
        rw [show 65=2*32+1 by norm_num, term_odd, norm_mul, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (oc_nonneg _)]
      _ ≤ (125:ℝ)^65 * oc 32 := by gcongr
      _ ≤ _ := by norm_num [oc, Nat.factorial]

private theorem tail_ratio {z : ℂ} (hz : ‖z‖ ≤ 125) {k : ℕ} (hk : 64 ≤ k) :
    ‖term z (k+2)‖ ≤ (1/2 : ℝ) * ‖term z k‖ := by
  let s : ℝ := (3/2:ℝ)*k+1/2
  have hk' : (64:ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
  have hs : (90:ℝ) ≤ s := by dsimp [s]; linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < s*(s+1)*(s+2) := by positivity
  have hl : (90:ℝ)*90*90 ≤ s*(s+1)*(s+2) := by gcongr <;> linarith
  have hp : ‖z‖^2 ≤ (1/2:ℝ) * (s*(s+1)*(s+2)) := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg z) hz 2]
  rw [term_two_step, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [show (3/2:ℝ)*k+3/2 = s+1 by dsimp [s]; ring,
    show (3/2:ℝ)*k+5/2 = s+2 by dsimp [s]; ring]
  change ‖term z k‖ * ‖z‖^2 / |s*(s+1)*(s+2)| ≤ _
  rw [abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (term z k))]

private theorem tail_geometric {z : ℂ} (hz : ‖z‖ ≤ 125) (n : ℕ) :
    ‖term z (n+64)‖ ≤ (1/10^13 : ℝ) * (3/4:ℝ)^n := by
  induction n using Nat.twoStepInduction
  · simpa using (tail_initial hz).1
  · simpa using (tail_initial hz).2
  · rename_i n ih0 ih1
    have h := tail_ratio hz (k:=n+64) (by omega)
    rw [show n+2+64 = (n+64)+2 by omega]
    calc
      _ ≤ (1/2:ℝ) * ‖term z (n+64)‖ := h
      _ ≤ (1/2:ℝ) * ((1/10^13:ℝ)*(3/4:ℝ)^n) := by gcongr
      _ ≤ _ := by rw [pow_add]; norm_num; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) n]

private theorem source_partial_bound {E : ℝ → ℝ → ℂ → ℂ} (hE : IsSourceSeries E)
    {z : ℂ} (hz : ‖z‖ ≤ 125) :
    ‖E (3/2) (1/2) z - partialSum z‖ ≤ (4/10^13 : ℝ) := by
  have hg : HasSum (fun n : ℕ => (1/10^13:ℝ)*(3/4:ℝ)^n) (4/10^13:ℝ) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num : (3/4:ℝ) < 1)).mul_left (1/10^13:ℝ) using 1 <;> norm_num
  have ht : Summable (fun n : ℕ => term z (n+64)) :=
    hg.summable.of_norm_bounded (tail_geometric hz)
  have hs : HasSum (term z) (partialSum z + ∑' n : ℕ, term z (n+64)) :=
    ht.hasSum.sum_range_add
  have heq : E (3/2) (1/2) z = partialSum z + ∑' n : ℕ, term z (n+64) :=
    (hE (3/2) (by norm_num) (1/2) z).unique hs
  rw [heq, add_sub_cancel_left]
  exact ht.hasSum.norm_le_of_bounded hg (tail_geometric hz)

private theorem certified_failure {E : ℝ → ℝ → ℂ → ℂ} (hE : IsSourceSeries E) :
    ‖E (3/2) (1/2) witness‖ < (E (3/2) (1/2) (witness.re : ℂ)).re := by
  have hw : ‖witness‖ ≤ 125 := by
    calc
      _ ≤ |witness.re|+|witness.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = _ := by norm_num [witness]
  have ha : ‖(-115:ℂ)‖ ≤ 125 := by norm_num
  have hp := source_partial_bound hE hw
  have hq := source_partial_bound hE ha
  have hb := partial_point
  have hn : ‖partialSum witness‖ ≤ (11/1000000:ℝ) := by
    calc
      _ ≤ |(partialSum witness).re|+|(partialSum witness).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by linarith [hb.1, hb.2]
  have hu : ‖E (3/2) (1/2) witness‖ ≤ (11/1000000:ℝ)+4/10^13 := by
    have h := norm_add_le (E (3/2) (1/2) witness - partialSum witness) (partialSum witness)
    rw [sub_add_cancel] at h
    linarith
  have hd := (Complex.abs_re_le_norm (E (3/2) (1/2) (-115) - partialSum (-115))).trans hq
  rw [Complex.sub_re] at hd
  have hl := (abs_le.mp hd).1
  have hl' := partial_axis
  rw [show (witness.re : ℂ) = (-115 : ℂ) by norm_num [witness]]
  linarith

private theorem gamma_ratio_tendsto {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => Real.Gamma (α*n+β) / Real.Gamma (α*(n+1)+β))
      atTop (𝓝 0) := by
  let l := (β-1)/α+1
  have hl : (1:ℝ)-1/α < l := by
    apply sub_pos.mp
    have he : l - (1 - 1/α) = β/α := by
      dsimp [l]
      ring
    rw [he]
    exact div_pos hβ hα
  have he : 1+α*(l-1) = β := by dsimp [l]; field_simp [hα.ne']; ring
  have h := D5.S3.Analytic.KilbasSaigo.Series.tendsto_inv_phi hα (by norm_num : (0:ℝ)<1) hl
  convert h using 1
  ext n
  simp only [D5.S3.Analytic.KilbasSaigo.Series.phi, mul_one, he, one_div_div]
  congr 2 <;> ring

private theorem source_norm_summable_positive {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (z : ℂ) :
    Summable (fun n : ℕ => ‖z^n / (Real.Gamma (α*n+β) : ℂ)‖) := by
  let f : ℕ → ℂ := fun n => z^n / (Real.Gamma (α*n+β) : ℂ)
  have hp (n : ℕ) : 0 < Real.Gamma (α*n+β) := Real.Gamma_pos_of_pos (by positivity)
  have hq : Tendsto (fun n : ℕ => ‖z‖*(Real.Gamma (α*n+β) / Real.Gamma (α*(n+1)+β)))
      atTop (𝓝 0) := by
    simpa using (gamma_ratio_tendsto hα hβ).const_mul ‖z‖
  have hr (n : ℕ) : ‖f (n+1)‖ =
      (‖z‖*(Real.Gamma (α*n+β) / Real.Gamma (α*(n+1)+β))) * ‖f n‖ := by
    dsimp [f]
    rw [norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hp n)]
    have hp' : 0 < Real.Gamma (α*((n+1:ℕ):ℝ)+β) := hp (n+1)
    rw [abs_of_pos hp', pow_succ]
    push_cast at hp' ⊢
    field_simp [(hp n).ne', hp'.ne'] <;> ring
  apply summable_of_ratio_norm_eventually_le (r:=1/2) (by norm_num)
  filter_upwards [hq.eventually_le_const (by norm_num : (0:ℝ)<1/2)] with n hn
  simp only [norm_norm]
  rw [hr]
  exact mul_le_mul_of_nonneg_right hn (norm_nonneg (f n))

private theorem source_norm_summable {α : ℝ} (hα : 0 < α) (β : ℝ) (z : ℂ) :
    Summable (fun n : ℕ => ‖z^n / (Real.Gamma (α*n+β) : ℂ)‖) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-β/α)
  have hb : 0 < α*N+β := by have := (div_lt_iff₀ hα).1 hN; nlinarith
  have hs := (source_norm_summable_positive hα hb z).mul_left ‖z^N‖
  apply (summable_nat_add_iff N).mp
  convert hs using 1
  ext n
  rw [show α*((n+N:ℕ):ℝ)+β = α*n+(α*N+β) by push_cast; ring, pow_add]
  rw [← norm_mul]
  congr 1
  ring

/-- For a fixed positive alpha and complex argument, the literal source family is
continuous in beta on the whole real line. Reciprocal Gamma is used
as an entire function, so each finite summand is continuous even at its zeros. -/
theorem source_continuous_beta {E : ℝ → ℝ → ℂ → ℂ} (hE : IsSourceSeries E)
    {α : ℝ} (hα : 0 < α) (z : ℂ) :
    Continuous (fun β : ℝ => E α β z) := by
  have heq (β : ℝ) : E α β z =
      ∑' n : ℕ, z ^ n / (Real.Gamma (α * n + β) : ℂ) :=
    (hE α hα β z).tsum_eq.symm
  simp_rw [heq]
  have hterm (n : ℕ) :
      Continuous (fun β : ℝ => z ^ n / (Real.Gamma (α * n + β) : ℂ)) := by
    simp_rw [div_eq_mul_inv, ← Complex.Gamma_ofReal]
    exact continuous_const.mul
      (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  rw [continuous_iff_continuousAt]
  intro b
  let a : ℝ := b - 1
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 - a) / α)
  have hN' : 2 ≤ α * N + a := by
    have := (div_lt_iff₀ hα).mp hN
    nlinarith
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ β ∈ Set.Icc a (b + 1),
      ‖z ^ n / (Real.Gamma (α * n + β) : ℂ)‖ ≤
        ‖z ^ n / (Real.Gamma (α * n + a) : ℂ)‖ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    intro β hβ
    have hna : 2 ≤ α * n + a := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hnb : 2 ≤ α * n + β := by linarith [hβ.1]
    have hG : Real.Gamma (α * n + a) ≤ Real.Gamma (α * n + β) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hna hnb (by linarith [hβ.1])
    rw [norm_div, norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by linarith : 0 < α * n + β)),
      abs_of_pos (Real.Gamma_pos_of_pos (by linarith : 0 < α * n + a))]
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (Real.Gamma_pos_of_pos (by linarith)) hG
  have hU := tendstoUniformlyOn_tsum_nat_eventually
    (source_norm_summable hα a z) hbound
  have hC : ContinuousOn
      (fun β : ℝ => ∑' n : ℕ, z ^ n / (Real.Gamma (α * n + β) : ℂ))
      (Set.Icc a (b + 1)) := by
    apply hU.continuousOn
    exact Filter.Frequently.of_forall fun M =>
      continuousOn_finsetSum _ fun n _ => (hterm n).continuousOn
  exact hC.continuousAt (Icc_mem_nhds (by dsimp [a]; linarith) (by linarith))

/-- The actual Barnes contour at the endpoint beta=alpha-1 vanishes as it moves left.
This uses the literal fixed-beta coefficient summability, not an assumed sector identity. -/
theorem source_left_integral_tendsto_zero {α : ℝ} (hα : 1 < α) {z : ℂ} (hz0 : z ≠ 0)
    (hz : 0 < MittagLefflerBarnesKernel.margin α z) :
    Tendsto (fun n : ℕ => ∫ y : ℝ,
      MittagLefflerBarnesKernel.kernel α (α - 1) z
        (MittagLefflerBarnesKernel.leftLine n + y * Complex.I)) atTop (𝓝 0) := by
  let δ : ℝ := MittagLefflerBarnesKernel.margin α z
  let b : ℝ := 3 * α / 2 - 1
  let M : ℝ := ∫ y : ℝ, Real.exp (-(δ * |y|))
  let B : ℝ := 2 * Real.pi * Real.exp (Real.log ‖z‖ / 2) * M
  have hα0 : 0 < α := by linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hM : 0 ≤ M := integral_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmall : Tendsto (fun n : ℕ =>
      B * ‖z ^ n / (Real.Gamma (α * (n : ℝ) + b) : ℂ)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (source_norm_summable_positive hα0 hb z).tendsto_atTop_zero.const_mul B
  have hbound (n : ℕ) :
      ‖∫ y : ℝ, MittagLefflerBarnesKernel.kernel α (α - 1) z
        (MittagLefflerBarnesKernel.leftLine (n + 1) + y * Complex.I)‖ ≤
          B * ‖z ^ n / (Real.Gamma (α * (n : ℝ) + b) : ℂ)‖ := by
    have hx : 1 / 2 ≤ α - 1 - α * MittagLefflerBarnesKernel.leftLine (n + 1) := by
      dsimp [MittagLefflerBarnesKernel.leftLine]
      push_cast
      nlinarith [Nat.cast_nonneg (R := ℝ) n]
    have harg : α - 1 - α * MittagLefflerBarnesKernel.leftLine (n + 1) =
        α * (n : ℝ) + b := by
      dsimp [MittagLefflerBarnesKernel.leftLine, b]
      push_cast
      ring
    have hrad : Real.exp (-MittagLefflerBarnesKernel.leftLine (n + 1) * Real.log ‖z‖) =
        Real.exp (Real.log ‖z‖ / 2) * ‖z‖ ^ n := by
      rw [show -MittagLefflerBarnesKernel.leftLine (n + 1) * Real.log ‖z‖ =
        Real.log ‖z‖ / 2 + (n : ℝ) * Real.log ‖z‖ by
          dsimp [MittagLefflerBarnesKernel.leftLine]
          push_cast
          ring, Real.exp_add, Real.exp_nat_mul, Real.exp_log hnorm]
    have h := MittagLefflerBarnesKernel.norm_integral_leftLine_le hα0 (α - 1) z hz
      (n + 1) hx
    rw [harg, hrad] at h
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by positivity : 0 < α * (n : ℝ) + b))]
    convert h using 1 <;> dsimp [B, M, δ] <;> ring
  have hshift : Tendsto (fun n : ℕ => ∫ y : ℝ,
      MittagLefflerBarnesKernel.kernel α (α - 1) z
        (MittagLefflerBarnesKernel.leftLine (n + 1) + y * Complex.I)) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hsmall
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- Literal-series identification with the Barnes integral at beta=alpha-1.
The factor is `1/(2*pi)` because the vertical line is parametrized by `dy`.
Every analytic contour obligation is discharged on the actual kernel. -/
theorem source_barnes_identity {E : ℝ → ℝ → ℂ → ℂ} (hE : IsSourceSeries E)
    {α : ℝ} (hα : 1 < α) {z : ℂ} (hz0 : z ≠ 0)
    (hz : 0 < MittagLefflerBarnesKernel.margin α z) :
    E α (α - 1) z = (1 / (2 * (Real.pi : ℂ))) *
      ∫ y : ℝ, MittagLefflerBarnesKernel.kernel α (α - 1) z
        ((1 / 2 : ℝ) + y * Complex.I) := by
  have hα0 : 0 < α := by linarith
  have hab (n : ℕ) : MittagLefflerBarnesKernel.leftLine (n + 1) ≤
      MittagLefflerBarnesKernel.leftLine n := by
    dsimp [MittagLefflerBarnesKernel.leftLine]
    push_cast
    linarith
  have hd : MellinBarnesSeries.MBSeriesData
      (MittagLefflerBarnesKernel.kernel α (α - 1) z)
      MittagLefflerBarnesKernel.leftLine (fun n : ℕ => -(n : ℂ))
      (MittagLefflerBarnesKernel.leftNumerator α (α - 1) z) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      simp only [Complex.neg_re, Complex.natCast_re]
      dsimp [MittagLefflerBarnesKernel.leftLine]
      push_cast
      linarith
    · intro n
      simp only [Complex.neg_re, Complex.natCast_re]
      dsimp [MittagLefflerBarnesKernel.leftLine]
      linarith
    · exact fun n => MittagLefflerBarnesKernel.differentiableOn_leftNumerator α (α - 1) z n
    · exact fun n s hs hn => MittagLefflerBarnesKernel.kernel_eq_leftNumerator α (α - 1) z n hs hn
    · intro n
      apply MittagLefflerBarnesKernel.integrable_line hα0 (α - 1) _ z _ hz
      intro he
      have := MittagLefflerBarnesKernel.abs_sin_leftLine n
      simpa only [he, abs_zero] using this
    · exact fun n => (MittagLefflerBarnesKernel.horizontal_tendsto_zero
        hα0 (α - 1) _ _ z (hab n) hz).1
    · exact fun n => (MittagLefflerBarnesKernel.horizontal_tendsto_zero
        hα0 (α - 1) _ _ z (hab n) hz).2
  have hs : Summable (fun n : ℕ =>
      MittagLefflerBarnesKernel.leftNumerator α (α - 1) z n (-(n : ℂ))) := by
    simp_rw [MittagLefflerBarnesKernel.leftNumerator_residue α (α - 1) hz0]
    exact (hE α hα0 (α - 1) z).summable
  have hm := MellinBarnesSeries.mbSeries_hasSum hd
    (source_left_integral_tendsto_zero hα hz0 hz) hs
  simp_rw [MittagLefflerBarnesKernel.leftNumerator_residue α (α - 1) hz0] at hm
  have he := (hE α hα0 (α - 1) z).mul_left (2 * (Real.pi : ℂ))
  have hid := hm.unique he
  have hid' : (∫ y : ℝ, MittagLefflerBarnesKernel.kernel α (α - 1) z
      ((1 / 2 : ℝ) + y * Complex.I)) = 2 * (Real.pi : ℂ) * E α (α - 1) z := by
    simpa only [MittagLefflerBarnesKernel.leftLine, Nat.cast_zero, sub_zero] using hid
  rw [hid']
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  field_simp

private theorem source_exists : ∃ E : ℝ → ℝ → ℂ → ℂ, IsSourceSeries E := by
  refine ⟨fun α β z => ∑' n : ℕ, z^n / (Real.Gamma (α*n+β) : ℂ), ?_⟩
  intro α hα β z
  exact (source_norm_summable hα β z).of_norm.hasSum

theorem result : ¬ claim := by
  intro h
  obtain ⟨E,hE⟩ := source_exists
  have ha := ((h.2 E hE (3/2) (1/2) (by norm_num) (by norm_num) (by norm_num)).1).mpr
    (by norm_num : (3/2:ℝ)-1 ≤ 1/2 ∧ (1/2:ℝ) ≤ 3/2)
  exact (not_lt_of_ge (ha witness)) (certified_failure hE)

end D5.S3.Analytic.Asymptotics.MittagLefflerModulusRefutation
