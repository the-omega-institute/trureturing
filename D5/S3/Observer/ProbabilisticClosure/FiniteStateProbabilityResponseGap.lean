/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteStateProbabilityResponseGap
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteStateProbabilityResponseGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Probability-valued rational responses of fixed degree have a positive gap. -/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

open Set Filter Polynomial
open scoped Topology

namespace D5.S3.Observer.ProbabilisticClosure.FiniteStateProbabilityResponseGap

local notation "Coeff" d => (Fin (d + 1) → ℝ)
local notation "Pair" d => (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)

private noncomputable def ev {d : ℕ} (v : Coeff d) (x : ℝ) : ℝ :=
  (Polynomial.ofFn (d + 1) v).eval x

private lemma ev_sum {d : ℕ} (v : Coeff d) (x : ℝ) :
    ev v x = ∑ i : Fin (d + 1), v i * x ^ (i : ℕ) := by
  simp [ev, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]

private lemma continuous_ev {d : ℕ} (x : ℝ) : Continuous (fun v : Coeff d => ev v x) := by
  simp_rw [ev_sum]
  fun_prop

private lemma ev_smul {d : ℕ} (c : ℝ) (v : Coeff d) (x : ℝ) :
    ev (c • v) x = c * ev v x := by
  simp [ev, Polynomial.eval_smul]

private lemma coeff_eq_zero_of_ev_zero {d : ℕ} {v : Coeff d} {l r : ℝ}
    (hlr : l < r) (hv : ∀ x ∈ Ioo l r, ev v x = 0) : v = 0 := by
  have hp : Polynomial.ofFn (d + 1) v = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite hlr).mono fun x hx => hv x hx
  apply Polynomial.injective_ofFn (d + 1)
  simpa using hp

private lemma analytic_ev {d : ℕ} (v : Coeff d) : AnalyticOnNhd ℝ (ev v) univ :=
  AnalyticOnNhd.eval_polynomial _

private lemma analytic_sign_obstruction {d : ℕ} {l a b r : ℝ} {f : ℝ → ℝ}
    (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hf : AnalyticOnNhd ℝ f (Ioo l r))
    (hneg : ∃ c ∈ Ioo l r, f c < 0)
    (p q : Coeff d) (hq : q ≠ 0)
    (hpos : ∀ x ∈ Ioo l r, 0 ≤ ev p x * ev q x)
    (heq : ∀ x ∈ Ioo a b, ev p x = f x * ev q x) : False := by
  obtain ⟨z, hza, hzb⟩ := exists_between hab
  have hzu : z ∈ Ioo l r := ⟨hla.trans_lt hza, hzb.trans_le hbr⟩
  have hevent : ev p =ᶠ[𝓝 z] (fun x => f x * ev q x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hza, hzb⟩] with x hx
    exact heq x hx
  have hall : AnalyticOnNhd ℝ (ev p) (Ioo l r) :=
    (analytic_ev p).mono (subset_univ _)
  have hprod : AnalyticOnNhd ℝ (fun x => f x * ev q x) (Ioo l r) :=
    hf.mul ((analytic_ev q).mono (subset_univ _))
  have heqU : EqOn (ev p) (fun x => f x * ev q x) (Ioo l r) :=
    hall.eqOn_of_preconnected_of_eventuallyEq hprod isPreconnected_Ioo hzu hevent
  obtain ⟨c, hcu, hfc⟩ := hneg
  have hnear : ∀ᶠ x in 𝓝 c, x ∈ Ioo l r ∧ f x < 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hcu,
      (hf c hcu).continuousAt.eventually (gt_mem_nhds hfc)] with x hxu hfx
    exact ⟨hxu, hfx⟩
  have hqnear : ev q =ᶠ[𝓝 c] (fun _ => 0) := by
    filter_upwards [hnear] with x hx
    have hp := hpos x hx.1
    rw [heqU hx.1] at hp
    have hsq : 0 ≤ (ev q x) ^ 2 := sq_nonneg _
    have hzq : (ev q x) ^ 2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp hzq
  have hqall : EqOn (ev q) (fun _ => 0) univ :=
    (analytic_ev q).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      isPreconnected_univ (mem_univ c) hqnear
  apply hq
  exact coeff_eq_zero_of_ev_zero (hla.trans_lt (hab.trans_le hbr))
    (fun x _ => hqall (mem_univ x))


private def Admissible {d : ℕ} (l r : ℝ) (v : Pair d) : Prop :=
  ‖v‖ = 1 ∧
    (∀ x ∈ Ioo l r, |ev v.1 x| ≤ |ev v.2 x|) ∧
    (∀ x ∈ Ioo l r, 0 ≤ ev v.1 x * ev v.2 x)

private lemma denominator_ne_zero {d : ℕ} {l r : ℝ} (hlr : l < r)
    (v : Pair d) (hv : Admissible l r v) : v.2 ≠ 0 := by
  intro hq
  have hp : v.1 = 0 := coeff_eq_zero_of_ev_zero hlr (fun x hx => by
    have hb := hv.2.1 x hx
    simpa [hq, ev] using hb)
  have hz : v = 0 := Prod.ext hp hq
  simpa [hz] using hv.1

private theorem normalized_gap {d : ℕ} {l a b r : ℝ} {f : ℝ → ℝ}
    (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hf : AnalyticOnNhd ℝ f (Ioo l r))
    (hneg : ∃ c ∈ Ioo l r, f c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Pair d, Admissible l r v →
      ∃ x ∈ Ioo a b, δ ≤ |ev v.1 x - f x * ev v.2 x| := by
  classical
  by_contra! h
  choose v hv hsmall using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Pair d) 1).tendsto_subseq
    (fun n => by simpa only [Metric.mem_sphere, dist_zero_right] using (hv n).1)
  have hp (x : ℝ) : Tendsto (fun n => ev (v (φ n)).1 x) atTop (𝓝 (ev w.1 x)) :=
    ((continuous_ev x).comp continuous_fst).continuousAt.tendsto.comp hlim
  have hq (x : ℝ) : Tendsto (fun n => ev (v (φ n)).2 x) atTop (𝓝 (ev w.2 x)) :=
    ((continuous_ev x).comp continuous_snd).continuousAt.tendsto.comp hlim
  have hwA : Admissible l r w := by
    refine ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hw, ?_, ?_⟩
    · intro x hx
      exact le_of_tendsto_of_tendsto (hp x).abs (hq x).abs
        (Eventually.of_forall fun n => (hv (φ n)).2.1 x hx)
    · intro x hx
      exact le_of_tendsto_of_tendsto tendsto_const_nhds ((hp x).mul (hq x))
        (Eventually.of_forall fun n => (hv (φ n)).2.2 x hx)
  apply analytic_sign_obstruction hla hab hbr hf hneg w.1 w.2
    (denominator_ne_zero (hla.trans_lt (hab.trans_le hbr)) w hwA) hwA.2.2
  intro x hx
  have hres := ((hp x).sub ((tendsto_const_nhds (x := f x)).mul (hq x))).abs
  have hε : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hz : |ev w.1 x - f x * ev w.2 x| ≤ 0 :=
    le_of_tendsto_of_tendsto hres hε
      (Eventually.of_forall fun n => (hsmall (φ n) x hx).le)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))


private lemma probability_constraints {p q : ℝ} (hq : q ≠ 0)
    (h : 0 ≤ p / q ∧ p / q ≤ 1) : |p| ≤ |q| ∧ 0 ≤ p * q := by
  have he : p = (p / q) * q := (div_mul_cancel₀ p hq).symm
  constructor
  · calc
      |p| = |p / q| * |q| := by nth_rw 1 [he]; rw [abs_mul]
      _ ≤ 1 * |q| := mul_le_mul_of_nonneg_right
        (by simpa only [abs_of_nonneg h.1] using h.2) (abs_nonneg _)
      _ = |q| := one_mul _
  · calc
      0 ≤ (p / q) * (q * q) := mul_nonneg h.1 (mul_self_nonneg _)
      _ = p * q := by rw [← mul_assoc, div_mul_cancel₀ p hq]

private lemma normalize_admissible {d : ℕ} {l r : ℝ} (hlr : l < r) (v : Pair d)
    (hq : ∀ x ∈ Ioo l r, ev v.2 x ≠ 0)
    (hprob : ∀ x ∈ Ioo l r, 0 ≤ ev v.1 x / ev v.2 x ∧ ev v.1 x / ev v.2 x ≤ 1) :
    Admissible l r (NormedSpace.normalize v) := by
  obtain ⟨x, hx⟩ := Set.nonempty_Ioo.mpr hlr
  have hv : v ≠ 0 := by
    intro hz
    simpa [hz, ev] using hq x hx
  refine ⟨NormedSpace.norm_normalize hv, ?_, ?_⟩
  · intro y hy
    have hc := (probability_constraints (hq y hy) (hprob y hy)).1
    change |ev (‖v‖⁻¹ • v.1) y| ≤ |ev (‖v‖⁻¹ • v.2) y|
    simpa only [ev_smul, abs_mul] using mul_le_mul_of_nonneg_left hc (abs_nonneg ‖v‖⁻¹)
  · intro y hy
    have hc := (probability_constraints (hq y hy) (hprob y hy)).2
    change 0 ≤ ev (‖v‖⁻¹ • v.1) y * ev (‖v‖⁻¹ • v.2) y
    simp only [ev_smul]
    nlinarith [mul_nonneg (sq_nonneg ‖v‖⁻¹) hc]

private theorem coefficient_probability_gap {d : ℕ} {l a b r : ℝ} {f : ℝ → ℝ}
    (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hf : AnalyticOnNhd ℝ f (Ioo l r))
    (hneg : ∃ c ∈ Ioo l r, f c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Pair d,
      (∀ x ∈ Ioo l r, ev v.2 x ≠ 0) →
      (∀ x ∈ Ioo l r, 0 ≤ ev v.1 x / ev v.2 x ∧ ev v.1 x / ev v.2 x ≤ 1) →
      ∃ x ∈ Ioo a b, ε ≤ |ev v.1 x / ev v.2 x - f x| := by
  obtain ⟨δ, hδ, hgap⟩ := normalized_gap (d := d) hla hab hbr hf hneg
  have hc : Continuous (fun vx : (Pair d) × ℝ => ev vx.1.2 vx.2) := by
    simp_rw [ev_sum]
    fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_sphere (0 : Pair d) 1).prod
    (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hc.continuousOn
  have hK : 0 < max M 0 + 1 := by positivity
  refine ⟨δ / (max M 0 + 1), div_pos hδ hK, ?_⟩
  intro v hq hprob
  let w := NormedSpace.normalize v
  have hw : Admissible l r w :=
    normalize_admissible (hla.trans_lt (hab.trans_le hbr)) v hq hprob
  obtain ⟨x, hx, hdx⟩ := hgap w hw
  have hxu : x ∈ Ioo l r := ⟨hla.trans_lt hx.1, hx.2.trans_le hbr⟩
  have heval : |ev w.2 x| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (w, x)
      ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hw.1,
        ⟨hx.1.le, hx.2.le⟩⟩
  have hv : v ≠ 0 := by
    intro hz
    simpa [hz, ev] using hq x hxu
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hratio : ev w.1 x / ev w.2 x = ev v.1 x / ev v.2 x := by
    change ev (‖v‖⁻¹ • v.1) x / ev (‖v‖⁻¹ • v.2) x = _
    simp only [ev_smul]
    exact mul_div_mul_left _ _ (inv_ne_zero hn)
  have hqwx : ev w.2 x ≠ 0 := by
    change ev (‖v‖⁻¹ • v.2) x ≠ 0
    rw [ev_smul]
    exact mul_ne_zero (inv_ne_zero hn) (hq x hxu)
  have hfactor : |ev w.1 x - f x * ev w.2 x| =
      |ev v.1 x / ev v.2 x - f x| * |ev w.2 x| := by
    rw [← hratio, ← abs_mul]
    congr 1
    rw [sub_mul, div_mul_cancel₀ _ hqwx]
  rw [hfactor] at hdx
  refine ⟨x, hx, (div_le_iff₀ hK).mpr ?_⟩
  have hbound : |ev w.2 x| ≤ max M 0 + 1 := (heval.trans (le_max_left _ _)).trans (by linarith)
  exact hdx.trans (mul_le_mul_of_nonneg_left hbound (abs_nonneg _))


theorem bounded_degree_probability_response_gap (d : ℕ) {l a b r : ℝ} {f : ℝ → ℝ}
    (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hf : AnalyticOnNhd ℝ f (Ioo l r))
    (hneg : ∃ c ∈ Ioo l r, f c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P D : ℝ[X], P.natDegree ≤ d → D.natDegree ≤ d →
      (∀ x ∈ Ioo l r, D.eval x ≠ 0) →
      (∀ x ∈ Ioo l r, 0 ≤ P.eval x / D.eval x ∧ P.eval x / D.eval x ≤ 1) →
      ∃ x ∈ Ioo a b, ε ≤ |P.eval x / D.eval x - f x| := by
  obtain ⟨ε, hε, hgap⟩ := coefficient_probability_gap (d := d) hla hab hbr hf hneg
  refine ⟨ε, hε, ?_⟩
  intro P D hP hD hq hprob
  have hp' := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hP)
  have hq' := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hD)
  simpa only [ev, hp', hq'] using hgap (Polynomial.toFn (d + 1) P,
    Polynomial.toFn (d + 1) D) (by simpa only [ev, hq'] using hq)
    (by simpa only [ev, hp', hq'] using hprob)


noncomputable def sourceTarget (B C β h : ℝ) : ℝ :=
  (1 - h / C) / (2 * B) - (1 / 16) * h ^ β

private lemma sourceTarget_analytic (B C β : ℝ) :
    AnalyticOnNhd ℝ (sourceTarget B C β) (Ioi 0) := by
  have hpExp : AnalyticOnNhd ℝ (fun h : ℝ => Real.exp (Real.log h * β)) (Ioi 0) :=
    (analyticOnNhd_log.mul analyticOnNhd_const).rexp
  have hp : AnalyticOnNhd ℝ (fun h : ℝ => h ^ β) (Ioi 0) :=
    AnalyticOnNhd.congr isOpen_Ioi hpExp (fun h hh => (Real.rpow_def_of_pos hh β).symm)
  exact ((analyticOnNhd_const.sub analyticOnNhd_id.div_const).div_const).sub
    (analyticOnNhd_const.mul hp)

private lemma sourceTarget_negative (B C β : ℝ) (hC : 0 < C) (hβ : 0 < β) :
    ∃ h ∈ Ioo 0 C, sourceTarget B C β h < 0 := by
  have hc : Continuous (sourceTarget B C β) := by
    unfold sourceTarget
    exact ((continuous_const.sub (continuous_id.div_const C)).div_const (2 * B)).sub
      (continuous_const.mul (Real.continuous_rpow_const hβ.le))
  have hv : sourceTarget B C β C < 0 := by
    simp only [sourceTarget, div_self hC.ne', sub_self, zero_div, zero_sub]
    exact neg_neg_of_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hC β))
  have hcl : C ∈ closure (Ioo (0 : ℝ) C) := by
    rw [closure_Ioo hC.ne]
    exact ⟨hC.le, le_rfl⟩
  obtain ⟨h, hhneg, hh⟩ := mem_closure_iff.mp hcl
    {h | sourceTarget B C β h < 0} (isOpen_lt hc continuous_const) hv
  exact ⟨h, hh, hhneg⟩

/-- The scalar response obstruction used by §348.4, after the affine change from
the common coin parameter to the original gain. -/
private theorem source_response_gap (d : ℕ) (B C β : ℝ) (hC : (1 / 4 : ℝ) < C) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P D : ℝ[X], P.natDegree ≤ d → D.natDegree ≤ d →
      (∀ h ∈ Ioo (0 : ℝ) C, D.eval h ≠ 0) →
      (∀ h ∈ Ioo (0 : ℝ) C, 0 ≤ P.eval h / D.eval h ∧ P.eval h / D.eval h ≤ 1) →
      ∃ h ∈ Ioo (0 : ℝ) (1 / 4), ε ≤ |P.eval h / D.eval h - sourceTarget B C β h| := by
  exact bounded_degree_probability_response_gap d le_rfl (by norm_num) hC.le
    ((sourceTarget_analytic B C β).mono (fun _ hx => hx.1))
    (sourceTarget_negative B C β (by linarith) hβ)


/-- The original common coin rate, with its affine coordinate change compiled. -/
private theorem original_coin_response_gap (d : ℕ) (B C β : ℝ)
    (hB : 1 < B) (hC : 1 ≤ C) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P D : ℝ[X], P.natDegree ≤ d → D.natDegree ≤ d →
      (∀ t ∈ Ioo (0 : ℝ) 1, D.eval t ≠ 0) →
      (∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ P.eval t / D.eval t ∧ P.eval t / D.eval t ≤ 1) →
      ∃ h ∈ Ioo (0 : ℝ) (1 / 4),
        ε ≤ |P.eval ((1 - h / C) / B) / D.eval ((1 - h / C) / B) -
          sourceTarget B C β h| := by
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < C := by linarith
  let T : ℝ[X] := Polynomial.C (1 / B) - Polynomial.C (1 / (B * C)) * X
  have hT (h : ℝ) : T.eval h = (1 - h / C) / B := by
    simp only [T, eval_sub, eval_C, eval_mul, eval_X]
    field_simp
  have hdeg : T.natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    refine max_le ?_ ?_
    · simp
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hmap : ∀ h ∈ Ioo (0 : ℝ) C, (1 - h / C) / B ∈ Ioo (0 : ℝ) 1 := by
    intro h hh
    have hhC : h / C < 1 := (div_lt_one hC0).mpr hh.2
    have hpos : 0 < h / C := div_pos hh.1 hC0
    constructor
    · exact div_pos (by linarith) hB0
    · apply (div_lt_one hB0).mpr
      linarith
  obtain ⟨ε, hε, hgap⟩ := source_response_gap d B C β (by linarith) hβ
  refine ⟨ε, hε, ?_⟩
  intro P D hP hD hq hprob
  have hPc : (P.comp T).natDegree ≤ d := calc
    _ ≤ P.natDegree * T.natDegree := natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hP hdeg
    _ = d := Nat.mul_one _
  have hDc : (D.comp T).natDegree ≤ d := calc
    _ ≤ D.natDegree * T.natDegree := natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hD hdeg
    _ = d := Nat.mul_one _
  obtain ⟨h, hh, herr⟩ := hgap (P.comp T) (D.comp T) hPc hDc
    (fun h hh => by simpa only [eval_comp, hT] using hq _ (hmap h hh))
    (fun h hh => by simpa only [eval_comp, hT] using hprob _ (hmap h hh))
  exact ⟨h, hh, by simpa only [eval_comp, hT] using herr⟩



open Matrix

/-- Finite-horizon probability of absorption into one selected terminal event. -/
noncomputable def absorptionApprox {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | k + 1 => r + Q *ᵥ absorptionApprox Q r k

private lemma absorptionApprox_bounds {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hr : ∀ i, 0 ≤ r i)
    (hrow : ∀ i, r i + ∑ j, Q i j ≤ 1) :
    ∀ k i, 0 ≤ absorptionApprox Q r k i ∧ absorptionApprox Q r k i ≤ 1 := by
  intro k
  induction k with
  | zero => intro i; simp [absorptionApprox]
  | succ k ih =>
    intro i
    change 0 ≤ r i + ∑ j, Q i j * absorptionApprox Q r k j ∧
      r i + ∑ j, Q i j * absorptionApprox Q r k j ≤ 1
    constructor
    · exact add_nonneg (hr i) (Finset.sum_nonneg fun j _ => mul_nonneg (hQ i j) (ih j).1)
    · apply le_trans _ (hrow i)
      exact add_le_add (le_refl _) (Finset.sum_le_sum fun j _ =>
        (mul_le_mul_of_nonneg_left (ih j).2 (hQ i j)).trans_eq (mul_one _))

private lemma absorptionApprox_mono {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hr : ∀ i, 0 ≤ r i) :
    Monotone (absorptionApprox Q r) := by
  apply monotone_nat_of_le_succ
  intro k
  induction k with
  | zero => intro i; simpa [absorptionApprox] using hr i
  | succ k ih =>
    intro i
    change r i + ∑ j, Q i j * absorptionApprox Q r k j ≤
      r i + ∑ j, Q i j * absorptionApprox Q r (k + 1) j
    exact add_le_add (le_refl _) (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ih j) (hQ i j))

/-- Increasing limit of the actual finite-horizon event probabilities. -/
noncomputable def absorptionProbability {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (i : Fin n) : ℝ := ⨆ k, absorptionApprox Q r k i

private lemma absorptionProbability_spec {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hr : ∀ i, 0 ≤ r i)
    (hrow : ∀ i, r i + ∑ j, Q i j ≤ 1) :
    (∀ i, 0 ≤ absorptionProbability Q r i ∧ absorptionProbability Q r i ≤ 1) ∧
    (1 - Q) *ᵥ absorptionProbability Q r = r := by
  have hb (i : Fin n) : BddAbove (range (fun k => absorptionApprox Q r k i)) :=
    ⟨1, by rintro _ ⟨k, rfl⟩; exact (absorptionApprox_bounds Q r hQ hr hrow k i).2⟩
  have hlim : Tendsto (absorptionApprox Q r) atTop (𝓝 (absorptionProbability Q r)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_atTop_ciSup (fun a b hab => absorptionApprox_mono Q r hQ hr hab i) (hb i)
  constructor
  · intro i
    exact ⟨(absorptionApprox_bounds Q r hQ hr hrow 0 i).1.trans (le_ciSup (hb i) 0),
      ciSup_le fun k => (absorptionApprox_bounds Q r hQ hr hrow k i).2⟩
  · have hc : Continuous (fun v : Fin n → ℝ => r + Q *ᵥ v) :=
      continuous_const.add (continuous_const.matrix_mulVec continuous_id)
    have heq : absorptionProbability Q r = r + Q *ᵥ absorptionProbability Q r :=
      tendsto_nhds_unique (hlim.comp (tendsto_add_atTop_nat 1))
        (hc.continuousAt.tendsto.comp hlim)
    rw [sub_mulVec, one_mulVec]
    exact (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using heq))

private lemma affine_system_rational {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (u v α : Fin n → ℝ) (γ : ℝ)
    (y : ℝ → Fin n → ℝ)
    (hsolve : ∀ t ∈ Ioo (0 : ℝ) 1, (t • A + B) *ᵥ y t = t • u + v)
    (hdet : ∀ t ∈ Ioo (0 : ℝ) 1, (t • A + B).det ≠ 0) :
    ∃ P D : ℝ[X], P.natDegree ≤ n ∧ D.natDegree ≤ n ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, D.eval t ≠ 0) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, γ + α ⬝ᵥ y t = P.eval t / D.eval t := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ[X] := (X : ℝ[X]) • A.map Polynomial.C + B.map Polynomial.C
  let D := M.det
  let N (i : Fin n) : ℝ[X] :=
    ((X : ℝ[X]) • (A.updateCol i u).map Polynomial.C + (B.updateCol i v).map Polynomial.C).det
  let P : ℝ[X] := Polynomial.C γ * D + ∑ i, Polynomial.C (α i) * N i
  have hD : D.natDegree ≤ n := by
    simpa [D, M] using Polynomial.natDegree_det_X_add_C_le A B
  have hN (i : Fin n) : (N i).natDegree ≤ n := by
    simpa [N] using Polynomial.natDegree_det_X_add_C_le (A.updateCol i u) (B.updateCol i v)
  have hP : P.natDegree ≤ n := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans hD
    · exact natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans (hN i)
  have heval (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
      ((X : ℝ[X]) • A.map Polynomial.C + B.map Polynomial.C).det.eval t = (t • A + B).det := by
    change (Polynomial.evalRingHom t) _ = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change ((X : ℝ[X]) * Polynomial.C (A i j) + Polynomial.C (B i j)).eval t =
      t * A i j + B i j
    simp only [eval_add, eval_mul, eval_X, eval_C]
  have hDeval (t : ℝ) : D.eval t = (t • A + B).det := heval A B t
  refine ⟨P, D, hP, hD, fun t ht => by rw [hDeval]; exact hdet t ht, ?_⟩
  intro t ht
  have hNi (i : Fin n) : (N i).eval t = (t • A + B).det * y t i := by
    rw [show (N i).eval t = (t • A.updateCol i u + B.updateCol i v).det from
      heval _ _ t]
    have hcol : t • A.updateCol i u + B.updateCol i v =
        (t • A + B).updateCol i (t • u + v) := by
      ext j k
      by_cases hki : k = i <;> simp [Matrix.updateCol, hki]
    rw [hcol, ← cramer_apply, cramer_eq_adjugate_mulVec, ← hsolve t ht,
      mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    rfl
  apply (eq_div_iff (by rw [hDeval]; exact hdet t ht)).mpr
  simp only [P, eval_add, eval_mul, eval_C, eval_finsetSum, hNi, hDeval,
    dotProduct]
  rw [add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A common-coin finite table for one terminal event.  The complementary
terminal event receives the remaining row mass.  Entries and private weights
are real and independent of the unknown coin rate. -/
structure EventController (n : ℕ) where
  Qzero : Matrix (Fin n) (Fin n) ℝ
  Qone : Matrix (Fin n) (Fin n) ℝ
  rzero : Fin n → ℝ
  rone : Fin n → ℝ
  initial : Fin n → ℝ
  immediate : ℝ
  Qzero_nonneg : ∀ i j, 0 ≤ Qzero i j
  Qone_nonneg : ∀ i j, 0 ≤ Qone i j
  rzero_nonneg : ∀ i, 0 ≤ rzero i
  rone_nonneg : ∀ i, 0 ≤ rone i
  row_zero : ∀ i, rzero i + ∑ j, Qzero i j ≤ 1
  row_one : ∀ i, rone i + ∑ j, Qone i j ≤ 1
  initial_nonneg : ∀ i, 0 ≤ initial i
  immediate_nonneg : 0 ≤ immediate
  initial_mass : immediate + ∑ i, initial i ≤ 1

noncomputable def EventController.transition {n : ℕ} (A : EventController n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1 - t) • A.Qzero + t • A.Qone

noncomputable def EventController.exit {n : ℕ} (A : EventController n) (t : ℝ) :
    Fin n → ℝ := (1 - t) • A.rzero + t • A.rone

noncomputable def EventController.response {n : ℕ} (A : EventController n) (t : ℝ) : ℝ :=
  A.immediate + A.initial ⬝ᵥ absorptionProbability (A.transition t) (A.exit t)

private lemma EventController.row_bounds {n : ℕ} (A : EventController n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∀ i j, 0 ≤ A.transition t i j) ∧ (∀ i, 0 ≤ A.exit t i) ∧
    (∀ i, A.exit t i + ∑ j, A.transition t i j ≤ 1) := by
  have ht' : 0 ≤ 1 - t := by linarith [ht.2]
  refine ⟨fun i j => add_nonneg (mul_nonneg ht' (A.Qzero_nonneg i j))
    (mul_nonneg ht.1.le (A.Qone_nonneg i j)),
    fun i => add_nonneg (mul_nonneg ht' (A.rzero_nonneg i))
      (mul_nonneg ht.1.le (A.rone_nonneg i)), ?_⟩
  intro i
  have h0 := mul_le_mul_of_nonneg_left (A.row_zero i) ht'
  have h1 := mul_le_mul_of_nonneg_left (A.row_one i) ht.1.le
  dsimp [EventController.exit, EventController.transition]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

private lemma absorptionApprox_zero_iff {n : ℕ}
    (Q Q' : Matrix (Fin n) (Fin n) ℝ) (r r' : Fin n → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQ' : ∀ i j, 0 ≤ Q' i j)
    (hr : ∀ i, 0 ≤ r i) (hr' : ∀ i, 0 ≤ r' i)
    (hrow : ∀ i, r i + ∑ j, Q i j ≤ 1)
    (hrow' : ∀ i, r' i + ∑ j, Q' i j ≤ 1)
    (hQs : ∀ i j, Q i j = 0 ↔ Q' i j = 0)
    (hrs : ∀ i, r i = 0 ↔ r' i = 0) :
    ∀ k i, absorptionApprox Q r k i = 0 ↔ absorptionApprox Q' r' k i = 0 := by
  intro k
  induction k with
  | zero => simp [absorptionApprox]
  | succ k ih =>
    intro i
    have hnon (j : Fin n) :=
      mul_nonneg (hQ i j) (absorptionApprox_bounds Q r hQ hr hrow k j).1
    have hnon' (j : Fin n) :=
      mul_nonneg (hQ' i j) (absorptionApprox_bounds Q' r' hQ' hr' hrow' k j).1
    change (r i + ∑ j, Q i j * absorptionApprox Q r k j = 0) ↔
      (r' i + ∑ j, Q' i j * absorptionApprox Q' r' k j = 0)
    rw [add_eq_zero_iff_of_nonneg (hr i) (Finset.sum_nonneg fun j _ => hnon j),
      add_eq_zero_iff_of_nonneg (hr' i) (Finset.sum_nonneg fun j _ => hnon' j),
      Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon j),
      Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon' j)]
    simp only [mul_eq_zero, hQs, hrs, ih]

private lemma total_absorptionApprox {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) :
    ∀ k, absorptionApprox Q (1 - Q *ᵥ 1) k = 1 - Q ^ k *ᵥ 1 := by
  intro k
  induction k with
  | zero => simp [absorptionApprox]
  | succ k ih =>
    simp only [absorptionApprox, ih, mulVec_sub, pow_succ', ← mulVec_mulVec]
    abel

private lemma det_ne_zero_of_exit {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hexit : ∀ i, ∃ k, 0 < absorptionApprox Q (1 - Q *ᵥ 1) k i) :
    (1 - Q).det ≠ 0 := by
  classical
  intro hz
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|)
    ⟨j, Finset.mem_univ j⟩
  have hM : 0 < |v i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ j))
  have hfix : Q *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hker
    exact hker.symm
  have hpow (k : ℕ) : Q ^ k *ᵥ v = v := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, hfix]
  obtain ⟨k, hk⟩ := hexit i
  rw [total_absorptionApprox] at hk
  have hbound : |v i| ≤ (Q ^ k *ᵥ (1 : Fin n → ℝ)) i * |v i| := by
    calc
      |v i| = |∑ j, (Q ^ k) i j * v j| := (congrArg (fun w : Fin n → ℝ => |w i|) (hpow k)).symm
      _ ≤ ∑ j, |(Q ^ k) i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, (Q ^ k) i j * |v j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (Matrix.pow_apply_nonneg hQ k i j)]
      _ ≤ ∑ j, (Q ^ k) i j * |v i| := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j))
          (Matrix.pow_apply_nonneg hQ k i j)
      _ = (Q ^ k *ᵥ (1 : Fin n → ℝ)) i * |v i| := by
        simp [mulVec, dotProduct, Finset.sum_mul]
  change 0 < 1 - (Q ^ k *ᵥ (1 : Fin n → ℝ)) i at hk
  nlinarith

/-- Total one-step terminal mass, independently of the selected event. -/
noncomputable def EventController.totalExit {n : ℕ} (A : EventController n) (t : ℝ) :
    Fin n → ℝ := 1 - A.transition t *ᵥ 1

/-- Almost-sure termination from every retained configuration at one interior rate. -/
def EventController.Terminates {n : ℕ} (A : EventController n) : Prop :=
  ∃ t ∈ Ioo (0 : ℝ) 1, ∀ i,
    absorptionProbability (A.transition t) (A.totalExit t) i = 1

private lemma EventController.total_bounds {n : ℕ} (A : EventController n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∀ i, 0 ≤ A.totalExit t i) ∧
    (∀ i, A.totalExit t i + ∑ j, A.transition t i j ≤ 1) := by
  have hb := A.row_bounds ht
  constructor
  · intro i
    have := hb.2.2 i
    have := hb.2.1 i
    simp only [EventController.totalExit, Pi.sub_apply, Pi.one_apply,
      mulVec, dotProduct, mul_one]
    linarith
  · intro i
    simp [EventController.totalExit, mulVec, dotProduct]

private lemma EventController.common_support {n : ℕ} (A : EventController n)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∀ i j, A.transition s i j = 0 ↔ A.transition t i j = 0) ∧
    (∀ i, A.totalExit s i = 0 ↔ A.totalExit t i = 0) := by
  have hz (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ)
      (hx : x ∈ Ioo (0 : ℝ) 1) :
      (1 - x) * a + x * b = 0 ↔ a = 0 ∧ b = 0 := by
    rw [add_eq_zero_iff_of_nonneg (mul_nonneg (by linarith [hx.2]) ha)
      (mul_nonneg hx.1.le hb)]
    simp only [mul_eq_zero, (by linarith [hx.2] : 1 - x ≠ 0), hx.1.ne', false_or]
  constructor
  · intro i j
    exact (hz _ _ (A.Qzero_nonneg i j) (A.Qone_nonneg i j) s hs).trans
      (hz _ _ (A.Qzero_nonneg i j) (A.Qone_nonneg i j) t ht).symm
  · intro i
    have he (x : ℝ) : A.totalExit x i =
        (1 - x) * (1 - ∑ j, A.Qzero i j) + x * (1 - ∑ j, A.Qone i j) := by
      simp [EventController.totalExit, EventController.transition, mulVec, dotProduct,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have h0 : 0 ≤ 1 - ∑ j, A.Qzero i j := by
      linarith [A.row_zero i, A.rzero_nonneg i]
    have h1 : 0 ≤ 1 - ∑ j, A.Qone i j := by
      linarith [A.row_one i, A.rone_nonneg i]
    rw [he, he]
    exact (hz _ _ h0 h1 s hs).trans (hz _ _ h0 h1 t ht).symm

private lemma EventController.det_ne_zero {n : ℕ} (A : EventController n)
    (hterm : A.Terminates) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 - A.transition t).det ≠ 0 := by
  obtain ⟨s, hs, hterm⟩ := hterm
  apply det_ne_zero_of_exit _ (A.row_bounds ht).1
  intro i
  have he : ∃ k, 0 < absorptionApprox (A.transition s) (A.totalExit s) k i := by
    by_contra! h
    have hle : absorptionProbability (A.transition s) (A.totalExit s) i ≤ 0 := ciSup_le h
    rw [hterm i] at hle
    linarith
  obtain ⟨k, hk⟩ := he
  have hzero := absorptionApprox_zero_iff (A.transition s) (A.transition t)
    (A.totalExit s) (A.totalExit t) (A.row_bounds hs).1 (A.row_bounds ht).1
    (A.total_bounds hs).1 (A.total_bounds ht).1
    (A.total_bounds hs).2 (A.total_bounds ht).2
    (A.common_support hs ht).1 (A.common_support hs ht).2 k i
  exact ⟨k, lt_of_le_of_ne (absorptionApprox_bounds _ _ (A.row_bounds ht).1
    (A.total_bounds ht).1 (A.total_bounds ht).2 k i).1
      (fun hz => hk.ne' (hzero.mpr hz.symm))⟩

private lemma EventController.rational_response {n : ℕ} (A : EventController n)
    (htrans : A.Terminates) :
    ∃ P D : ℝ[X], P.natDegree ≤ n ∧ D.natDegree ≤ n ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, D.eval t ≠ 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, A.response t = P.eval t / D.eval t) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ A.response t ∧ A.response t ≤ 1) := by
  have heq (t : ℝ) : t • (A.Qzero - A.Qone) + (1 - A.Qzero) = 1 - A.transition t := by
    ext i j
    simp [EventController.transition]
    ring
  have hexit (t : ℝ) : t • (A.rone - A.rzero) + A.rzero = A.exit t := by
    ext i
    simp [EventController.exit]
    ring
  have hspec (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    absorptionProbability_spec (A.transition t) (A.exit t) (A.row_bounds ht).1
      (A.row_bounds ht).2.1 (A.row_bounds ht).2.2
  obtain ⟨P, D, hP, hD, hden, hrat⟩ := affine_system_rational
    (A.Qzero - A.Qone) (1 - A.Qzero) (A.rone - A.rzero) A.rzero
    A.initial A.immediate (fun t => absorptionProbability (A.transition t) (A.exit t))
    (fun t ht => by rw [heq, hexit]; exact (hspec t ht).2)
    (fun t ht => by rw [heq]; exact A.det_ne_zero htrans ht)
  refine ⟨P, D, hP, hD, hden, hrat, ?_⟩
  intro t ht
  constructor
  · exact add_nonneg A.immediate_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (A.initial_nonneg i) ((hspec t ht).1 i).1)
  · apply le_trans _ A.initial_mass
    exact add_le_add (le_refl _) (Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_left ((hspec t ht).1 i).2 (A.initial_nonneg i)).trans_eq (mul_one _))

/-- Uniform event-error obstruction for actual finite-horizon absorption limits,
assuming almost-sure termination at one interior common-coin rate. -/
theorem transient_event_response_gap (d : ℕ) (B C β : ℝ)
    (hB : 1 < B) (hC : 1 ≤ C) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n ≤ d, ∀ A : EventController n, A.Terminates →
      ∃ h ∈ Ioo (0 : ℝ) (1 / 4),
        ε ≤ |A.response ((1 - h / C) / B) - sourceTarget B C β h| := by
  obtain ⟨ε, hε, hgap⟩ := original_coin_response_gap d B C β hB hC hβ
  refine ⟨ε, hε, ?_⟩
  intro n hn A htrans
  obtain ⟨P, D, hP, hD, hden, hrat, hprob⟩ := A.rational_response htrans
  obtain ⟨h, hh, herr⟩ := hgap P D (hP.trans hn) (hD.trans hn) hden
    (fun t ht => by rw [← hrat t ht]; exact hprob t ht)
  have ht : (1 - h / C) / B ∈ Ioo (0 : ℝ) 1 := by
    have hC0 : 0 < C := by linarith
    have hB0 : 0 < B := by linarith
    have hp : 0 < h / C := div_pos hh.1 hC0
    have hlt : h / C < 1 := (div_lt_one hC0).mpr (by linarith [hh.2])
    exact ⟨div_pos (by linarith) hB0, (div_lt_one hB0).mpr (by linarith)⟩
  exact ⟨h, hh, by rw [hrat _ ht]; exact herr⟩

end D5.S3.Observer.ProbabilisticClosure.FiniteStateProbabilityResponseGap
