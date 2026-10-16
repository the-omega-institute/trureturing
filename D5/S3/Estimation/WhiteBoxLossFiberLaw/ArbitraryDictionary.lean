/- GID: D5/S3/Estimation/WhiteBoxLossFiberLaw/ArbitraryDictionary
   generality: G
   mirror-B: D5/B/S3/Estimation/WhiteBoxLossFiberLaw/ArbitraryDictionary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Radial equality and exact absorption for arbitrary finite unit dictionaries. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

namespace D5.S3.Estimation.WhiteBoxLossFiberLaw.ArbitraryDictionary

open scoped BigOperators RealInnerProductSpace

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def FeasibleCode (c : ι → ℝ) : Prop := ∀ i, 0 ≤ c i

def combination (D : ι → E) (c : ι → ℝ) : E := ∑ i, c i • D i

def energy (lam : ℝ) (x : E) (D : ι → E) (c : ι → ℝ) : ℝ :=
  ‖x - combination D c‖ ^ 2 / 2 + lam * ∑ i, c i

def cost (lam : ℝ) (x : E) (D : ι → E) : ℝ :=
  sInf {z : ℝ | ∃ c, FeasibleCode c ∧ energy lam x D c = z}

private theorem energy_nonneg (lam : ℝ) (x : E) (D : ι → E) (c : ι → ℝ)
    (hlam : 0 ≤ lam) (hc : FeasibleCode c) : 0 ≤ energy lam x D c :=
  add_nonneg (by positivity) (mul_nonneg hlam (Finset.sum_nonneg (fun i _ => hc i)))

private theorem cost_nonempty (lam : ℝ) (x : E) (D : ι → E) :
    {z : ℝ | ∃ c, FeasibleCode c ∧ energy lam x D c = z}.Nonempty :=
  ⟨energy lam x D (fun _ => 0), (fun _ => 0), (fun _ => le_rfl), rfl⟩

private theorem cost_bdd (lam : ℝ) (x : E) (D : ι → E) (hlam : 0 ≤ lam) :
    BddBelow {z : ℝ | ∃ c, FeasibleCode c ∧ energy lam x D c = z} := by
  refine ⟨0, ?_⟩
  rintro z ⟨c, hc, rfl⟩
  exact energy_nonneg lam x D c hlam hc

private theorem cost_le_energy (lam : ℝ) (x : E) (D : ι → E) (c : ι → ℝ)
    (hlam : 0 ≤ lam) (hc : FeasibleCode c) : cost lam x D ≤ energy lam x D c :=
  csInf_le (cost_bdd lam x D hlam) ⟨c, hc, rfl⟩

/- Positive regularization confines every improving nonnegative code to a compact box. -/
private theorem cost_attained (lam : ℝ) (x : E) (D : ι → E) (hlam : 0 < lam) :
    ∃ c, FeasibleCode c ∧ energy lam x D c = cost lam x D := by
  classical
  let B : ℝ := ‖x‖ ^ 2 / (2 * lam)
  have hB : 0 ≤ B := by simp only [B]; positivity
  have hzero : (0 : ι → ℝ) ∈ Set.Icc 0 (fun _ => B) :=
    ⟨le_rfl, fun _ => hB⟩
  have hcont : Continuous (energy lam x D) := by
    unfold energy combination
    fun_prop
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  have hfc : FeasibleCode c := hc.1
  have hglob : ∀ d, FeasibleCode d → energy lam x D c ≤ energy lam x D d := by
    intro d hd
    by_cases hdbox : d ∈ Set.Icc 0 (fun _ => B)
    · exact hmin hdbox
    · have hi : ∃ i, B < d i := by
        by_contra hn
        push Not at hn
        exact hdbox ⟨hd, hn⟩
      obtain ⟨i, hi⟩ := hi
      have hs : d i ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
      have hpen : lam * B < lam * ∑ j, d j :=
        mul_lt_mul_of_pos_left (hi.trans_le hs) hlam
      have hbase : lam * B = ‖x‖ ^ 2 / 2 := by simp only [B]; field_simp
      have hz0 : energy lam x D c ≤ energy lam x D 0 := hmin hzero
      have hz : energy lam x D c ≤ ‖x‖ ^ 2 / 2 := by
        simpa only [energy, combination, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
          sub_zero, mul_zero, add_zero] using hz0
      have hres := sq_nonneg ‖x - combination D d‖
      change ‖x - combination D c‖ ^ 2 / 2 + lam * ∑ i, c i ≤ ‖x‖ ^ 2 / 2 at hz
      change energy lam x D c ≤ energy lam x D d
      unfold energy
      rw [hbase] at hpen
      linarith
  refine ⟨c, hfc, le_antisymm ?_ (cost_le_energy lam x D c hlam.le hfc)⟩
  apply le_csInf (cost_nonempty lam x D)
  rintro z ⟨d, hd, rfl⟩
  exact hglob d hd

private theorem energy_excess (lam n : ℝ) (e : E) (D : ι → E) (c : ι → ℝ)
    (he : ‖e‖ = 1) :
    energy lam (n • e) D c - (lam * n - lam ^ 2 / 2) =
      ‖(n - lam) • e - combination D c‖ ^ 2 / 2 +
        lam * ∑ i, c i * (1 - inner ℝ e (D i)) := by
  unfold energy
  rw [norm_sub_sq_real, norm_sub_sq_real]
  have hs : inner ℝ e (combination D c) = ∑ i, c i * inner ℝ e (D i) := by
    simp [combination, inner_sum, inner_smul_right]
  rw [real_inner_smul_left, real_inner_smul_left, hs]
  simp only [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

omit [Fintype ι] in
private theorem defects_nonneg (e : E) (D : ι → E) (c : ι → ℝ)
    (he : ‖e‖ = 1) (hD : ∀ i, ‖D i‖ = 1) (hc : FeasibleCode c) :
    ∀ i, 0 ≤ c i * (1 - inner ℝ e (D i)) := by
  intro i
  have hi := real_inner_le_norm e (D i)
  rw [he, hD i, mul_one] at hi
  exact mul_nonneg (hc i) (sub_nonneg.mpr hi)

private theorem energy_radial_lower (lam n : ℝ) (e : E) (D : ι → E) (c : ι → ℝ)
    (he : ‖e‖ = 1) (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 ≤ lam) (hc : FeasibleCode c) :
    lam * n - lam ^ 2 / 2 ≤ energy lam (n • e) D c := by
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => defects_nonneg e D c he hD hc i)
  have hp := mul_nonneg hlam hs
  have hr := sq_nonneg ‖(n - lam) • e - combination D c‖
  have hx := energy_excess lam n e D c he
  linarith

private theorem cost_radial_lower (lam n : ℝ) (e : E) (D : ι → E)
    (he : ‖e‖ = 1) (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 ≤ lam) :
    lam * n - lam ^ 2 / 2 ≤ cost lam (n • e) D := by
  apply le_csInf (cost_nonempty lam (n • e) D)
  rintro z ⟨c, hc, rfl⟩
  exact energy_radial_lower lam n e D c he hD hlam hc

/- Vanishing energy excess forces every positive coefficient into the signal direction. -/
private theorem energy_radial_iff (lam n : ℝ) (e : E) (D : ι → E) (c : ι → ℝ)
    (he : ‖e‖ = 1) (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 < lam) (hc : FeasibleCode c) :
    energy lam (n • e) D c = lam * n - lam ^ 2 / 2 ↔
      (∑ i, c i) = n - lam ∧ ∀ i, c i ≠ 0 → D i = e := by
  constructor
  · intro hcost
    have hterms := defects_nonneg e D c he hD hc
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterms i)
    have hp := mul_nonneg hlam.le hs
    have hr := sq_nonneg ‖(n - lam) • e - combination D c‖
    have hx := energy_excess lam n e D c he
    have hsum : (∑ i, c i * (1 - inner ℝ e (D i))) = 0 := by nlinarith
    have hres : (n - lam) • e = combination D c := by
      have hz : ‖(n - lam) • e - combination D c‖ = 0 := by nlinarith
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    have halign : ∀ i, c i ≠ 0 → D i = e := by
      intro i hi
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterms j)).mp hsum i
        (Finset.mem_univ i)
      have hinner : inner ℝ e (D i) = 1 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact (hi h).elim
        · linarith
      exact ((inner_eq_one_iff_of_norm_eq_one he (hD i)).mp hinner).symm
    have hcomb : combination D c = (∑ i, c i) • e := by
      unfold combination
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i = 0
      · simp [hi]
      · rw [halign i hi]
    have hn : n - lam = ∑ i, c i := by
      have hin := congrArg (fun y => inner ℝ e y) (hres.trans hcomb)
      simpa [inner_smul_right, real_inner_self_eq_norm_sq, he] using hin
    exact ⟨hn.symm, halign⟩
  · rintro ⟨hsum, halign⟩
    have hcomb : combination D c = (n - lam) • e := by
      rw [← hsum, combination, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i = 0
      · simp [hi]
      · rw [halign i hi]
    unfold energy
    rw [hcomb, hsum]
    have hsub : n • e - (n - lam) • e = lam • e := by module
    rw [hsub, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hlam]
    ring

private theorem radial_cost_iff (lam n : ℝ) (e : E) (D : ι → E)
    (he : ‖e‖ = 1) (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 < lam) (hn : lam < n) :
    cost lam (n • e) D = lam * n - lam ^ 2 / 2 ↔ ∃ i, D i = e := by
  classical
  constructor
  · intro hcost
    obtain ⟨c, hc, hce⟩ := cost_attained lam (n • e) D hlam
    obtain ⟨hmass, halign⟩ := (energy_radial_iff lam n e D c he hD hlam hc).mp
      (hce.trans hcost)
    have hex : ∃ i, c i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      simp [hnone] at hmass
      linarith
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, halign i hi⟩
  · rintro ⟨i, hi⟩
    let c : ι → ℝ := fun j => if j = i then n - lam else 0
    have hc : FeasibleCode c := by intro j; dsimp [c]; split_ifs <;> linarith
    have hmass : (∑ j, c j) = n - lam := by simp [c]
    have halign : ∀ j, c j ≠ 0 → D j = e := by
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hi
      · exact (hj (by simp [c, hji])).elim
    have henergy := (energy_radial_iff lam n e D c he hD hlam hc).mpr ⟨hmass, halign⟩
    apply le_antisymm
    · exact henergy ▸ cost_le_energy lam (n • e) D c hlam.le hc
    · exact cost_radial_lower lam n e D he hD hlam.le

/-- The radial floor, exact alignment criterion, and all nonnegative optimal
splittings for a nonzero signal in an arbitrary finite unit dictionary. -/
theorem single_point_radial (lam : ℝ) (x : E) (D : ι → E)
    (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 < lam) (hx : lam < ‖x‖) :
    lam * ‖x‖ - lam ^ 2 / 2 ≤ cost lam x D ∧
    (cost lam x D = lam * ‖x‖ - lam ^ 2 / 2 ↔ ∃ i, D i = ‖x‖⁻¹ • x) ∧
    (∀ c, FeasibleCode c →
      (energy lam x D c = lam * ‖x‖ - lam ^ 2 / 2 ↔
        (∑ i, c i) = ‖x‖ - lam ∧ ∀ i, c i ≠ 0 → D i = ‖x‖⁻¹ • x)) ∧
    (∀ i, D i = ‖x‖⁻¹ • x →
      FeasibleCode (fun j => if j = i then ‖x‖ - lam else 0) ∧
      energy lam x D (fun j => if j = i then ‖x‖ - lam else 0) = cost lam x D) := by
  classical
  have hnx : 0 < ‖x‖ := hlam.trans hx
  have he : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx), inv_mul_cancel₀ hnx.ne']
  have hrepr : ‖x‖ • (‖x‖⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  have hlow := cost_radial_lower lam ‖x‖ (‖x‖⁻¹ • x) D he hD hlam.le
  have heq := radial_cost_iff lam ‖x‖ (‖x‖⁻¹ • x) D he hD hlam hx
  rw [hrepr] at hlow heq
  refine ⟨hlow, heq, ?_, ?_⟩
  · intro c hc
    simpa only [hrepr] using energy_radial_iff lam ‖x‖ (‖x‖⁻¹ • x) D c he hD hlam hc
  · intro i hi
    have hc : FeasibleCode (fun j => if j = i then ‖x‖ - lam else 0) := by
      intro j; dsimp only; split_ifs <;> linarith
    refine ⟨hc, ?_⟩
    rw [heq.mpr ⟨i, hi⟩]
    have hcrit := energy_radial_iff lam ‖x‖ (‖x‖⁻¹ • x) D
      (fun j => if j = i then ‖x‖ - lam else 0) he hD hlam hc
    rw [hrepr] at hcrit
    apply hcrit.mpr
    refine ⟨by simp, ?_⟩
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact (hj (by simp [hji])).elim

/-- Expected coding cost on the three-point support, with unrestricted zero weight. -/
def objective (lam p0 a b : ℝ) (u v : E) (D : ι → E) : ℝ :=
  p0 * cost lam 0 D + a * cost lam u D + b * cost lam (u + v) D

private theorem cost_zero (lam : ℝ) (D : ι → E) (hlam : 0 ≤ lam) :
    cost lam 0 D = 0 := by
  apply le_antisymm
  · simpa [energy, combination] using cost_le_energy lam 0 D (fun _ => 0) hlam
      (fun _ => le_rfl)
  · apply le_csInf (cost_nonempty lam 0 D)
    rintro z ⟨c, hc, rfl⟩
    exact energy_nonneg lam 0 D c hlam hc

private theorem faithful_sum_cost (lam : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1) :
    cost lam (u + v) (![u, v]) = 2 * lam - lam ^ 2 := by
  have henergy : ∀ c : Fin 2 → ℝ,
      energy lam (u + v) (![u, v]) c = 2 * lam - lam ^ 2 +
        ((c 0 - (1 - lam)) ^ 2 + (c 1 - (1 - lam)) ^ 2) / 2 := by
    intro c
    have hcomb : combination (![u, v]) c = c 0 • u + c 1 • v := by
      simp [combination, Fin.sum_univ_two]
    have hsub : u + v - (c 0 • u + c 1 • v) =
        (1 - c 0) • u + (1 - c 1) • v := by module
    unfold energy
    rw [hcomb, hsub, norm_add_sq_real]
    simp only [norm_smul, hu, hv, mul_one, Real.norm_eq_abs, sq_abs,
      inner_smul_right, real_inner_smul_left, horth, mul_zero, add_zero, Fin.sum_univ_two]
    ring
  apply le_antisymm
  · let c : Fin 2 → ℝ := fun _ => 1 - lam
    have hc : FeasibleCode c := fun _ => sub_nonneg.mpr hsmall.le
    have he : energy lam (u + v) (![u, v]) c = 2 * lam - lam ^ 2 := by
      rw [henergy]; dsimp [c]; ring
    exact he ▸ cost_le_energy lam (u + v) (![u, v]) c hlam.le hc
  · apply le_csInf (cost_nonempty lam (u + v) (![u, v]))
    rintro z ⟨c, _, rfl⟩
    rw [henergy]
    nlinarith [sq_nonneg (c 0 - (1 - lam)), sq_nonneg (c 1 - (1 - lam))]

/-- For every finite unit dictionary the strict-hierarchy objective has exactly
the dictionaries containing both sample directions as minimizers. The canonical
pair attains the common lower bound; every optimal joint-sample code splits its
mass only between repeated copies of the bisector. The orthogonal pair has the
stated strictly positive excess. -/
theorem whitebox_absorption (lam p0 a b : ℝ) (u v : E) (D : ι → E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0)
    (hD : ∀ i, ‖D i‖ = 1) (hlam : 0 < lam) (hsmall : lam < 1)
    (ha : 0 < a) (hb : 0 < b) :
    let w := (Real.sqrt 2)⁻¹ • (u + v)
    let B := a * (lam - lam ^ 2 / 2) + b * (Real.sqrt 2 * lam - lam ^ 2 / 2)
    B ≤ objective lam p0 a b u v D ∧
    (objective lam p0 a b u v D = B ↔
      (∃ i, D i = u) ∧ (∃ i, D i = w)) ∧
    (objective lam p0 a b u v D = B → ∀ c, FeasibleCode c →
      (energy lam (u + v) D c = cost lam (u + v) D ↔
        (∑ i, c i) = Real.sqrt 2 - lam ∧ ∀ i, c i ≠ 0 → D i = w)) ∧
    objective lam p0 a b u v (![u, w]) = B ∧
    objective lam p0 a b u v (![u, v]) - B =
      b * lam * (2 - Real.sqrt 2 - lam / 2) ∧
    0 < b * lam * (2 - Real.sqrt 2 - lam / 2) ∧
    B < objective lam p0 a b u v (![u, v]) := by
  classical
  let w := (Real.sqrt 2)⁻¹ • (u + v)
  let B := a * (lam - lam ^ 2 / 2) + b * (Real.sqrt 2 * lam - lam ^ 2 / 2)
  change B ≤ _ ∧ _
  have hsqrt : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg 2
    nlinarith
  have hsum : ‖u + v‖ = Real.sqrt 2 := by
    have h := norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr horth
    simpa only [hu, hv, mul_one, one_add_one_eq_two] using h
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith)), hsum,
      inv_mul_cancel₀ (ne_of_gt (by linarith : 0 < Real.sqrt 2))]
  have hpair : ∀ i : Fin 2, ‖(![u, w]) i‖ = 1 := by intro i; fin_cases i <;> assumption
  have hfaith : ∀ i : Fin 2, ‖(![u, v]) i‖ = 1 := by intro i; fin_cases i <;> assumption
  have hzero := cost_zero lam D hlam.le
  have hru := single_point_radial lam u D hD hlam (by simpa [hu] using hsmall)
  have hrw := single_point_radial lam (u + v) D hD hlam (by rw [hsum]; linarith)
  simp only [hu, inv_one, one_smul, mul_one] at hru
  rw [hsum] at hrw
  have hlowu := hru.1
  have hloww : Real.sqrt 2 * lam - lam ^ 2 / 2 ≤ cost lam (u + v) D := by
    simpa [mul_comm] using hrw.1
  have hweightsu := mul_le_mul_of_nonneg_left hlowu ha.le
  have hweightsw := mul_le_mul_of_nonneg_left hloww hb.le
  have hobj : objective lam p0 a b u v D =
      a * cost lam u D + b * cost lam (u + v) D := by simp [objective, hzero]
  have hequ : objective lam p0 a b u v D = B → cost lam u D = lam - lam ^ 2 / 2 := by
    intro h; rw [hobj] at h; simp only [B] at h; nlinarith
  have heqw : objective lam p0 a b u v D = B →
      cost lam (u + v) D = lam * Real.sqrt 2 - lam ^ 2 / 2 := by
    intro h; rw [hobj] at h; simp only [B] at h; nlinarith
  have hcanonicalu : cost lam u (![u, w]) = lam - lam ^ 2 / 2 := by
    have h := (single_point_radial lam u (![u, w]) hpair hlam (by simpa [hu] using hsmall)).2.1
    simpa [hu] using h.mpr ⟨0, by simp [hu]⟩
  have hcanonicalw : cost lam (u + v) (![u, w]) = Real.sqrt 2 * lam - lam ^ 2 / 2 := by
    have h := (single_point_radial lam (u + v) (![u, w]) hpair hlam
      (by rw [hsum]; linarith)).2.1
    simpa [hsum, mul_comm] using h.mpr ⟨1, by simp [hsum, w]⟩
  have hfaithu : cost lam u (![u, v]) = lam - lam ^ 2 / 2 := by
    have h := (single_point_radial lam u (![u, v]) hfaith hlam (by simpa [hu] using hsmall)).2.1
    simpa [hu] using h.mpr ⟨0, by simp [hu]⟩
  have hfaithw := faithful_sum_cost lam u v hu hv horth hlam hsmall
  have hgap : objective lam p0 a b u v (![u, v]) - B =
      b * lam * (2 - Real.sqrt 2 - lam / 2) := by
    rw [objective, cost_zero lam (![u, v]) hlam.le, hfaithu, hfaithw]
    simp only [B]
    ring
  have hgappos : 0 < b * lam * (2 - Real.sqrt 2 - lam / 2) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hbound : Real.sqrt 2 < 3 / 2 := by nlinarith
    exact mul_pos (mul_pos hb hlam) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, hgap, hgappos, ?_⟩
  · rw [hobj]; simp only [B]; linarith
  · constructor
    · intro h
      exact ⟨hru.2.1.mp (hequ h), hrw.2.1.mp (heqw h)⟩
    · rintro ⟨hi, hj⟩
      rw [hobj, hru.2.1.mpr hi, hrw.2.1.mpr hj]
      ring
  · intro h c hc
    rw [heqw h]
    exact hrw.2.2.1 c hc
  · rw [objective, cost_zero lam (![u, w]) hlam.le, hcanonicalu, hcanonicalw]
    ring
  · simp only [B] at hgap
    linarith

end D5.S3.Estimation.WhiteBoxLossFiberLaw.ArbitraryDictionary

#print axioms D5.S3.Estimation.WhiteBoxLossFiberLaw.ArbitraryDictionary.single_point_radial

#print axioms D5.S3.Estimation.WhiteBoxLossFiberLaw.ArbitraryDictionary.whitebox_absorption
