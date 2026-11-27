/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/FundamentalKernel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/FundamentalKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.PeriodRings.FundamentalKernel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/PeriodRings/FundamentalKernel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.TateSen.DeRhamFiltration
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Kernel of the fundamental exact sequence for B_max; pole bound by powers of μ. -/


open Algebra IsScalarTower IsLocalization.Away algebraMap Function
variable {p} [ThePrime p]

/-- Let y ∈ B, a ∈ ℕ, and let ν ∈ A_inf be divisible by μ. If the image of φ^n(y) in B_dR lies
in t^(−a)B_dR^+ for every n ≥ 0, then ν^a y lies in the image of B^+. -/
lemma pow_smul_mem_range_BPlus (y : Bcris) (a : ℕ) {ν} (hν : mu ∣ ν) (h : ∀ n,
  ↑((⟨.ofAdd n, 1⟩ : FrobGal) • y) ∈ hodgeFil (-a)) : ∃ c : BPlus, c = ν ^ a • y :=
  hν.elim fun s E ↦ (surj (mu : BPlus) (ν ^ a • y)).rec (·.rec (by grind) fun N ih ⟨c, H⟩ ↦ ih
  ((c.dvd_of_thetaBPlus_frobEnd_eq_zero mu_dvd_of_theta_frobEnd fun n ↦ thetaBdR_algebraMap_BPlus ▸
  algebraMap_mem_hodgeFil_one_iff.1 (hodgeFil_anti (by lia) (Set.mem_of_eq_of_mem (by
  linear_combination (norm := (simp [E, smul_def, ← algebraMap_apply, FrobGal.smul_def]; ring))
    -congr((↑((⟨.ofAdd n, 1⟩ : FrobGal) • $H) : BdR)))
  (mul_mem_hodgeFil (h n) (algebraMap_mem_hodgeFil_iff_xi_pow_dvd.2 (.mul_left
  (pow_dvd_pow_of_dvd (map_dvd _ (theta_eq_zero_iff_xi_dvd.1 (by simp))) (a + N.succ)) ↑(frobEnd^[n]
  s ^ a))))))).imp fun _ _ ↦ (algebraMap_isUnit (mu : BPlus)).mul_left_cancel (by grind)))

/-- Kernel in the fundamental exact sequence: an element y of B with φ(y) = y whose image in
B_dR lies in B_dR^+ belongs to Q_p.

Known result: Fontaine's period rings and the fundamental exact sequence. -/
lemma Bcris.exists_padic_eq_of_frobEnd_fixed {y : Bcris} (h : frobEnd y = y) {x : BdRPlus} (hx :
  (y : BdR) = x) : ∃ a : ℚ_[p], a = y := by
  obtain ⟨c,
    rfl⟩ := by simpa [FrobGal.smul_def, iterate_fixed, *] using pow_smul_mem_range_BPlus y 0 dvd_rfl
  simp [injective_BPlus_Bcris.eq_iff] at h; let ⟨m, _, H⟩ := c.exists_p_pow_mul_eq_amax
  let ⟨a, e⟩ := exists_Ainf_eq_of_contraction {_} 0 1 (by simp [amaxImage]) (by simp_all [← H]) _ H
  obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_frobenius_eq a ((coe_inj _ BPlus).1
    (by simp [← frobEnd_eq_frobenius, ← frobEnd_algebraMap, e, h]))
  use b / p / p ^ m, (coe_inj _ BdR).1 (by simpa [field, algebraMap_apply _ ℚ_[p] BdR b, NeZero.ne,
    ← algebraMap_apply] using congr(($e : BdR)))
