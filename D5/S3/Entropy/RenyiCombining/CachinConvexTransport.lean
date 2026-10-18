/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexTransport
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identification of real-power elasticity with the Riccati denominator. -/

import D5.S3.Entropy.RenyiCombining.CachinConvexBranch
import D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

/-! These identities concern arbitrary real parameters and variable coordinates. -/

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexTransport

open CachinConvexBranch

noncomputable def D₁ (n z : ℝ) : ℝ := deriv (C n) z + n

theorem bias_mem (r : ℝ) (hr : r ∈ Ioo 0 1) :
    (1 - r) / (1 + r) ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < 1 + r := by linarith [hr.1]
  constructor
  · exact div_pos (by linarith [hr.2]) hp
  · exact (div_lt_one hp).mpr (by linarith [hr.1])

private theorem C_mobius_eq (n r : ℝ) (hn : 0 < n) (hr : r ∈ Ioo 0 1) :
    C n (((1 - r) / (1 + r)) ^ 2) =
      n * ((1 - r) / (1 + r)) * (1 + r ^ n) / (1 - r ^ n) := by
  let t := (1 - r) / (1 + r)
  have ht : t ∈ Ioo (0 : ℝ) 1 := bias_mem r hr
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have hpow : (1 - t) ^ n / (1 + t) ^ n = r ^ n := by
    rw [← Real.div_rpow hm.le hp.le]
    congr 1
    apply (div_eq_iff hp.ne').mpr
    dsimp [t]
    field_simp [show 1 + r ≠ 0 by linarith [hr.1]]
    <;> ring
  have hM : (1 - t) ^ n = r ^ n * (1 + t) ^ n :=
    (div_eq_iff (Real.rpow_pos_of_pos hp n).ne').mp hpow
  have hq : r ^ n < 1 := Real.rpow_lt_one hr.1.le hr.2 hn
  change C n (t ^ 2) = _
  rw [C_eq_power_quotient n t hn ht, hM]
  change n * t * ((1 + t) ^ n + r ^ n * (1 + t) ^ n) /
      ((1 + t) ^ n - r ^ n * (1 + t) ^ n) = n * t * (1 + r ^ n) / (1 - r ^ n)
  field_simp [(Real.rpow_pos_of_pos hp n).ne', sub_ne_zero.mpr hq.ne']
  <;> ring

theorem F_eq_denominator_elasticity (n r : ℝ) (hn : 0 < n)
    (hr : r ∈ Ioo 0 1) :
    CachinElasticityMonotone.F n r =
      elasticity (D n) (D₁ n) (((1 - r) / (1 + r)) ^ 2) := by
  let t := (1 - r) / (1 + r)
  have ht : t ∈ Ioo (0 : ℝ) 1 := bias_mem r hr
  have hz : t ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨sq_pos_of_pos ht.1, by nlinarith [ht.1, ht.2]⟩
  have hr1 : 1 + r ≠ 0 := by linarith [hr.1]
  have hqpos : 0 < r ^ n := Real.rpow_pos_of_pos hr.1 n
  have hqlt : r ^ n < 1 := Real.rpow_lt_one hr.1.le hr.2 hn
  have hq1 : 1 - r ^ n ≠ 0 := sub_ne_zero.mpr hqlt.ne'
  have hq2 : 1 + r ^ n ≠ 0 := by linarith
  have h1r : 1 - r ≠ 0 := by linarith [hr.2]
  have h1z : 1 - t ^ 2 ≠ 0 := by linarith [hz.2]
  have hc := C_mobius_eq n r hn hr
  change C n (t ^ 2) = n * t * (1 + r ^ n) / (1 - r ^ n) at hc
  have hcne : C n (t ^ 2) ≠ 0 := (C_pos n _ hn hz).ne'
  have hDne : D n (t ^ 2) ≠ 0 := (D_pos n _ hn hz).ne'
  have hA : CachinElasticityMonotone.A n r =
      ((C n (t ^ 2)) ^ 2 - n ^ 2 * t ^ 2) / ((1 - t ^ 2) * C n (t ^ 2)) := by
    rw [CachinElasticityMonotone.A_eq n r hr.1, Real.rpow_sub hr.1, Real.rpow_one, hc]
    dsimp [t]
    field_simp [hr.1.ne', hr1, hq1, hq2, h1r, hn.ne', h1z]
    <;> ring_nf
    <;> (try field_simp [hr.1.ne', hr1])
    <;> ring
  have hB : CachinElasticityMonotone.B n r = n * t ^ 2 / C n (t ^ 2) := by
    rw [hc]
    dsimp [CachinElasticityMonotone.B, CachinElasticityMonotone.T, t]
    field_simp [hr1, hq1, hq2, h1r, hn.ne']
    <;> ring
  change CachinElasticityMonotone.F n r = elasticity (D n) (D₁ n) (t ^ 2)
  unfold CachinElasticityMonotone.F elasticity D₁
  rw [hA, hB, (C_hasDerivAt n (t ^ 2) hn hz).deriv]
  have hDne' : C n (t ^ 2) + n * t ^ 2 ≠ 0 := hDne
  unfold D
  have hplus : 1 + n * t ^ 2 / C n (t ^ 2) ≠ 0 := by
    have hpos : 0 < n * t ^ 2 / C n (t ^ 2) :=
      div_pos (mul_pos hn hz.1) (C_pos n _ hn hz)
    linarith
  have hDne'' : t ^ 2 * n + C n (t ^ 2) ≠ 0 := by
    convert hDne' using 1 <;> ring
  field_simp [hcne, h1z, hn.ne', ht.1.ne', hplus, hDne']
  <;> ring_nf
  <;> (try field_simp [hDne''])
  <;> ring

end D5.S3.Entropy.RenyiCombining.CachinConvexTransport
