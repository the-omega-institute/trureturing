/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg
   digest: Complete exact K6 scalar partition, including all boundary faces. -/


import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain03
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain04
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain05
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain06
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part01
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part10
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part11

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate
open SixRowHeadPolynomial
noncomputable section

private theorem node324 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (3 / 4) (3 / 4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node322 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (3 / 4) (21 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node320 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part11.box85 z k h hz hm hk hK hh hH
  · exact node322 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node319 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 32)
  · exact node320 z k h hz hZ hk hK hh hm hg
  · exact Part11.box86 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node317 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (5 / 8) (21 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node315 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part11.box83 z k h hz hm hk hK hh hH
  · exact node317 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node314 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 32)
  · exact node315 z k h hz hZ hk hK hh hm hg
  · exact Part11.box84 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node313 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5 / 8)
  · exact node314 z k h hz hZ hk hm hh hH hg
  · exact node319 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node312 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node313 z k h hz hm hk hK hh hH hg
  · exact node324 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node311 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (3 / 4) (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node310 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (3 / 4) (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node308 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part11.box82 z k h hz hm hk hK hh hH
  · exact node310 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node307 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (3 / 4) (15 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node305 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (3 / 4) (27 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node304 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 64)
  · exact node305 z k h hz hZ hk hK hh hm hg
  · exact Part11.box81 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node303 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (11 / 16) (15 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node302 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11 / 16)
  · exact node303 z k h hz hZ hk hm hh hH hg
  · exact node304 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node301 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact node302 z k h hz hm hk hK hh hH hg
  · exact node307 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node300 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 32)
  · exact node301 z k h hz hZ hk hK hh hm hg
  · exact node308 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node299 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (5 / 8) (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node297 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part11.box80 z k h hz hm hk hK hh hH
  · exact node299 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node296 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (5 / 8) (15 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node295 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 32)
  · exact node296 z k h hz hZ hk hK hh hm hg
  · exact node297 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node294 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5 / 8)
  · exact node295 z k h hz hZ hk hm hh hH hg
  · exact node300 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node293 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node294 z k h hz hm hk hK hh hH hg
  · exact node311 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node292 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 16)
  · exact node293 z k h hz hZ hk hK hh hm hg
  · exact node312 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node291 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 4)
  · exact node292 z k h hz hZ hk hm hh hH hg
  · exact Domain03.node325 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node289 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact Part10.box79 z k h hz hm hk hK hh hH
  · exact node291 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node81 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 8)
  · exact Domain04.node82 z k h hz hZ hk hK hh hm hg
  · exact node289 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node5 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 2)
  · exact Domain05.node6 z k h hz hZ hk hm hh hH hg
  · exact node81 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node3 (z k h : ℝ)
    (hz : (3 / 8) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (9 / 16)
  · exact Part01.box1 z k h hz hm hk hK hh hH
  · exact node5 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node2 (z k h : ℝ)
    (hz : (3 / 8) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 4)
  · exact node3 z k h hz hZ hk hK hh hm hg
  · exact Domain06.node384 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node0 (z k h : ℝ)
    (hz : 0 ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (3 / 8)
  · exact Part01.box0 z k h hz hm hk hK hh hH
  · exact node2 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

theorem polynomial_nonneg (z k h : ℝ)
    (hz : 0 ≤ z) (hZ : z ≤ 3 / 4) (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ 3 / 2) (hg : 0 ≤ constraint z k h) :
    0 ≤ P z k h := node0 z k h hz hZ hk hK hh hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate
