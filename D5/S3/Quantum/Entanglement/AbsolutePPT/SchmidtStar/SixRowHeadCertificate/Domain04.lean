/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain04
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain04
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain04.node82
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain01
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain02
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part08
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part09
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part10
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain04
open SixRowHeadPolynomial
noncomputable section

private theorem node288 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) 1 (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node287 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 32) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) 1 (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node286 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (21 / 64) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) 1 (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node284 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (21 / 64) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part10.box78 z k h hz hm hk hK hh hH
  · exact node286 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node283 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 32) ≤ h) (hH : h ≤ (21 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) 1 (21 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node282 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 32) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 64)
  · exact node283 z k h hz hZ hk hK hh hm hg
  · exact node284 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node281 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (21 / 64) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) (15 / 16) (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node279 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (21 / 64) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part10.box77 z k h hz hm hk hK hh hH
  · exact node281 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node278 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 32) ≤ h) (hH : h ≤ (21 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (15 / 16) (21 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node277 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 32) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 64)
  · exact node278 z k h hz hZ hk hK hh hm hg
  · exact node279 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node276 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 32) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15 / 16)
  · exact node277 z k h hz hZ hk hm hh hH hg
  · exact node282 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node275 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 32) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact node276 z k h hz hm hk hK hh hH hg
  · exact node287 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node274 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) 1 (9 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node273 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node274 z k h hz hZ hk hK hh hm hg
  · exact node275 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node272 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (7 / 8) (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node271 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node272 z k h hz hZ hk hm hh hH hg
  · exact node273 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node270 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node271 z k h hz hm hk hK hh hH hg
  · exact node288 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node269 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) 1 (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node268 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 16)
  · exact node269 z k h hz hZ hk hK hh hm hg
  · exact node270 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node267 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (3 / 4) (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node266 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 4)
  · exact node267 z k h hz hZ hk hm hh hH hg
  · exact node268 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node263 (z k h : ℝ)
    (hz : (333 / 512) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333 / 512) 1 (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node261 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333 / 512)
  · exact Part10.box74 z k h hz hm hk hK hh hH
  · exact node263 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node260 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (27 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) 1 (27 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node259 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 128)
  · exact node260 z k h hz hZ hk hK hh hm hg
  · exact node261 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node258 (z k h : ℝ)
    (hz : (333 / 512) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333 / 512) (31 / 32) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node256 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333 / 512)
  · exact Part10.box73 z k h hz hm hk hK hh hH
  · exact node258 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node255 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (27 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (31 / 32) (27 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node254 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 128)
  · exact node255 z k h hz hZ hk hK hh hm hg
  · exact node256 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node253 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (31 / 32)
  · exact node254 z k h hz hZ hk hm hh hH hg
  · exact node259 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node251 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part10.box72 z k h hz hm hk hK hh hH
  · exact node253 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node250 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node251 z k h hz hZ hk hK hh hm hg
  · exact Part10.box75 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node248 (z k h : ℝ)
    (hz : (333 / 512) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333 / 512) (15 / 16) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node246 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (27 / 128) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333 / 512)
  · exact Part09.box70 z k h hz hm hk hK hh hH
  · exact node248 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node245 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (27 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (15 / 16) (27 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node244 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 128)
  · exact node245 z k h hz hZ hk hK hh hm hg
  · exact node246 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node243 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (29 / 32))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (29 / 32) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node242 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (29 / 32)
  · exact node243 z k h hz hZ hk hm hh hH hg
  · exact node244 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node240 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part09.box69 z k h hz hm hk hK hh hH
  · exact node242 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node239 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node240 z k h hz hZ hk hK hh hm hg
  · exact Part09.box71 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node238 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15 / 16)
  · exact node239 z k h hz hZ hk hm hh hH hg
  · exact node250 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node236 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part09.box68 z k h hz hm hk hK hh hH
  · exact node238 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node235 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node236 z k h hz hZ hk hK hh hm hg
  · exact Part10.box76 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node232 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (7 / 8) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node230 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part09.box65 z k h hz hm hk hK hh hH
  · exact node232 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node229 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node230 z k h hz hZ hk hK hh hm hg
  · exact Part09.box66 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node227 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (13 / 16) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node225 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part08.box63 z k h hz hm hk hK hh hH
  · exact node227 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node224 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node225 z k h hz hZ hk hK hh hm hg
  · exact Part09.box64 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node223 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13 / 16)
  · exact node224 z k h hz hZ hk hm hh hH hg
  · exact node229 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node221 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part08.box62 z k h hz hm hk hK hh hH
  · exact node223 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node220 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node221 z k h hz hZ hk hK hh hm hg
  · exact Part09.box67 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node219 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node220 z k h hz hZ hk hm hh hH hg
  · exact node235 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node217 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part08.box61 z k h hz hm hk hK hh hH
  · exact node219 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node151 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 16)
  · exact Domain01.node152 z k h hz hZ hk hK hh hm hg
  · exact node217 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node83 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 4)
  · exact Domain02.node84 z k h hz hZ hk hm hh hH hg
  · exact node151 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

theorem node82 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact node83 z k h hz hm hk hK hh hH hg
  · exact node266 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain04
