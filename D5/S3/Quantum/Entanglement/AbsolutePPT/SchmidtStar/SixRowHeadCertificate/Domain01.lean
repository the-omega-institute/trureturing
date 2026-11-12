/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain01
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain01
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain01.node152
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part06
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part07
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part08
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain01
open SixRowHeadPolynomial
noncomputable section

private theorem node216 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) 1 (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node214 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part08.box60 z k h hz hm hk hK hh hH
  · exact node216 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node213 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) 1 (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node211 (z k h : ℝ)
    (hz : (327 / 512) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (327 / 512) 1 (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node209 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (327 / 512)
  · exact Part08.box58 z k h hz hm hk hK hh hH
  · exact node211 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node208 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (31 / 32) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node209 z k h hz hZ hk hK hh hm hg
  · exact Part08.box59 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node206 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (31 / 32) (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node205 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (15 / 16) ≤ k) (hK : k ≤ (31 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node206 z k h hz hZ hk hK hh hm hg
  · exact Part08.box57 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node204 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (31 / 32)
  · exact node205 z k h hz hZ hk hm hh hH hg
  · exact node208 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node203 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact node204 z k h hz hm hk hK hh hH hg
  · exact node213 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node202 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node203 z k h hz hZ hk hK hh hm hg
  · exact node214 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node201 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (15 / 16) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node199 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part08.box56 z k h hz hm hk hK hh hH
  · exact node201 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node198 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (15 / 16) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node196 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (15 / 16) (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node195 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (29 / 32) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node196 z k h hz hZ hk hK hh hm hg
  · exact Part07.box55 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node193 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (29 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (29 / 32) (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node192 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (29 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node193 z k h hz hZ hk hK hh hm hg
  · exact Part07.box54 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node191 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (29 / 32)
  · exact node192 z k h hz hZ hk hm hh hH hg
  · exact node195 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node190 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact node191 z k h hz hm hk hK hh hH hg
  · exact node198 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node189 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node190 z k h hz hZ hk hK hh hm hg
  · exact node199 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node188 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15 / 16)
  · exact node189 z k h hz hZ hk hm hh hH hg
  · exact node202 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node186 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part07.box53 z k h hz hm hk hK hh hH
  · exact node188 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node185 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) 1 (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node183 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part07.box52 z k h hz hm hk hK hh hH
  · exact node185 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node182 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node183 z k h hz hZ hk hK hh hm hg
  · exact node186 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node181 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (7 / 8) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node179 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part07.box51 z k h hz hm hk hK hh hH
  · exact node181 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node178 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (7 / 8) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node176 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (27 / 32) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (7 / 8) (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node175 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (27 / 32) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node176 z k h hz hZ hk hK hh hm hg
  · exact Part07.box50 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node173 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (27 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (15 / 128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (27 / 32) (15 / 128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node172 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (27 / 32))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 128)
  · exact node173 z k h hz hZ hk hK hh hm hg
  · exact Part07.box49 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node171 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (165 / 256))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (27 / 32)
  · exact node172 z k h hz hZ hk hm hh hH hg
  · exact node175 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node170 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact node171 z k h hz hm hk hK hh hH hg
  · exact node178 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node169 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node170 z k h hz hZ hk hK hh hm hg
  · exact node179 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node168 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (13 / 16) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node166 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part07.box48 z k h hz hm hk hK hh hH
  · exact node168 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node165 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (13 / 16) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node163 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part06.box47 z k h hz hm hk hK hh hH
  · exact node165 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node162 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node163 z k h hz hZ hk hK hh hm hg
  · exact node166 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node161 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13 / 16)
  · exact node162 z k h hz hZ hk hm hh hH hg
  · exact node169 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node159 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part06.box46 z k h hz hm hk hK hh hH
  · exact node161 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node158 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (7 / 8) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node156 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part06.box45 z k h hz hm hk hK hh hH
  · exact node158 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node155 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node156 z k h hz hZ hk hK hh hm hg
  · exact node159 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node154 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node155 z k h hz hZ hk hm hh hH hg
  · exact node182 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

theorem node152 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part06.box44 z k h hz hm hk hK hh hH
  · exact node154 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain01
