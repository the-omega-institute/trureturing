/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain03
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain03
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain03.node325
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part11
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part12
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part13
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain03
open SixRowHeadPolynomial
noncomputable section

private theorem node383 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) 1 (3 / 4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node380 (z k h : ℝ)
    (hz : (177 / 256) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (39 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (177 / 256) 1 (39 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node378 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (39 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (177 / 256)
  · exact Part13.box101 z k h hz hm hk hK hh hH
  · exact node380 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node377 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (39 / 64)
  · exact node378 z k h hz hZ hk hK hh hm hg
  · exact Part13.box102 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node375 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (39 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (15 / 16) (39 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node374 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (39 / 64)
  · exact node375 z k h hz hZ hk hK hh hm hg
  · exact Part13.box100 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node373 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15 / 16)
  · exact node374 z k h hz hZ hk hm hh hH hg
  · exact node377 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node371 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part13.box99 z k h hz hm hk hK hh hH
  · exact node373 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node370 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 32)
  · exact node371 z k h hz hZ hk hK hh hm hg
  · exact Part13.box103 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node368 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (7 / 8) (21 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node366 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part13.box97 z k h hz hm hk hK hh hH
  · exact node368 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node365 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 32)
  · exact node366 z k h hz hZ hk hK hh hm hg
  · exact Part13.box98 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node364 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node365 z k h hz hZ hk hm hh hH hg
  · exact node370 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node363 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node364 z k h hz hm hk hK hh hH hg
  · exact node383 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node362 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) 1 (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node361 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) 1 (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node359 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part13.box96 z k h hz hm hk hK hh hH
  · exact node361 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node358 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) 1 (15 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node356 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) 1 (27 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node354 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part12.box94 z k h hz hm hk hK hh hH
  · exact node356 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node353 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (15 / 16) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 64)
  · exact node354 z k h hz hZ hk hK hh hm hg
  · exact Part12.box95 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node351 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) (15 / 16) (27 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node349 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part12.box92 z k h hz hm hk hK hh hH
  · exact node351 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node348 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ (15 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 64)
  · exact node349 z k h hz hZ hk hK hh hm hg
  · exact Part12.box93 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node347 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15 / 16)
  · exact node348 z k h hz hZ hk hm hh hH hg
  · exact node353 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node346 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact node347 z k h hz hm hk hK hh hH hg
  · exact node358 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node345 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 32)
  · exact node346 z k h hz hZ hk hK hh hm hg
  · exact node359 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node344 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (7 / 8) (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node342 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (15 / 32) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact Part12.box91 z k h hz hm hk hK hh hH
  · exact node344 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node341 (z k h : ℝ)
    (hz : (87 / 128) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87 / 128) (7 / 8) (15 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node339 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) (7 / 8) (27 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node337 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part12.box89 z k h hz hm hk hK hh hH
  · exact node339 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node336 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (13 / 16) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 64)
  · exact node337 z k h hz hZ hk hK hh hm hg
  · exact Part12.box90 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node334 (z k h : ℝ)
    (hz : (171 / 256) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171 / 256) (13 / 16) (27 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node332 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (27 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171 / 256)
  · exact Part11.box87 z k h hz hm hk hK hh hH
  · exact node334 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node331 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (13 / 16))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 64)
  · exact node332 z k h hz hZ hk hK hh hm hg
  · exact Part12.box88 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node330 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (87 / 128))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13 / 16)
  · exact node331 z k h hz hZ hk hm hh hH hg
  · exact node336 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node329 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (15 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87 / 128)
  · exact node330 z k h hz hm hk hK hh hH hg
  · exact node341 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node328 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 32)
  · exact node329 z k h hz hZ hk hK hh hm hg
  · exact node342 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node327 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node328 z k h hz hZ hk hm hh hH hg
  · exact node345 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node326 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node327 z k h hz hm hk hK hh hH hg
  · exact node362 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

theorem node325 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 16)
  · exact node326 z k h hz hZ hk hK hh hm hg
  · exact node363 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain03
