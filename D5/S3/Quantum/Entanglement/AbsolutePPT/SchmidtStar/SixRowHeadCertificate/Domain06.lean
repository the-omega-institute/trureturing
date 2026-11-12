/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain06
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain06
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain06.node384
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part14
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part15
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain06
open SixRowHeadPolynomial
noncomputable section

private theorem node432 (z k h : ℝ)
    (hz : (93 / 128) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (27 / 32) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (93 / 128) 1 (15 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node430 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (27 / 32) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (93 / 128)
  · exact Part15.box116 z k h hz hm hk hK hh hH
  · exact node432 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node429 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (27 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) 1 (27 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node428 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (7 / 8) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27 / 32)
  · exact node429 z k h hz hZ hk hK hh hm hg
  · exact node430 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node427 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ (7 / 8))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (7 / 8) (15 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node426 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 8)
  · exact node427 z k h hz hZ hk hm hh hH hg
  · exact node428 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node424 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part15.box115 z k h hz hm hk hK hh hH
  · exact node426 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node423 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (3 / 4) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 16)
  · exact node424 z k h hz hZ hk hK hh hm hg
  · exact Part15.box117 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node422 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (15 / 16) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (3 / 4) (9 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node420 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (15 / 16) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part15.box114 z k h hz hm hk hK hh hH
  · exact node422 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node419 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (3 / 4) (15 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node417 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part15.box113 z k h hz hm hk hK hh hH
  · exact node419 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node416 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 16)
  · exact node417 z k h hz hZ hk hK hh hm hg
  · exact node420 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node415 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 4)
  · exact node416 z k h hz hZ hk hm hh hH hg
  · exact node423 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node413 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact Part15.box112 z k h hz hm hk hK hh hH
  · exact node415 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node412 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 2) ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 8)
  · exact node413 z k h hz hZ hk hK hh hm hg
  · exact Part15.box118 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node410 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (21 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (1 / 2) (21 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node408 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (21 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part14.box110 z k h hz hm hk hK hh hH
  · exact node410 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node407 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 16)
  · exact node408 z k h hz hZ hk hK hh hm hg
  · exact Part14.box111 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node406 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (21 / 16) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (1 / 4) (3 / 2)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node404 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (21 / 16) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part14.box109 z k h hz hm hk hK hh hH
  · exact node406 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node403 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (21 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 4) (21 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node402 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 16)
  · exact node403 z k h hz hZ hk hK hh hm hg
  · exact node404 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node401 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 4)
  · exact node402 z k h hz hZ hk hm hh hH hg
  · exact node407 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node399 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 8) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact Part14.box108 z k h hz hm hk hK hh hH
  · exact node401 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node398 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (15 / 16) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (1 / 2) (9 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node396 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (15 / 16) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part14.box107 z k h hz hm hk hK hh hH
  · exact node398 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node395 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (1 / 2) (15 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node393 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (15 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact Part14.box106 z k h hz hm hk hK hh hH
  · exact node395 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node392 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 16)
  · exact node393 z k h hz hZ hk hK hh hm hg
  · exact node396 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node391 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 4) (9 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node390 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 4)
  · exact node391 z k h hz hZ hk hm hh hH hg
  · exact node392 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node388 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (9 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact Part14.box105 z k h hz hm hk hK hh hH
  · exact node390 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node387 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 4) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 8)
  · exact node388 z k h hz hZ hk hK hh hm hg
  · exact node399 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node386 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 2)
  · exact node387 z k h hz hZ hk hm hh hH hg
  · exact node412 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

theorem node384 (z k h : ℝ)
    (hz : (3 / 8) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : (3 / 4) ≤ h) (hH : h ≤ (3 / 2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (9 / 16)
  · exact Part14.box104 z k h hz hm hk hK hh hH
  · exact node386 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain06
