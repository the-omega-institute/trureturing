/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain02
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain02
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain02.node84
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part03
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part04
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part05
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part06
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain02
open SixRowHeadPolynomial
noncomputable section

private theorem node148 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (3 / 4) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node146 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part06.box41 z k h hz hm hk hK hh hH
  · exact node148 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node145 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node146 z k h hz hZ hk hK hh hm hg
  · exact Part06.box42 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node143 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (11 / 16) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node141 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part05.box39 z k h hz hm hk hK hh hH
  · exact node143 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node140 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node141 z k h hz hZ hk hK hh hm hg
  · exact Part06.box40 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node139 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11 / 16)
  · exact node140 z k h hz hZ hk hm hh hH hg
  · exact node145 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node137 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part05.box38 z k h hz hm hk hK hh hH
  · exact node139 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node136 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node137 z k h hz hZ hk hK hh hm hg
  · exact Part06.box43 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node133 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (5 / 8) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node131 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part05.box35 z k h hz hm hk hK hh hH
  · exact node133 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node130 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node131 z k h hz hZ hk hK hh hm hg
  · exact Part05.box36 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node128 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (9 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (9 / 16) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node126 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (9 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part05.box33 z k h hz hm hk hK hh hH
  · exact node128 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node125 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (9 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node126 z k h hz hZ hk hK hh hm hg
  · exact Part05.box34 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node124 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (9 / 16)
  · exact node125 z k h hz hZ hk hm hh hH hg
  · exact node130 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node122 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part05.box32 z k h hz hm hk hK hh hH
  · exact node124 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node121 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node122 z k h hz hZ hk hK hh hm hg
  · exact Part05.box37 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node120 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5 / 8)
  · exact node121 z k h hz hZ hk hm hh hH hg
  · exact node136 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node118 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part04.box31 z k h hz hm hk hK hh hH
  · exact node120 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node117 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (3 / 4) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node115 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part04.box30 z k h hz hm hk hK hh hH
  · exact node117 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node114 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (3 / 4) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node113 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (11 / 16) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node114 z k h hz hZ hk hK hh hm hg
  · exact node115 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node112 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (11 / 16) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node110 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part04.box29 z k h hz hm hk hK hh hH
  · exact node112 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node109 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (11 / 16) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node108 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (11 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node109 z k h hz hZ hk hK hh hm hg
  · exact node110 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node107 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11 / 16)
  · exact node108 z k h hz hZ hk hm hh hH hg
  · exact node113 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node105 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part04.box28 z k h hz hm hk hK hh hH
  · exact node107 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node104 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (3 / 4) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node102 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part04.box27 z k h hz hm hk hK hh hH
  · exact node104 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node101 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (5 / 8) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node102 z k h hz hZ hk hK hh hm hg
  · exact node105 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node100 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (5 / 8) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node98 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (9 / 64) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part04.box26 z k h hz hm hk hK hh hH
  · exact node100 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node97 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (9 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (5 / 8) (9 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node96 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (9 / 16) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 64)
  · exact node97 z k h hz hZ hk hK hh hm hg
  · exact node98 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node95 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (9 / 16))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (9 / 16) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node94 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (9 / 16)
  · exact node95 z k h hz hZ hk hm hh hH hg
  · exact node96 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node92 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part04.box25 z k h hz hm hk hK hh hH
  · exact node94 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node91 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (5 / 8) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node89 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part04.box24 z k h hz hm hk hK hh hH
  · exact node91 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node88 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (5 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node89 z k h hz hZ hk hK hh hm hg
  · exact node92 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node87 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5 / 8)
  · exact node88 z k h hz hZ hk hm hh hH hg
  · exact node101 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node85 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part03.box23 z k h hz hm hk hK hh hH
  · exact node87 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

theorem node84 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 2) ≤ k) (hK : k ≤ (3 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 16)
  · exact node85 z k h hz hZ hk hK hh hm hg
  · exact node118 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain02
