/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain05
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain05
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Domain05.node6
   digest: Exact feasible-domain subtree for the K6 scalar polynomial. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part01
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part02
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part03
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain05
open SixRowHeadPolynomial
noncomputable section

private theorem node80 (z k h : ℝ)
    (hz : (45 / 64) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45 / 64) (1 / 2) (3 / 4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node78 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (21 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 2) (21 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node77 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21 / 32)
  · exact node78 z k h hz hZ hk hK hh hm hg
  · exact Part03.box22 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node76 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (3 / 8) (3 / 4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node75 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (45 / 64))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 8)
  · exact node76 z k h hz hZ hk hm hh hH hg
  · exact node77 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node74 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (9 / 16) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45 / 64)
  · exact node75 z k h hz hm hk hK hh hH hg
  · exact node80 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node73 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (9 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 2) (9 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node72 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 16)
  · exact node73 z k h hz hZ hk hK hh hm hg
  · exact node74 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node71 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 4) (3 / 4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node70 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 4)
  · exact node71 z k h hz hZ hk hm hh hH hg
  · exact node72 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node68 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 8) ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact Part03.box21 z k h hz hm hk hK hh hH
  · exact node70 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node67 (z k h : ℝ)
    (hz : (21 / 32) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21 / 32) (1 / 2) (3 / 8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node64 (z k h : ℝ)
    (hz : (165 / 256) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 16) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165 / 256) (1 / 2) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node62 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 16) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165 / 256)
  · exact Part03.box18 z k h hz hm hk hK hh hH
  · exact node64 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node61 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (7 / 16) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node62 z k h hz hZ hk hK hh hm hg
  · exact Part03.box19 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node59 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (7 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (15 / 64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (7 / 16) (15 / 64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node58 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (7 / 16))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15 / 64)
  · exact node59 z k h hz hZ hk hK hh hm hg
  · exact Part03.box17 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node57 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7 / 16)
  · exact node58 z k h hz hZ hk hm hh hH hg
  · exact node61 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node55 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part03.box16 z k h hz hm hk hK hh hH
  · exact node57 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node54 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node55 z k h hz hZ hk hK hh hm hg
  · exact Part03.box20 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node52 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (3 / 8) (9 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node50 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (9 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part02.box14 z k h hz hm hk hK hh hH
  · exact node52 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node49 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9 / 32)
  · exact node50 z k h hz hZ hk hK hh hm hg
  · exact Part02.box15 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node48 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 8)
  · exact node49 z k h hz hZ hk hm hh hH hg
  · exact node54 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node46 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 16) ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part02.box13 z k h hz hm hk hK hh hH
  · exact node48 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node45 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 2) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node43 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part02.box12 z k h hz hm hk hK hh hH
  · exact node45 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node42 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 2) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node40 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part02.box11 z k h hz hm hk hK hh hH
  · exact node42 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node39 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (3 / 8) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node40 z k h hz hZ hk hK hh hm hg
  · exact node43 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node38 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (3 / 8) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node36 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part02.box10 z k h hz hm hk hK hh hH
  · exact node38 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node35 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (3 / 8) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node33 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part02.box9 z k h hz hm hk hK hh hH
  · exact node35 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node32 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (3 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node33 z k h hz hZ hk hK hh hm hg
  · exact node36 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node31 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3 / 8)
  · exact node32 z k h hz hZ hk hm hh hH hg
  · exact node39 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node29 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part02.box8 z k h hz hm hk hK hh hH
  · exact node31 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node28 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 4) ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 16)
  · exact node29 z k h hz hZ hk hK hh hm hg
  · exact node46 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node26 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 8) ≤ k) (hK : k ≤ (1 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 4) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node24 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 8) ≤ k) (hK : k ≤ (1 / 4))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part01.box6 z k h hz hm hk hK hh hH
  · exact node26 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node23 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 8) ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 4) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node21 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 8) ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part01.box5 z k h hz hm hk hK hh hH
  · exact node23 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node20 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : (1 / 8) ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node21 z k h hz hZ hk hK hh hm hg
  · exact node24 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node19 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 8) (3 / 16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node17 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 8))
    (hh : (3 / 32) ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part01.box4 z k h hz hm hk hK hh hH
  · exact node19 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node16 (z k h : ℝ)
    (hz : (81 / 128) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81 / 128) (1 / 8) (3 / 32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  dsimp only [constraint] at hg
  linarith only [hg, hb]

private theorem node14 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81 / 128)
  · exact Part01.box3 z k h hz hm hk hK hh hH
  · exact node16 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node13 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 8))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 32)
  · exact node14 z k h hz hZ hk hK hh hm hg
  · exact node17 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node12 (z k h : ℝ)
    (hz : (39 / 64) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 8)
  · exact node13 z k h hz hZ hk hm hh hH hg
  · exact node20 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node10 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39 / 64)
  · exact Part01.box2 z k h hz hm hk hK hh hH
  · exact node12 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node9 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 4))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 16)
  · exact node10 z k h hz hZ hk hK hh hm hg
  · exact Part01.box7 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node8 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (21 / 32))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1 / 4)
  · exact node9 z k h hz hZ hk hm hh hH hg
  · exact node28 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node7 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21 / 32)
  · exact node8 z k h hz hm hk hK hh hH hg
  · exact node67 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

theorem node6 (z k h : ℝ)
    (hz : (9 / 16) ≤ z) (hZ : z ≤ (3 / 4))
    (hk : 0 ≤ k) (hK : k ≤ (1 / 2))
    (hh : 0 ≤ h) (hH : h ≤ (3 / 4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3 / 8)
  · exact node7 z k h hz hZ hk hK hh hm hg
  · exact node68 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Domain05
