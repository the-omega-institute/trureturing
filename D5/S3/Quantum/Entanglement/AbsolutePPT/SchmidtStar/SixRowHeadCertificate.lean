/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Complete exact K6 scalar partition, including all boundary faces. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part01

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part02

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part03

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part04

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part05

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part06

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part07

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part08

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part09

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part10

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part11

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part12

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part13

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part14

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate.Part15

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate
open SixRowHeadPolynomial
noncomputable section

private theorem node432 (z k h : ℝ)
    (hz : (93/128) ≤ z) (hZ : z ≤ (3/4))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (27/32) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (93/128) 1 (15/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node430 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (27/32) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (93/128)
  · exact Part15.box116 z k h hz hm hk hK hh hH
  · exact node432 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node429 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (27/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) 1 (27/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node428 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/32)
  · exact node429 z k h hz hZ hk hK hh hm hg
  · exact node430 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node427 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (7/8) (15/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node426 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node427 z k h hz hZ hk hm hh hH hg
  · exact node428 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node424 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part15.box115 z k h hz hm hk hK hh hH
  · exact node426 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node423 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/16)
  · exact node424 z k h hz hZ hk hK hh hm hg
  · exact Part15.box117 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node422 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (15/16) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (3/4) (9/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node420 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (15/16) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part15.box114 z k h hz hm hk hK hh hH
  · exact node422 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node419 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (3/4) (15/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node417 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part15.box113 z k h hz hm hk hK hh hH
  · exact node419 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node416 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/16)
  · exact node417 z k h hz hZ hk hK hh hm hg
  · exact node420 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node415 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/4)
  · exact node416 z k h hz hZ hk hm hh hH hg
  · exact node423 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node413 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact Part15.box112 z k h hz hm hk hK hh hH
  · exact node415 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node412 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/8)
  · exact node413 z k h hz hZ hk hK hh hm hg
  · exact Part15.box118 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node410 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/8) ≤ h) (hH : h ≤ (21/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (1/2) (21/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node408 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/8) ≤ h) (hH : h ≤ (21/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part14.box110 z k h hz hm hk hK hh hH
  · exact node410 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node407 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/8) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/16)
  · exact node408 z k h hz hZ hk hK hh hm hg
  · exact Part14.box111 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node406 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (21/16) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (1/4) (3/2)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node404 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (21/16) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part14.box109 z k h hz hm hk hK hh hH
  · exact node406 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node403 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (9/8) ≤ h) (hH : h ≤ (21/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/4) (21/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node402 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (9/8) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/16)
  · exact node403 z k h hz hZ hk hK hh hm hg
  · exact node404 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node401 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (9/8) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/4)
  · exact node402 z k h hz hZ hk hm hh hH hg
  · exact node407 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node399 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (9/8) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact Part14.box108 z k h hz hm hk hK hh hH
  · exact node401 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node398 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (15/16) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (1/2) (9/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node396 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (15/16) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part14.box107 z k h hz hm hk hK hh hH
  · exact node398 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node395 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (1/2) (15/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node393 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (15/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact Part14.box106 z k h hz hm hk hK hh hH
  · exact node395 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node392 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/16)
  · exact node393 z k h hz hZ hk hK hh hm hg
  · exact node396 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node391 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/4) (9/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node390 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/4)
  · exact node391 z k h hz hZ hk hm hh hH hg
  · exact node392 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node388 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (9/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact Part14.box105 z k h hz hm hk hK hh hH
  · exact node390 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node387 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (3/4) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/8)
  · exact node388 z k h hz hZ hk hK hh hm hg
  · exact node399 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node386 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/2)
  · exact node387 z k h hz hZ hk hm hh hH hg
  · exact node412 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node384 (z k h : ℝ)
    (hz : (3/8) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : (3/4) ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (9/16)
  · exact Part14.box104 z k h hz hm hk hK hh hH
  · exact node386 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node383 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) 1 (3/4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node380 (z k h : ℝ)
    (hz : (177/256) ≤ z) (hZ : z ≤ (45/64))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (39/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (177/256) 1 (39/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node378 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (39/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (177/256)
  · exact Part13.box101 z k h hz hm hk hK hh hH
  · exact node380 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node377 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (39/64)
  · exact node378 z k h hz hZ hk hK hh hm hg
  · exact Part13.box102 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node375 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/16) ≤ h) (hH : h ≤ (39/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (15/16) (39/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node374 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (39/64)
  · exact node375 z k h hz hZ hk hK hh hm hg
  · exact Part13.box100 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node373 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15/16)
  · exact node374 z k h hz hZ hk hm hh hH hg
  · exact node377 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node371 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part13.box99 z k h hz hm hk hK hh hH
  · exact node373 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node370 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/32)
  · exact node371 z k h hz hZ hk hK hh hm hg
  · exact Part13.box103 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node368 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (7/8) (21/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node366 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part13.box97 z k h hz hm hk hK hh hH
  · exact node368 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node365 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/32)
  · exact node366 z k h hz hZ hk hK hh hm hg
  · exact Part13.box98 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node364 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node365 z k h hz hZ hk hm hh hH hg
  · exact node370 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node363 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node364 z k h hz hm hk hK hh hH hg
  · exact node383 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node362 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) 1 (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node361 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) 1 (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node359 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part13.box96 z k h hz hm hk hK hh hH
  · exact node361 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node358 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) 1 (15/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node356 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) 1 (27/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node354 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part12.box94 z k h hz hm hk hK hh hH
  · exact node356 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node353 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/64)
  · exact node354 z k h hz hZ hk hK hh hm hg
  · exact Part12.box95 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node351 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) (15/16) (27/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node349 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part12.box92 z k h hz hm hk hK hh hH
  · exact node351 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node348 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/64)
  · exact node349 z k h hz hZ hk hK hh hm hg
  · exact Part12.box93 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node347 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15/16)
  · exact node348 z k h hz hZ hk hm hh hH hg
  · exact node353 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node346 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact node347 z k h hz hm hk hK hh hH hg
  · exact node358 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node345 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/32)
  · exact node346 z k h hz hZ hk hK hh hm hg
  · exact node359 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node344 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (7/8) (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node342 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part12.box91 z k h hz hm hk hK hh hH
  · exact node344 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node341 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (7/8) (15/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node339 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) (7/8) (27/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node337 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part12.box89 z k h hz hm hk hK hh hH
  · exact node339 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node336 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/64)
  · exact node337 z k h hz hZ hk hK hh hm hg
  · exact Part12.box90 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node334 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) (13/16) (27/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node332 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part11.box87 z k h hz hm hk hK hh hH
  · exact node334 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node331 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/64)
  · exact node332 z k h hz hZ hk hK hh hm hg
  · exact Part12.box88 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node330 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13/16)
  · exact node331 z k h hz hZ hk hm hh hH hg
  · exact node336 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node329 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact node330 z k h hz hm hk hK hh hH hg
  · exact node341 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node328 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/32)
  · exact node329 z k h hz hZ hk hK hh hm hg
  · exact node342 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node327 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node328 z k h hz hZ hk hm hh hH hg
  · exact node345 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node326 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node327 z k h hz hm hk hK hh hH hg
  · exact node362 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node325 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/16)
  · exact node326 z k h hz hZ hk hK hh hm hg
  · exact node363 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node324 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (3/4) (3/4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node322 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (3/4) (21/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node320 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part11.box85 z k h hz hm hk hK hh hH
  · exact node322 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node319 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/32)
  · exact node320 z k h hz hZ hk hK hh hm hg
  · exact Part11.box86 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node317 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (5/8) (21/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node315 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part11.box83 z k h hz hm hk hK hh hH
  · exact node317 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node314 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/32)
  · exact node315 z k h hz hZ hk hK hh hm hg
  · exact Part11.box84 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node313 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5/8)
  · exact node314 z k h hz hZ hk hm hh hH hg
  · exact node319 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node312 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node313 z k h hz hm hk hK hh hH hg
  · exact node324 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node311 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (3/4) (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node310 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (3/4) (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node308 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part11.box82 z k h hz hm hk hK hh hH
  · exact node310 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node307 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (3/4) (15/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node305 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (27/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (3/4) (27/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node304 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/64)
  · exact node305 z k h hz hZ hk hK hh hm hg
  · exact Part11.box81 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node303 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (11/16) (15/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node302 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11/16)
  · exact node303 z k h hz hZ hk hm hh hH hg
  · exact node304 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node301 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact node302 z k h hz hm hk hK hh hH hg
  · exact node307 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node300 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/32)
  · exact node301 z k h hz hZ hk hK hh hm hg
  · exact node308 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node299 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) (5/8) (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node297 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (15/32) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact Part11.box80 z k h hz hm hk hK hh hH
  · exact node299 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node296 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (15/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (5/8) (15/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node295 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/32)
  · exact node296 z k h hz hZ hk hK hh hm hg
  · exact node297 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node294 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5/8)
  · exact node295 z k h hz hZ hk hm hh hH hg
  · exact node300 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node293 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node294 z k h hz hm hk hK hh hH hg
  · exact node311 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node292 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/16)
  · exact node293 z k h hz hZ hk hK hh hm hg
  · exact node312 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node291 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/4)
  · exact node292 z k h hz hZ hk hm hh hH hg
  · exact node325 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node289 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact Part10.box79 z k h hz hm hk hK hh hH
  · exact node291 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node288 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) 1 (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node287 (z k h : ℝ)
    (hz : (87/128) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/32) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (87/128) 1 (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node286 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (21/64) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) 1 (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node284 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (21/64) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part10.box78 z k h hz hm hk hK hh hH
  · exact node286 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node283 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/32) ≤ h) (hH : h ≤ (21/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) 1 (21/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node282 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/32) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/64)
  · exact node283 z k h hz hZ hk hK hh hm hg
  · exact node284 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node281 (z k h : ℝ)
    (hz : (171/256) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (21/64) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (171/256) (15/16) (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node279 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (21/64) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (171/256)
  · exact Part10.box77 z k h hz hm hk hK hh hH
  · exact node281 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node278 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/32) ≤ h) (hH : h ≤ (21/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (15/16) (21/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node277 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/32) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/64)
  · exact node278 z k h hz hZ hk hK hh hm hg
  · exact node279 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node276 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (87/128))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/32) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15/16)
  · exact node277 z k h hz hZ hk hm hh hH hg
  · exact node282 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node275 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (9/32) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (87/128)
  · exact node276 z k h hz hm hk hK hh hH hg
  · exact node287 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node274 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) 1 (9/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node273 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node274 z k h hz hZ hk hK hh hm hg
  · exact node275 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node272 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (7/8) (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node271 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node272 z k h hz hZ hk hm hh hH hg
  · exact node273 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node270 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node271 z k h hz hm hk hK hh hH hg
  · exact node288 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node269 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) 1 (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node268 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/16)
  · exact node269 z k h hz hZ hk hK hh hm hg
  · exact node270 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node267 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (3/4) (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node266 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/4)
  · exact node267 z k h hz hZ hk hm hh hH hg
  · exact node268 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node263 (z k h : ℝ)
    (hz : (333/512) ≤ z) (hZ : z ≤ (21/32))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333/512) 1 (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node261 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333/512)
  · exact Part10.box74 z k h hz hm hk hK hh hH
  · exact node263 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node260 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (27/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) 1 (27/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node259 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/128)
  · exact node260 z k h hz hZ hk hK hh hm hg
  · exact node261 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node258 (z k h : ℝ)
    (hz : (333/512) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333/512) (31/32) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node256 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333/512)
  · exact Part10.box73 z k h hz hm hk hK hh hH
  · exact node258 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node255 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (3/16) ≤ h) (hH : h ≤ (27/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (31/32) (27/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node254 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/128)
  · exact node255 z k h hz hZ hk hK hh hm hg
  · exact node256 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node253 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (31/32)
  · exact node254 z k h hz hZ hk hm hh hH hg
  · exact node259 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node251 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part10.box72 z k h hz hm hk hK hh hH
  · exact node253 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node250 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node251 z k h hz hZ hk hK hh hm hg
  · exact Part10.box75 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node248 (z k h : ℝ)
    (hz : (333/512) ≤ z) (hZ : z ≤ (21/32))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (333/512) (15/16) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node246 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (27/128) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (333/512)
  · exact Part09.box70 z k h hz hm hk hK hh hH
  · exact node248 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node245 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (27/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (15/16) (27/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node244 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (27/128)
  · exact node245 z k h hz hZ hk hK hh hm hg
  · exact node246 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node243 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (29/32))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (29/32) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node242 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (29/32)
  · exact node243 z k h hz hZ hk hm hh hH hg
  · exact node244 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node240 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part09.box69 z k h hz hm hk hK hh hH
  · exact node242 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node239 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node240 z k h hz hZ hk hK hh hm hg
  · exact Part09.box71 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node238 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15/16)
  · exact node239 z k h hz hZ hk hm hh hH hg
  · exact node250 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node236 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part09.box68 z k h hz hm hk hK hh hH
  · exact node238 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node235 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node236 z k h hz hZ hk hK hh hm hg
  · exact Part10.box76 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node232 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (7/8) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node230 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part09.box65 z k h hz hm hk hK hh hH
  · exact node232 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node229 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node230 z k h hz hZ hk hK hh hm hg
  · exact Part09.box66 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node227 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (13/16) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node225 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part08.box63 z k h hz hm hk hK hh hH
  · exact node227 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node224 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node225 z k h hz hZ hk hK hh hm hg
  · exact Part09.box64 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node223 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13/16)
  · exact node224 z k h hz hZ hk hm hh hH hg
  · exact node229 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node221 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part08.box62 z k h hz hm hk hK hh hH
  · exact node223 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node220 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node221 z k h hz hZ hk hK hh hm hg
  · exact Part09.box67 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node219 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node220 z k h hz hZ hk hm hh hH hg
  · exact node235 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node217 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part08.box61 z k h hz hm hk hK hh hH
  · exact node219 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node216 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) 1 (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node214 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part08.box60 z k h hz hm hk hK hh hH
  · exact node216 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node213 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) 1 (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node211 (z k h : ℝ)
    (hz : (327/512) ≤ z) (hZ : z ≤ (165/256))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (327/512) 1 (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node209 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (327/512)
  · exact Part08.box58 z k h hz hm hk hK hh hH
  · exact node211 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node208 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (31/32) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node209 z k h hz hZ hk hK hh hm hg
  · exact Part08.box59 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node206 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (31/32) (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node205 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (15/16) ≤ k) (hK : k ≤ (31/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node206 z k h hz hZ hk hK hh hm hg
  · exact Part08.box57 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node204 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (31/32)
  · exact node205 z k h hz hZ hk hm hh hH hg
  · exact node208 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node203 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact node204 z k h hz hm hk hK hh hH hg
  · exact node213 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node202 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (15/16) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node203 z k h hz hZ hk hK hh hm hg
  · exact node214 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node201 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (15/16) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node199 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part08.box56 z k h hz hm hk hK hh hH
  · exact node201 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node198 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (15/16) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node196 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (15/16) (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node195 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (29/32) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node196 z k h hz hZ hk hK hh hm hg
  · exact Part07.box55 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node193 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (7/8) ≤ k) (hK : k ≤ (29/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (29/32) (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node192 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (7/8) ≤ k) (hK : k ≤ (29/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node193 z k h hz hZ hk hK hh hm hg
  · exact Part07.box54 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node191 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (29/32)
  · exact node192 z k h hz hZ hk hm hh hH hg
  · exact node195 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node190 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact node191 z k h hz hm hk hK hh hH hg
  · exact node198 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node189 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ (15/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node190 z k h hz hZ hk hK hh hm hg
  · exact node199 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node188 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (15/16)
  · exact node189 z k h hz hZ hk hm hh hH hg
  · exact node202 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node186 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part07.box53 z k h hz hm hk hK hh hH
  · exact node188 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node185 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) 1 (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node183 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part07.box52 z k h hz hm hk hK hh hH
  · exact node185 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node182 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/8) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node183 z k h hz hZ hk hK hh hm hg
  · exact node186 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node181 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (7/8) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node179 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part07.box51 z k h hz hm hk hK hh hH
  · exact node181 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node178 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (7/8) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node176 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (27/32) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (7/8) (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node175 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (27/32) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node176 z k h hz hZ hk hK hh hm hg
  · exact Part07.box50 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node173 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (13/16) ≤ k) (hK : k ≤ (27/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (15/128))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (27/32) (15/128)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node172 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (13/16) ≤ k) (hK : k ≤ (27/32))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/128)
  · exact node173 z k h hz hZ hk hK hh hm hg
  · exact Part07.box49 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node171 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (165/256))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (27/32)
  · exact node172 z k h hz hZ hk hm hh hH hg
  · exact node175 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node170 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact node171 z k h hz hm hk hK hh hH hg
  · exact node178 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node169 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (13/16) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node170 z k h hz hZ hk hK hh hm hg
  · exact node179 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node168 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (13/16) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node166 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part07.box48 z k h hz hm hk hK hh hH
  · exact node168 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node165 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (13/16) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node163 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part06.box47 z k h hz hm hk hK hh hH
  · exact node165 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node162 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (13/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node163 z k h hz hZ hk hK hh hm hg
  · exact node166 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node161 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (13/16)
  · exact node162 z k h hz hZ hk hm hh hH hg
  · exact node169 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node159 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part06.box46 z k h hz hm hk hK hh hH
  · exact node161 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node158 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (7/8) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node156 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part06.box45 z k h hz hm hk hK hh hH
  · exact node158 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node155 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ (7/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node156 z k h hz hZ hk hK hh hm hg
  · exact node159 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node154 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/8)
  · exact node155 z k h hz hZ hk hm hh hH hg
  · exact node182 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node152 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part06.box44 z k h hz hm hk hK hh hH
  · exact node154 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node151 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/4) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/16)
  · exact node152 z k h hz hZ hk hK hh hm hg
  · exact node217 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node148 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (3/4) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node146 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part06.box41 z k h hz hm hk hK hh hH
  · exact node148 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node145 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node146 z k h hz hZ hk hK hh hm hg
  · exact Part06.box42 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node143 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (11/16) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node141 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part05.box39 z k h hz hm hk hK hh hH
  · exact node143 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node140 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node141 z k h hz hZ hk hK hh hm hg
  · exact Part06.box40 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node139 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11/16)
  · exact node140 z k h hz hZ hk hm hh hH hg
  · exact node145 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node137 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part05.box38 z k h hz hm hk hK hh hH
  · exact node139 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node136 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node137 z k h hz hZ hk hK hh hm hg
  · exact Part06.box43 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node133 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (5/8) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node131 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part05.box35 z k h hz hm hk hK hh hH
  · exact node133 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node130 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node131 z k h hz hZ hk hK hh hm hg
  · exact Part05.box36 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node128 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (9/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (9/16) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node126 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (9/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part05.box33 z k h hz hm hk hK hh hH
  · exact node128 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node125 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (9/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node126 z k h hz hZ hk hK hh hm hg
  · exact Part05.box34 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node124 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (9/16)
  · exact node125 z k h hz hZ hk hm hh hH hg
  · exact node130 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node122 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part05.box32 z k h hz hm hk hK hh hH
  · exact node124 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node121 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node122 z k h hz hZ hk hK hh hm hg
  · exact Part05.box37 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node120 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5/8)
  · exact node121 z k h hz hZ hk hm hh hH hg
  · exact node136 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node118 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part04.box31 z k h hz hm hk hK hh hH
  · exact node120 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node117 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (3/4) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node115 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part04.box30 z k h hz hm hk hK hh hH
  · exact node117 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node114 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (3/4) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node113 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (11/16) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node114 z k h hz hZ hk hK hh hm hg
  · exact node115 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node112 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (11/16) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node110 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part04.box29 z k h hz hm hk hK hh hH
  · exact node112 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node109 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (11/16) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node108 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (11/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node109 z k h hz hZ hk hK hh hm hg
  · exact node110 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node107 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (11/16)
  · exact node108 z k h hz hZ hk hm hh hH hg
  · exact node113 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node105 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part04.box28 z k h hz hm hk hK hh hH
  · exact node107 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node104 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (3/4) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node102 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part04.box27 z k h hz hm hk hK hh hH
  · exact node104 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node101 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (5/8) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node102 z k h hz hZ hk hK hh hm hg
  · exact node105 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node100 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (5/8) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node98 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (9/64) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part04.box26 z k h hz hm hk hK hh hH
  · exact node100 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node97 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (9/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (5/8) (9/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node96 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (9/16) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/64)
  · exact node97 z k h hz hZ hk hK hh hm hg
  · exact node98 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node95 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (9/16))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (9/16) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node94 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (9/16)
  · exact node95 z k h hz hZ hk hm hh hH hg
  · exact node96 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node92 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part04.box25 z k h hz hm hk hK hh hH
  · exact node94 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node91 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (5/8) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node89 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part04.box24 z k h hz hm hk hK hh hH
  · exact node91 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node88 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (5/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node89 z k h hz hZ hk hK hh hm hg
  · exact node92 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node87 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (5/8)
  · exact node88 z k h hz hZ hk hm hh hH hg
  · exact node101 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node85 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part03.box23 z k h hz hm hk hK hh hH
  · exact node87 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node84 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ (3/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/16)
  · exact node85 z k h hz hZ hk hK hh hm hg
  · exact node118 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node83 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/4)
  · exact node84 z k h hz hZ hk hm hh hH hg
  · exact node151 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node82 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact node83 z k h hz hm hk hK hh hH hg
  · exact node266 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node81 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/2) ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/8)
  · exact node82 z k h hz hZ hk hK hh hm hg
  · exact node289 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node80 (z k h : ℝ)
    (hz : (45/64) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (45/64) (1/2) (3/4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node78 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/16) ≤ h) (hH : h ≤ (21/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/2) (21/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node77 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (21/32)
  · exact node78 z k h hz hZ hk hK hh hm hg
  · exact Part03.box22 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node76 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (3/8) (3/4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node75 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (45/64))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/8)
  · exact node76 z k h hz hZ hk hm hh hH hg
  · exact node77 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node74 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (9/16) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (45/64)
  · exact node75 z k h hz hm hk hK hh hH hg
  · exact node80 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node73 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/8) ≤ h) (hH : h ≤ (9/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/2) (9/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node72 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/16)
  · exact node73 z k h hz hZ hk hK hh hm hg
  · exact node74 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node71 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/4) (3/4)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node70 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/4)
  · exact node71 z k h hz hZ hk hm hh hH hg
  · exact node72 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node68 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : (3/8) ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact Part03.box21 z k h hz hm hk hK hh hH
  · exact node70 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node67 (z k h : ℝ)
    (hz : (21/32) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (21/32) (1/2) (3/8)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node64 (z k h : ℝ)
    (hz : (165/256) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/16) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (165/256) (1/2) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node62 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/16) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (165/256)
  · exact Part03.box18 z k h hz hm hk hK hh hH
  · exact node64 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node61 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (7/16) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node62 z k h hz hZ hk hK hh hm hg
  · exact Part03.box19 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node59 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (7/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (15/64))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (7/16) (15/64)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node58 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (7/16))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (15/64)
  · exact node59 z k h hz hZ hk hK hh hm hg
  · exact Part03.box17 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node57 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (7/16)
  · exact node58 z k h hz hZ hk hm hh hH hg
  · exact node61 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node55 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part03.box16 z k h hz hm hk hK hh hH
  · exact node57 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node54 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node55 z k h hz hZ hk hK hh hm hg
  · exact Part03.box20 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node52 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (3/8) (9/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node50 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (9/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part02.box14 z k h hz hm hk hK hh hH
  · exact node52 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node49 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (9/32)
  · exact node50 z k h hz hZ hk hK hh hm hg
  · exact Part02.box15 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node48 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/8)
  · exact node49 z k h hz hZ hk hm hh hH hg
  · exact node54 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node46 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/16) ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part02.box13 z k h hz hm hk hK hh hH
  · exact node48 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node45 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/2) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node43 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part02.box12 z k h hz hm hk hK hh hH
  · exact node45 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node42 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/2) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node40 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part02.box11 z k h hz hm hk hK hh hH
  · exact node42 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node39 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (3/8) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node40 z k h hz hZ hk hK hh hm hg
  · exact node43 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node38 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (3/8) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node36 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part02.box10 z k h hz hm hk hK hh hH
  · exact node38 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node35 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (3/8) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node33 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part02.box9 z k h hz hm hk hK hh hH
  · exact node35 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node32 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (3/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node33 z k h hz hZ hk hK hh hm hg
  · exact node36 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node31 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (3/8)
  · exact node32 z k h hz hZ hk hm hh hH hg
  · exact node39 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node29 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part02.box8 z k h hz hm hk hK hh hH
  · exact node31 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node28 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/4) ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/16)
  · exact node29 z k h hz hZ hk hK hh hm hg
  · exact node46 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node26 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/8) ≤ k) (hK : k ≤ (1/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/4) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node24 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/8) ≤ k) (hK : k ≤ (1/4))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part01.box6 z k h hz hm hk hK hh hH
  · exact node26 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node23 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/8) ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/4) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node21 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/8) ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part01.box5 z k h hz hm hk hK hh hH
  · exact node23 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node20 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : (1/8) ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node21 z k h hz hZ hk hK hh hm hg
  · exact node24 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node19 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/8) (3/16)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node17 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/8))
    (hh : (3/32) ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part01.box4 z k h hz hm hk hK hh hH
  · exact node19 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node16 (z k h : ℝ)
    (hz : (81/128) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  have hzu : z ≤ 1 := by linarith only [hZ]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hb := constraint_upper z k h (81/128) (1/8) (3/32)
    (by norm_num) hz hzu hk0 hK hh0 hH
  norm_num [constraint] at hb
  linarith only [hg, hb]

private theorem node14 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/32))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (81/128)
  · exact Part01.box3 z k h hz hm hk hK hh hH
  · exact node16 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node13 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/8))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/32)
  · exact node14 z k h hz hZ hk hK hh hm hg
  · exact node17 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node12 (z k h : ℝ)
    (hz : (39/64) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/8)
  · exact node13 z k h hz hZ hk hm hh hH hg
  · exact node20 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node10 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/16))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (39/64)
  · exact Part01.box2 z k h hz hm hk hK hh hH
  · exact node12 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node9 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/4))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/16)
  · exact node10 z k h hz hZ hk hK hh hm hg
  · exact Part01.box7 z k h hz hZ hk hK (le_of_not_ge hm) hH

private theorem node8 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (21/32))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/4)
  · exact node9 z k h hz hZ hk hm hh hH hg
  · exact node28 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node7 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/8))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (21/32)
  · exact node8 z k h hz hm hk hK hh hH hg
  · exact node67 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node6 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ (1/2))
    (hh : 0 ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/8)
  · exact node7 z k h hz hZ hk hK hh hm hg
  · exact node68 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node5 (z k h : ℝ)
    (hz : (9/16) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : k ≤ (1/2)
  · exact node6 z k h hz hZ hk hm hh hH hg
  · exact node81 z k h hz hZ (le_of_not_ge hm) hK hh hH hg

private theorem node3 (z k h : ℝ)
    (hz : (3/8) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/4))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (9/16)
  · exact Part01.box1 z k h hz hm hk hK hh hH
  · exact node5 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

private theorem node2 (z k h : ℝ)
    (hz : (3/8) ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : h ≤ (3/4)
  · exact node3 z k h hz hZ hk hK hh hm hg
  · exact node384 z k h hz hZ hk hK (le_of_not_ge hm) hH hg

private theorem node0 (z k h : ℝ)
    (hz : 0 ≤ z) (hZ : z ≤ (3/4))
    (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ (3/2))
    (hg : 0 ≤ constraint z k h) : 0 ≤ P z k h := by
  by_cases hm : z ≤ (3/8)
  · exact Part01.box0 z k h hz hm hk hK hh hH
  · exact node2 z k h (le_of_not_ge hm) hZ hk hK hh hH hg

theorem polynomial_nonneg (z k h : ℝ)
    (hz : 0 ≤ z) (hZ : z ≤ 3/4) (hk : 0 ≤ k) (hK : k ≤ 1)
    (hh : 0 ≤ h) (hH : h ≤ 3/2) (hg : 0 ≤ constraint z k h) :
    0 ≤ P z k h := node0 z k h hz hZ hk hK hh hH hg

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate
