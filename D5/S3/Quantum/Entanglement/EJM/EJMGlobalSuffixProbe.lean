/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbe
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbe
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: All 2497 original suffix nodes compose through 124 complete subtree receipts and all 41 remaining four-child splits. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock2
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock3
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock4
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock6
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock8
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock9
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock10
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock11
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock0
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock1
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock2
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock3
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock4
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock6
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock8
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock9
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock10
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock11
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock14

private theorem receipt2412 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨2412, by decide⟩ cache2412 partial2412 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![2413,2442,2459,2480])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(5454898159496622 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2413
  · exact receipt2442
  · exact receipt2459
  · exact receipt2480

private theorem receipt2160 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨2160, by decide⟩ cache2160 partial2160 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![2161,2162,2163,2204])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(4847808790466095 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2161
  · exact receipt2162
  · exact receipt2163
  · exact receipt2204

private theorem receipt2159 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨2159, by decide⟩ cache2159 partial2159 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![2160,2249,2306,2367])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(5206326365064718 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2160
  · exact receipt2249
  · exact receipt2306
  · exact receipt2367

private theorem receipt2038 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨2038, by decide⟩ cache2038 partial2038 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![2039,2040,2081,2130])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(4685037030145775 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2039
  · exact receipt2040
  · exact receipt2081
  · exact receipt2130

private theorem receipt1909 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1909, by decide⟩ cache1909 partial1909 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1910,1911,1952,1997])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(4392497663897295 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1910
  · exact receipt1911
  · exact receipt1952
  · exact receipt1997

private theorem receipt1796 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1796, by decide⟩ cache1796 partial1796 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1797,1798,1803,1864])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(4099947562328239 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1797
  · exact receipt1798
  · exact receipt1803
  · exact receipt1864

private theorem receipt1794 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨1794, by decide⟩ cache1794 partial1794 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![1795,1796,1909,2038])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(4482634516848750 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1795
  · exact receipt1796
  · exact receipt1909
  · exact receipt2038

private theorem receipt1792 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 ⟨1792, by decide⟩ cache1792 partial1792 = true := by
  apply actual_split (i := (13 : Fin 20))
    (children := ![1793,1794,2159,2412])
    (by
      change (.split (13 : Fin 20)
        (fun a => ⟨(5305203431890989 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (13 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1793
  · exact receipt1794
  · exact receipt2159
  · exact receipt2412

#print axioms receipt1792

private theorem receipt1662 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1662, by decide⟩ cache1662 partial1662 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1663,1664,1665,1682])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3699651224063984 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1663
  · exact receipt1664
  · exact receipt1665
  · exact receipt1682

private theorem receipt1658 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1658, by decide⟩ cache1658 partial1658 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1659,1660,1661,1662])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(3655668610944879 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1659
  · exact receipt1660
  · exact receipt1661
  · exact receipt1662

private theorem receipt1512 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1512, by decide⟩ cache1512 partial1512 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1513,1514,1515,1540])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3387309371473200 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1513
  · exact receipt1514
  · exact receipt1515
  · exact receipt1540

private theorem receipt1508 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1508, by decide⟩ cache1508 partial1508 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1509,1510,1511,1512])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(3325734572309679 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1509
  · exact receipt1510
  · exact receipt1511
  · exact receipt1512

private theorem receipt1507 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨1507, by decide⟩ cache1507 partial1507 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![1508,1597,1658,1739])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(3824991782747278 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1508
  · exact receipt1597
  · exact receipt1658
  · exact receipt1739

private theorem receipt1438 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1438, by decide⟩ cache1438 partial1438 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1439,1440,1441,1466])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3224541912413168 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1439
  · exact receipt1440
  · exact receipt1441
  · exact receipt1466

private theorem receipt1373 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1373, by decide⟩ cache1373 partial1373 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1374,1375,1376,1401])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3081570495671248 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1374
  · exact receipt1375
  · exact receipt1376
  · exact receipt1401

private theorem receipt1370 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1370, by decide⟩ cache1370 partial1370 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1371,1372,1373,1438])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(3162932745120623 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1371
  · exact receipt1372
  · exact receipt1373
  · exact receipt1438

private theorem receipt1289 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1289, by decide⟩ cache1289 partial1289 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1290,1291,1292,1325])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(2914399620079952 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1290
  · exact receipt1291
  · exact receipt1292
  · exact receipt1325

private theorem receipt1212 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1212, by decide⟩ cache1212 partial1212 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1213,1214,1215,1240])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(2727441294202800 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1213
  · exact receipt1214
  · exact receipt1215
  · exact receipt1240

private theorem receipt1209 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1209, by decide⟩ cache1209 partial1209 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1210,1211,1212,1289])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(2835191822718799 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1210
  · exact receipt1211
  · exact receipt1212
  · exact receipt1289

private theorem receipt1136 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1136, by decide⟩ cache1136 partial1136 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1137,1138,1139,1168])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(2569070807649840 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1137
  · exact receipt1138
  · exact receipt1139
  · exact receipt1168

private theorem receipt1067 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1067, by decide⟩ cache1067 partial1067 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1068,1069,1070,1091])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(2399708963833232 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1068
  · exact receipt1069
  · exact receipt1070
  · exact receipt1091

private theorem receipt1064 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1064, by decide⟩ cache1064 partial1064 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1065,1066,1067,1136])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(2498663399327023 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1065
  · exact receipt1066
  · exact receipt1067
  · exact receipt1136

private theorem receipt955 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨955, by decide⟩ cache955 partial955 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![956,957,958,1003])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(2206134773118864 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt956
  · exact receipt957
  · exact receipt958
  · exact receipt1003

private theorem receipt862 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨862, by decide⟩ cache862 partial862 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![863,864,865,906])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1992779576142832 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt863
  · exact receipt864
  · exact receipt865
  · exact receipt906

private theorem receipt859 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨859, by decide⟩ cache859 partial859 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![860,861,862,955])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(2100530104658831 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt860
  · exact receipt861
  · exact receipt862
  · exact receipt955

private theorem receipt858 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨858, by decide⟩ cache858 partial858 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![859,1064,1209,1370])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(3013311076526958 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt859
  · exact receipt1064
  · exact receipt1209
  · exact receipt1370

private theorem receipt781 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨781, by decide⟩ cache781 partial781 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![782,783,784,821])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1805819102257616 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt782
  · exact receipt783
  · exact receipt784
  · exact receipt821

private theorem receipt692 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨692, by decide⟩ cache692 partial692 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![693,694,695,744])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1636446518400688 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt693
  · exact receipt694
  · exact receipt695
  · exact receipt744

private theorem receipt627 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨627, by decide⟩ cache627 partial627 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![628,629,630,659])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1449494636547728 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt628
  · exact receipt629
  · exact receipt630
  · exact receipt659

private theorem receipt625 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨625, by decide⟩ cache625 partial625 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![626,627,692,781])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(1717808759459407 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt626
  · exact receipt627
  · exact receipt692
  · exact receipt781

private theorem receipt528 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨528, by decide⟩ cache528 partial528 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![529,530,531,572])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1258126450115120 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt529
  · exact receipt530
  · exact receipt531
  · exact receipt572

private theorem receipt447 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨447, by decide⟩ cache447 partial447 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![448,449,450,487])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(1071165976229904 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt448
  · exact receipt449
  · exact receipt450
  · exact receipt487

private theorem receipt378 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨378, by decide⟩ cache378 partial378 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![379,380,381,406])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(893008039391088 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt379
  · exact receipt380
  · exact receipt381
  · exact receipt406

private theorem receipt376 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨376, by decide⟩ cache376 partial376 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![377,378,447,528])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(1161324309786415 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt377
  · exact receipt378
  · exact receipt447
  · exact receipt528

private theorem receipt251 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨251, by decide⟩ cache251 partial251 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![252,253,254,315])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(692828723879824 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt252
  · exact receipt253
  · exact receipt254
  · exact receipt315

private theorem receipt134 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨134, by decide⟩ cache134 partial134 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![135,136,137,194])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(426684080722160 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt135
  · exact receipt136
  · exact receipt137
  · exact receipt194

private theorem receipt9 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨9, by decide⟩ cache9 partial9 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![10,11,12,73])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(160535141548368 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt10
  · exact receipt11
  · exact receipt12
  · exact receipt73

private theorem receipt7 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨7, by decide⟩ cache7 partial7 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![8,9,134,251])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(552026779025679 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt8
  · exact receipt9
  · exact receipt134
  · exact receipt251

private theorem receipt5 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 ⟨5, by decide⟩ cache5 partial5 = true := by
  apply actual_split (i := (14 : Fin 20))
    (children := ![6,7,376,625])
    (by
      change (.split (14 : Fin 20)
        (fun a => ⟨(1374591399100622 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (14 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt6
  · exact receipt7
  · exact receipt376
  · exact receipt625

private theorem receipt3 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 ⟨3, by decide⟩ cache3 partial3 = true := by
  apply actual_split (i := (13 : Fin 20))
    (children := ![4,5,858,1507])
    (by
      change (.split (13 : Fin 20)
        (fun a => ⟨(3314388682014861 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (13 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt4
  · exact receipt5
  · exact receipt858
  · exact receipt1507

set_option trace.profiler true in
private theorem receipt0 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 9 ⟨0, by decide⟩ cache0 partial0 = true := by
  apply actual_split (i := (12 : Fin 20))
    (children := ![1,2,3,1792])
    (by
      change (.split (12 : Fin 20)
        (fun a => ⟨(3940651284824108 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (12 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1
  · exact receipt2
  · exact receipt3
  · exact receipt1792

#print axioms receipt0

private theorem pilot_suffix :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 9 ⟨0, by decide⟩ pilotCache pilotPartial = true :=
  receipt0

#print axioms pilot_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbe
