/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock16
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock16
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock16
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1293 : Cache :=
  step cache1292 ⟨17, by decide⟩ 0
private def partial1293 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1292 ⟨17, by decide⟩ (some 0)

private def cache1294 : Cache :=
  step cache1292 ⟨17, by decide⟩ 1
private def partial1294 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1292 ⟨17, by decide⟩ (some 1)

private def cache1295 : Cache :=
  step cache1292 ⟨17, by decide⟩ 2
private def partial1295 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1292 ⟨17, by decide⟩ (some 2)

private def cache1296 : Cache :=
  step cache1295 ⟨18, by decide⟩ 0
private def partial1296 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1295 ⟨18, by decide⟩ (some 0)

private def cache1297 : Cache :=
  step cache1295 ⟨18, by decide⟩ 1
private def partial1297 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1295 ⟨18, by decide⟩ (some 1)

private def cache1298 : Cache :=
  step cache1295 ⟨18, by decide⟩ 2
private def partial1298 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1295 ⟨18, by decide⟩ (some 2)

private def cache1299 : Cache :=
  step cache1298 ⟨19, by decide⟩ 0
private def partial1299 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1298 ⟨19, by decide⟩ (some 0)

private def cache1300 : Cache :=
  step cache1298 ⟨19, by decide⟩ 1
private def partial1300 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1298 ⟨19, by decide⟩ (some 1)

private def cache1301 : Cache :=
  step cache1298 ⟨19, by decide⟩ 2
private def partial1301 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1298 ⟨19, by decide⟩ (some 2)

private def cache1302 : Cache :=
  step cache1298 ⟨19, by decide⟩ 3
private def partial1302 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1298 ⟨19, by decide⟩ (some 3)

private def cache1303 : Cache :=
  step cache1295 ⟨18, by decide⟩ 3
private def partial1303 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1295 ⟨18, by decide⟩ (some 3)

private def cache1304 : Cache :=
  step cache1303 ⟨19, by decide⟩ 0
private def partial1304 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1303 ⟨19, by decide⟩ (some 0)

private def cache1305 : Cache :=
  step cache1303 ⟨19, by decide⟩ 1
private def partial1305 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1303 ⟨19, by decide⟩ (some 1)

private def cache1306 : Cache :=
  step cache1303 ⟨19, by decide⟩ 2
private def partial1306 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1303 ⟨19, by decide⟩ (some 2)

private def cache1307 : Cache :=
  step cache1303 ⟨19, by decide⟩ 3
private def partial1307 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1303 ⟨19, by decide⟩ (some 3)

private def cache1308 : Cache :=
  step cache1292 ⟨17, by decide⟩ 3
private def partial1308 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1292 ⟨17, by decide⟩ (some 3)

private def cache1309 : Cache :=
  step cache1308 ⟨18, by decide⟩ 0
private def partial1309 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1308 ⟨18, by decide⟩ (some 0)

private def cache1310 : Cache :=
  step cache1309 ⟨19, by decide⟩ 0
private def partial1310 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1309 ⟨19, by decide⟩ (some 0)

private def cache1311 : Cache :=
  step cache1309 ⟨19, by decide⟩ 1
private def partial1311 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1309 ⟨19, by decide⟩ (some 1)

private def cache1312 : Cache :=
  step cache1309 ⟨19, by decide⟩ 2
private def partial1312 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1309 ⟨19, by decide⟩ (some 2)

private def cache1313 : Cache :=
  step cache1309 ⟨19, by decide⟩ 3
private def partial1313 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1309 ⟨19, by decide⟩ (some 3)

private def cache1314 : Cache :=
  step cache1308 ⟨18, by decide⟩ 1
private def partial1314 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1308 ⟨18, by decide⟩ (some 1)

private def cache1315 : Cache :=
  step cache1314 ⟨19, by decide⟩ 0
private def partial1315 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1314 ⟨19, by decide⟩ (some 0)

private def cache1316 : Cache :=
  step cache1314 ⟨19, by decide⟩ 1
private def partial1316 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1314 ⟨19, by decide⟩ (some 1)

private def cache1317 : Cache :=
  step cache1314 ⟨19, by decide⟩ 2
private def partial1317 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1314 ⟨19, by decide⟩ (some 2)

private def cache1318 : Cache :=
  step cache1314 ⟨19, by decide⟩ 3
private def partial1318 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1314 ⟨19, by decide⟩ (some 3)

private def cache1319 : Cache :=
  step cache1308 ⟨18, by decide⟩ 2
private def partial1319 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1308 ⟨18, by decide⟩ (some 2)

private def cache1320 : Cache :=
  step cache1319 ⟨19, by decide⟩ 0
private def partial1320 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1319 ⟨19, by decide⟩ (some 0)

private def cache1321 : Cache :=
  step cache1319 ⟨19, by decide⟩ 1
private def partial1321 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1319 ⟨19, by decide⟩ (some 1)

private def cache1322 : Cache :=
  step cache1319 ⟨19, by decide⟩ 2
private def partial1322 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1319 ⟨19, by decide⟩ (some 2)

private def cache1323 : Cache :=
  step cache1319 ⟨19, by decide⟩ 3
private def partial1323 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1319 ⟨19, by decide⟩ (some 3)

private def cache1324 : Cache :=
  step cache1308 ⟨18, by decide⟩ 3
private def partial1324 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1308 ⟨18, by decide⟩ (some 3)

private theorem receipt1324 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1324, by decide⟩ cache1324 partial1324 = true := by
  decide +kernel

private theorem receipt1323 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1323, by decide⟩ cache1323 partial1323 = true := by
  decide +kernel

private theorem receipt1322 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1322, by decide⟩ cache1322 partial1322 = true := by
  decide +kernel

private theorem receipt1321 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1321, by decide⟩ cache1321 partial1321 = true := by
  decide +kernel

private theorem receipt1320 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1320, by decide⟩ cache1320 partial1320 = true := by
  decide +kernel

private theorem receipt1319 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1319, by decide⟩ cache1319 partial1319 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1320,1321,1322,1323])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2910017683629331 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1320
  · exact receipt1321
  · exact receipt1322
  · exact receipt1323

private theorem receipt1318 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1318, by decide⟩ cache1318 partial1318 = true := by
  decide +kernel

private theorem receipt1317 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1317, by decide⟩ cache1317 partial1317 = true := by
  decide +kernel

private theorem receipt1316 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1316, by decide⟩ cache1316 partial1316 = true := by
  decide +kernel

private theorem receipt1315 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1315, by decide⟩ cache1315 partial1315 = true := by
  decide +kernel

private theorem receipt1314 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1314, by decide⟩ cache1314 partial1314 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1315,1316,1317,1318])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2899019882341491 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1315
  · exact receipt1316
  · exact receipt1317
  · exact receipt1318

private theorem receipt1313 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1313, by decide⟩ cache1313 partial1313 = true := by
  decide +kernel

private theorem receipt1312 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1312, by decide⟩ cache1312 partial1312 = true := by
  decide +kernel

private theorem receipt1311 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1311, by decide⟩ cache1311 partial1311 = true := by
  decide +kernel

private theorem receipt1310 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1310, by decide⟩ cache1310 partial1310 = true := by
  decide +kernel

private theorem receipt1309 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1309, by decide⟩ cache1309 partial1309 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1310,1311,1312,1313])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2888022081053651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1310
  · exact receipt1311
  · exact receipt1312
  · exact receipt1313

private theorem receipt1308 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1308, by decide⟩ cache1308 partial1308 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1309,1314,1319,1324])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2912215095354290 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1309
  · exact receipt1314
  · exact receipt1319
  · exact receipt1324

private theorem receipt1307 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1307, by decide⟩ cache1307 partial1307 = true := by
  decide +kernel

private theorem receipt1306 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1306, by decide⟩ cache1306 partial1306 = true := by
  decide +kernel

private theorem receipt1305 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1305, by decide⟩ cache1305 partial1305 = true := by
  decide +kernel

private theorem receipt1304 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1304, by decide⟩ cache1304 partial1304 = true := by
  decide +kernel

private theorem receipt1303 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1303, by decide⟩ cache1303 partial1303 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1304,1305,1306,1307])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2874824719508243 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1304
  · exact receipt1305
  · exact receipt1306
  · exact receipt1307

private theorem receipt1302 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1302, by decide⟩ cache1302 partial1302 = true := by
  decide +kernel

private theorem receipt1301 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1301, by decide⟩ cache1301 partial1301 = true := by
  decide +kernel

private theorem receipt1300 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1300, by decide⟩ cache1300 partial1300 = true := by
  decide +kernel

private theorem receipt1299 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1299, by decide⟩ cache1299 partial1299 = true := by
  decide +kernel

private theorem receipt1298 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1298, by decide⟩ cache1298 partial1298 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1299,1300,1301,1302])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2863826918220403 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1299
  · exact receipt1300
  · exact receipt1301
  · exact receipt1302

private theorem receipt1297 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1297, by decide⟩ cache1297 partial1297 = true := by
  decide +kernel

private theorem receipt1296 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1296, by decide⟩ cache1296 partial1296 = true := by
  decide +kernel

private theorem receipt1295 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1295, by decide⟩ cache1295 partial1295 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1296,1297,1298,1303])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2866024330469906 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1296
  · exact receipt1297
  · exact receipt1298
  · exact receipt1303

private theorem receipt1294 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1294, by decide⟩ cache1294 partial1294 = true := by
  decide +kernel

private theorem receipt1293 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1293, by decide⟩ cache1293 partial1293 = true := by
  decide +kernel

theorem receipt1292 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1292, by decide⟩ cache1292 partial1292 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1293,1294,1295,1308])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2877017835741617 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1293
  · exact receipt1294
  · exact receipt1295
  · exact receipt1308

theorem receipt1291 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1291, by decide⟩ cache1291 partial1291 = true := by
  decide +kernel

theorem receipt1290 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1290, by decide⟩ cache1290 partial1290 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock16
