/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock15
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock15
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock15
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1326 : Cache :=
  step cache1325 ⟨17, by decide⟩ 0
private def partial1326 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1325 ⟨17, by decide⟩ (some 0)

private def cache1327 : Cache :=
  step cache1325 ⟨17, by decide⟩ 1
private def partial1327 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1325 ⟨17, by decide⟩ (some 1)

private def cache1328 : Cache :=
  step cache1327 ⟨18, by decide⟩ 0
private def partial1328 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1327 ⟨18, by decide⟩ (some 0)

private def cache1329 : Cache :=
  step cache1327 ⟨18, by decide⟩ 1
private def partial1329 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1327 ⟨18, by decide⟩ (some 1)

private def cache1330 : Cache :=
  step cache1329 ⟨19, by decide⟩ 0
private def partial1330 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1329 ⟨19, by decide⟩ (some 0)

private def cache1331 : Cache :=
  step cache1329 ⟨19, by decide⟩ 1
private def partial1331 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1329 ⟨19, by decide⟩ (some 1)

private def cache1332 : Cache :=
  step cache1329 ⟨19, by decide⟩ 2
private def partial1332 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1329 ⟨19, by decide⟩ (some 2)

private def cache1333 : Cache :=
  step cache1329 ⟨19, by decide⟩ 3
private def partial1333 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1329 ⟨19, by decide⟩ (some 3)

private def cache1334 : Cache :=
  step cache1327 ⟨18, by decide⟩ 2
private def partial1334 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1327 ⟨18, by decide⟩ (some 2)

private def cache1335 : Cache :=
  step cache1327 ⟨18, by decide⟩ 3
private def partial1335 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1327 ⟨18, by decide⟩ (some 3)

private def cache1336 : Cache :=
  step cache1325 ⟨17, by decide⟩ 2
private def partial1336 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1325 ⟨17, by decide⟩ (some 2)

private def cache1337 : Cache :=
  step cache1336 ⟨18, by decide⟩ 0
private def partial1337 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1336 ⟨18, by decide⟩ (some 0)

private def cache1338 : Cache :=
  step cache1337 ⟨19, by decide⟩ 0
private def partial1338 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1337 ⟨19, by decide⟩ (some 0)

private def cache1339 : Cache :=
  step cache1337 ⟨19, by decide⟩ 1
private def partial1339 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1337 ⟨19, by decide⟩ (some 1)

private def cache1340 : Cache :=
  step cache1337 ⟨19, by decide⟩ 2
private def partial1340 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1337 ⟨19, by decide⟩ (some 2)

private def cache1341 : Cache :=
  step cache1337 ⟨19, by decide⟩ 3
private def partial1341 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1337 ⟨19, by decide⟩ (some 3)

private def cache1342 : Cache :=
  step cache1336 ⟨18, by decide⟩ 1
private def partial1342 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1336 ⟨18, by decide⟩ (some 1)

private def cache1343 : Cache :=
  step cache1342 ⟨19, by decide⟩ 0
private def partial1343 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1342 ⟨19, by decide⟩ (some 0)

private def cache1344 : Cache :=
  step cache1342 ⟨19, by decide⟩ 1
private def partial1344 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1342 ⟨19, by decide⟩ (some 1)

private def cache1345 : Cache :=
  step cache1342 ⟨19, by decide⟩ 2
private def partial1345 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1342 ⟨19, by decide⟩ (some 2)

private def cache1346 : Cache :=
  step cache1342 ⟨19, by decide⟩ 3
private def partial1346 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1342 ⟨19, by decide⟩ (some 3)

private def cache1347 : Cache :=
  step cache1336 ⟨18, by decide⟩ 2
private def partial1347 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1336 ⟨18, by decide⟩ (some 2)

private def cache1348 : Cache :=
  step cache1347 ⟨19, by decide⟩ 0
private def partial1348 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1347 ⟨19, by decide⟩ (some 0)

private def cache1349 : Cache :=
  step cache1347 ⟨19, by decide⟩ 1
private def partial1349 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1347 ⟨19, by decide⟩ (some 1)

private def cache1350 : Cache :=
  step cache1347 ⟨19, by decide⟩ 2
private def partial1350 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1347 ⟨19, by decide⟩ (some 2)

private def cache1351 : Cache :=
  step cache1347 ⟨19, by decide⟩ 3
private def partial1351 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1347 ⟨19, by decide⟩ (some 3)

private def cache1352 : Cache :=
  step cache1336 ⟨18, by decide⟩ 3
private def partial1352 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1336 ⟨18, by decide⟩ (some 3)

private def cache1353 : Cache :=
  step cache1352 ⟨19, by decide⟩ 0
private def partial1353 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1352 ⟨19, by decide⟩ (some 0)

private def cache1354 : Cache :=
  step cache1352 ⟨19, by decide⟩ 1
private def partial1354 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1352 ⟨19, by decide⟩ (some 1)

private def cache1355 : Cache :=
  step cache1352 ⟨19, by decide⟩ 2
private def partial1355 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1352 ⟨19, by decide⟩ (some 2)

private def cache1356 : Cache :=
  step cache1352 ⟨19, by decide⟩ 3
private def partial1356 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1352 ⟨19, by decide⟩ (some 3)

private def cache1357 : Cache :=
  step cache1325 ⟨17, by decide⟩ 3
private def partial1357 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1325 ⟨17, by decide⟩ (some 3)

private def cache1358 : Cache :=
  step cache1357 ⟨18, by decide⟩ 0
private def partial1358 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1357 ⟨18, by decide⟩ (some 0)

private def cache1359 : Cache :=
  step cache1358 ⟨19, by decide⟩ 0
private def partial1359 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1358 ⟨19, by decide⟩ (some 0)

private def cache1360 : Cache :=
  step cache1358 ⟨19, by decide⟩ 1
private def partial1360 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1358 ⟨19, by decide⟩ (some 1)

private def cache1361 : Cache :=
  step cache1358 ⟨19, by decide⟩ 2
private def partial1361 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1358 ⟨19, by decide⟩ (some 2)

private def cache1362 : Cache :=
  step cache1358 ⟨19, by decide⟩ 3
private def partial1362 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1358 ⟨19, by decide⟩ (some 3)

private def cache1363 : Cache :=
  step cache1357 ⟨18, by decide⟩ 1
private def partial1363 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1357 ⟨18, by decide⟩ (some 1)

private def cache1364 : Cache :=
  step cache1363 ⟨19, by decide⟩ 0
private def partial1364 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1363 ⟨19, by decide⟩ (some 0)

private def cache1365 : Cache :=
  step cache1363 ⟨19, by decide⟩ 1
private def partial1365 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1363 ⟨19, by decide⟩ (some 1)

private def cache1366 : Cache :=
  step cache1363 ⟨19, by decide⟩ 2
private def partial1366 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1363 ⟨19, by decide⟩ (some 2)

private def cache1367 : Cache :=
  step cache1363 ⟨19, by decide⟩ 3
private def partial1367 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1363 ⟨19, by decide⟩ (some 3)

private def cache1368 : Cache :=
  step cache1357 ⟨18, by decide⟩ 2
private def partial1368 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1357 ⟨18, by decide⟩ (some 2)

private def cache1369 : Cache :=
  step cache1357 ⟨18, by decide⟩ 3
private def partial1369 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1357 ⟨18, by decide⟩ (some 3)

private theorem receipt1369 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1369, by decide⟩ cache1369 partial1369 = true := by
  decide +kernel

private theorem receipt1368 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1368, by decide⟩ cache1368 partial1368 = true := by
  decide +kernel

private theorem receipt1367 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1367, by decide⟩ cache1367 partial1367 = true := by
  decide +kernel

private theorem receipt1366 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1366, by decide⟩ cache1366 partial1366 = true := by
  decide +kernel

private theorem receipt1365 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1365, by decide⟩ cache1365 partial1365 = true := by
  decide +kernel

private theorem receipt1364 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1364, by decide⟩ cache1364 partial1364 = true := by
  decide +kernel

private theorem receipt1363 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1363, by decide⟩ cache1363 partial1363 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1364,1365,1366,1367])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3006798334962323 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1364
  · exact receipt1365
  · exact receipt1366
  · exact receipt1367

private theorem receipt1362 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1362, by decide⟩ cache1362 partial1362 = true := by
  decide +kernel

private theorem receipt1361 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1361, by decide⟩ cache1361 partial1361 = true := by
  decide +kernel

private theorem receipt1360 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1360, by decide⟩ cache1360 partial1360 = true := by
  decide +kernel

private theorem receipt1359 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1359, by decide⟩ cache1359 partial1359 = true := by
  decide +kernel

private theorem receipt1358 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1358, by decide⟩ cache1358 partial1358 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1359,1360,1361,1362])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2995800533674483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1359
  · exact receipt1360
  · exact receipt1361
  · exact receipt1362

private theorem receipt1357 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1357, by decide⟩ cache1357 partial1357 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1358,1363,1368,1369])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3011197454952914 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1358
  · exact receipt1363
  · exact receipt1368
  · exact receipt1369

private theorem receipt1356 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1356, by decide⟩ cache1356 partial1356 = true := by
  decide +kernel

private theorem receipt1355 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1355, by decide⟩ cache1355 partial1355 = true := by
  decide +kernel

private theorem receipt1354 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1354, by decide⟩ cache1354 partial1354 = true := by
  decide +kernel

private theorem receipt1353 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1353, by decide⟩ cache1353 partial1353 = true := by
  decide +kernel

private theorem receipt1352 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1352, by decide⟩ cache1352 partial1352 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1353,1354,1355,1356])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2982603172129075 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1353
  · exact receipt1354
  · exact receipt1355
  · exact receipt1356

private theorem receipt1351 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1351, by decide⟩ cache1351 partial1351 = true := by
  decide +kernel

private theorem receipt1350 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1350, by decide⟩ cache1350 partial1350 = true := by
  decide +kernel

private theorem receipt1349 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1349, by decide⟩ cache1349 partial1349 = true := by
  decide +kernel

private theorem receipt1348 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1348, by decide⟩ cache1348 partial1348 = true := by
  decide +kernel

private theorem receipt1347 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1347, by decide⟩ cache1347 partial1347 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1348,1349,1350,1351])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2971605370841235 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1348
  · exact receipt1349
  · exact receipt1350
  · exact receipt1351

private theorem receipt1346 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1346, by decide⟩ cache1346 partial1346 = true := by
  decide +kernel

private theorem receipt1345 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1345, by decide⟩ cache1345 partial1345 = true := by
  decide +kernel

private theorem receipt1344 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1344, by decide⟩ cache1344 partial1344 = true := by
  decide +kernel

private theorem receipt1343 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1343, by decide⟩ cache1343 partial1343 = true := by
  decide +kernel

private theorem receipt1342 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1342, by decide⟩ cache1342 partial1342 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1343,1344,1345,1346])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2960607569553395 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1343
  · exact receipt1344
  · exact receipt1345
  · exact receipt1346

private theorem receipt1341 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1341, by decide⟩ cache1341 partial1341 = true := by
  decide +kernel

private theorem receipt1340 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1340, by decide⟩ cache1340 partial1340 = true := by
  decide +kernel

private theorem receipt1339 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1339, by decide⟩ cache1339 partial1339 = true := by
  decide +kernel

private theorem receipt1338 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1338, by decide⟩ cache1338 partial1338 = true := by
  decide +kernel

private theorem receipt1337 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1337, by decide⟩ cache1337 partial1337 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1338,1339,1340,1341])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2949609768265555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1338
  · exact receipt1339
  · exact receipt1340
  · exact receipt1341

private theorem receipt1336 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1336, by decide⟩ cache1336 partial1336 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1337,1342,1347,1352])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2973802782566194 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1337
  · exact receipt1342
  · exact receipt1347
  · exact receipt1352

private theorem receipt1335 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1335, by decide⟩ cache1335 partial1335 = true := by
  decide +kernel

private theorem receipt1334 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1334, by decide⟩ cache1334 partial1334 = true := by
  decide +kernel

private theorem receipt1333 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1333, by decide⟩ cache1333 partial1333 = true := by
  decide +kernel

private theorem receipt1332 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1332, by decide⟩ cache1332 partial1332 = true := by
  decide +kernel

private theorem receipt1331 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1331, by decide⟩ cache1331 partial1331 = true := by
  decide +kernel

private theorem receipt1330 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1330, by decide⟩ cache1330 partial1330 = true := by
  decide +kernel

private theorem receipt1329 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1329, by decide⟩ cache1329 partial1329 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1330,1331,1332,1333])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2932013286205011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1330
  · exact receipt1331
  · exact receipt1332
  · exact receipt1333

private theorem receipt1328 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1328, by decide⟩ cache1328 partial1328 = true := by
  decide +kernel

private theorem receipt1327 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1327, by decide⟩ cache1327 partial1327 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1328,1329,1334,1335])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2936412406195730 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1328
  · exact receipt1329
  · exact receipt1334
  · exact receipt1335

private theorem receipt1326 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1326, by decide⟩ cache1326 partial1326 = true := by
  decide +kernel

theorem receipt1325 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1325, by decide⟩ cache1325 partial1325 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1326,1327,1336,1357])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2984791991297489 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1326
  · exact receipt1327
  · exact receipt1336
  · exact receipt1357


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock15
