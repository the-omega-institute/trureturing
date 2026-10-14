/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock6
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock6
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock6
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

private def cache1377 : Cache :=
  step cache1376 ⟨17, by decide⟩ 0
private def partial1377 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1376 ⟨17, by decide⟩ (some 0)

private def cache1378 : Cache :=
  step cache1376 ⟨17, by decide⟩ 1
private def partial1378 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1376 ⟨17, by decide⟩ (some 1)

private def cache1379 : Cache :=
  step cache1376 ⟨17, by decide⟩ 2
private def partial1379 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1376 ⟨17, by decide⟩ (some 2)

private def cache1380 : Cache :=
  step cache1379 ⟨18, by decide⟩ 0
private def partial1380 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1379 ⟨18, by decide⟩ (some 0)

private def cache1381 : Cache :=
  step cache1379 ⟨18, by decide⟩ 1
private def partial1381 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1379 ⟨18, by decide⟩ (some 1)

private def cache1382 : Cache :=
  step cache1379 ⟨18, by decide⟩ 2
private def partial1382 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1379 ⟨18, by decide⟩ (some 2)

private def cache1383 : Cache :=
  step cache1379 ⟨18, by decide⟩ 3
private def partial1383 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1379 ⟨18, by decide⟩ (some 3)

private def cache1384 : Cache :=
  step cache1383 ⟨19, by decide⟩ 0
private def partial1384 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1383 ⟨19, by decide⟩ (some 0)

private def cache1385 : Cache :=
  step cache1383 ⟨19, by decide⟩ 1
private def partial1385 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1383 ⟨19, by decide⟩ (some 1)

private def cache1386 : Cache :=
  step cache1383 ⟨19, by decide⟩ 2
private def partial1386 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1383 ⟨19, by decide⟩ (some 2)

private def cache1387 : Cache :=
  step cache1383 ⟨19, by decide⟩ 3
private def partial1387 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1383 ⟨19, by decide⟩ (some 3)

private def cache1388 : Cache :=
  step cache1376 ⟨17, by decide⟩ 3
private def partial1388 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1376 ⟨17, by decide⟩ (some 3)

private def cache1389 : Cache :=
  step cache1388 ⟨18, by decide⟩ 0
private def partial1389 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1388 ⟨18, by decide⟩ (some 0)

private def cache1390 : Cache :=
  step cache1389 ⟨19, by decide⟩ 0
private def partial1390 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1389 ⟨19, by decide⟩ (some 0)

private def cache1391 : Cache :=
  step cache1389 ⟨19, by decide⟩ 1
private def partial1391 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1389 ⟨19, by decide⟩ (some 1)

private def cache1392 : Cache :=
  step cache1389 ⟨19, by decide⟩ 2
private def partial1392 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1389 ⟨19, by decide⟩ (some 2)

private def cache1393 : Cache :=
  step cache1389 ⟨19, by decide⟩ 3
private def partial1393 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1389 ⟨19, by decide⟩ (some 3)

private def cache1394 : Cache :=
  step cache1388 ⟨18, by decide⟩ 1
private def partial1394 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1388 ⟨18, by decide⟩ (some 1)

private def cache1395 : Cache :=
  step cache1394 ⟨19, by decide⟩ 0
private def partial1395 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1394 ⟨19, by decide⟩ (some 0)

private def cache1396 : Cache :=
  step cache1394 ⟨19, by decide⟩ 1
private def partial1396 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1394 ⟨19, by decide⟩ (some 1)

private def cache1397 : Cache :=
  step cache1394 ⟨19, by decide⟩ 2
private def partial1397 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1394 ⟨19, by decide⟩ (some 2)

private def cache1398 : Cache :=
  step cache1394 ⟨19, by decide⟩ 3
private def partial1398 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1394 ⟨19, by decide⟩ (some 3)

private def cache1399 : Cache :=
  step cache1388 ⟨18, by decide⟩ 2
private def partial1399 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1388 ⟨18, by decide⟩ (some 2)

private def cache1400 : Cache :=
  step cache1388 ⟨18, by decide⟩ 3
private def partial1400 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1388 ⟨18, by decide⟩ (some 3)

private def cache1402 : Cache :=
  step cache1401 ⟨17, by decide⟩ 0
private def partial1402 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 0)

private def cache1403 : Cache :=
  step cache1401 ⟨17, by decide⟩ 1
private def partial1403 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 1)

private def cache1404 : Cache :=
  step cache1403 ⟨18, by decide⟩ 0
private def partial1404 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 0)

private def cache1405 : Cache :=
  step cache1403 ⟨18, by decide⟩ 1
private def partial1405 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 1)

private def cache1406 : Cache :=
  step cache1405 ⟨19, by decide⟩ 0
private def partial1406 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 0)

private def cache1407 : Cache :=
  step cache1405 ⟨19, by decide⟩ 1
private def partial1407 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 1)

private def cache1408 : Cache :=
  step cache1405 ⟨19, by decide⟩ 2
private def partial1408 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 2)

private def cache1409 : Cache :=
  step cache1405 ⟨19, by decide⟩ 3
private def partial1409 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 3)

private def cache1410 : Cache :=
  step cache1403 ⟨18, by decide⟩ 2
private def partial1410 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 2)

private def cache1411 : Cache :=
  step cache1403 ⟨18, by decide⟩ 3
private def partial1411 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 3)

private def cache1412 : Cache :=
  step cache1411 ⟨19, by decide⟩ 0
private def partial1412 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 0)

private def cache1413 : Cache :=
  step cache1411 ⟨19, by decide⟩ 1
private def partial1413 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 1)

private def cache1414 : Cache :=
  step cache1411 ⟨19, by decide⟩ 2
private def partial1414 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 2)

private def cache1415 : Cache :=
  step cache1411 ⟨19, by decide⟩ 3
private def partial1415 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 3)

private def cache1416 : Cache :=
  step cache1401 ⟨17, by decide⟩ 2
private def partial1416 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 2)

private def cache1417 : Cache :=
  step cache1416 ⟨18, by decide⟩ 0
private def partial1417 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 0)

private def cache1418 : Cache :=
  step cache1417 ⟨19, by decide⟩ 0
private def partial1418 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 0)

private def cache1419 : Cache :=
  step cache1417 ⟨19, by decide⟩ 1
private def partial1419 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 1)

private def cache1420 : Cache :=
  step cache1417 ⟨19, by decide⟩ 2
private def partial1420 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 2)

private def cache1421 : Cache :=
  step cache1417 ⟨19, by decide⟩ 3
private def partial1421 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 3)

private def cache1422 : Cache :=
  step cache1416 ⟨18, by decide⟩ 1
private def partial1422 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 1)

private def cache1423 : Cache :=
  step cache1422 ⟨19, by decide⟩ 0
private def partial1423 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 0)

private def cache1424 : Cache :=
  step cache1422 ⟨19, by decide⟩ 1
private def partial1424 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 1)

private def cache1425 : Cache :=
  step cache1422 ⟨19, by decide⟩ 2
private def partial1425 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 2)

private def cache1426 : Cache :=
  step cache1422 ⟨19, by decide⟩ 3
private def partial1426 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 3)

private def cache1427 : Cache :=
  step cache1416 ⟨18, by decide⟩ 2
private def partial1427 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 2)

private def cache1428 : Cache :=
  step cache1416 ⟨18, by decide⟩ 3
private def partial1428 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 3)

private def cache1429 : Cache :=
  step cache1428 ⟨19, by decide⟩ 0
private def partial1429 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 0)

private def cache1430 : Cache :=
  step cache1428 ⟨19, by decide⟩ 1
private def partial1430 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 1)

private def cache1431 : Cache :=
  step cache1428 ⟨19, by decide⟩ 2
private def partial1431 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 2)

private def cache1432 : Cache :=
  step cache1428 ⟨19, by decide⟩ 3
private def partial1432 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 3)

private def cache1433 : Cache :=
  step cache1401 ⟨17, by decide⟩ 3
private def partial1433 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 3)

private def cache1434 : Cache :=
  step cache1433 ⟨18, by decide⟩ 0
private def partial1434 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 0)

private def cache1435 : Cache :=
  step cache1433 ⟨18, by decide⟩ 1
private def partial1435 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 1)

private def cache1436 : Cache :=
  step cache1433 ⟨18, by decide⟩ 2
private def partial1436 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 2)

private def cache1437 : Cache :=
  step cache1433 ⟨18, by decide⟩ 3
private def partial1437 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 3)

private def cache1442 : Cache :=
  step cache1441 ⟨17, by decide⟩ 0
private def partial1442 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 0)

private def cache1443 : Cache :=
  step cache1441 ⟨17, by decide⟩ 1
private def partial1443 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 1)

private def cache1444 : Cache :=
  step cache1441 ⟨17, by decide⟩ 2
private def partial1444 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 2)

private def cache1445 : Cache :=
  step cache1444 ⟨18, by decide⟩ 0
private def partial1445 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 0)

private def cache1446 : Cache :=
  step cache1444 ⟨18, by decide⟩ 1
private def partial1446 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 1)

private def cache1447 : Cache :=
  step cache1444 ⟨18, by decide⟩ 2
private def partial1447 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 2)

private def cache1448 : Cache :=
  step cache1444 ⟨18, by decide⟩ 3
private def partial1448 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 3)

private def cache1449 : Cache :=
  step cache1448 ⟨19, by decide⟩ 0
private def partial1449 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 0)

private def cache1450 : Cache :=
  step cache1448 ⟨19, by decide⟩ 1
private def partial1450 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 1)

private def cache1451 : Cache :=
  step cache1448 ⟨19, by decide⟩ 2
private def partial1451 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 2)

private def cache1452 : Cache :=
  step cache1448 ⟨19, by decide⟩ 3
private def partial1452 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 3)

private def cache1453 : Cache :=
  step cache1441 ⟨17, by decide⟩ 3
private def partial1453 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 3)

private def cache1454 : Cache :=
  step cache1453 ⟨18, by decide⟩ 0
private def partial1454 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 0)

private def cache1455 : Cache :=
  step cache1454 ⟨19, by decide⟩ 0
private def partial1455 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 0)

private def cache1456 : Cache :=
  step cache1454 ⟨19, by decide⟩ 1
private def partial1456 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 1)

private def cache1457 : Cache :=
  step cache1454 ⟨19, by decide⟩ 2
private def partial1457 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 2)

private def cache1458 : Cache :=
  step cache1454 ⟨19, by decide⟩ 3
private def partial1458 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 3)

private def cache1459 : Cache :=
  step cache1453 ⟨18, by decide⟩ 1
private def partial1459 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 1)

private def cache1460 : Cache :=
  step cache1459 ⟨19, by decide⟩ 0
private def partial1460 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 0)

private def cache1461 : Cache :=
  step cache1459 ⟨19, by decide⟩ 1
private def partial1461 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 1)

private def cache1462 : Cache :=
  step cache1459 ⟨19, by decide⟩ 2
private def partial1462 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 2)

private def cache1463 : Cache :=
  step cache1459 ⟨19, by decide⟩ 3
private def partial1463 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 3)

private def cache1464 : Cache :=
  step cache1453 ⟨18, by decide⟩ 2
private def partial1464 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 2)

private def cache1465 : Cache :=
  step cache1453 ⟨18, by decide⟩ 3
private def partial1465 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 3)

private theorem receipt1465 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1465, by decide⟩ cache1465 partial1465 = true := by
  decide +kernel

private theorem receipt1464 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1464, by decide⟩ cache1464 partial1464 = true := by
  decide +kernel

private theorem receipt1463 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1463, by decide⟩ cache1463 partial1463 = true := by
  decide +kernel

private theorem receipt1462 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1462, by decide⟩ cache1462 partial1462 = true := by
  decide +kernel

private theorem receipt1461 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1461, by decide⟩ cache1461 partial1461 = true := by
  decide +kernel

private theorem receipt1460 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1460, by decide⟩ cache1460 partial1460 = true := by
  decide +kernel

private theorem receipt1459 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1459, by decide⟩ cache1459 partial1459 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1460,1461,1462,1463])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3217956119688851 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1460
  · exact receipt1461
  · exact receipt1462
  · exact receipt1463

private theorem receipt1458 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1458, by decide⟩ cache1458 partial1458 = true := by
  decide +kernel

private theorem receipt1457 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1457, by decide⟩ cache1457 partial1457 = true := by
  decide +kernel

private theorem receipt1456 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1456, by decide⟩ cache1456 partial1456 = true := by
  decide +kernel

private theorem receipt1455 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1455, by decide⟩ cache1455 partial1455 = true := by
  decide +kernel

private theorem receipt1454 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1454, by decide⟩ cache1454 partial1454 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1455,1456,1457,1458])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3206958318401011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1455
  · exact receipt1456
  · exact receipt1457
  · exact receipt1458

private theorem receipt1453 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1453, by decide⟩ cache1453 partial1453 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1454,1459,1464,1465])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3222355239679442 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1454
  · exact receipt1459
  · exact receipt1464
  · exact receipt1465

private theorem receipt1452 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1452, by decide⟩ cache1452 partial1452 = true := by
  decide +kernel

private theorem receipt1451 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1451, by decide⟩ cache1451 partial1451 = true := by
  decide +kernel

private theorem receipt1450 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1450, by decide⟩ cache1450 partial1450 = true := by
  decide +kernel

private theorem receipt1449 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1449, by decide⟩ cache1449 partial1449 = true := by
  decide +kernel

private theorem receipt1448 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1448, by decide⟩ cache1448 partial1448 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1449,1450,1451,1452])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3193760956855603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1449
  · exact receipt1450
  · exact receipt1451
  · exact receipt1452

private theorem receipt1447 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1447, by decide⟩ cache1447 partial1447 = true := by
  decide +kernel

private theorem receipt1446 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1446, by decide⟩ cache1446 partial1446 = true := by
  decide +kernel

private theorem receipt1445 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1445, by decide⟩ cache1445 partial1445 = true := by
  decide +kernel

private theorem receipt1444 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1444, by decide⟩ cache1444 partial1444 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1445,1446,1447,1448])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3184962715825330 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1445
  · exact receipt1446
  · exact receipt1447
  · exact receipt1448

private theorem receipt1443 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1443, by decide⟩ cache1443 partial1443 = true := by
  decide +kernel

private theorem receipt1442 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1442, by decide⟩ cache1442 partial1442 = true := by
  decide +kernel

theorem receipt1441 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1441, by decide⟩ cache1441 partial1441 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1442,1443,1444,1453])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3195956221097041 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1442
  · exact receipt1443
  · exact receipt1444
  · exact receipt1453

theorem receipt1440 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1440, by decide⟩ cache1440 partial1440 = true := by
  decide +kernel

theorem receipt1439 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1439, by decide⟩ cache1439 partial1439 = true := by
  decide +kernel

private theorem receipt1437 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1437, by decide⟩ cache1437 partial1437 = true := by
  decide +kernel

private theorem receipt1436 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1436, by decide⟩ cache1436 partial1436 = true := by
  decide +kernel

private theorem receipt1435 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1435, by decide⟩ cache1435 partial1435 = true := by
  decide +kernel

private theorem receipt1434 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1434, by decide⟩ cache1434 partial1434 = true := by
  decide +kernel

private theorem receipt1433 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1433, by decide⟩ cache1433 partial1433 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1434,1435,1436,1437])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3160767552992082 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1434
  · exact receipt1435
  · exact receipt1436
  · exact receipt1437

private theorem receipt1432 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1432, by decide⟩ cache1432 partial1432 = true := by
  decide +kernel

private theorem receipt1431 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1431, by decide⟩ cache1431 partial1431 = true := by
  decide +kernel

private theorem receipt1430 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1430, by decide⟩ cache1430 partial1430 = true := by
  decide +kernel

private theorem receipt1429 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1429, by decide⟩ cache1429 partial1429 = true := by
  decide +kernel

private theorem receipt1428 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1428, by decide⟩ cache1428 partial1428 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1429,1430,1431,1432])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3149769751704243 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1429
  · exact receipt1430
  · exact receipt1431
  · exact receipt1432

private theorem receipt1427 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1427, by decide⟩ cache1427 partial1427 = true := by
  decide +kernel

private theorem receipt1426 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1426, by decide⟩ cache1426 partial1426 = true := by
  decide +kernel

private theorem receipt1425 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1425, by decide⟩ cache1425 partial1425 = true := by
  decide +kernel

private theorem receipt1424 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1424, by decide⟩ cache1424 partial1424 = true := by
  decide +kernel

private theorem receipt1423 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1423, by decide⟩ cache1423 partial1423 = true := by
  decide +kernel

private theorem receipt1422 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1422, by decide⟩ cache1422 partial1422 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1423,1424,1425,1426])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3136572390158835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1423
  · exact receipt1424
  · exact receipt1425
  · exact receipt1426

private theorem receipt1421 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1421, by decide⟩ cache1421 partial1421 = true := by
  decide +kernel

private theorem receipt1420 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1420, by decide⟩ cache1420 partial1420 = true := by
  decide +kernel

private theorem receipt1419 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1419, by decide⟩ cache1419 partial1419 = true := by
  decide +kernel

private theorem receipt1418 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1418, by decide⟩ cache1418 partial1418 = true := by
  decide +kernel

private theorem receipt1417 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1417, by decide⟩ cache1417 partial1417 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1418,1419,1420,1421])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3125574588870995 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1418
  · exact receipt1419
  · exact receipt1420
  · exact receipt1421

private theorem receipt1416 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1416, by decide⟩ cache1416 partial1416 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1417,1422,1427,1428])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3140971510149426 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1417
  · exact receipt1422
  · exact receipt1427
  · exact receipt1428

private theorem receipt1415 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1415, by decide⟩ cache1415 partial1415 = true := by
  decide +kernel

private theorem receipt1414 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1414, by decide⟩ cache1414 partial1414 = true := by
  decide +kernel

private theorem receipt1413 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1413, by decide⟩ cache1413 partial1413 = true := by
  decide +kernel

private theorem receipt1412 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1412, by decide⟩ cache1412 partial1412 = true := by
  decide +kernel

private theorem receipt1411 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1411, by decide⟩ cache1411 partial1411 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1412,1413,1414,1415])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3112377227325587 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1412
  · exact receipt1413
  · exact receipt1414
  · exact receipt1415

private theorem receipt1410 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1410, by decide⟩ cache1410 partial1410 = true := by
  decide +kernel

private theorem receipt1409 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1409, by decide⟩ cache1409 partial1409 = true := by
  decide +kernel

private theorem receipt1408 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1408, by decide⟩ cache1408 partial1408 = true := by
  decide +kernel

private theorem receipt1407 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1407, by decide⟩ cache1407 partial1407 = true := by
  decide +kernel

private theorem receipt1406 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1406, by decide⟩ cache1406 partial1406 = true := by
  decide +kernel

private theorem receipt1405 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1405, by decide⟩ cache1405 partial1405 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1406,1407,1408,1409])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3099179865780179 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1406
  · exact receipt1407
  · exact receipt1408
  · exact receipt1409

private theorem receipt1404 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1404, by decide⟩ cache1404 partial1404 = true := by
  decide +kernel

private theorem receipt1403 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1403, by decide⟩ cache1403 partial1403 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1404,1405,1410,1411])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3103578985770898 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1404
  · exact receipt1405
  · exact receipt1410
  · exact receipt1411

private theorem receipt1402 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1402, by decide⟩ cache1402 partial1402 = true := by
  decide +kernel

theorem receipt1401 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1401, by decide⟩ cache1401 partial1401 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1402,1403,1416,1433])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3151960718356305 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1402
  · exact receipt1403
  · exact receipt1416
  · exact receipt1433

private theorem receipt1400 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1400, by decide⟩ cache1400 partial1400 = true := by
  decide +kernel

private theorem receipt1399 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1399, by decide⟩ cache1399 partial1399 = true := by
  decide +kernel

private theorem receipt1398 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1398, by decide⟩ cache1398 partial1398 = true := by
  decide +kernel

private theorem receipt1397 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1397, by decide⟩ cache1397 partial1397 = true := by
  decide +kernel

private theorem receipt1396 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1396, by decide⟩ cache1396 partial1396 = true := by
  decide +kernel

private theorem receipt1395 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1395, by decide⟩ cache1395 partial1395 = true := by
  decide +kernel

private theorem receipt1394 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1394, by decide⟩ cache1394 partial1394 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1395,1396,1397,1398])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3074984702946931 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1395
  · exact receipt1396
  · exact receipt1397
  · exact receipt1398

private theorem receipt1393 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1393, by decide⟩ cache1393 partial1393 = true := by
  decide +kernel

private theorem receipt1392 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1392, by decide⟩ cache1392 partial1392 = true := by
  decide +kernel

private theorem receipt1391 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1391, by decide⟩ cache1391 partial1391 = true := by
  decide +kernel

private theorem receipt1390 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1390, by decide⟩ cache1390 partial1390 = true := by
  decide +kernel

private theorem receipt1389 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1389, by decide⟩ cache1389 partial1389 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1390,1391,1392,1393])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3063986901659091 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1390
  · exact receipt1391
  · exact receipt1392
  · exact receipt1393

private theorem receipt1388 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1388, by decide⟩ cache1388 partial1388 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1389,1394,1399,1400])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3079383822937522 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1389
  · exact receipt1394
  · exact receipt1399
  · exact receipt1400

private theorem receipt1387 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1387, by decide⟩ cache1387 partial1387 = true := by
  decide +kernel

private theorem receipt1386 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1386, by decide⟩ cache1386 partial1386 = true := by
  decide +kernel

private theorem receipt1385 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1385, by decide⟩ cache1385 partial1385 = true := by
  decide +kernel

private theorem receipt1384 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1384, by decide⟩ cache1384 partial1384 = true := by
  decide +kernel

private theorem receipt1383 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1383, by decide⟩ cache1383 partial1383 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1384,1385,1386,1387])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3050789540113683 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1384
  · exact receipt1385
  · exact receipt1386
  · exact receipt1387

private theorem receipt1382 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1382, by decide⟩ cache1382 partial1382 = true := by
  decide +kernel

private theorem receipt1381 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1381, by decide⟩ cache1381 partial1381 = true := by
  decide +kernel

private theorem receipt1380 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1380, by decide⟩ cache1380 partial1380 = true := by
  decide +kernel

private theorem receipt1379 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1379, by decide⟩ cache1379 partial1379 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1380,1381,1382,1383])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3041991299083410 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1380
  · exact receipt1381
  · exact receipt1382
  · exact receipt1383

private theorem receipt1378 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1378, by decide⟩ cache1378 partial1378 = true := by
  decide +kernel

private theorem receipt1377 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1377, by decide⟩ cache1377 partial1377 = true := by
  decide +kernel

theorem receipt1376 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1376, by decide⟩ cache1376 partial1376 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1377,1378,1379,1388])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3052984804355121 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1377
  · exact receipt1378
  · exact receipt1379
  · exact receipt1388

theorem receipt1375 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1375, by decide⟩ cache1375 partial1375 = true := by
  decide +kernel

theorem receipt1374 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1374, by decide⟩ cache1374 partial1374 = true := by
  decide +kernel

theorem receipt1372 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1372, by decide⟩ cache1372 partial1372 = true := by
  decide +kernel

theorem receipt1371 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1371, by decide⟩ cache1371 partial1371 = true := by
  decide +kernel

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


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock6
