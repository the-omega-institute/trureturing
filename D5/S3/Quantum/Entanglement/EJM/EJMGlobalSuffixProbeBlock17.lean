/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock17
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock17
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock17
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1241 : Cache :=
  step cache1240 ⟨17, by decide⟩ 0
private def partial1241 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 0)

private def cache1242 : Cache :=
  step cache1240 ⟨17, by decide⟩ 1
private def partial1242 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 1)

private def cache1243 : Cache :=
  step cache1242 ⟨18, by decide⟩ 0
private def partial1243 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 0)

private def cache1244 : Cache :=
  step cache1242 ⟨18, by decide⟩ 1
private def partial1244 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 1)

private def cache1245 : Cache :=
  step cache1244 ⟨19, by decide⟩ 0
private def partial1245 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 0)

private def cache1246 : Cache :=
  step cache1244 ⟨19, by decide⟩ 1
private def partial1246 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 1)

private def cache1247 : Cache :=
  step cache1244 ⟨19, by decide⟩ 2
private def partial1247 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 2)

private def cache1248 : Cache :=
  step cache1244 ⟨19, by decide⟩ 3
private def partial1248 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 3)

private def cache1249 : Cache :=
  step cache1242 ⟨18, by decide⟩ 2
private def partial1249 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 2)

private def cache1250 : Cache :=
  step cache1242 ⟨18, by decide⟩ 3
private def partial1250 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 3)

private def cache1251 : Cache :=
  step cache1250 ⟨19, by decide⟩ 0
private def partial1251 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 0)

private def cache1252 : Cache :=
  step cache1250 ⟨19, by decide⟩ 1
private def partial1252 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 1)

private def cache1253 : Cache :=
  step cache1250 ⟨19, by decide⟩ 2
private def partial1253 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 2)

private def cache1254 : Cache :=
  step cache1250 ⟨19, by decide⟩ 3
private def partial1254 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 3)

private def cache1255 : Cache :=
  step cache1240 ⟨17, by decide⟩ 2
private def partial1255 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 2)

private def cache1256 : Cache :=
  step cache1255 ⟨18, by decide⟩ 0
private def partial1256 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 0)

private def cache1257 : Cache :=
  step cache1256 ⟨19, by decide⟩ 0
private def partial1257 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 0)

private def cache1258 : Cache :=
  step cache1256 ⟨19, by decide⟩ 1
private def partial1258 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 1)

private def cache1259 : Cache :=
  step cache1256 ⟨19, by decide⟩ 2
private def partial1259 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 2)

private def cache1260 : Cache :=
  step cache1256 ⟨19, by decide⟩ 3
private def partial1260 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 3)

private def cache1261 : Cache :=
  step cache1255 ⟨18, by decide⟩ 1
private def partial1261 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 1)

private def cache1262 : Cache :=
  step cache1261 ⟨19, by decide⟩ 0
private def partial1262 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 0)

private def cache1263 : Cache :=
  step cache1261 ⟨19, by decide⟩ 1
private def partial1263 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 1)

private def cache1264 : Cache :=
  step cache1261 ⟨19, by decide⟩ 2
private def partial1264 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 2)

private def cache1265 : Cache :=
  step cache1261 ⟨19, by decide⟩ 3
private def partial1265 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 3)

private def cache1266 : Cache :=
  step cache1255 ⟨18, by decide⟩ 2
private def partial1266 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 2)

private def cache1267 : Cache :=
  step cache1266 ⟨19, by decide⟩ 0
private def partial1267 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 0)

private def cache1268 : Cache :=
  step cache1266 ⟨19, by decide⟩ 1
private def partial1268 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 1)

private def cache1269 : Cache :=
  step cache1266 ⟨19, by decide⟩ 2
private def partial1269 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 2)

private def cache1270 : Cache :=
  step cache1266 ⟨19, by decide⟩ 3
private def partial1270 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 3)

private def cache1271 : Cache :=
  step cache1255 ⟨18, by decide⟩ 3
private def partial1271 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 3)

private def cache1272 : Cache :=
  step cache1271 ⟨19, by decide⟩ 0
private def partial1272 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 0)

private def cache1273 : Cache :=
  step cache1271 ⟨19, by decide⟩ 1
private def partial1273 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 1)

private def cache1274 : Cache :=
  step cache1271 ⟨19, by decide⟩ 2
private def partial1274 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 2)

private def cache1275 : Cache :=
  step cache1271 ⟨19, by decide⟩ 3
private def partial1275 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 3)

private def cache1276 : Cache :=
  step cache1240 ⟨17, by decide⟩ 3
private def partial1276 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 3)

private def cache1277 : Cache :=
  step cache1276 ⟨18, by decide⟩ 0
private def partial1277 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 0)

private def cache1278 : Cache :=
  step cache1277 ⟨19, by decide⟩ 0
private def partial1278 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 0)

private def cache1279 : Cache :=
  step cache1277 ⟨19, by decide⟩ 1
private def partial1279 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 1)

private def cache1280 : Cache :=
  step cache1277 ⟨19, by decide⟩ 2
private def partial1280 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 2)

private def cache1281 : Cache :=
  step cache1277 ⟨19, by decide⟩ 3
private def partial1281 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 3)

private def cache1282 : Cache :=
  step cache1276 ⟨18, by decide⟩ 1
private def partial1282 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 1)

private def cache1283 : Cache :=
  step cache1282 ⟨19, by decide⟩ 0
private def partial1283 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 0)

private def cache1284 : Cache :=
  step cache1282 ⟨19, by decide⟩ 1
private def partial1284 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 1)

private def cache1285 : Cache :=
  step cache1282 ⟨19, by decide⟩ 2
private def partial1285 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 2)

private def cache1286 : Cache :=
  step cache1282 ⟨19, by decide⟩ 3
private def partial1286 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 3)

private def cache1287 : Cache :=
  step cache1276 ⟨18, by decide⟩ 2
private def partial1287 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 2)

private def cache1288 : Cache :=
  step cache1276 ⟨18, by decide⟩ 3
private def partial1288 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 3)

private theorem receipt1288 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1288, by decide⟩ cache1288 partial1288 = true := by
  decide +kernel

private theorem receipt1287 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1287, by decide⟩ cache1287 partial1287 = true := by
  decide +kernel

private theorem receipt1286 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1286, by decide⟩ cache1286 partial1286 = true := by
  decide +kernel

private theorem receipt1285 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1285, by decide⟩ cache1285 partial1285 = true := by
  decide +kernel

private theorem receipt1284 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1284, by decide⟩ cache1284 partial1284 = true := by
  decide +kernel

private theorem receipt1283 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1283, by decide⟩ cache1283 partial1283 = true := by
  decide +kernel

private theorem receipt1282 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1282, by decide⟩ cache1282 partial1282 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1283,1284,1285,1286])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2828633954099315 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1283
  · exact receipt1284
  · exact receipt1285
  · exact receipt1286

private theorem receipt1281 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1281, by decide⟩ cache1281 partial1281 = true := by
  decide +kernel

private theorem receipt1280 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1280, by decide⟩ cache1280 partial1280 = true := by
  decide +kernel

#print axioms receipt1280

private theorem receipt1279 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1279, by decide⟩ cache1279 partial1279 = true := by
  decide +kernel

private theorem receipt1278 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1278, by decide⟩ cache1278 partial1278 = true := by
  decide +kernel

private theorem receipt1277 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1277, by decide⟩ cache1277 partial1277 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1278,1279,1280,1281])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2817636152811475 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1278
  · exact receipt1279
  · exact receipt1280
  · exact receipt1281

private theorem receipt1276 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1276, by decide⟩ cache1276 partial1276 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1277,1282,1287,1288])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2833033074089906 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1277
  · exact receipt1282
  · exact receipt1287
  · exact receipt1288

private theorem receipt1275 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1275, by decide⟩ cache1275 partial1275 = true := by
  decide +kernel

private theorem receipt1274 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1274, by decide⟩ cache1274 partial1274 = true := by
  decide +kernel

private theorem receipt1273 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1273, by decide⟩ cache1273 partial1273 = true := by
  decide +kernel

private theorem receipt1272 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1272, by decide⟩ cache1272 partial1272 = true := by
  decide +kernel

private theorem receipt1271 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1271, by decide⟩ cache1271 partial1271 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1272,1273,1274,1275])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2804438791266067 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1272
  · exact receipt1273
  · exact receipt1274
  · exact receipt1275

private theorem receipt1270 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1270, by decide⟩ cache1270 partial1270 = true := by
  decide +kernel

private theorem receipt1269 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1269, by decide⟩ cache1269 partial1269 = true := by
  decide +kernel

private theorem receipt1268 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1268, by decide⟩ cache1268 partial1268 = true := by
  decide +kernel

private theorem receipt1267 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1267, by decide⟩ cache1267 partial1267 = true := by
  decide +kernel

private theorem receipt1266 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1266, by decide⟩ cache1266 partial1266 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1267,1268,1269,1270])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2793440989978227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1267
  · exact receipt1268
  · exact receipt1269
  · exact receipt1270

private theorem receipt1265 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1265, by decide⟩ cache1265 partial1265 = true := by
  decide +kernel

private theorem receipt1264 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1264, by decide⟩ cache1264 partial1264 = true := by
  decide +kernel

private theorem receipt1263 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1263, by decide⟩ cache1263 partial1263 = true := by
  decide +kernel

private theorem receipt1262 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1262, by decide⟩ cache1262 partial1262 = true := by
  decide +kernel

private theorem receipt1261 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1261, by decide⟩ cache1261 partial1261 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1262,1263,1264,1265])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2782443188690387 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1262
  · exact receipt1263
  · exact receipt1264
  · exact receipt1265

private theorem receipt1260 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1260, by decide⟩ cache1260 partial1260 = true := by
  decide +kernel

private theorem receipt1259 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1259, by decide⟩ cache1259 partial1259 = true := by
  decide +kernel

private theorem receipt1258 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1258, by decide⟩ cache1258 partial1258 = true := by
  decide +kernel

private theorem receipt1257 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1257, by decide⟩ cache1257 partial1257 = true := by
  decide +kernel

private theorem receipt1256 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1256, by decide⟩ cache1256 partial1256 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1257,1258,1259,1260])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2771445387402547 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1257
  · exact receipt1258
  · exact receipt1259
  · exact receipt1260

private theorem receipt1255 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1255, by decide⟩ cache1255 partial1255 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1256,1261,1266,1271])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2795638401703186 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1256
  · exact receipt1261
  · exact receipt1266
  · exact receipt1271

private theorem receipt1254 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1254, by decide⟩ cache1254 partial1254 = true := by
  decide +kernel

private theorem receipt1253 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1253, by decide⟩ cache1253 partial1253 = true := by
  decide +kernel

private theorem receipt1252 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1252, by decide⟩ cache1252 partial1252 = true := by
  decide +kernel

private theorem receipt1251 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1251, by decide⟩ cache1251 partial1251 = true := by
  decide +kernel

private theorem receipt1250 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1250, by decide⟩ cache1250 partial1250 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1251,1252,1253,1254])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2758248025857139 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1251
  · exact receipt1252
  · exact receipt1253
  · exact receipt1254

private theorem receipt1249 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1249, by decide⟩ cache1249 partial1249 = true := by
  decide +kernel

private theorem receipt1248 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1248, by decide⟩ cache1248 partial1248 = true := by
  decide +kernel

private theorem receipt1247 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1247, by decide⟩ cache1247 partial1247 = true := by
  decide +kernel

private theorem receipt1246 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1246, by decide⟩ cache1246 partial1246 = true := by
  decide +kernel

private theorem receipt1245 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1245, by decide⟩ cache1245 partial1245 = true := by
  decide +kernel

private theorem receipt1244 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1244, by decide⟩ cache1244 partial1244 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1245,1246,1247,1248])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2745050664311731 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1245
  · exact receipt1246
  · exact receipt1247
  · exact receipt1248

private theorem receipt1243 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1243, by decide⟩ cache1243 partial1243 = true := by
  decide +kernel

private theorem receipt1242 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1242, by decide⟩ cache1242 partial1242 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1243,1244,1249,1250])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2749449784302450 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1243
  · exact receipt1244
  · exact receipt1249
  · exact receipt1250

private theorem receipt1241 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1241, by decide⟩ cache1241 partial1241 = true := by
  decide +kernel

theorem receipt1240 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1240, by decide⟩ cache1240 partial1240 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1241,1242,1255,1276])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2806627609910065 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1241
  · exact receipt1242
  · exact receipt1255
  · exact receipt1276


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock17
