/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock12
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock12
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache255 : Cache :=
  step cache254 ⟨17, by decide⟩ 0
private def partial255 : Partial (Fin 20) (Fin 4) :=
  Function.update partial254 ⟨17, by decide⟩ (some 0)

private def cache256 : Cache :=
  step cache254 ⟨17, by decide⟩ 1
private def partial256 : Partial (Fin 20) (Fin 4) :=
  Function.update partial254 ⟨17, by decide⟩ (some 1)

private def cache257 : Cache :=
  step cache256 ⟨18, by decide⟩ 0
private def partial257 : Partial (Fin 20) (Fin 4) :=
  Function.update partial256 ⟨18, by decide⟩ (some 0)

private def cache258 : Cache :=
  step cache256 ⟨18, by decide⟩ 1
private def partial258 : Partial (Fin 20) (Fin 4) :=
  Function.update partial256 ⟨18, by decide⟩ (some 1)

private def cache259 : Cache :=
  step cache258 ⟨19, by decide⟩ 0
private def partial259 : Partial (Fin 20) (Fin 4) :=
  Function.update partial258 ⟨19, by decide⟩ (some 0)

private def cache260 : Cache :=
  step cache258 ⟨19, by decide⟩ 1
private def partial260 : Partial (Fin 20) (Fin 4) :=
  Function.update partial258 ⟨19, by decide⟩ (some 1)

private def cache261 : Cache :=
  step cache258 ⟨19, by decide⟩ 2
private def partial261 : Partial (Fin 20) (Fin 4) :=
  Function.update partial258 ⟨19, by decide⟩ (some 2)

private def cache262 : Cache :=
  step cache258 ⟨19, by decide⟩ 3
private def partial262 : Partial (Fin 20) (Fin 4) :=
  Function.update partial258 ⟨19, by decide⟩ (some 3)

private def cache263 : Cache :=
  step cache256 ⟨18, by decide⟩ 2
private def partial263 : Partial (Fin 20) (Fin 4) :=
  Function.update partial256 ⟨18, by decide⟩ (some 2)

private def cache264 : Cache :=
  step cache263 ⟨19, by decide⟩ 0
private def partial264 : Partial (Fin 20) (Fin 4) :=
  Function.update partial263 ⟨19, by decide⟩ (some 0)

private def cache265 : Cache :=
  step cache263 ⟨19, by decide⟩ 1
private def partial265 : Partial (Fin 20) (Fin 4) :=
  Function.update partial263 ⟨19, by decide⟩ (some 1)

private def cache266 : Cache :=
  step cache263 ⟨19, by decide⟩ 2
private def partial266 : Partial (Fin 20) (Fin 4) :=
  Function.update partial263 ⟨19, by decide⟩ (some 2)

private def cache267 : Cache :=
  step cache263 ⟨19, by decide⟩ 3
private def partial267 : Partial (Fin 20) (Fin 4) :=
  Function.update partial263 ⟨19, by decide⟩ (some 3)

private def cache268 : Cache :=
  step cache256 ⟨18, by decide⟩ 3
private def partial268 : Partial (Fin 20) (Fin 4) :=
  Function.update partial256 ⟨18, by decide⟩ (some 3)

private def cache269 : Cache :=
  step cache268 ⟨19, by decide⟩ 0
private def partial269 : Partial (Fin 20) (Fin 4) :=
  Function.update partial268 ⟨19, by decide⟩ (some 0)

private def cache270 : Cache :=
  step cache268 ⟨19, by decide⟩ 1
private def partial270 : Partial (Fin 20) (Fin 4) :=
  Function.update partial268 ⟨19, by decide⟩ (some 1)

private def cache271 : Cache :=
  step cache268 ⟨19, by decide⟩ 2
private def partial271 : Partial (Fin 20) (Fin 4) :=
  Function.update partial268 ⟨19, by decide⟩ (some 2)

private def cache272 : Cache :=
  step cache268 ⟨19, by decide⟩ 3
private def partial272 : Partial (Fin 20) (Fin 4) :=
  Function.update partial268 ⟨19, by decide⟩ (some 3)

private def cache273 : Cache :=
  step cache254 ⟨17, by decide⟩ 2
private def partial273 : Partial (Fin 20) (Fin 4) :=
  Function.update partial254 ⟨17, by decide⟩ (some 2)

private def cache274 : Cache :=
  step cache273 ⟨18, by decide⟩ 0
private def partial274 : Partial (Fin 20) (Fin 4) :=
  Function.update partial273 ⟨18, by decide⟩ (some 0)

private def cache275 : Cache :=
  step cache274 ⟨19, by decide⟩ 0
private def partial275 : Partial (Fin 20) (Fin 4) :=
  Function.update partial274 ⟨19, by decide⟩ (some 0)

private def cache276 : Cache :=
  step cache274 ⟨19, by decide⟩ 1
private def partial276 : Partial (Fin 20) (Fin 4) :=
  Function.update partial274 ⟨19, by decide⟩ (some 1)

private def cache277 : Cache :=
  step cache274 ⟨19, by decide⟩ 2
private def partial277 : Partial (Fin 20) (Fin 4) :=
  Function.update partial274 ⟨19, by decide⟩ (some 2)

private def cache278 : Cache :=
  step cache274 ⟨19, by decide⟩ 3
private def partial278 : Partial (Fin 20) (Fin 4) :=
  Function.update partial274 ⟨19, by decide⟩ (some 3)

private def cache279 : Cache :=
  step cache273 ⟨18, by decide⟩ 1
private def partial279 : Partial (Fin 20) (Fin 4) :=
  Function.update partial273 ⟨18, by decide⟩ (some 1)

private def cache280 : Cache :=
  step cache279 ⟨19, by decide⟩ 0
private def partial280 : Partial (Fin 20) (Fin 4) :=
  Function.update partial279 ⟨19, by decide⟩ (some 0)

private def cache281 : Cache :=
  step cache279 ⟨19, by decide⟩ 1
private def partial281 : Partial (Fin 20) (Fin 4) :=
  Function.update partial279 ⟨19, by decide⟩ (some 1)

private def cache282 : Cache :=
  step cache279 ⟨19, by decide⟩ 2
private def partial282 : Partial (Fin 20) (Fin 4) :=
  Function.update partial279 ⟨19, by decide⟩ (some 2)

private def cache283 : Cache :=
  step cache279 ⟨19, by decide⟩ 3
private def partial283 : Partial (Fin 20) (Fin 4) :=
  Function.update partial279 ⟨19, by decide⟩ (some 3)

private def cache284 : Cache :=
  step cache273 ⟨18, by decide⟩ 2
private def partial284 : Partial (Fin 20) (Fin 4) :=
  Function.update partial273 ⟨18, by decide⟩ (some 2)

private def cache285 : Cache :=
  step cache284 ⟨19, by decide⟩ 0
private def partial285 : Partial (Fin 20) (Fin 4) :=
  Function.update partial284 ⟨19, by decide⟩ (some 0)

private def cache286 : Cache :=
  step cache284 ⟨19, by decide⟩ 1
private def partial286 : Partial (Fin 20) (Fin 4) :=
  Function.update partial284 ⟨19, by decide⟩ (some 1)

private def cache287 : Cache :=
  step cache284 ⟨19, by decide⟩ 2
private def partial287 : Partial (Fin 20) (Fin 4) :=
  Function.update partial284 ⟨19, by decide⟩ (some 2)

private def cache288 : Cache :=
  step cache284 ⟨19, by decide⟩ 3
private def partial288 : Partial (Fin 20) (Fin 4) :=
  Function.update partial284 ⟨19, by decide⟩ (some 3)

private def cache289 : Cache :=
  step cache273 ⟨18, by decide⟩ 3
private def partial289 : Partial (Fin 20) (Fin 4) :=
  Function.update partial273 ⟨18, by decide⟩ (some 3)

private def cache290 : Cache :=
  step cache289 ⟨19, by decide⟩ 0
private def partial290 : Partial (Fin 20) (Fin 4) :=
  Function.update partial289 ⟨19, by decide⟩ (some 0)

private def cache291 : Cache :=
  step cache289 ⟨19, by decide⟩ 1
private def partial291 : Partial (Fin 20) (Fin 4) :=
  Function.update partial289 ⟨19, by decide⟩ (some 1)

private def cache292 : Cache :=
  step cache289 ⟨19, by decide⟩ 2
private def partial292 : Partial (Fin 20) (Fin 4) :=
  Function.update partial289 ⟨19, by decide⟩ (some 2)

private def cache293 : Cache :=
  step cache289 ⟨19, by decide⟩ 3
private def partial293 : Partial (Fin 20) (Fin 4) :=
  Function.update partial289 ⟨19, by decide⟩ (some 3)

private def cache294 : Cache :=
  step cache254 ⟨17, by decide⟩ 3
private def partial294 : Partial (Fin 20) (Fin 4) :=
  Function.update partial254 ⟨17, by decide⟩ (some 3)

private def cache295 : Cache :=
  step cache294 ⟨18, by decide⟩ 0
private def partial295 : Partial (Fin 20) (Fin 4) :=
  Function.update partial294 ⟨18, by decide⟩ (some 0)

private def cache296 : Cache :=
  step cache295 ⟨19, by decide⟩ 0
private def partial296 : Partial (Fin 20) (Fin 4) :=
  Function.update partial295 ⟨19, by decide⟩ (some 0)

private def cache297 : Cache :=
  step cache295 ⟨19, by decide⟩ 1
private def partial297 : Partial (Fin 20) (Fin 4) :=
  Function.update partial295 ⟨19, by decide⟩ (some 1)

private def cache298 : Cache :=
  step cache295 ⟨19, by decide⟩ 2
private def partial298 : Partial (Fin 20) (Fin 4) :=
  Function.update partial295 ⟨19, by decide⟩ (some 2)

private def cache299 : Cache :=
  step cache295 ⟨19, by decide⟩ 3
private def partial299 : Partial (Fin 20) (Fin 4) :=
  Function.update partial295 ⟨19, by decide⟩ (some 3)

private def cache300 : Cache :=
  step cache294 ⟨18, by decide⟩ 1
private def partial300 : Partial (Fin 20) (Fin 4) :=
  Function.update partial294 ⟨18, by decide⟩ (some 1)

private def cache301 : Cache :=
  step cache300 ⟨19, by decide⟩ 0
private def partial301 : Partial (Fin 20) (Fin 4) :=
  Function.update partial300 ⟨19, by decide⟩ (some 0)

private def cache302 : Cache :=
  step cache300 ⟨19, by decide⟩ 1
private def partial302 : Partial (Fin 20) (Fin 4) :=
  Function.update partial300 ⟨19, by decide⟩ (some 1)

private def cache303 : Cache :=
  step cache300 ⟨19, by decide⟩ 2
private def partial303 : Partial (Fin 20) (Fin 4) :=
  Function.update partial300 ⟨19, by decide⟩ (some 2)

private def cache304 : Cache :=
  step cache300 ⟨19, by decide⟩ 3
private def partial304 : Partial (Fin 20) (Fin 4) :=
  Function.update partial300 ⟨19, by decide⟩ (some 3)

private def cache305 : Cache :=
  step cache294 ⟨18, by decide⟩ 2
private def partial305 : Partial (Fin 20) (Fin 4) :=
  Function.update partial294 ⟨18, by decide⟩ (some 2)

private def cache306 : Cache :=
  step cache305 ⟨19, by decide⟩ 0
private def partial306 : Partial (Fin 20) (Fin 4) :=
  Function.update partial305 ⟨19, by decide⟩ (some 0)

private def cache307 : Cache :=
  step cache305 ⟨19, by decide⟩ 1
private def partial307 : Partial (Fin 20) (Fin 4) :=
  Function.update partial305 ⟨19, by decide⟩ (some 1)

private def cache308 : Cache :=
  step cache305 ⟨19, by decide⟩ 2
private def partial308 : Partial (Fin 20) (Fin 4) :=
  Function.update partial305 ⟨19, by decide⟩ (some 2)

private def cache309 : Cache :=
  step cache305 ⟨19, by decide⟩ 3
private def partial309 : Partial (Fin 20) (Fin 4) :=
  Function.update partial305 ⟨19, by decide⟩ (some 3)

private def cache310 : Cache :=
  step cache294 ⟨18, by decide⟩ 3
private def partial310 : Partial (Fin 20) (Fin 4) :=
  Function.update partial294 ⟨18, by decide⟩ (some 3)

private def cache311 : Cache :=
  step cache310 ⟨19, by decide⟩ 0
private def partial311 : Partial (Fin 20) (Fin 4) :=
  Function.update partial310 ⟨19, by decide⟩ (some 0)

private def cache312 : Cache :=
  step cache310 ⟨19, by decide⟩ 1
private def partial312 : Partial (Fin 20) (Fin 4) :=
  Function.update partial310 ⟨19, by decide⟩ (some 1)

private def cache313 : Cache :=
  step cache310 ⟨19, by decide⟩ 2
private def partial313 : Partial (Fin 20) (Fin 4) :=
  Function.update partial310 ⟨19, by decide⟩ (some 2)

private def cache314 : Cache :=
  step cache310 ⟨19, by decide⟩ 3
private def partial314 : Partial (Fin 20) (Fin 4) :=
  Function.update partial310 ⟨19, by decide⟩ (some 3)

private def cache316 : Cache :=
  step cache315 ⟨17, by decide⟩ 0
private def partial316 : Partial (Fin 20) (Fin 4) :=
  Function.update partial315 ⟨17, by decide⟩ (some 0)

private def cache317 : Cache :=
  step cache315 ⟨17, by decide⟩ 1
private def partial317 : Partial (Fin 20) (Fin 4) :=
  Function.update partial315 ⟨17, by decide⟩ (some 1)

private def cache318 : Cache :=
  step cache317 ⟨18, by decide⟩ 0
private def partial318 : Partial (Fin 20) (Fin 4) :=
  Function.update partial317 ⟨18, by decide⟩ (some 0)

private def cache319 : Cache :=
  step cache317 ⟨18, by decide⟩ 1
private def partial319 : Partial (Fin 20) (Fin 4) :=
  Function.update partial317 ⟨18, by decide⟩ (some 1)

private def cache320 : Cache :=
  step cache319 ⟨19, by decide⟩ 0
private def partial320 : Partial (Fin 20) (Fin 4) :=
  Function.update partial319 ⟨19, by decide⟩ (some 0)

private def cache321 : Cache :=
  step cache319 ⟨19, by decide⟩ 1
private def partial321 : Partial (Fin 20) (Fin 4) :=
  Function.update partial319 ⟨19, by decide⟩ (some 1)

private def cache322 : Cache :=
  step cache319 ⟨19, by decide⟩ 2
private def partial322 : Partial (Fin 20) (Fin 4) :=
  Function.update partial319 ⟨19, by decide⟩ (some 2)

private def cache323 : Cache :=
  step cache319 ⟨19, by decide⟩ 3
private def partial323 : Partial (Fin 20) (Fin 4) :=
  Function.update partial319 ⟨19, by decide⟩ (some 3)

private def cache324 : Cache :=
  step cache317 ⟨18, by decide⟩ 2
private def partial324 : Partial (Fin 20) (Fin 4) :=
  Function.update partial317 ⟨18, by decide⟩ (some 2)

private def cache325 : Cache :=
  step cache324 ⟨19, by decide⟩ 0
private def partial325 : Partial (Fin 20) (Fin 4) :=
  Function.update partial324 ⟨19, by decide⟩ (some 0)

private def cache326 : Cache :=
  step cache324 ⟨19, by decide⟩ 1
private def partial326 : Partial (Fin 20) (Fin 4) :=
  Function.update partial324 ⟨19, by decide⟩ (some 1)

private def cache327 : Cache :=
  step cache324 ⟨19, by decide⟩ 2
private def partial327 : Partial (Fin 20) (Fin 4) :=
  Function.update partial324 ⟨19, by decide⟩ (some 2)

private def cache328 : Cache :=
  step cache324 ⟨19, by decide⟩ 3
private def partial328 : Partial (Fin 20) (Fin 4) :=
  Function.update partial324 ⟨19, by decide⟩ (some 3)

private def cache329 : Cache :=
  step cache317 ⟨18, by decide⟩ 3
private def partial329 : Partial (Fin 20) (Fin 4) :=
  Function.update partial317 ⟨18, by decide⟩ (some 3)

private def cache330 : Cache :=
  step cache329 ⟨19, by decide⟩ 0
private def partial330 : Partial (Fin 20) (Fin 4) :=
  Function.update partial329 ⟨19, by decide⟩ (some 0)

private def cache331 : Cache :=
  step cache329 ⟨19, by decide⟩ 1
private def partial331 : Partial (Fin 20) (Fin 4) :=
  Function.update partial329 ⟨19, by decide⟩ (some 1)

private def cache332 : Cache :=
  step cache329 ⟨19, by decide⟩ 2
private def partial332 : Partial (Fin 20) (Fin 4) :=
  Function.update partial329 ⟨19, by decide⟩ (some 2)

private def cache333 : Cache :=
  step cache329 ⟨19, by decide⟩ 3
private def partial333 : Partial (Fin 20) (Fin 4) :=
  Function.update partial329 ⟨19, by decide⟩ (some 3)

private def cache334 : Cache :=
  step cache315 ⟨17, by decide⟩ 2
private def partial334 : Partial (Fin 20) (Fin 4) :=
  Function.update partial315 ⟨17, by decide⟩ (some 2)

private def cache335 : Cache :=
  step cache334 ⟨18, by decide⟩ 0
private def partial335 : Partial (Fin 20) (Fin 4) :=
  Function.update partial334 ⟨18, by decide⟩ (some 0)

private def cache336 : Cache :=
  step cache335 ⟨19, by decide⟩ 0
private def partial336 : Partial (Fin 20) (Fin 4) :=
  Function.update partial335 ⟨19, by decide⟩ (some 0)

private def cache337 : Cache :=
  step cache335 ⟨19, by decide⟩ 1
private def partial337 : Partial (Fin 20) (Fin 4) :=
  Function.update partial335 ⟨19, by decide⟩ (some 1)

private def cache338 : Cache :=
  step cache335 ⟨19, by decide⟩ 2
private def partial338 : Partial (Fin 20) (Fin 4) :=
  Function.update partial335 ⟨19, by decide⟩ (some 2)

private def cache339 : Cache :=
  step cache335 ⟨19, by decide⟩ 3
private def partial339 : Partial (Fin 20) (Fin 4) :=
  Function.update partial335 ⟨19, by decide⟩ (some 3)

private def cache340 : Cache :=
  step cache334 ⟨18, by decide⟩ 1
private def partial340 : Partial (Fin 20) (Fin 4) :=
  Function.update partial334 ⟨18, by decide⟩ (some 1)

private def cache341 : Cache :=
  step cache340 ⟨19, by decide⟩ 0
private def partial341 : Partial (Fin 20) (Fin 4) :=
  Function.update partial340 ⟨19, by decide⟩ (some 0)

private def cache342 : Cache :=
  step cache340 ⟨19, by decide⟩ 1
private def partial342 : Partial (Fin 20) (Fin 4) :=
  Function.update partial340 ⟨19, by decide⟩ (some 1)

private def cache343 : Cache :=
  step cache340 ⟨19, by decide⟩ 2
private def partial343 : Partial (Fin 20) (Fin 4) :=
  Function.update partial340 ⟨19, by decide⟩ (some 2)

private def cache344 : Cache :=
  step cache340 ⟨19, by decide⟩ 3
private def partial344 : Partial (Fin 20) (Fin 4) :=
  Function.update partial340 ⟨19, by decide⟩ (some 3)

private def cache345 : Cache :=
  step cache334 ⟨18, by decide⟩ 2
private def partial345 : Partial (Fin 20) (Fin 4) :=
  Function.update partial334 ⟨18, by decide⟩ (some 2)

private def cache346 : Cache :=
  step cache345 ⟨19, by decide⟩ 0
private def partial346 : Partial (Fin 20) (Fin 4) :=
  Function.update partial345 ⟨19, by decide⟩ (some 0)

private def cache347 : Cache :=
  step cache345 ⟨19, by decide⟩ 1
private def partial347 : Partial (Fin 20) (Fin 4) :=
  Function.update partial345 ⟨19, by decide⟩ (some 1)

private def cache348 : Cache :=
  step cache345 ⟨19, by decide⟩ 2
private def partial348 : Partial (Fin 20) (Fin 4) :=
  Function.update partial345 ⟨19, by decide⟩ (some 2)

private def cache349 : Cache :=
  step cache345 ⟨19, by decide⟩ 3
private def partial349 : Partial (Fin 20) (Fin 4) :=
  Function.update partial345 ⟨19, by decide⟩ (some 3)

private def cache350 : Cache :=
  step cache334 ⟨18, by decide⟩ 3
private def partial350 : Partial (Fin 20) (Fin 4) :=
  Function.update partial334 ⟨18, by decide⟩ (some 3)

private def cache351 : Cache :=
  step cache350 ⟨19, by decide⟩ 0
private def partial351 : Partial (Fin 20) (Fin 4) :=
  Function.update partial350 ⟨19, by decide⟩ (some 0)

private def cache352 : Cache :=
  step cache350 ⟨19, by decide⟩ 1
private def partial352 : Partial (Fin 20) (Fin 4) :=
  Function.update partial350 ⟨19, by decide⟩ (some 1)

private def cache353 : Cache :=
  step cache350 ⟨19, by decide⟩ 2
private def partial353 : Partial (Fin 20) (Fin 4) :=
  Function.update partial350 ⟨19, by decide⟩ (some 2)

private def cache354 : Cache :=
  step cache350 ⟨19, by decide⟩ 3
private def partial354 : Partial (Fin 20) (Fin 4) :=
  Function.update partial350 ⟨19, by decide⟩ (some 3)

private def cache355 : Cache :=
  step cache315 ⟨17, by decide⟩ 3
private def partial355 : Partial (Fin 20) (Fin 4) :=
  Function.update partial315 ⟨17, by decide⟩ (some 3)

private def cache356 : Cache :=
  step cache355 ⟨18, by decide⟩ 0
private def partial356 : Partial (Fin 20) (Fin 4) :=
  Function.update partial355 ⟨18, by decide⟩ (some 0)

private def cache357 : Cache :=
  step cache356 ⟨19, by decide⟩ 0
private def partial357 : Partial (Fin 20) (Fin 4) :=
  Function.update partial356 ⟨19, by decide⟩ (some 0)

private def cache358 : Cache :=
  step cache356 ⟨19, by decide⟩ 1
private def partial358 : Partial (Fin 20) (Fin 4) :=
  Function.update partial356 ⟨19, by decide⟩ (some 1)

private def cache359 : Cache :=
  step cache356 ⟨19, by decide⟩ 2
private def partial359 : Partial (Fin 20) (Fin 4) :=
  Function.update partial356 ⟨19, by decide⟩ (some 2)

private def cache360 : Cache :=
  step cache356 ⟨19, by decide⟩ 3
private def partial360 : Partial (Fin 20) (Fin 4) :=
  Function.update partial356 ⟨19, by decide⟩ (some 3)

private def cache361 : Cache :=
  step cache355 ⟨18, by decide⟩ 1
private def partial361 : Partial (Fin 20) (Fin 4) :=
  Function.update partial355 ⟨18, by decide⟩ (some 1)

private def cache362 : Cache :=
  step cache361 ⟨19, by decide⟩ 0
private def partial362 : Partial (Fin 20) (Fin 4) :=
  Function.update partial361 ⟨19, by decide⟩ (some 0)

private def cache363 : Cache :=
  step cache361 ⟨19, by decide⟩ 1
private def partial363 : Partial (Fin 20) (Fin 4) :=
  Function.update partial361 ⟨19, by decide⟩ (some 1)

private def cache364 : Cache :=
  step cache361 ⟨19, by decide⟩ 2
private def partial364 : Partial (Fin 20) (Fin 4) :=
  Function.update partial361 ⟨19, by decide⟩ (some 2)

private def cache365 : Cache :=
  step cache361 ⟨19, by decide⟩ 3
private def partial365 : Partial (Fin 20) (Fin 4) :=
  Function.update partial361 ⟨19, by decide⟩ (some 3)

private def cache366 : Cache :=
  step cache355 ⟨18, by decide⟩ 2
private def partial366 : Partial (Fin 20) (Fin 4) :=
  Function.update partial355 ⟨18, by decide⟩ (some 2)

private def cache367 : Cache :=
  step cache366 ⟨19, by decide⟩ 0
private def partial367 : Partial (Fin 20) (Fin 4) :=
  Function.update partial366 ⟨19, by decide⟩ (some 0)

private def cache368 : Cache :=
  step cache366 ⟨19, by decide⟩ 1
private def partial368 : Partial (Fin 20) (Fin 4) :=
  Function.update partial366 ⟨19, by decide⟩ (some 1)

private def cache369 : Cache :=
  step cache366 ⟨19, by decide⟩ 2
private def partial369 : Partial (Fin 20) (Fin 4) :=
  Function.update partial366 ⟨19, by decide⟩ (some 2)

private def cache370 : Cache :=
  step cache366 ⟨19, by decide⟩ 3
private def partial370 : Partial (Fin 20) (Fin 4) :=
  Function.update partial366 ⟨19, by decide⟩ (some 3)

private def cache371 : Cache :=
  step cache355 ⟨18, by decide⟩ 3
private def partial371 : Partial (Fin 20) (Fin 4) :=
  Function.update partial355 ⟨18, by decide⟩ (some 3)

private def cache372 : Cache :=
  step cache371 ⟨19, by decide⟩ 0
private def partial372 : Partial (Fin 20) (Fin 4) :=
  Function.update partial371 ⟨19, by decide⟩ (some 0)

private def cache373 : Cache :=
  step cache371 ⟨19, by decide⟩ 1
private def partial373 : Partial (Fin 20) (Fin 4) :=
  Function.update partial371 ⟨19, by decide⟩ (some 1)

private def cache374 : Cache :=
  step cache371 ⟨19, by decide⟩ 2
private def partial374 : Partial (Fin 20) (Fin 4) :=
  Function.update partial371 ⟨19, by decide⟩ (some 2)

private def cache375 : Cache :=
  step cache371 ⟨19, by decide⟩ 3
private def partial375 : Partial (Fin 20) (Fin 4) :=
  Function.update partial371 ⟨19, by decide⟩ (some 3)

private def cache382 : Cache :=
  step cache381 ⟨17, by decide⟩ 0
private def partial382 : Partial (Fin 20) (Fin 4) :=
  Function.update partial381 ⟨17, by decide⟩ (some 0)

private def cache383 : Cache :=
  step cache381 ⟨17, by decide⟩ 1
private def partial383 : Partial (Fin 20) (Fin 4) :=
  Function.update partial381 ⟨17, by decide⟩ (some 1)

private def cache384 : Cache :=
  step cache383 ⟨18, by decide⟩ 0
private def partial384 : Partial (Fin 20) (Fin 4) :=
  Function.update partial383 ⟨18, by decide⟩ (some 0)

private def cache385 : Cache :=
  step cache383 ⟨18, by decide⟩ 1
private def partial385 : Partial (Fin 20) (Fin 4) :=
  Function.update partial383 ⟨18, by decide⟩ (some 1)

private def cache386 : Cache :=
  step cache383 ⟨18, by decide⟩ 2
private def partial386 : Partial (Fin 20) (Fin 4) :=
  Function.update partial383 ⟨18, by decide⟩ (some 2)

private def cache387 : Cache :=
  step cache386 ⟨19, by decide⟩ 0
private def partial387 : Partial (Fin 20) (Fin 4) :=
  Function.update partial386 ⟨19, by decide⟩ (some 0)

private def cache388 : Cache :=
  step cache386 ⟨19, by decide⟩ 1
private def partial388 : Partial (Fin 20) (Fin 4) :=
  Function.update partial386 ⟨19, by decide⟩ (some 1)

private def cache389 : Cache :=
  step cache386 ⟨19, by decide⟩ 2
private def partial389 : Partial (Fin 20) (Fin 4) :=
  Function.update partial386 ⟨19, by decide⟩ (some 2)

private def cache390 : Cache :=
  step cache386 ⟨19, by decide⟩ 3
private def partial390 : Partial (Fin 20) (Fin 4) :=
  Function.update partial386 ⟨19, by decide⟩ (some 3)

private def cache391 : Cache :=
  step cache383 ⟨18, by decide⟩ 3
private def partial391 : Partial (Fin 20) (Fin 4) :=
  Function.update partial383 ⟨18, by decide⟩ (some 3)

private def cache392 : Cache :=
  step cache381 ⟨17, by decide⟩ 2
private def partial392 : Partial (Fin 20) (Fin 4) :=
  Function.update partial381 ⟨17, by decide⟩ (some 2)

private def cache393 : Cache :=
  step cache392 ⟨18, by decide⟩ 0
private def partial393 : Partial (Fin 20) (Fin 4) :=
  Function.update partial392 ⟨18, by decide⟩ (some 0)

private def cache394 : Cache :=
  step cache392 ⟨18, by decide⟩ 1
private def partial394 : Partial (Fin 20) (Fin 4) :=
  Function.update partial392 ⟨18, by decide⟩ (some 1)

private def cache395 : Cache :=
  step cache392 ⟨18, by decide⟩ 2
private def partial395 : Partial (Fin 20) (Fin 4) :=
  Function.update partial392 ⟨18, by decide⟩ (some 2)

private def cache396 : Cache :=
  step cache392 ⟨18, by decide⟩ 3
private def partial396 : Partial (Fin 20) (Fin 4) :=
  Function.update partial392 ⟨18, by decide⟩ (some 3)

private def cache397 : Cache :=
  step cache381 ⟨17, by decide⟩ 3
private def partial397 : Partial (Fin 20) (Fin 4) :=
  Function.update partial381 ⟨17, by decide⟩ (some 3)

private def cache398 : Cache :=
  step cache397 ⟨18, by decide⟩ 0
private def partial398 : Partial (Fin 20) (Fin 4) :=
  Function.update partial397 ⟨18, by decide⟩ (some 0)

private def cache399 : Cache :=
  step cache397 ⟨18, by decide⟩ 1
private def partial399 : Partial (Fin 20) (Fin 4) :=
  Function.update partial397 ⟨18, by decide⟩ (some 1)

private def cache400 : Cache :=
  step cache397 ⟨18, by decide⟩ 2
private def partial400 : Partial (Fin 20) (Fin 4) :=
  Function.update partial397 ⟨18, by decide⟩ (some 2)

private def cache401 : Cache :=
  step cache400 ⟨19, by decide⟩ 0
private def partial401 : Partial (Fin 20) (Fin 4) :=
  Function.update partial400 ⟨19, by decide⟩ (some 0)

private def cache402 : Cache :=
  step cache400 ⟨19, by decide⟩ 1
private def partial402 : Partial (Fin 20) (Fin 4) :=
  Function.update partial400 ⟨19, by decide⟩ (some 1)

private def cache403 : Cache :=
  step cache400 ⟨19, by decide⟩ 2
private def partial403 : Partial (Fin 20) (Fin 4) :=
  Function.update partial400 ⟨19, by decide⟩ (some 2)

private def cache404 : Cache :=
  step cache400 ⟨19, by decide⟩ 3
private def partial404 : Partial (Fin 20) (Fin 4) :=
  Function.update partial400 ⟨19, by decide⟩ (some 3)

private def cache405 : Cache :=
  step cache397 ⟨18, by decide⟩ 3
private def partial405 : Partial (Fin 20) (Fin 4) :=
  Function.update partial397 ⟨18, by decide⟩ (some 3)

private def cache407 : Cache :=
  step cache406 ⟨17, by decide⟩ 0
private def partial407 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 0)

private def cache408 : Cache :=
  step cache406 ⟨17, by decide⟩ 1
private def partial408 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 1)

private def cache409 : Cache :=
  step cache408 ⟨18, by decide⟩ 0
private def partial409 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 0)

private def cache410 : Cache :=
  step cache408 ⟨18, by decide⟩ 1
private def partial410 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 1)

private def cache411 : Cache :=
  step cache410 ⟨19, by decide⟩ 0
private def partial411 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 0)

private def cache412 : Cache :=
  step cache410 ⟨19, by decide⟩ 1
private def partial412 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 1)

private def cache413 : Cache :=
  step cache410 ⟨19, by decide⟩ 2
private def partial413 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 2)

private def cache414 : Cache :=
  step cache410 ⟨19, by decide⟩ 3
private def partial414 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 3)

private def cache415 : Cache :=
  step cache408 ⟨18, by decide⟩ 2
private def partial415 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 2)

private def cache416 : Cache :=
  step cache415 ⟨19, by decide⟩ 0
private def partial416 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 0)

private def cache417 : Cache :=
  step cache415 ⟨19, by decide⟩ 1
private def partial417 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 1)

private def cache418 : Cache :=
  step cache415 ⟨19, by decide⟩ 2
private def partial418 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 2)

private def cache419 : Cache :=
  step cache415 ⟨19, by decide⟩ 3
private def partial419 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 3)

private def cache420 : Cache :=
  step cache408 ⟨18, by decide⟩ 3
private def partial420 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 3)

private def cache421 : Cache :=
  step cache420 ⟨19, by decide⟩ 0
private def partial421 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 0)

private def cache422 : Cache :=
  step cache420 ⟨19, by decide⟩ 1
private def partial422 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 1)

private def cache423 : Cache :=
  step cache420 ⟨19, by decide⟩ 2
private def partial423 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 2)

private def cache424 : Cache :=
  step cache420 ⟨19, by decide⟩ 3
private def partial424 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 3)

private def cache425 : Cache :=
  step cache406 ⟨17, by decide⟩ 2
private def partial425 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 2)

private def cache426 : Cache :=
  step cache425 ⟨18, by decide⟩ 0
private def partial426 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 0)

private def cache427 : Cache :=
  step cache425 ⟨18, by decide⟩ 1
private def partial427 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 1)

private def cache428 : Cache :=
  step cache425 ⟨18, by decide⟩ 2
private def partial428 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 2)

private def cache429 : Cache :=
  step cache425 ⟨18, by decide⟩ 3
private def partial429 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 3)

private def cache430 : Cache :=
  step cache406 ⟨17, by decide⟩ 3
private def partial430 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 3)

private def cache431 : Cache :=
  step cache430 ⟨18, by decide⟩ 0
private def partial431 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 0)

private def cache432 : Cache :=
  step cache430 ⟨18, by decide⟩ 1
private def partial432 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 1)

private def cache433 : Cache :=
  step cache432 ⟨19, by decide⟩ 0
private def partial433 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 0)

private def cache434 : Cache :=
  step cache432 ⟨19, by decide⟩ 1
private def partial434 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 1)

private def cache435 : Cache :=
  step cache432 ⟨19, by decide⟩ 2
private def partial435 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 2)

private def cache436 : Cache :=
  step cache432 ⟨19, by decide⟩ 3
private def partial436 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 3)

private def cache437 : Cache :=
  step cache430 ⟨18, by decide⟩ 2
private def partial437 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 2)

private def cache438 : Cache :=
  step cache437 ⟨19, by decide⟩ 0
private def partial438 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 0)

private def cache439 : Cache :=
  step cache437 ⟨19, by decide⟩ 1
private def partial439 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 1)

private def cache440 : Cache :=
  step cache437 ⟨19, by decide⟩ 2
private def partial440 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 2)

private def cache441 : Cache :=
  step cache437 ⟨19, by decide⟩ 3
private def partial441 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 3)

private def cache442 : Cache :=
  step cache430 ⟨18, by decide⟩ 3
private def partial442 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 3)

private def cache443 : Cache :=
  step cache442 ⟨19, by decide⟩ 0
private def partial443 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 0)

private def cache444 : Cache :=
  step cache442 ⟨19, by decide⟩ 1
private def partial444 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 1)

private def cache445 : Cache :=
  step cache442 ⟨19, by decide⟩ 2
private def partial445 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 2)

private def cache446 : Cache :=
  step cache442 ⟨19, by decide⟩ 3
private def partial446 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 3)

private theorem receipt446 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨446, by decide⟩ cache446 partial446 = true := by
  decide +kernel

private theorem receipt445 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨445, by decide⟩ cache445 partial445 = true := by
  decide +kernel

private theorem receipt444 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨444, by decide⟩ cache444 partial444 = true := by
  decide +kernel

private theorem receipt443 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨443, by decide⟩ cache443 partial443 = true := by
  decide +kernel

private theorem receipt442 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨442, by decide⟩ cache442 partial442 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![443,444,445,446])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(981003337742195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt443
  · exact receipt444
  · exact receipt445
  · exact receipt446

private theorem receipt441 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨441, by decide⟩ cache441 partial441 = true := by
  decide +kernel

private theorem receipt440 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨440, by decide⟩ cache440 partial440 = true := by
  decide +kernel

private theorem receipt439 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨439, by decide⟩ cache439 partial439 = true := by
  decide +kernel

private theorem receipt438 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨438, by decide⟩ cache438 partial438 = true := by
  decide +kernel

private theorem receipt437 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨437, by decide⟩ cache437 partial437 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![438,439,440,441])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(970005536454355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt438
  · exact receipt439
  · exact receipt440
  · exact receipt441

private theorem receipt436 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨436, by decide⟩ cache436 partial436 = true := by
  decide +kernel

private theorem receipt435 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨435, by decide⟩ cache435 partial435 = true := by
  decide +kernel

private theorem receipt434 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨434, by decide⟩ cache434 partial434 = true := by
  decide +kernel

private theorem receipt433 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨433, by decide⟩ cache433 partial433 = true := by
  decide +kernel

private theorem receipt432 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨432, by decide⟩ cache432 partial432 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![433,434,435,436])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(959007735166515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt433
  · exact receipt434
  · exact receipt435
  · exact receipt436

private theorem receipt431 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨431, by decide⟩ cache431 partial431 = true := by
  decide +kernel

private theorem receipt430 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨430, by decide⟩ cache430 partial430 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![431,432,437,442])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(972202948179442 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt431
  · exact receipt432
  · exact receipt437
  · exact receipt442

private theorem receipt429 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨429, by decide⟩ cache429 partial429 = true := by
  decide +kernel

private theorem receipt428 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨428, by decide⟩ cache428 partial428 = true := by
  decide +kernel

private theorem receipt427 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨427, by decide⟩ cache427 partial427 = true := by
  decide +kernel

private theorem receipt426 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨426, by decide⟩ cache426 partial426 = true := by
  decide +kernel

private theorem receipt425 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨425, by decide⟩ cache425 partial425 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![426,427,428,429])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(943610813363538 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt426
  · exact receipt427
  · exact receipt428
  · exact receipt429

private theorem receipt424 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨424, by decide⟩ cache424 partial424 = true := by
  decide +kernel

private theorem receipt423 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨423, by decide⟩ cache423 partial423 = true := by
  decide +kernel

private theorem receipt422 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨422, by decide⟩ cache422 partial422 = true := by
  decide +kernel

private theorem receipt421 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨421, by decide⟩ cache421 partial421 = true := by
  decide +kernel

private theorem receipt420 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨420, by decide⟩ cache420 partial420 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![421,422,423,424])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(932613012075699 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt421
  · exact receipt422
  · exact receipt423
  · exact receipt424

private theorem receipt419 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨419, by decide⟩ cache419 partial419 = true := by
  decide +kernel

private theorem receipt418 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨418, by decide⟩ cache418 partial418 = true := by
  decide +kernel

private theorem receipt417 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨417, by decide⟩ cache417 partial417 = true := by
  decide +kernel

private theorem receipt416 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨416, by decide⟩ cache416 partial416 = true := by
  decide +kernel

private theorem receipt415 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨415, by decide⟩ cache415 partial415 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![416,417,418,419])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(921615210787859 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt416
  · exact receipt417
  · exact receipt418
  · exact receipt419

private theorem receipt414 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨414, by decide⟩ cache414 partial414 = true := by
  decide +kernel

private theorem receipt413 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨413, by decide⟩ cache413 partial413 = true := by
  decide +kernel

private theorem receipt412 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨412, by decide⟩ cache412 partial412 = true := by
  decide +kernel

private theorem receipt411 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨411, by decide⟩ cache411 partial411 = true := by
  decide +kernel

private theorem receipt410 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨410, by decide⟩ cache410 partial410 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![411,412,413,414])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(910617409500019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt411
  · exact receipt412
  · exact receipt413
  · exact receipt414

private theorem receipt409 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨409, by decide⟩ cache409 partial409 = true := by
  decide +kernel

private theorem receipt408 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨408, by decide⟩ cache408 partial408 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![409,410,415,420])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(923812622512946 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt409
  · exact receipt410
  · exact receipt415
  · exact receipt420

private theorem receipt407 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨407, by decide⟩ cache407 partial407 = true := by
  decide +kernel

theorem receipt406 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨406, by decide⟩ cache406 partial406 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![407,408,425,430])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(945808223515377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt407
  · exact receipt408
  · exact receipt425
  · exact receipt430

private theorem receipt405 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨405, by decide⟩ cache405 partial405 = true := by
  decide +kernel

private theorem receipt404 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨404, by decide⟩ cache404 partial404 = true := by
  decide +kernel

private theorem receipt403 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨403, by decide⟩ cache403 partial403 = true := by
  decide +kernel

private theorem receipt402 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨402, by decide⟩ cache402 partial402 = true := by
  decide +kernel

private theorem receipt401 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨401, by decide⟩ cache401 partial401 = true := by
  decide +kernel

private theorem receipt400 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨400, by decide⟩ cache400 partial400 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![401,402,403,404])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(888621806924339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt401
  · exact receipt402
  · exact receipt403
  · exact receipt404

private theorem receipt399 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨399, by decide⟩ cache399 partial399 = true := by
  decide +kernel

private theorem receipt398 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨398, by decide⟩ cache398 partial398 = true := by
  decide +kernel

private theorem receipt397 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨397, by decide⟩ cache397 partial397 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![398,399,400,405])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(890819219173842 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt398
  · exact receipt399
  · exact receipt400
  · exact receipt405

private theorem receipt396 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨396, by decide⟩ cache396 partial396 = true := by
  decide +kernel

private theorem receipt395 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨395, by decide⟩ cache395 partial395 = true := by
  decide +kernel

private theorem receipt394 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨394, by decide⟩ cache394 partial394 = true := by
  decide +kernel

private theorem receipt393 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨393, by decide⟩ cache393 partial393 = true := by
  decide +kernel

private theorem receipt392 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨392, by decide⟩ cache392 partial392 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![393,394,395,396])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(871025324863794 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt393
  · exact receipt394
  · exact receipt395
  · exact receipt396

private theorem receipt391 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨391, by decide⟩ cache391 partial391 = true := by
  decide +kernel

private theorem receipt390 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨390, by decide⟩ cache390 partial390 = true := by
  decide +kernel

private theorem receipt389 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨389, by decide⟩ cache389 partial389 = true := by
  decide +kernel

private theorem receipt388 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨388, by decide⟩ cache388 partial388 = true := by
  decide +kernel

private theorem receipt387 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨387, by decide⟩ cache387 partial387 = true := by
  decide +kernel

private theorem receipt386 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨386, by decide⟩ cache386 partial386 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![387,388,389,390])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(857827963318387 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt387
  · exact receipt388
  · exact receipt389
  · exact receipt390

private theorem receipt385 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨385, by decide⟩ cache385 partial385 = true := by
  decide +kernel

private theorem receipt384 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨384, by decide⟩ cache384 partial384 = true := by
  decide +kernel

private theorem receipt383 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨383, by decide⟩ cache383 partial383 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![384,385,386,391])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(860025375567890 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt384
  · exact receipt385
  · exact receipt386
  · exact receipt391

private theorem receipt382 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨382, by decide⟩ cache382 partial382 = true := by
  decide +kernel

theorem receipt381 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨381, by decide⟩ cache381 partial381 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![382,383,392,397])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(873222736064465 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt382
  · exact receipt383
  · exact receipt392
  · exact receipt397

theorem receipt380 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨380, by decide⟩ cache380 partial380 = true := by
  decide +kernel

theorem receipt379 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨379, by decide⟩ cache379 partial379 = true := by
  decide +kernel

theorem receipt377 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨377, by decide⟩ cache377 partial377 = true := by
  decide +kernel

private theorem receipt375 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨375, by decide⟩ cache375 partial375 = true := by
  decide +kernel

private theorem receipt374 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨374, by decide⟩ cache374 partial374 = true := by
  decide +kernel

private theorem receipt373 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨373, by decide⟩ cache373 partial373 = true := by
  decide +kernel

private theorem receipt372 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨372, by decide⟩ cache372 partial372 = true := by
  decide +kernel

private theorem receipt371 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨371, by decide⟩ cache371 partial371 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![372,373,374,375])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(824834559454867 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt372
  · exact receipt373
  · exact receipt374
  · exact receipt375

private theorem receipt370 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨370, by decide⟩ cache370 partial370 = true := by
  decide +kernel

private theorem receipt369 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨369, by decide⟩ cache369 partial369 = true := by
  decide +kernel

private theorem receipt368 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨368, by decide⟩ cache368 partial368 = true := by
  decide +kernel

private theorem receipt367 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨367, by decide⟩ cache367 partial367 = true := by
  decide +kernel

private theorem receipt366 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨366, by decide⟩ cache366 partial366 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![367,368,369,370])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(813836758167027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt367
  · exact receipt368
  · exact receipt369
  · exact receipt370

private theorem receipt365 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨365, by decide⟩ cache365 partial365 = true := by
  decide +kernel

private theorem receipt364 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨364, by decide⟩ cache364 partial364 = true := by
  decide +kernel

private theorem receipt363 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨363, by decide⟩ cache363 partial363 = true := by
  decide +kernel

private theorem receipt362 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨362, by decide⟩ cache362 partial362 = true := by
  decide +kernel

private theorem receipt361 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨361, by decide⟩ cache361 partial361 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![362,363,364,365])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(802838956879187 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt362
  · exact receipt363
  · exact receipt364
  · exact receipt365

private theorem receipt360 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨360, by decide⟩ cache360 partial360 = true := by
  decide +kernel

private theorem receipt359 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨359, by decide⟩ cache359 partial359 = true := by
  decide +kernel

private theorem receipt358 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨358, by decide⟩ cache358 partial358 = true := by
  decide +kernel

private theorem receipt357 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨357, by decide⟩ cache357 partial357 = true := by
  decide +kernel

private theorem receipt356 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨356, by decide⟩ cache356 partial356 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![357,358,359,360])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(791841155591347 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt357
  · exact receipt358
  · exact receipt359
  · exact receipt360

private theorem receipt355 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨355, by decide⟩ cache355 partial355 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![356,361,366,371])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(816034169891986 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt356
  · exact receipt361
  · exact receipt366
  · exact receipt371

private theorem receipt354 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨354, by decide⟩ cache354 partial354 = true := by
  decide +kernel

private theorem receipt353 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨353, by decide⟩ cache353 partial353 = true := by
  decide +kernel

private theorem receipt352 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨352, by decide⟩ cache352 partial352 = true := by
  decide +kernel

private theorem receipt351 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨351, by decide⟩ cache351 partial351 = true := by
  decide +kernel

private theorem receipt350 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨350, by decide⟩ cache350 partial350 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![351,352,353,354])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(778643794045939 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt351
  · exact receipt352
  · exact receipt353
  · exact receipt354

private theorem receipt349 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨349, by decide⟩ cache349 partial349 = true := by
  decide +kernel

private theorem receipt348 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨348, by decide⟩ cache348 partial348 = true := by
  decide +kernel

private theorem receipt347 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨347, by decide⟩ cache347 partial347 = true := by
  decide +kernel

private theorem receipt346 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨346, by decide⟩ cache346 partial346 = true := by
  decide +kernel

private theorem receipt345 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨345, by decide⟩ cache345 partial345 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![346,347,348,349])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(767645992758099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt346
  · exact receipt347
  · exact receipt348
  · exact receipt349

private theorem receipt344 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨344, by decide⟩ cache344 partial344 = true := by
  decide +kernel

private theorem receipt343 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨343, by decide⟩ cache343 partial343 = true := by
  decide +kernel

private theorem receipt342 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨342, by decide⟩ cache342 partial342 = true := by
  decide +kernel

private theorem receipt341 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨341, by decide⟩ cache341 partial341 = true := by
  decide +kernel

private theorem receipt340 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨340, by decide⟩ cache340 partial340 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![341,342,343,344])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(756648191470259 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt341
  · exact receipt342
  · exact receipt343
  · exact receipt344

private theorem receipt339 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨339, by decide⟩ cache339 partial339 = true := by
  decide +kernel

private theorem receipt338 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨338, by decide⟩ cache338 partial338 = true := by
  decide +kernel

private theorem receipt337 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨337, by decide⟩ cache337 partial337 = true := by
  decide +kernel

private theorem receipt336 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨336, by decide⟩ cache336 partial336 = true := by
  decide +kernel

private theorem receipt335 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨335, by decide⟩ cache335 partial335 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![336,337,338,339])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(745650390182419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt336
  · exact receipt337
  · exact receipt338
  · exact receipt339

private theorem receipt334 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨334, by decide⟩ cache334 partial334 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![335,340,345,350])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(769843404483058 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt335
  · exact receipt340
  · exact receipt345
  · exact receipt350

private theorem receipt333 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨333, by decide⟩ cache333 partial333 = true := by
  decide +kernel

private theorem receipt332 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨332, by decide⟩ cache332 partial332 = true := by
  decide +kernel

private theorem receipt331 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨331, by decide⟩ cache331 partial331 = true := by
  decide +kernel

private theorem receipt330 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨330, by decide⟩ cache330 partial330 = true := by
  decide +kernel

private theorem receipt329 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨329, by decide⟩ cache329 partial329 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![330,331,332,333])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(732453028637011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt330
  · exact receipt331
  · exact receipt332
  · exact receipt333

private theorem receipt328 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨328, by decide⟩ cache328 partial328 = true := by
  decide +kernel

private theorem receipt327 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨327, by decide⟩ cache327 partial327 = true := by
  decide +kernel

private theorem receipt326 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨326, by decide⟩ cache326 partial326 = true := by
  decide +kernel

private theorem receipt325 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨325, by decide⟩ cache325 partial325 = true := by
  decide +kernel

private theorem receipt324 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨324, by decide⟩ cache324 partial324 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![325,326,327,328])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(721455227349171 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt325
  · exact receipt326
  · exact receipt327
  · exact receipt328

private theorem receipt323 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨323, by decide⟩ cache323 partial323 = true := by
  decide +kernel

private theorem receipt322 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨322, by decide⟩ cache322 partial322 = true := by
  decide +kernel

private theorem receipt321 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨321, by decide⟩ cache321 partial321 = true := by
  decide +kernel

private theorem receipt320 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨320, by decide⟩ cache320 partial320 = true := by
  decide +kernel

private theorem receipt319 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨319, by decide⟩ cache319 partial319 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![320,321,322,323])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(710457426061331 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt320
  · exact receipt321
  · exact receipt322
  · exact receipt323

private theorem receipt318 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨318, by decide⟩ cache318 partial318 = true := by
  decide +kernel

private theorem receipt317 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨317, by decide⟩ cache317 partial317 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![318,319,324,329])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(723652639074258 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt318
  · exact receipt319
  · exact receipt324
  · exact receipt329

private theorem receipt316 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨316, by decide⟩ cache316 partial316 = true := by
  decide +kernel

theorem receipt315 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨315, by decide⟩ cache315 partial315 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![316,317,334,355])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(780832612165521 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt316
  · exact receipt317
  · exact receipt334
  · exact receipt355

private theorem receipt314 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨314, by decide⟩ cache314 partial314 = true := by
  decide +kernel

private theorem receipt313 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨313, by decide⟩ cache313 partial313 = true := by
  decide +kernel

private theorem receipt312 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨312, by decide⟩ cache312 partial312 = true := by
  decide +kernel

private theorem receipt311 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨311, by decide⟩ cache311 partial311 = true := by
  decide +kernel

private theorem receipt310 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨310, by decide⟩ cache310 partial310 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![311,312,313,314])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(690661383743219 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt311
  · exact receipt312
  · exact receipt313
  · exact receipt314

private theorem receipt309 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨309, by decide⟩ cache309 partial309 = true := by
  decide +kernel

private theorem receipt308 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨308, by decide⟩ cache308 partial308 = true := by
  decide +kernel

private theorem receipt307 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨307, by decide⟩ cache307 partial307 = true := by
  decide +kernel

private theorem receipt306 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨306, by decide⟩ cache306 partial306 = true := by
  decide +kernel

private theorem receipt305 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨305, by decide⟩ cache305 partial305 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![306,307,308,309])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(679663582455379 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt306
  · exact receipt307
  · exact receipt308
  · exact receipt309

private theorem receipt304 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨304, by decide⟩ cache304 partial304 = true := by
  decide +kernel

private theorem receipt303 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨303, by decide⟩ cache303 partial303 = true := by
  decide +kernel

private theorem receipt302 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨302, by decide⟩ cache302 partial302 = true := by
  decide +kernel

private theorem receipt301 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨301, by decide⟩ cache301 partial301 = true := by
  decide +kernel

private theorem receipt300 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨300, by decide⟩ cache300 partial300 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![301,302,303,304])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(668665781167539 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt301
  · exact receipt302
  · exact receipt303
  · exact receipt304

private theorem receipt299 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨299, by decide⟩ cache299 partial299 = true := by
  decide +kernel

private theorem receipt298 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨298, by decide⟩ cache298 partial298 = true := by
  decide +kernel

private theorem receipt297 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨297, by decide⟩ cache297 partial297 = true := by
  decide +kernel

private theorem receipt296 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨296, by decide⟩ cache296 partial296 = true := by
  decide +kernel

private theorem receipt295 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨295, by decide⟩ cache295 partial295 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![296,297,298,299])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(657667979879699 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt296
  · exact receipt297
  · exact receipt298
  · exact receipt299

private theorem receipt294 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨294, by decide⟩ cache294 partial294 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![295,300,305,310])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(681860994180338 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt295
  · exact receipt300
  · exact receipt305
  · exact receipt310

private theorem receipt293 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨293, by decide⟩ cache293 partial293 = true := by
  decide +kernel

private theorem receipt292 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨292, by decide⟩ cache292 partial292 = true := by
  decide +kernel

private theorem receipt291 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨291, by decide⟩ cache291 partial291 = true := by
  decide +kernel

private theorem receipt290 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨290, by decide⟩ cache290 partial290 = true := by
  decide +kernel

private theorem receipt289 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨289, by decide⟩ cache289 partial289 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![290,291,292,293])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(644470618334291 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt290
  · exact receipt291
  · exact receipt292
  · exact receipt293

private theorem receipt288 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨288, by decide⟩ cache288 partial288 = true := by
  decide +kernel

private theorem receipt287 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨287, by decide⟩ cache287 partial287 = true := by
  decide +kernel

private theorem receipt286 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨286, by decide⟩ cache286 partial286 = true := by
  decide +kernel

private theorem receipt285 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨285, by decide⟩ cache285 partial285 = true := by
  decide +kernel

private theorem receipt284 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨284, by decide⟩ cache284 partial284 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![285,286,287,288])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(633472817046451 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt285
  · exact receipt286
  · exact receipt287
  · exact receipt288

private theorem receipt283 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨283, by decide⟩ cache283 partial283 = true := by
  decide +kernel

private theorem receipt282 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨282, by decide⟩ cache282 partial282 = true := by
  decide +kernel

private theorem receipt281 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨281, by decide⟩ cache281 partial281 = true := by
  decide +kernel

private theorem receipt280 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨280, by decide⟩ cache280 partial280 = true := by
  decide +kernel

private theorem receipt279 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨279, by decide⟩ cache279 partial279 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![280,281,282,283])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(622475015758611 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt280
  · exact receipt281
  · exact receipt282
  · exact receipt283

private theorem receipt278 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨278, by decide⟩ cache278 partial278 = true := by
  decide +kernel

private theorem receipt277 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨277, by decide⟩ cache277 partial277 = true := by
  decide +kernel

private theorem receipt276 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨276, by decide⟩ cache276 partial276 = true := by
  decide +kernel

private theorem receipt275 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨275, by decide⟩ cache275 partial275 = true := by
  decide +kernel

private theorem receipt274 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨274, by decide⟩ cache274 partial274 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![275,276,277,278])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(611477214470771 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt275
  · exact receipt276
  · exact receipt277
  · exact receipt278

private theorem receipt273 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨273, by decide⟩ cache273 partial273 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![274,279,284,289])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(635670228771410 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt274
  · exact receipt279
  · exact receipt284
  · exact receipt289

private theorem receipt272 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨272, by decide⟩ cache272 partial272 = true := by
  decide +kernel

private theorem receipt271 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨271, by decide⟩ cache271 partial271 = true := by
  decide +kernel

private theorem receipt270 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨270, by decide⟩ cache270 partial270 = true := by
  decide +kernel

private theorem receipt269 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨269, by decide⟩ cache269 partial269 = true := by
  decide +kernel

private theorem receipt268 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨268, by decide⟩ cache268 partial268 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![269,270,271,272])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(598279852925363 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt269
  · exact receipt270
  · exact receipt271
  · exact receipt272

private theorem receipt267 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨267, by decide⟩ cache267 partial267 = true := by
  decide +kernel

private theorem receipt266 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨266, by decide⟩ cache266 partial266 = true := by
  decide +kernel

private theorem receipt265 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨265, by decide⟩ cache265 partial265 = true := by
  decide +kernel

private theorem receipt264 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨264, by decide⟩ cache264 partial264 = true := by
  decide +kernel

private theorem receipt263 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨263, by decide⟩ cache263 partial263 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![264,265,266,267])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(587282051637523 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt264
  · exact receipt265
  · exact receipt266
  · exact receipt267

private theorem receipt262 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨262, by decide⟩ cache262 partial262 = true := by
  decide +kernel

private theorem receipt261 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨261, by decide⟩ cache261 partial261 = true := by
  decide +kernel

private theorem receipt260 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨260, by decide⟩ cache260 partial260 = true := by
  decide +kernel

private theorem receipt259 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨259, by decide⟩ cache259 partial259 = true := by
  decide +kernel

private theorem receipt258 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨258, by decide⟩ cache258 partial258 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![259,260,261,262])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(576284250349683 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt259
  · exact receipt260
  · exact receipt261
  · exact receipt262

private theorem receipt257 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨257, by decide⟩ cache257 partial257 = true := by
  decide +kernel

private theorem receipt256 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨256, by decide⟩ cache256 partial256 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![257,258,263,268])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(589479463362610 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt257
  · exact receipt258
  · exact receipt263
  · exact receipt268

#print axioms receipt256

private theorem receipt255 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨255, by decide⟩ cache255 partial255 = true := by
  decide +kernel

theorem receipt254 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨254, by decide⟩ cache254 partial254 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![255,256,273,294])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(646659436453873 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt255
  · exact receipt256
  · exact receipt273
  · exact receipt294

theorem receipt253 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨253, by decide⟩ cache253 partial253 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
