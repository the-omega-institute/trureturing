/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_335,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_336,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_397,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_398,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_399,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart05.traversal_402
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart03
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart04
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
theorem traversal_335 (fuel : Nat) (hf : 335 < fuel) :
    walk nodes fuel 335 = List.range' 217 119 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 335).rule = .split 1 (15/8) 227 334 := by rfl
      simp only [walk, hr]
      rw [traversal_227 f (by omega), traversal_334 f (by omega)]
      change (List.range' 217 11 ++ List.range' (217+11) 107) ++
        [217+(11+107)] = List.range' 217 ((11+107)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 11+107)).symm

theorem traversal_336 (fuel : Nat) (hf : 336 < fuel) :
    walk nodes fuel 336 = List.range' 336 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 336).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_337 (fuel : Nat) (hf : 337 < fuel) :
    walk nodes fuel 337 = List.range' 337 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 337).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_338 (fuel : Nat) (hf : 338 < fuel) :
    walk nodes fuel 338 = List.range' 338 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 338).rule = .bound .leftEnd 1 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_339 (fuel : Nat) (hf : 339 < fuel) :
    walk nodes fuel 339 = List.range' 339 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 339).rule = .bound .leftEnd 8 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_340 (fuel : Nat) (hf : 340 < fuel) :
    walk nodes fuel 340 = List.range' 340 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 340).rule = .bound .leftEnd 8 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_341 (fuel : Nat) (hf : 341 < fuel) :
    walk nodes fuel 341 = List.range' 341 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 341).rule = .bound .leftEnd 8 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_342 (fuel : Nat) (hf : 342 < fuel) :
    walk nodes fuel 342 = List.range' 342 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 342).rule = .bound .leftEnd 1 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_343 (fuel : Nat) (hf : 343 < fuel) :
    walk nodes fuel 343 = List.range' 343 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 343).rule = .bound .leftEnd 2 (55/96) (457533/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_344 (fuel : Nat) (hf : 344 < fuel) :
    walk nodes fuel 344 = List.range' 344 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 344).rule = .bound .leftEnd 1 (3467/6144) (464529/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_345 (fuel : Nat) (hf : 345 < fuel) :
    walk nodes fuel 345 = List.range' 343 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 345).rule = .split 3 (99/128) 343 344 := by rfl
      simp only [walk, hr]
      rw [traversal_343 f (by omega), traversal_344 f (by omega)]
      change (List.range' 343 1 ++ List.range' (343+1) 1) ++
        [343+(1+1)] = List.range' 343 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 343) (n := 1+1)).symm

private theorem traversal_346 (fuel : Nat) (hf : 346 < fuel) :
    walk nodes fuel 346 = List.range' 342 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 346).rule = .split 2 (983/512) 342 345 := by rfl
      simp only [walk, hr]
      rw [traversal_342 f (by omega), traversal_345 f (by omega)]
      change (List.range' 342 1 ++ List.range' (342+1) 3) ++
        [342+(1+3)] = List.range' 342 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 342) (n := 1+3)).symm

private theorem traversal_347 (fuel : Nat) (hf : 347 < fuel) :
    walk nodes fuel 347 = List.range' 341 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 347).rule = .split 1 (295/128) 341 346 := by rfl
      simp only [walk, hr]
      rw [traversal_341 f (by omega), traversal_346 f (by omega)]
      change (List.range' 341 1 ++ List.range' (341+1) 5) ++
        [341+(1+5)] = List.range' 341 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 341) (n := 1+5)).symm

private theorem traversal_348 (fuel : Nat) (hf : 348 < fuel) :
    walk nodes fuel 348 = List.range' 348 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 348).rule = .bound .leftEnd 1 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_349 (fuel : Nat) (hf : 349 < fuel) :
    walk nodes fuel 349 = List.range' 341 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 349).rule = .split 0 (1/160) 347 348 := by rfl
      simp only [walk, hr]
      rw [traversal_347 f (by omega), traversal_348 f (by omega)]
      change (List.range' 341 7 ++ List.range' (341+7) 1) ++
        [341+(7+1)] = List.range' 341 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 341) (n := 7+1)).symm

private theorem traversal_350 (fuel : Nat) (hf : 350 < fuel) :
    walk nodes fuel 350 = List.range' 350 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 350).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_351 (fuel : Nat) (hf : 351 < fuel) :
    walk nodes fuel 351 = List.range' 341 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 351).rule = .split 3 (51/64) 349 350 := by rfl
      simp only [walk, hr]
      rw [traversal_349 f (by omega), traversal_350 f (by omega)]
      change (List.range' 341 9 ++ List.range' (341+9) 1) ++
        [341+(9+1)] = List.range' 341 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 341) (n := 9+1)).symm

private theorem traversal_352 (fuel : Nat) (hf : 352 < fuel) :
    walk nodes fuel 352 = List.range' 352 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 352).rule = .bound .leftEnd 8 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_353 (fuel : Nat) (hf : 353 < fuel) :
    walk nodes fuel 353 = List.range' 353 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 353).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_354 (fuel : Nat) (hf : 354 < fuel) :
    walk nodes fuel 354 = List.range' 352 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 354).rule = .split 1 (295/128) 352 353 := by rfl
      simp only [walk, hr]
      rw [traversal_352 f (by omega), traversal_353 f (by omega)]
      change (List.range' 352 1 ++ List.range' (352+1) 1) ++
        [352+(1+1)] = List.range' 352 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 352) (n := 1+1)).symm

private theorem traversal_355 (fuel : Nat) (hf : 355 < fuel) :
    walk nodes fuel 355 = List.range' 355 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 355).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_356 (fuel : Nat) (hf : 356 < fuel) :
    walk nodes fuel 356 = List.range' 352 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 356).rule = .split 0 (1/160) 354 355 := by rfl
      simp only [walk, hr]
      rw [traversal_354 f (by omega), traversal_355 f (by omega)]
      change (List.range' 352 3 ++ List.range' (352+3) 1) ++
        [352+(3+1)] = List.range' 352 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 352) (n := 3+1)).symm

private theorem traversal_357 (fuel : Nat) (hf : 357 < fuel) :
    walk nodes fuel 357 = List.range' 357 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 357).rule = .bound .leftEnd 8 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_358 (fuel : Nat) (hf : 358 < fuel) :
    walk nodes fuel 358 = List.range' 358 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 358).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_359 (fuel : Nat) (hf : 359 < fuel) :
    walk nodes fuel 359 = List.range' 357 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 359).rule = .split 1 (295/128) 357 358 := by rfl
      simp only [walk, hr]
      rw [traversal_357 f (by omega), traversal_358 f (by omega)]
      change (List.range' 357 1 ++ List.range' (357+1) 1) ++
        [357+(1+1)] = List.range' 357 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 357) (n := 1+1)).symm

private theorem traversal_360 (fuel : Nat) (hf : 360 < fuel) :
    walk nodes fuel 360 = List.range' 360 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 360).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_361 (fuel : Nat) (hf : 361 < fuel) :
    walk nodes fuel 361 = List.range' 357 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 361).rule = .split 0 (1/160) 359 360 := by rfl
      simp only [walk, hr]
      rw [traversal_359 f (by omega), traversal_360 f (by omega)]
      change (List.range' 357 3 ++ List.range' (357+3) 1) ++
        [357+(3+1)] = List.range' 357 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 357) (n := 3+1)).symm

private theorem traversal_362 (fuel : Nat) (hf : 362 < fuel) :
    walk nodes fuel 362 = List.range' 352 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 362).rule = .split 3 (51/64) 356 361 := by rfl
      simp only [walk, hr]
      rw [traversal_356 f (by omega), traversal_361 f (by omega)]
      change (List.range' 352 5 ++ List.range' (352+5) 5) ++
        [352+(5+5)] = List.range' 352 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 352) (n := 5+5)).symm

private theorem traversal_363 (fuel : Nat) (hf : 363 < fuel) :
    walk nodes fuel 363 = List.range' 341 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 363).rule = .split 2 (501/256) 351 362 := by rfl
      simp only [walk, hr]
      rw [traversal_351 f (by omega), traversal_362 f (by omega)]
      change (List.range' 341 11 ++ List.range' (341+11) 11) ++
        [341+(11+11)] = List.range' 341 ((11+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 341) (n := 11+11)).symm

private theorem traversal_364 (fuel : Nat) (hf : 364 < fuel) :
    walk nodes fuel 364 = List.range' 340 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 364).rule = .split 1 (145/64) 340 363 := by rfl
      simp only [walk, hr]
      rw [traversal_340 f (by omega), traversal_363 f (by omega)]
      change (List.range' 340 1 ++ List.range' (340+1) 23) ++
        [340+(1+23)] = List.range' 340 ((1+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 340) (n := 1+23)).symm

private theorem traversal_365 (fuel : Nat) (hf : 365 < fuel) :
    walk nodes fuel 365 = List.range' 365 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 365).rule = .bound .leftEnd 8 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_366 (fuel : Nat) (hf : 366 < fuel) :
    walk nodes fuel 366 = List.range' 366 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 366).rule = .bound .leftEnd 1 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_367 (fuel : Nat) (hf : 367 < fuel) :
    walk nodes fuel 367 = List.range' 365 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 367).rule = .split 1 (145/64) 365 366 := by rfl
      simp only [walk, hr]
      rw [traversal_365 f (by omega), traversal_366 f (by omega)]
      change (List.range' 365 1 ++ List.range' (365+1) 1) ++
        [365+(1+1)] = List.range' 365 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 365) (n := 1+1)).symm

private theorem traversal_368 (fuel : Nat) (hf : 368 < fuel) :
    walk nodes fuel 368 = List.range' 340 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 368).rule = .split 0 (1/80) 364 367 := by rfl
      simp only [walk, hr]
      rw [traversal_364 f (by omega), traversal_367 f (by omega)]
      change (List.range' 340 25 ++ List.range' (340+25) 3) ++
        [340+(25+3)] = List.range' 340 ((25+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 340) (n := 25+3)).symm

private theorem traversal_369 (fuel : Nat) (hf : 369 < fuel) :
    walk nodes fuel 369 = List.range' 369 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 369).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_370 (fuel : Nat) (hf : 370 < fuel) :
    walk nodes fuel 370 = List.range' 340 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 370).rule = .split 3 (27/32) 368 369 := by rfl
      simp only [walk, hr]
      rw [traversal_368 f (by omega), traversal_369 f (by omega)]
      change (List.range' 340 29 ++ List.range' (340+29) 1) ++
        [340+(29+1)] = List.range' 340 ((29+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 340) (n := 29+1)).symm

private theorem traversal_371 (fuel : Nat) (hf : 371 < fuel) :
    walk nodes fuel 371 = List.range' 339 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 371).rule = .split 2 (241/128) 339 370 := by rfl
      simp only [walk, hr]
      rw [traversal_339 f (by omega), traversal_370 f (by omega)]
      change (List.range' 339 1 ++ List.range' (339+1) 31) ++
        [339+(1+31)] = List.range' 339 ((1+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 1+31)).symm

private theorem traversal_372 (fuel : Nat) (hf : 372 < fuel) :
    walk nodes fuel 372 = List.range' 372 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 372).rule = .bound .leftEnd 1 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_373 (fuel : Nat) (hf : 373 < fuel) :
    walk nodes fuel 373 = List.range' 373 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 373).rule = .bound .leftEnd 1 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_374 (fuel : Nat) (hf : 374 < fuel) :
    walk nodes fuel 374 = List.range' 374 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 374).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_375 (fuel : Nat) (hf : 375 < fuel) :
    walk nodes fuel 375 = List.range' 375 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 375).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_376 (fuel : Nat) (hf : 376 < fuel) :
    walk nodes fuel 376 = List.range' 374 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 376).rule = .split 3 (51/64) 374 375 := by rfl
      simp only [walk, hr]
      rw [traversal_374 f (by omega), traversal_375 f (by omega)]
      change (List.range' 374 1 ++ List.range' (374+1) 1) ++
        [374+(1+1)] = List.range' 374 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 374) (n := 1+1)).symm

private theorem traversal_377 (fuel : Nat) (hf : 377 < fuel) :
    walk nodes fuel 377 = List.range' 373 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 377).rule = .split 2 (501/256) 373 376 := by rfl
      simp only [walk, hr]
      rw [traversal_373 f (by omega), traversal_376 f (by omega)]
      change (List.range' 373 1 ++ List.range' (373+1) 3) ++
        [373+(1+3)] = List.range' 373 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 373) (n := 1+3)).symm

private theorem traversal_378 (fuel : Nat) (hf : 378 < fuel) :
    walk nodes fuel 378 = List.range' 378 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 378).rule = .bound .leftEnd 1 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_379 (fuel : Nat) (hf : 379 < fuel) :
    walk nodes fuel 379 = List.range' 373 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 379).rule = .split 1 (155/64) 377 378 := by rfl
      simp only [walk, hr]
      rw [traversal_377 f (by omega), traversal_378 f (by omega)]
      change (List.range' 373 5 ++ List.range' (373+5) 1) ++
        [373+(5+1)] = List.range' 373 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 373) (n := 5+1)).symm

private theorem traversal_380 (fuel : Nat) (hf : 380 < fuel) :
    walk nodes fuel 380 = List.range' 380 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 380).rule = .bound .leftEnd 1 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_381 (fuel : Nat) (hf : 381 < fuel) :
    walk nodes fuel 381 = List.range' 373 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 381).rule = .split 0 (1/80) 379 380 := by rfl
      simp only [walk, hr]
      rw [traversal_379 f (by omega), traversal_380 f (by omega)]
      change (List.range' 373 7 ++ List.range' (373+7) 1) ++
        [373+(7+1)] = List.range' 373 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 373) (n := 7+1)).symm

private theorem traversal_382 (fuel : Nat) (hf : 382 < fuel) :
    walk nodes fuel 382 = List.range' 382 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 382).rule = .bound .leftEnd 1 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_383 (fuel : Nat) (hf : 383 < fuel) :
    walk nodes fuel 383 = List.range' 373 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 383).rule = .split 3 (27/32) 381 382 := by rfl
      simp only [walk, hr]
      rw [traversal_381 f (by omega), traversal_382 f (by omega)]
      change (List.range' 373 9 ++ List.range' (373+9) 1) ++
        [373+(9+1)] = List.range' 373 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 373) (n := 9+1)).symm

private theorem traversal_384 (fuel : Nat) (hf : 384 < fuel) :
    walk nodes fuel 384 = List.range' 372 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 384).rule = .split 2 (241/128) 372 383 := by rfl
      simp only [walk, hr]
      rw [traversal_372 f (by omega), traversal_383 f (by omega)]
      change (List.range' 372 1 ++ List.range' (372+1) 11) ++
        [372+(1+11)] = List.range' 372 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 372) (n := 1+11)).symm

private theorem traversal_385 (fuel : Nat) (hf : 385 < fuel) :
    walk nodes fuel 385 = List.range' 339 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 385).rule = .split 1 (75/32) 371 384 := by rfl
      simp only [walk, hr]
      rw [traversal_371 f (by omega), traversal_384 f (by omega)]
      change (List.range' 339 33 ++ List.range' (339+33) 13) ++
        [339+(33+13)] = List.range' 339 ((33+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 33+13)).symm

private theorem traversal_386 (fuel : Nat) (hf : 386 < fuel) :
    walk nodes fuel 386 = List.range' 386 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 386).rule = .bound .leftEnd 1 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_387 (fuel : Nat) (hf : 387 < fuel) :
    walk nodes fuel 387 = List.range' 339 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 387).rule = .split 0 (1/40) 385 386 := by rfl
      simp only [walk, hr]
      rw [traversal_385 f (by omega), traversal_386 f (by omega)]
      change (List.range' 339 47 ++ List.range' (339+47) 1) ++
        [339+(47+1)] = List.range' 339 ((47+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 47+1)).symm

private theorem traversal_388 (fuel : Nat) (hf : 388 < fuel) :
    walk nodes fuel 388 = List.range' 388 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 388).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_389 (fuel : Nat) (hf : 389 < fuel) :
    walk nodes fuel 389 = List.range' 339 51 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 389).rule = .split 3 (15/16) 387 388 := by rfl
      simp only [walk, hr]
      rw [traversal_387 f (by omega), traversal_388 f (by omega)]
      change (List.range' 339 49 ++ List.range' (339+49) 1) ++
        [339+(49+1)] = List.range' 339 ((49+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 49+1)).symm

private theorem traversal_390 (fuel : Nat) (hf : 390 < fuel) :
    walk nodes fuel 390 = List.range' 338 53 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 390).rule = .split 2 (111/64) 338 389 := by rfl
      simp only [walk, hr]
      rw [traversal_338 f (by omega), traversal_389 f (by omega)]
      change (List.range' 338 1 ++ List.range' (338+1) 51) ++
        [338+(1+51)] = List.range' 338 ((1+51)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 338) (n := 1+51)).symm

private theorem traversal_391 (fuel : Nat) (hf : 391 < fuel) :
    walk nodes fuel 391 = List.range' 337 55 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 391).rule = .split 1 (35/16) 337 390 := by rfl
      simp only [walk, hr]
      rw [traversal_337 f (by omega), traversal_390 f (by omega)]
      change (List.range' 337 1 ++ List.range' (337+1) 53) ++
        [337+(1+53)] = List.range' 337 ((1+53)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 337) (n := 1+53)).symm

private theorem traversal_392 (fuel : Nat) (hf : 392 < fuel) :
    walk nodes fuel 392 = List.range' 392 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 392).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_393 (fuel : Nat) (hf : 393 < fuel) :
    walk nodes fuel 393 = List.range' 393 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 393).rule = .bound .leftEnd 1 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_394 (fuel : Nat) (hf : 394 < fuel) :
    walk nodes fuel 394 = List.range' 392 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 394).rule = .split 1 (35/16) 392 393 := by rfl
      simp only [walk, hr]
      rw [traversal_392 f (by omega), traversal_393 f (by omega)]
      change (List.range' 392 1 ++ List.range' (392+1) 1) ++
        [392+(1+1)] = List.range' 392 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 392) (n := 1+1)).symm

private theorem traversal_395 (fuel : Nat) (hf : 395 < fuel) :
    walk nodes fuel 395 = List.range' 337 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 395).rule = .split 0 (1/20) 391 394 := by rfl
      simp only [walk, hr]
      rw [traversal_391 f (by omega), traversal_394 f (by omega)]
      change (List.range' 337 55 ++ List.range' (337+55) 3) ++
        [337+(55+3)] = List.range' 337 ((55+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 337) (n := 55+3)).symm

private theorem traversal_396 (fuel : Nat) (hf : 396 < fuel) :
    walk nodes fuel 396 = List.range' 396 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 396).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_397 (fuel : Nat) (hf : 397 < fuel) :
    walk nodes fuel 397 = List.range' 337 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 397).rule = .split 3 (9/8) 395 396 := by rfl
      simp only [walk, hr]
      rw [traversal_395 f (by omega), traversal_396 f (by omega)]
      change (List.range' 337 59 ++ List.range' (337+59) 1) ++
        [337+(59+1)] = List.range' 337 ((59+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 337) (n := 59+1)).symm

theorem traversal_398 (fuel : Nat) (hf : 398 < fuel) :
    walk nodes fuel 398 = List.range' 398 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 398).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_399 (fuel : Nat) (hf : 399 < fuel) :
    walk nodes fuel 399 = List.range' 399 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 399).rule = .bound .leftEnd 8 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_400 (fuel : Nat) (hf : 400 < fuel) :
    walk nodes fuel 400 = List.range' 400 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 400).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_401 (fuel : Nat) (hf : 401 < fuel) :
    walk nodes fuel 401 = List.range' 401 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 401).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_402 (fuel : Nat) (hf : 402 < fuel) :
    walk nodes fuel 402 = List.range' 400 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 402).rule = .split 3 (27/32) 400 401 := by rfl
      simp only [walk, hr]
      rw [traversal_400 f (by omega), traversal_401 f (by omega)]
      change (List.range' 400 1 ++ List.range' (400+1) 1) ++
        [400+(1+1)] = List.range' 400 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 400) (n := 1+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
