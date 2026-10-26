/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_366,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_379,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_392,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_393,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_396,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_397,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_400,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_401,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_402,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart05.traversal_403
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart04
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_336 (fuel : Nat) (hf : 336 < fuel) :
    walk nodes fuel 336 = List.range' 330 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 336).rule = .split 0 (1/20) 334 335 := by rfl
      simp only [walk, hr]
      rw [traversal_334 f (by omega), traversal_335 f (by omega)]
      change (List.range' 330 5 ++ List.range' (330+5) 1) ++
        [330+(5+1)] = List.range' 330 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 330) (n := 5+1)).symm

private theorem traversal_337 (fuel : Nat) (hf : 337 < fuel) :
    walk nodes fuel 337 = List.range' 323 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 337).rule = .split 3 (9/8) 329 336 := by rfl
      simp only [walk, hr]
      rw [traversal_329 f (by omega), traversal_336 f (by omega)]
      change (List.range' 323 7 ++ List.range' (323+7) 7) ++
        [323+(7+7)] = List.range' 323 ((7+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 323) (n := 7+7)).symm

private theorem traversal_338 (fuel : Nat) (hf : 338 < fuel) :
    walk nodes fuel 338 = List.range' 298 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 338).rule = .split 2 (103/32) 322 337 := by rfl
      simp only [walk, hr]
      rw [traversal_322 f (by omega), traversal_337 f (by omega)]
      change (List.range' 298 25 ++ List.range' (298+25) 15) ++
        [298+(25+15)] = List.range' 298 ((25+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 298) (n := 25+15)).symm

private theorem traversal_339 (fuel : Nat) (hf : 339 < fuel) :
    walk nodes fuel 339 = List.range' 339 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 339).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_340 (fuel : Nat) (hf : 340 < fuel) :
    walk nodes fuel 340 = List.range' 340 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 340).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_341 (fuel : Nat) (hf : 341 < fuel) :
    walk nodes fuel 341 = List.range' 341 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 341).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_342 (fuel : Nat) (hf : 342 < fuel) :
    walk nodes fuel 342 = List.range' 340 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 342).rule = .split 1 (65/32) 340 341 := by rfl
      simp only [walk, hr]
      rw [traversal_340 f (by omega), traversal_341 f (by omega)]
      change (List.range' 340 1 ++ List.range' (340+1) 1) ++
        [340+(1+1)] = List.range' 340 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 340) (n := 1+1)).symm

private theorem traversal_343 (fuel : Nat) (hf : 343 < fuel) :
    walk nodes fuel 343 = List.range' 343 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 343).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_344 (fuel : Nat) (hf : 344 < fuel) :
    walk nodes fuel 344 = List.range' 340 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 344).rule = .split 0 (1/40) 342 343 := by rfl
      simp only [walk, hr]
      rw [traversal_342 f (by omega), traversal_343 f (by omega)]
      change (List.range' 340 3 ++ List.range' (340+3) 1) ++
        [340+(3+1)] = List.range' 340 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 340) (n := 3+1)).symm

private theorem traversal_345 (fuel : Nat) (hf : 345 < fuel) :
    walk nodes fuel 345 = List.range' 339 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 345).rule = .split 3 (15/16) 339 344 := by rfl
      simp only [walk, hr]
      rw [traversal_339 f (by omega), traversal_344 f (by omega)]
      change (List.range' 339 1 ++ List.range' (339+1) 5) ++
        [339+(1+5)] = List.range' 339 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 1+5)).symm

private theorem traversal_346 (fuel : Nat) (hf : 346 < fuel) :
    walk nodes fuel 346 = List.range' 346 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 346).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_347 (fuel : Nat) (hf : 347 < fuel) :
    walk nodes fuel 347 = List.range' 339 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 347).rule = .split 2 (187/64) 345 346 := by rfl
      simp only [walk, hr]
      rw [traversal_345 f (by omega), traversal_346 f (by omega)]
      change (List.range' 339 7 ++ List.range' (339+7) 1) ++
        [339+(7+1)] = List.range' 339 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 7+1)).symm

private theorem traversal_348 (fuel : Nat) (hf : 348 < fuel) :
    walk nodes fuel 348 = List.range' 348 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 348).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_349 (fuel : Nat) (hf : 349 < fuel) :
    walk nodes fuel 349 = List.range' 339 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 349).rule = .split 1 (35/16) 347 348 := by rfl
      simp only [walk, hr]
      rw [traversal_347 f (by omega), traversal_348 f (by omega)]
      change (List.range' 339 9 ++ List.range' (339+9) 1) ++
        [339+(9+1)] = List.range' 339 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 9+1)).symm

private theorem traversal_350 (fuel : Nat) (hf : 350 < fuel) :
    walk nodes fuel 350 = List.range' 350 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 350).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_351 (fuel : Nat) (hf : 351 < fuel) :
    walk nodes fuel 351 = List.range' 339 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 351).rule = .split 0 (1/20) 349 350 := by rfl
      simp only [walk, hr]
      rw [traversal_349 f (by omega), traversal_350 f (by omega)]
      change (List.range' 339 11 ++ List.range' (339+11) 1) ++
        [339+(11+1)] = List.range' 339 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 11+1)).symm

private theorem traversal_352 (fuel : Nat) (hf : 352 < fuel) :
    walk nodes fuel 352 = List.range' 352 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 352).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_353 (fuel : Nat) (hf : 353 < fuel) :
    walk nodes fuel 353 = List.range' 353 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 353).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_354 (fuel : Nat) (hf : 354 < fuel) :
    walk nodes fuel 354 = List.range' 352 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 354).rule = .split 2 (187/64) 352 353 := by rfl
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
      have hr : (node nodes 355).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_356 (fuel : Nat) (hf : 356 < fuel) :
    walk nodes fuel 356 = List.range' 352 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 356).rule = .split 1 (35/16) 354 355 := by rfl
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
      have hr : (node nodes 357).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_358 (fuel : Nat) (hf : 358 < fuel) :
    walk nodes fuel 358 = List.range' 352 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 358).rule = .split 0 (1/20) 356 357 := by rfl
      simp only [walk, hr]
      rw [traversal_356 f (by omega), traversal_357 f (by omega)]
      change (List.range' 352 5 ++ List.range' (352+5) 1) ++
        [352+(5+1)] = List.range' 352 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 352) (n := 5+1)).symm

private theorem traversal_359 (fuel : Nat) (hf : 359 < fuel) :
    walk nodes fuel 359 = List.range' 339 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 359).rule = .split 3 (9/8) 351 358 := by rfl
      simp only [walk, hr]
      rw [traversal_351 f (by omega), traversal_358 f (by omega)]
      change (List.range' 339 13 ++ List.range' (339+13) 7) ++
        [339+(13+7)] = List.range' 339 ((13+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 13+7)).symm

private theorem traversal_360 (fuel : Nat) (hf : 360 < fuel) :
    walk nodes fuel 360 = List.range' 360 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 360).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_361 (fuel : Nat) (hf : 361 < fuel) :
    walk nodes fuel 361 = List.range' 339 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 361).rule = .split 2 (103/32) 359 360 := by rfl
      simp only [walk, hr]
      rw [traversal_359 f (by omega), traversal_360 f (by omega)]
      change (List.range' 339 21 ++ List.range' (339+21) 1) ++
        [339+(21+1)] = List.range' 339 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 339) (n := 21+1)).symm

private theorem traversal_362 (fuel : Nat) (hf : 362 < fuel) :
    walk nodes fuel 362 = List.range' 298 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 362).rule = .split 1 (15/8) 338 361 := by rfl
      simp only [walk, hr]
      rw [traversal_338 f (by omega), traversal_361 f (by omega)]
      change (List.range' 298 41 ++ List.range' (298+41) 23) ++
        [298+(41+23)] = List.range' 298 ((41+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 298) (n := 41+23)).symm

private theorem traversal_363 (fuel : Nat) (hf : 363 < fuel) :
    walk nodes fuel 363 = List.range' 297 67 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 363).rule = .split 3 (3/4) 297 362 := by rfl
      simp only [walk, hr]
      rw [traversal_297 f (by omega), traversal_362 f (by omega)]
      change (List.range' 297 1 ++ List.range' (297+1) 65) ++
        [297+(1+65)] = List.range' 297 ((1+65)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 297) (n := 1+65)).symm

private theorem traversal_364 (fuel : Nat) (hf : 364 < fuel) :
    walk nodes fuel 364 = List.range' 364 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 364).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_365 (fuel : Nat) (hf : 365 < fuel) :
    walk nodes fuel 365 = List.range' 297 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 365).rule = .split 2 (61/16) 363 364 := by rfl
      simp only [walk, hr]
      rw [traversal_363 f (by omega), traversal_364 f (by omega)]
      change (List.range' 297 67 ++ List.range' (297+67) 1) ++
        [297+(67+1)] = List.range' 297 ((67+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 297) (n := 67+1)).symm

theorem traversal_366 (fuel : Nat) (hf : 366 < fuel) :
    walk nodes fuel 366 = List.range' 284 83 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 366).rule = .split 1 (5/4) 296 365 := by rfl
      simp only [walk, hr]
      rw [traversal_296 f (by omega), traversal_365 f (by omega)]
      change (List.range' 284 13 ++ List.range' (284+13) 69) ++
        [284+(13+69)] = List.range' 284 ((13+69)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 284) (n := 13+69)).symm

private theorem traversal_367 (fuel : Nat) (hf : 367 < fuel) :
    walk nodes fuel 367 = List.range' 367 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 367).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_368 (fuel : Nat) (hf : 368 < fuel) :
    walk nodes fuel 368 = List.range' 368 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 368).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_369 (fuel : Nat) (hf : 369 < fuel) :
    walk nodes fuel 369 = List.range' 369 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 369).rule = .bound .vertex 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_370 (fuel : Nat) (hf : 370 < fuel) :
    walk nodes fuel 370 = List.range' 370 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 370).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_371 (fuel : Nat) (hf : 371 < fuel) :
    walk nodes fuel 371 = List.range' 369 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 371).rule = .split 3 (21/8) 369 370 := by rfl
      simp only [walk, hr]
      rw [traversal_369 f (by omega), traversal_370 f (by omega)]
      change (List.range' 369 1 ++ List.range' (369+1) 1) ++
        [369+(1+1)] = List.range' 369 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 369) (n := 1+1)).symm

private theorem traversal_372 (fuel : Nat) (hf : 372 < fuel) :
    walk nodes fuel 372 = List.range' 368 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 372).rule = .split 2 (103/32) 368 371 := by rfl
      simp only [walk, hr]
      rw [traversal_368 f (by omega), traversal_371 f (by omega)]
      change (List.range' 368 1 ++ List.range' (368+1) 3) ++
        [368+(1+3)] = List.range' 368 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 368) (n := 1+3)).symm

private theorem traversal_373 (fuel : Nat) (hf : 373 < fuel) :
    walk nodes fuel 373 = List.range' 373 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 373).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_374 (fuel : Nat) (hf : 374 < fuel) :
    walk nodes fuel 374 = List.range' 374 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 374).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_375 (fuel : Nat) (hf : 375 < fuel) :
    walk nodes fuel 375 = List.range' 375 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 375).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_376 (fuel : Nat) (hf : 376 < fuel) :
    walk nodes fuel 376 = List.range' 374 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 376).rule = .split 3 (21/8) 374 375 := by rfl
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
      have hr : (node nodes 377).rule = .split 2 (103/32) 373 376 := by rfl
      simp only [walk, hr]
      rw [traversal_373 f (by omega), traversal_376 f (by omega)]
      change (List.range' 373 1 ++ List.range' (373+1) 3) ++
        [373+(1+3)] = List.range' 373 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 373) (n := 1+3)).symm

private theorem traversal_378 (fuel : Nat) (hf : 378 < fuel) :
    walk nodes fuel 378 = List.range' 368 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 378).rule = .split 1 (5/8) 372 377 := by rfl
      simp only [walk, hr]
      rw [traversal_372 f (by omega), traversal_377 f (by omega)]
      change (List.range' 368 5 ++ List.range' (368+5) 5) ++
        [368+(5+5)] = List.range' 368 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 368) (n := 5+5)).symm

theorem traversal_379 (fuel : Nat) (hf : 379 < fuel) :
    walk nodes fuel 379 = List.range' 367 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 379).rule = .split 3 (9/4) 367 378 := by rfl
      simp only [walk, hr]
      rw [traversal_367 f (by omega), traversal_378 f (by omega)]
      change (List.range' 367 1 ++ List.range' (367+1) 11) ++
        [367+(1+11)] = List.range' 367 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 367) (n := 1+11)).symm

private theorem traversal_380 (fuel : Nat) (hf : 380 < fuel) :
    walk nodes fuel 380 = List.range' 380 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 380).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_381 (fuel : Nat) (hf : 381 < fuel) :
    walk nodes fuel 381 = List.range' 381 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 381).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_382 (fuel : Nat) (hf : 382 < fuel) :
    walk nodes fuel 382 = List.range' 382 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 382).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_383 (fuel : Nat) (hf : 383 < fuel) :
    walk nodes fuel 383 = List.range' 381 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 383).rule = .split 0 (1/20) 381 382 := by rfl
      simp only [walk, hr]
      rw [traversal_381 f (by omega), traversal_382 f (by omega)]
      change (List.range' 381 1 ++ List.range' (381+1) 1) ++
        [381+(1+1)] = List.range' 381 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 381) (n := 1+1)).symm

private theorem traversal_384 (fuel : Nat) (hf : 384 < fuel) :
    walk nodes fuel 384 = List.range' 384 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 384).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_385 (fuel : Nat) (hf : 385 < fuel) :
    walk nodes fuel 385 = List.range' 385 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 385).rule = .bound .vertex 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_386 (fuel : Nat) (hf : 386 < fuel) :
    walk nodes fuel 386 = List.range' 384 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 386).rule = .split 1 (15/16) 384 385 := by rfl
      simp only [walk, hr]
      rw [traversal_384 f (by omega), traversal_385 f (by omega)]
      change (List.range' 384 1 ++ List.range' (384+1) 1) ++
        [384+(1+1)] = List.range' 384 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 384) (n := 1+1)).symm

private theorem traversal_387 (fuel : Nat) (hf : 387 < fuel) :
    walk nodes fuel 387 = List.range' 387 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 387).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_388 (fuel : Nat) (hf : 388 < fuel) :
    walk nodes fuel 388 = List.range' 384 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 388).rule = .split 0 (1/20) 386 387 := by rfl
      simp only [walk, hr]
      rw [traversal_386 f (by omega), traversal_387 f (by omega)]
      change (List.range' 384 3 ++ List.range' (384+3) 1) ++
        [384+(3+1)] = List.range' 384 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 384) (n := 3+1)).symm

private theorem traversal_389 (fuel : Nat) (hf : 389 < fuel) :
    walk nodes fuel 389 = List.range' 381 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 389).rule = .split 3 (15/8) 383 388 := by rfl
      simp only [walk, hr]
      rw [traversal_383 f (by omega), traversal_388 f (by omega)]
      change (List.range' 381 3 ++ List.range' (381+3) 5) ++
        [381+(3+5)] = List.range' 381 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 381) (n := 3+5)).symm

private theorem traversal_390 (fuel : Nat) (hf : 390 < fuel) :
    walk nodes fuel 390 = List.range' 390 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 390).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_391 (fuel : Nat) (hf : 391 < fuel) :
    walk nodes fuel 391 = List.range' 381 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 391).rule = .split 2 (141/32) 389 390 := by rfl
      simp only [walk, hr]
      rw [traversal_389 f (by omega), traversal_390 f (by omega)]
      change (List.range' 381 9 ++ List.range' (381+9) 1) ++
        [381+(9+1)] = List.range' 381 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 381) (n := 9+1)).symm

theorem traversal_392 (fuel : Nat) (hf : 392 < fuel) :
    walk nodes fuel 392 = List.range' 380 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 392).rule = .split 1 (5/8) 380 391 := by rfl
      simp only [walk, hr]
      rw [traversal_380 f (by omega), traversal_391 f (by omega)]
      change (List.range' 380 1 ++ List.range' (380+1) 11) ++
        [380+(1+11)] = List.range' 380 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 380) (n := 1+11)).symm

theorem traversal_393 (fuel : Nat) (hf : 393 < fuel) :
    walk nodes fuel 393 = List.range' 393 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 393).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_394 (fuel : Nat) (hf : 394 < fuel) :
    walk nodes fuel 394 = List.range' 394 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 394).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_395 (fuel : Nat) (hf : 395 < fuel) :
    walk nodes fuel 395 = List.range' 395 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 395).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_396 (fuel : Nat) (hf : 396 < fuel) :
    walk nodes fuel 396 = List.range' 394 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 396).rule = .split 3 (45/16) 394 395 := by rfl
      simp only [walk, hr]
      rw [traversal_394 f (by omega), traversal_395 f (by omega)]
      change (List.range' 394 1 ++ List.range' (394+1) 1) ++
        [394+(1+1)] = List.range' 394 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 394) (n := 1+1)).symm

theorem traversal_397 (fuel : Nat) (hf : 397 < fuel) :
    walk nodes fuel 397 = List.range' 397 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 397).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_398 (fuel : Nat) (hf : 398 < fuel) :
    walk nodes fuel 398 = List.range' 398 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 398).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_399 (fuel : Nat) (hf : 399 < fuel) :
    walk nodes fuel 399 = List.range' 399 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 399).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_400 (fuel : Nat) (hf : 400 < fuel) :
    walk nodes fuel 400 = List.range' 398 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 400).rule = .split 3 (93/32) 398 399 := by rfl
      simp only [walk, hr]
      rw [traversal_398 f (by omega), traversal_399 f (by omega)]
      change (List.range' 398 1 ++ List.range' (398+1) 1) ++
        [398+(1+1)] = List.range' 398 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 1+1)).symm

theorem traversal_401 (fuel : Nat) (hf : 401 < fuel) :
    walk nodes fuel 401 = List.range' 401 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 401).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_402 (fuel : Nat) (hf : 402 < fuel) :
    walk nodes fuel 402 = List.range' 402 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 402).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_403 (fuel : Nat) (hf : 403 < fuel) :
    walk nodes fuel 403 = List.range' 403 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 403).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
