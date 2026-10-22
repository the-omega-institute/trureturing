/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05.traversal_363,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05.traversal_386,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05.traversal_401,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart05.traversal_402
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart03
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart04
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_336 (fuel : Nat) (hf : 336 < fuel) :
    walk nodes fuel 336 = List.range' 336 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 336).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_337 (fuel : Nat) (hf : 337 < fuel) :
    walk nodes fuel 337 = List.range' 333 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 337).rule = .split 0 (1/20) 335 336 := by rfl
      simp only [walk, hr]
      rw [traversal_335 f (by omega), traversal_336 f (by omega)]
      change (List.range' 333 3 ++ List.range' (333+3) 1) ++
        [333+(3+1)] = List.range' 333 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 333) (n := 3+1)).symm

private theorem traversal_338 (fuel : Nat) (hf : 338 < fuel) :
    walk nodes fuel 338 = List.range' 338 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 338).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_339 (fuel : Nat) (hf : 339 < fuel) :
    walk nodes fuel 339 = List.range' 333 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 339).rule = .split 3 (15/8) 337 338 := by rfl
      simp only [walk, hr]
      rw [traversal_337 f (by omega), traversal_338 f (by omega)]
      change (List.range' 333 5 ++ List.range' (333+5) 1) ++
        [333+(5+1)] = List.range' 333 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 333) (n := 5+1)).symm

private theorem traversal_340 (fuel : Nat) (hf : 340 < fuel) :
    walk nodes fuel 340 = List.range' 332 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 340).rule = .split 2 (103/32) 332 339 := by rfl
      simp only [walk, hr]
      rw [traversal_332 f (by omega), traversal_339 f (by omega)]
      change (List.range' 332 1 ++ List.range' (332+1) 7) ++
        [332+(1+7)] = List.range' 332 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 332) (n := 1+7)).symm

private theorem traversal_341 (fuel : Nat) (hf : 341 < fuel) :
    walk nodes fuel 341 = List.range' 341 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 341).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_342 (fuel : Nat) (hf : 342 < fuel) :
    walk nodes fuel 342 = List.range' 332 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 342).rule = .split 1 (15/8) 340 341 := by rfl
      simp only [walk, hr]
      rw [traversal_340 f (by omega), traversal_341 f (by omega)]
      change (List.range' 332 9 ++ List.range' (332+9) 1) ++
        [332+(9+1)] = List.range' 332 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 332) (n := 9+1)).symm

private theorem traversal_343 (fuel : Nat) (hf : 343 < fuel) :
    walk nodes fuel 343 = List.range' 343 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 343).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_344 (fuel : Nat) (hf : 344 < fuel) :
    walk nodes fuel 344 = List.range' 344 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 344).rule = .bound .leftEnd 1 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_345 (fuel : Nat) (hf : 345 < fuel) :
    walk nodes fuel 345 = List.range' 345 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 345).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_346 (fuel : Nat) (hf : 346 < fuel) :
    walk nodes fuel 346 = List.range' 344 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 346).rule = .split 3 (39/16) 344 345 := by rfl
      simp only [walk, hr]
      rw [traversal_344 f (by omega), traversal_345 f (by omega)]
      change (List.range' 344 1 ++ List.range' (344+1) 1) ++
        [344+(1+1)] = List.range' 344 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 344) (n := 1+1)).symm

private theorem traversal_347 (fuel : Nat) (hf : 347 < fuel) :
    walk nodes fuel 347 = List.range' 347 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 347).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_348 (fuel : Nat) (hf : 348 < fuel) :
    walk nodes fuel 348 = List.range' 344 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 348).rule = .split 2 (225/64) 346 347 := by rfl
      simp only [walk, hr]
      rw [traversal_346 f (by omega), traversal_347 f (by omega)]
      change (List.range' 344 3 ++ List.range' (344+3) 1) ++
        [344+(3+1)] = List.range' 344 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 344) (n := 3+1)).symm

private theorem traversal_349 (fuel : Nat) (hf : 349 < fuel) :
    walk nodes fuel 349 = List.range' 349 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 349).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_350 (fuel : Nat) (hf : 350 < fuel) :
    walk nodes fuel 350 = List.range' 344 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 350).rule = .split 1 (25/16) 348 349 := by rfl
      simp only [walk, hr]
      rw [traversal_348 f (by omega), traversal_349 f (by omega)]
      change (List.range' 344 5 ++ List.range' (344+5) 1) ++
        [344+(5+1)] = List.range' 344 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 344) (n := 5+1)).symm

private theorem traversal_351 (fuel : Nat) (hf : 351 < fuel) :
    walk nodes fuel 351 = List.range' 351 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 351).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_352 (fuel : Nat) (hf : 352 < fuel) :
    walk nodes fuel 352 = List.range' 344 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 352).rule = .split 0 (1/20) 350 351 := by rfl
      simp only [walk, hr]
      rw [traversal_350 f (by omega), traversal_351 f (by omega)]
      change (List.range' 344 7 ++ List.range' (344+7) 1) ++
        [344+(7+1)] = List.range' 344 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 344) (n := 7+1)).symm

private theorem traversal_353 (fuel : Nat) (hf : 353 < fuel) :
    walk nodes fuel 353 = List.range' 353 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 353).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_354 (fuel : Nat) (hf : 354 < fuel) :
    walk nodes fuel 354 = List.range' 344 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 354).rule = .split 3 (21/8) 352 353 := by rfl
      simp only [walk, hr]
      rw [traversal_352 f (by omega), traversal_353 f (by omega)]
      change (List.range' 344 9 ++ List.range' (344+9) 1) ++
        [344+(9+1)] = List.range' 344 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 344) (n := 9+1)).symm

private theorem traversal_355 (fuel : Nat) (hf : 355 < fuel) :
    walk nodes fuel 355 = List.range' 343 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 355).rule = .split 2 (103/32) 343 354 := by rfl
      simp only [walk, hr]
      rw [traversal_343 f (by omega), traversal_354 f (by omega)]
      change (List.range' 343 1 ++ List.range' (343+1) 11) ++
        [343+(1+11)] = List.range' 343 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 343) (n := 1+11)).symm

private theorem traversal_356 (fuel : Nat) (hf : 356 < fuel) :
    walk nodes fuel 356 = List.range' 356 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 356).rule = .bound .leftEnd 3 (121661/393216) (421449/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_357 (fuel : Nat) (hf : 357 < fuel) :
    walk nodes fuel 357 = List.range' 343 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 357).rule = .split 1 (15/8) 355 356 := by rfl
      simp only [walk, hr]
      rw [traversal_355 f (by omega), traversal_356 f (by omega)]
      change (List.range' 343 13 ++ List.range' (343+13) 1) ++
        [343+(13+1)] = List.range' 343 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 343) (n := 13+1)).symm

private theorem traversal_358 (fuel : Nat) (hf : 358 < fuel) :
    walk nodes fuel 358 = List.range' 332 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 358).rule = .split 3 (9/4) 342 357 := by rfl
      simp only [walk, hr]
      rw [traversal_342 f (by omega), traversal_357 f (by omega)]
      change (List.range' 332 11 ++ List.range' (332+11) 15) ++
        [332+(11+15)] = List.range' 332 ((11+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 332) (n := 11+15)).symm

private theorem traversal_359 (fuel : Nat) (hf : 359 < fuel) :
    walk nodes fuel 359 = List.range' 359 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 359).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_360 (fuel : Nat) (hf : 360 < fuel) :
    walk nodes fuel 360 = List.range' 332 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 360).rule = .split 2 (61/16) 358 359 := by rfl
      simp only [walk, hr]
      rw [traversal_358 f (by omega), traversal_359 f (by omega)]
      change (List.range' 332 27 ++ List.range' (332+27) 1) ++
        [332+(27+1)] = List.range' 332 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 332) (n := 27+1)).symm

private theorem traversal_361 (fuel : Nat) (hf : 361 < fuel) :
    walk nodes fuel 361 = List.range' 261 101 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 361).rule = .split 1 (5/4) 331 360 := by rfl
      simp only [walk, hr]
      rw [traversal_331 f (by omega), traversal_360 f (by omega)]
      change (List.range' 261 71 ++ List.range' (261+71) 29) ++
        [261+(71+29)] = List.range' 261 ((71+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 261) (n := 71+29)).symm

private theorem traversal_362 (fuel : Nat) (hf : 362 < fuel) :
    walk nodes fuel 362 = List.range' 228 135 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 362).rule = .split 3 (3/2) 260 361 := by rfl
      simp only [walk, hr]
      rw [traversal_260 f (by omega), traversal_361 f (by omega)]
      change (List.range' 228 33 ++ List.range' (228+33) 101) ++
        [228+(33+101)] = List.range' 228 ((33+101)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 228) (n := 33+101)).symm

theorem traversal_363 (fuel : Nat) (hf : 363 < fuel) :
    walk nodes fuel 363 = List.range' 1 363 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 363).rule = .split 2 (21/8) 227 362 := by rfl
      simp only [walk, hr]
      rw [traversal_227 f (by omega), traversal_362 f (by omega)]
      change (List.range' 1 227 ++ List.range' (1+227) 135) ++
        [1+(227+135)] = List.range' 1 ((227+135)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 227+135)).symm

private theorem traversal_364 (fuel : Nat) (hf : 364 < fuel) :
    walk nodes fuel 364 = List.range' 364 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 364).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_365 (fuel : Nat) (hf : 365 < fuel) :
    walk nodes fuel 365 = List.range' 365 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 365).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_366 (fuel : Nat) (hf : 366 < fuel) :
    walk nodes fuel 366 = List.range' 364 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 366).rule = .split 3 (3/16) 364 365 := by rfl
      simp only [walk, hr]
      rw [traversal_364 f (by omega), traversal_365 f (by omega)]
      change (List.range' 364 1 ++ List.range' (364+1) 1) ++
        [364+(1+1)] = List.range' 364 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 1+1)).symm

private theorem traversal_367 (fuel : Nat) (hf : 367 < fuel) :
    walk nodes fuel 367 = List.range' 367 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 367).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_368 (fuel : Nat) (hf : 368 < fuel) :
    walk nodes fuel 368 = List.range' 364 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 368).rule = .split 2 (35/64) 366 367 := by rfl
      simp only [walk, hr]
      rw [traversal_366 f (by omega), traversal_367 f (by omega)]
      change (List.range' 364 3 ++ List.range' (364+3) 1) ++
        [364+(3+1)] = List.range' 364 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 3+1)).symm

private theorem traversal_369 (fuel : Nat) (hf : 369 < fuel) :
    walk nodes fuel 369 = List.range' 369 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 369).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_370 (fuel : Nat) (hf : 370 < fuel) :
    walk nodes fuel 370 = List.range' 364 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 370).rule = .split 1 (45/16) 368 369 := by rfl
      simp only [walk, hr]
      rw [traversal_368 f (by omega), traversal_369 f (by omega)]
      change (List.range' 364 5 ++ List.range' (364+5) 1) ++
        [364+(5+1)] = List.range' 364 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 5+1)).symm

private theorem traversal_371 (fuel : Nat) (hf : 371 < fuel) :
    walk nodes fuel 371 = List.range' 371 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 371).rule = .bound .leftEnd 1 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_372 (fuel : Nat) (hf : 372 < fuel) :
    walk nodes fuel 372 = List.range' 364 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 372).rule = .split 0 (1/20) 370 371 := by rfl
      simp only [walk, hr]
      rw [traversal_370 f (by omega), traversal_371 f (by omega)]
      change (List.range' 364 7 ++ List.range' (364+7) 1) ++
        [364+(7+1)] = List.range' 364 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 7+1)).symm

private theorem traversal_373 (fuel : Nat) (hf : 373 < fuel) :
    walk nodes fuel 373 = List.range' 373 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 373).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_374 (fuel : Nat) (hf : 374 < fuel) :
    walk nodes fuel 374 = List.range' 364 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 374).rule = .split 3 (3/8) 372 373 := by rfl
      simp only [walk, hr]
      rw [traversal_372 f (by omega), traversal_373 f (by omega)]
      change (List.range' 364 9 ++ List.range' (364+9) 1) ++
        [364+(9+1)] = List.range' 364 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 9+1)).symm

private theorem traversal_375 (fuel : Nat) (hf : 375 < fuel) :
    walk nodes fuel 375 = List.range' 375 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 375).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_376 (fuel : Nat) (hf : 376 < fuel) :
    walk nodes fuel 376 = List.range' 376 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 376).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_377 (fuel : Nat) (hf : 377 < fuel) :
    walk nodes fuel 377 = List.range' 375 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 377).rule = .split 3 (3/8) 375 376 := by rfl
      simp only [walk, hr]
      rw [traversal_375 f (by omega), traversal_376 f (by omega)]
      change (List.range' 375 1 ++ List.range' (375+1) 1) ++
        [375+(1+1)] = List.range' 375 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 375) (n := 1+1)).symm

private theorem traversal_378 (fuel : Nat) (hf : 378 < fuel) :
    walk nodes fuel 378 = List.range' 364 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 378).rule = .split 2 (27/32) 374 377 := by rfl
      simp only [walk, hr]
      rw [traversal_374 f (by omega), traversal_377 f (by omega)]
      change (List.range' 364 11 ++ List.range' (364+11) 3) ++
        [364+(11+3)] = List.range' 364 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 11+3)).symm

private theorem traversal_379 (fuel : Nat) (hf : 379 < fuel) :
    walk nodes fuel 379 = List.range' 379 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 379).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_380 (fuel : Nat) (hf : 380 < fuel) :
    walk nodes fuel 380 = List.range' 380 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 380).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_381 (fuel : Nat) (hf : 381 < fuel) :
    walk nodes fuel 381 = List.range' 381 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 381).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_382 (fuel : Nat) (hf : 382 < fuel) :
    walk nodes fuel 382 = List.range' 380 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 382).rule = .split 3 (3/8) 380 381 := by rfl
      simp only [walk, hr]
      rw [traversal_380 f (by omega), traversal_381 f (by omega)]
      change (List.range' 380 1 ++ List.range' (380+1) 1) ++
        [380+(1+1)] = List.range' 380 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 380) (n := 1+1)).symm

private theorem traversal_383 (fuel : Nat) (hf : 383 < fuel) :
    walk nodes fuel 383 = List.range' 379 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 383).rule = .split 2 (27/32) 379 382 := by rfl
      simp only [walk, hr]
      rw [traversal_379 f (by omega), traversal_382 f (by omega)]
      change (List.range' 379 1 ++ List.range' (379+1) 3) ++
        [379+(1+3)] = List.range' 379 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 379) (n := 1+3)).symm

private theorem traversal_384 (fuel : Nat) (hf : 384 < fuel) :
    walk nodes fuel 384 = List.range' 364 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 384).rule = .split 1 (25/8) 378 383 := by rfl
      simp only [walk, hr]
      rw [traversal_378 f (by omega), traversal_383 f (by omega)]
      change (List.range' 364 15 ++ List.range' (364+15) 5) ++
        [364+(15+5)] = List.range' 364 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 15+5)).symm

private theorem traversal_385 (fuel : Nat) (hf : 385 < fuel) :
    walk nodes fuel 385 = List.range' 385 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 385).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_386 (fuel : Nat) (hf : 386 < fuel) :
    walk nodes fuel 386 = List.range' 364 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 386).rule = .split 3 (3/4) 384 385 := by rfl
      simp only [walk, hr]
      rw [traversal_384 f (by omega), traversal_385 f (by omega)]
      change (List.range' 364 21 ++ List.range' (364+21) 1) ++
        [364+(21+1)] = List.range' 364 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 21+1)).symm

private theorem traversal_387 (fuel : Nat) (hf : 387 < fuel) :
    walk nodes fuel 387 = List.range' 387 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 387).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_388 (fuel : Nat) (hf : 388 < fuel) :
    walk nodes fuel 388 = List.range' 388 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 388).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_389 (fuel : Nat) (hf : 389 < fuel) :
    walk nodes fuel 389 = List.range' 389 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 389).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_390 (fuel : Nat) (hf : 390 < fuel) :
    walk nodes fuel 390 = List.range' 388 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 390).rule = .split 3 (9/16) 388 389 := by rfl
      simp only [walk, hr]
      rw [traversal_388 f (by omega), traversal_389 f (by omega)]
      change (List.range' 388 1 ++ List.range' (388+1) 1) ++
        [388+(1+1)] = List.range' 388 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 388) (n := 1+1)).symm

private theorem traversal_391 (fuel : Nat) (hf : 391 < fuel) :
    walk nodes fuel 391 = List.range' 391 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 391).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_392 (fuel : Nat) (hf : 392 < fuel) :
    walk nodes fuel 392 = List.range' 388 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 392).rule = .split 2 (111/64) 390 391 := by rfl
      simp only [walk, hr]
      rw [traversal_390 f (by omega), traversal_391 f (by omega)]
      change (List.range' 388 3 ++ List.range' (388+3) 1) ++
        [388+(3+1)] = List.range' 388 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 388) (n := 3+1)).symm

private theorem traversal_393 (fuel : Nat) (hf : 393 < fuel) :
    walk nodes fuel 393 = List.range' 393 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 393).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_394 (fuel : Nat) (hf : 394 < fuel) :
    walk nodes fuel 394 = List.range' 388 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 394).rule = .split 1 (45/16) 392 393 := by rfl
      simp only [walk, hr]
      rw [traversal_392 f (by omega), traversal_393 f (by omega)]
      change (List.range' 388 5 ++ List.range' (388+5) 1) ++
        [388+(5+1)] = List.range' 388 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 388) (n := 5+1)).symm

private theorem traversal_395 (fuel : Nat) (hf : 395 < fuel) :
    walk nodes fuel 395 = List.range' 395 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 395).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_396 (fuel : Nat) (hf : 396 < fuel) :
    walk nodes fuel 396 = List.range' 388 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 396).rule = .split 0 (1/20) 394 395 := by rfl
      simp only [walk, hr]
      rw [traversal_394 f (by omega), traversal_395 f (by omega)]
      change (List.range' 388 7 ++ List.range' (388+7) 1) ++
        [388+(7+1)] = List.range' 388 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 388) (n := 7+1)).symm

private theorem traversal_397 (fuel : Nat) (hf : 397 < fuel) :
    walk nodes fuel 397 = List.range' 387 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 397).rule = .split 3 (3/8) 387 396 := by rfl
      simp only [walk, hr]
      rw [traversal_387 f (by omega), traversal_396 f (by omega)]
      change (List.range' 387 1 ++ List.range' (387+1) 9) ++
        [387+(1+9)] = List.range' 387 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 387) (n := 1+9)).symm

private theorem traversal_398 (fuel : Nat) (hf : 398 < fuel) :
    walk nodes fuel 398 = List.range' 398 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 398).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_399 (fuel : Nat) (hf : 399 < fuel) :
    walk nodes fuel 399 = List.range' 387 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 399).rule = .split 2 (65/32) 397 398 := by rfl
      simp only [walk, hr]
      rw [traversal_397 f (by omega), traversal_398 f (by omega)]
      change (List.range' 387 11 ++ List.range' (387+11) 1) ++
        [387+(11+1)] = List.range' 387 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 387) (n := 11+1)).symm

private theorem traversal_400 (fuel : Nat) (hf : 400 < fuel) :
    walk nodes fuel 400 = List.range' 400 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 400).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_401 (fuel : Nat) (hf : 401 < fuel) :
    walk nodes fuel 401 = List.range' 387 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 401).rule = .split 1 (25/8) 399 400 := by rfl
      simp only [walk, hr]
      rw [traversal_399 f (by omega), traversal_400 f (by omega)]
      change (List.range' 387 13 ++ List.range' (387+13) 1) ++
        [387+(13+1)] = List.range' 387 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 387) (n := 13+1)).symm

theorem traversal_402 (fuel : Nat) (hf : 402 < fuel) :
    walk nodes fuel 402 = List.range' 402 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 402).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
