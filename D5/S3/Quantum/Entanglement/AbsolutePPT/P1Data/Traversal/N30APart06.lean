/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart06
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart06
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart06.traversal_422,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart06.traversal_423,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart06.traversal_468
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart05
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_403 (fuel : Nat) (hf : 403 < fuel) :
    walk nodes fuel 403 = List.range' 403 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 403).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_404 (fuel : Nat) (hf : 404 < fuel) :
    walk nodes fuel 404 = List.range' 404 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 404).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_405 (fuel : Nat) (hf : 405 < fuel) :
    walk nodes fuel 405 = List.range' 403 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 405).rule = .split 0 (1/20) 403 404 := by rfl
      simp only [walk, hr]
      rw [traversal_403 f (by omega), traversal_404 f (by omega)]
      change (List.range' 403 1 ++ List.range' (403+1) 1) ++
        [403+(1+1)] = List.range' 403 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 403) (n := 1+1)).symm

private theorem traversal_406 (fuel : Nat) (hf : 406 < fuel) :
    walk nodes fuel 406 = List.range' 406 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 406).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_407 (fuel : Nat) (hf : 407 < fuel) :
    walk nodes fuel 407 = List.range' 403 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 407).rule = .split 3 (9/8) 405 406 := by rfl
      simp only [walk, hr]
      rw [traversal_405 f (by omega), traversal_406 f (by omega)]
      change (List.range' 403 3 ++ List.range' (403+3) 1) ++
        [403+(3+1)] = List.range' 403 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 403) (n := 3+1)).symm

private theorem traversal_408 (fuel : Nat) (hf : 408 < fuel) :
    walk nodes fuel 408 = List.range' 402 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 408).rule = .split 2 (65/32) 402 407 := by rfl
      simp only [walk, hr]
      rw [traversal_402 f (by omega), traversal_407 f (by omega)]
      change (List.range' 402 1 ++ List.range' (402+1) 5) ++
        [402+(1+5)] = List.range' 402 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 402) (n := 1+5)).symm

private theorem traversal_409 (fuel : Nat) (hf : 409 < fuel) :
    walk nodes fuel 409 = List.range' 409 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 409).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_410 (fuel : Nat) (hf : 410 < fuel) :
    walk nodes fuel 410 = List.range' 402 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 410).rule = .split 1 (25/8) 408 409 := by rfl
      simp only [walk, hr]
      rw [traversal_408 f (by omega), traversal_409 f (by omega)]
      change (List.range' 402 7 ++ List.range' (402+7) 1) ++
        [402+(7+1)] = List.range' 402 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 402) (n := 7+1)).symm

private theorem traversal_411 (fuel : Nat) (hf : 411 < fuel) :
    walk nodes fuel 411 = List.range' 387 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 411).rule = .split 3 (3/4) 401 410 := by rfl
      simp only [walk, hr]
      rw [traversal_401 f (by omega), traversal_410 f (by omega)]
      change (List.range' 387 15 ++ List.range' (387+15) 9) ++
        [387+(15+9)] = List.range' 387 ((15+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 387) (n := 15+9)).symm

private theorem traversal_412 (fuel : Nat) (hf : 412 < fuel) :
    walk nodes fuel 412 = List.range' 364 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 412).rule = .split 2 (23/16) 386 411 := by rfl
      simp only [walk, hr]
      rw [traversal_386 f (by omega), traversal_411 f (by omega)]
      change (List.range' 364 23 ++ List.range' (364+23) 25) ++
        [364+(23+25)] = List.range' 364 ((23+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 23+25)).symm

private theorem traversal_413 (fuel : Nat) (hf : 413 < fuel) :
    walk nodes fuel 413 = List.range' 413 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 413).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_414 (fuel : Nat) (hf : 414 < fuel) :
    walk nodes fuel 414 = List.range' 414 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 414).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_415 (fuel : Nat) (hf : 415 < fuel) :
    walk nodes fuel 415 = List.range' 413 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 415).rule = .split 2 (23/16) 413 414 := by rfl
      simp only [walk, hr]
      rw [traversal_413 f (by omega), traversal_414 f (by omega)]
      change (List.range' 413 1 ++ List.range' (413+1) 1) ++
        [413+(1+1)] = List.range' 413 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 413) (n := 1+1)).symm

private theorem traversal_416 (fuel : Nat) (hf : 416 < fuel) :
    walk nodes fuel 416 = List.range' 364 53 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 416).rule = .split 1 (15/4) 412 415 := by rfl
      simp only [walk, hr]
      rw [traversal_412 f (by omega), traversal_415 f (by omega)]
      change (List.range' 364 49 ++ List.range' (364+49) 3) ++
        [364+(49+3)] = List.range' 364 ((49+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 49+3)).symm

private theorem traversal_417 (fuel : Nat) (hf : 417 < fuel) :
    walk nodes fuel 417 = List.range' 417 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 417).rule = .bound .leftEnd 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_418 (fuel : Nat) (hf : 418 < fuel) :
    walk nodes fuel 418 = List.range' 364 55 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 418).rule = .split 3 (3/2) 416 417 := by rfl
      simp only [walk, hr]
      rw [traversal_416 f (by omega), traversal_417 f (by omega)]
      change (List.range' 364 53 ++ List.range' (364+53) 1) ++
        [364+(53+1)] = List.range' 364 ((53+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 53+1)).symm

private theorem traversal_419 (fuel : Nat) (hf : 419 < fuel) :
    walk nodes fuel 419 = List.range' 419 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 419).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_420 (fuel : Nat) (hf : 420 < fuel) :
    walk nodes fuel 420 = List.range' 364 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 420).rule = .split 2 (21/8) 418 419 := by rfl
      simp only [walk, hr]
      rw [traversal_418 f (by omega), traversal_419 f (by omega)]
      change (List.range' 364 55 ++ List.range' (364+55) 1) ++
        [364+(55+1)] = List.range' 364 ((55+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 364) (n := 55+1)).symm

private theorem traversal_421 (fuel : Nat) (hf : 421 < fuel) :
    walk nodes fuel 421 = List.range' 1 421 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 421).rule = .split 1 (5/2) 363 420 := by rfl
      simp only [walk, hr]
      rw [traversal_363 f (by omega), traversal_420 f (by omega)]
      change (List.range' 1 363 ++ List.range' (1+363) 57) ++
        [1+(363+57)] = List.range' 1 ((363+57)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 363+57)).symm

theorem traversal_422 (fuel : Nat) (hf : 422 < fuel) :
    walk nodes fuel 422 = List.range' 0 423 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 422).rule = .split 2 (1/4) 0 421 := by rfl
      simp only [walk, hr]
      rw [traversal_0 f (by omega), traversal_421 f (by omega)]
      change (List.range' 0 1 ++ List.range' (0+1) 421) ++
        [0+(1+421)] = List.range' 0 ((1+421)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 1+421)).symm

theorem traversal_423 (fuel : Nat) (hf : 423 < fuel) :
    walk nodes fuel 423 = List.range' 423 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 423).rule = .bound .vertex 8 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_424 (fuel : Nat) (hf : 424 < fuel) :
    walk nodes fuel 424 = List.range' 424 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 424).rule = .bound .leftEnd 5 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_425 (fuel : Nat) (hf : 425 < fuel) :
    walk nodes fuel 425 = List.range' 425 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 425).rule = .bound .leftEnd 1 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_426 (fuel : Nat) (hf : 426 < fuel) :
    walk nodes fuel 426 = List.range' 424 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 426).rule = .split 0 (3/20) 424 425 := by rfl
      simp only [walk, hr]
      rw [traversal_424 f (by omega), traversal_425 f (by omega)]
      change (List.range' 424 1 ++ List.range' (424+1) 1) ++
        [424+(1+1)] = List.range' 424 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 1+1)).symm

private theorem traversal_427 (fuel : Nat) (hf : 427 < fuel) :
    walk nodes fuel 427 = List.range' 427 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 427).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_428 (fuel : Nat) (hf : 428 < fuel) :
    walk nodes fuel 428 = List.range' 424 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 428).rule = .split 3 (3/8) 426 427 := by rfl
      simp only [walk, hr]
      rw [traversal_426 f (by omega), traversal_427 f (by omega)]
      change (List.range' 424 3 ++ List.range' (424+3) 1) ++
        [424+(3+1)] = List.range' 424 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 3+1)).symm

private theorem traversal_429 (fuel : Nat) (hf : 429 < fuel) :
    walk nodes fuel 429 = List.range' 429 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 429).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_430 (fuel : Nat) (hf : 430 < fuel) :
    walk nodes fuel 430 = List.range' 430 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 430).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_431 (fuel : Nat) (hf : 431 < fuel) :
    walk nodes fuel 431 = List.range' 429 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 431).rule = .split 1 (25/16) 429 430 := by rfl
      simp only [walk, hr]
      rw [traversal_429 f (by omega), traversal_430 f (by omega)]
      change (List.range' 429 1 ++ List.range' (429+1) 1) ++
        [429+(1+1)] = List.range' 429 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 1+1)).symm

private theorem traversal_432 (fuel : Nat) (hf : 432 < fuel) :
    walk nodes fuel 432 = List.range' 432 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 432).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_433 (fuel : Nat) (hf : 433 < fuel) :
    walk nodes fuel 433 = List.range' 429 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 433).rule = .split 0 (3/20) 431 432 := by rfl
      simp only [walk, hr]
      rw [traversal_431 f (by omega), traversal_432 f (by omega)]
      change (List.range' 429 3 ++ List.range' (429+3) 1) ++
        [429+(3+1)] = List.range' 429 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 3+1)).symm

private theorem traversal_434 (fuel : Nat) (hf : 434 < fuel) :
    walk nodes fuel 434 = List.range' 434 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 434).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_435 (fuel : Nat) (hf : 435 < fuel) :
    walk nodes fuel 435 = List.range' 429 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 435).rule = .split 3 (3/8) 433 434 := by rfl
      simp only [walk, hr]
      rw [traversal_433 f (by omega), traversal_434 f (by omega)]
      change (List.range' 429 5 ++ List.range' (429+5) 1) ++
        [429+(5+1)] = List.range' 429 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 5+1)).symm

private theorem traversal_436 (fuel : Nat) (hf : 436 < fuel) :
    walk nodes fuel 436 = List.range' 424 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 436).rule = .split 2 (5/8) 428 435 := by rfl
      simp only [walk, hr]
      rw [traversal_428 f (by omega), traversal_435 f (by omega)]
      change (List.range' 424 5 ++ List.range' (424+5) 7) ++
        [424+(5+7)] = List.range' 424 ((5+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 5+7)).symm

private theorem traversal_437 (fuel : Nat) (hf : 437 < fuel) :
    walk nodes fuel 437 = List.range' 437 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 437).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_438 (fuel : Nat) (hf : 438 < fuel) :
    walk nodes fuel 438 = List.range' 438 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 438).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_439 (fuel : Nat) (hf : 439 < fuel) :
    walk nodes fuel 439 = List.range' 439 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 439).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_440 (fuel : Nat) (hf : 440 < fuel) :
    walk nodes fuel 440 = List.range' 438 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 440).rule = .split 3 (3/8) 438 439 := by rfl
      simp only [walk, hr]
      rw [traversal_438 f (by omega), traversal_439 f (by omega)]
      change (List.range' 438 1 ++ List.range' (438+1) 1) ++
        [438+(1+1)] = List.range' 438 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 438) (n := 1+1)).symm

private theorem traversal_441 (fuel : Nat) (hf : 441 < fuel) :
    walk nodes fuel 441 = List.range' 437 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 441).rule = .split 2 (5/8) 437 440 := by rfl
      simp only [walk, hr]
      rw [traversal_437 f (by omega), traversal_440 f (by omega)]
      change (List.range' 437 1 ++ List.range' (437+1) 3) ++
        [437+(1+3)] = List.range' 437 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 437) (n := 1+3)).symm

private theorem traversal_442 (fuel : Nat) (hf : 442 < fuel) :
    walk nodes fuel 442 = List.range' 424 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 442).rule = .split 1 (15/8) 436 441 := by rfl
      simp only [walk, hr]
      rw [traversal_436 f (by omega), traversal_441 f (by omega)]
      change (List.range' 424 13 ++ List.range' (424+13) 5) ++
        [424+(13+5)] = List.range' 424 ((13+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 13+5)).symm

private theorem traversal_443 (fuel : Nat) (hf : 443 < fuel) :
    walk nodes fuel 443 = List.range' 443 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 443).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_444 (fuel : Nat) (hf : 444 < fuel) :
    walk nodes fuel 444 = List.range' 444 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 444).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_445 (fuel : Nat) (hf : 445 < fuel) :
    walk nodes fuel 445 = List.range' 445 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 445).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_446 (fuel : Nat) (hf : 446 < fuel) :
    walk nodes fuel 446 = List.range' 444 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 446).rule = .split 3 (3/8) 444 445 := by rfl
      simp only [walk, hr]
      rw [traversal_444 f (by omega), traversal_445 f (by omega)]
      change (List.range' 444 1 ++ List.range' (444+1) 1) ++
        [444+(1+1)] = List.range' 444 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 444) (n := 1+1)).symm

private theorem traversal_447 (fuel : Nat) (hf : 447 < fuel) :
    walk nodes fuel 447 = List.range' 443 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 447).rule = .split 2 (5/8) 443 446 := by rfl
      simp only [walk, hr]
      rw [traversal_443 f (by omega), traversal_446 f (by omega)]
      change (List.range' 443 1 ++ List.range' (443+1) 3) ++
        [443+(1+3)] = List.range' 443 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 443) (n := 1+3)).symm

private theorem traversal_448 (fuel : Nat) (hf : 448 < fuel) :
    walk nodes fuel 448 = List.range' 448 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 448).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_449 (fuel : Nat) (hf : 449 < fuel) :
    walk nodes fuel 449 = List.range' 443 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 449).rule = .split 1 (15/8) 447 448 := by rfl
      simp only [walk, hr]
      rw [traversal_447 f (by omega), traversal_448 f (by omega)]
      change (List.range' 443 5 ++ List.range' (443+5) 1) ++
        [443+(5+1)] = List.range' 443 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 443) (n := 5+1)).symm

private theorem traversal_450 (fuel : Nat) (hf : 450 < fuel) :
    walk nodes fuel 450 = List.range' 424 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 450).rule = .split 0 (1/5) 442 449 := by rfl
      simp only [walk, hr]
      rw [traversal_442 f (by omega), traversal_449 f (by omega)]
      change (List.range' 424 19 ++ List.range' (424+19) 7) ++
        [424+(19+7)] = List.range' 424 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 19+7)).symm

private theorem traversal_451 (fuel : Nat) (hf : 451 < fuel) :
    walk nodes fuel 451 = List.range' 451 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 451).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_452 (fuel : Nat) (hf : 452 < fuel) :
    walk nodes fuel 452 = List.range' 424 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 452).rule = .split 3 (3/4) 450 451 := by rfl
      simp only [walk, hr]
      rw [traversal_450 f (by omega), traversal_451 f (by omega)]
      change (List.range' 424 27 ++ List.range' (424+27) 1) ++
        [424+(27+1)] = List.range' 424 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 27+1)).symm

private theorem traversal_453 (fuel : Nat) (hf : 453 < fuel) :
    walk nodes fuel 453 = List.range' 453 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 453).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_454 (fuel : Nat) (hf : 454 < fuel) :
    walk nodes fuel 454 = List.range' 454 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 454).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_455 (fuel : Nat) (hf : 455 < fuel) :
    walk nodes fuel 455 = List.range' 453 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 455).rule = .split 3 (3/8) 453 454 := by rfl
      simp only [walk, hr]
      rw [traversal_453 f (by omega), traversal_454 f (by omega)]
      change (List.range' 453 1 ++ List.range' (453+1) 1) ++
        [453+(1+1)] = List.range' 453 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 453) (n := 1+1)).symm

private theorem traversal_456 (fuel : Nat) (hf : 456 < fuel) :
    walk nodes fuel 456 = List.range' 456 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 456).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_457 (fuel : Nat) (hf : 457 < fuel) :
    walk nodes fuel 457 = List.range' 453 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 457).rule = .split 2 (15/8) 455 456 := by rfl
      simp only [walk, hr]
      rw [traversal_455 f (by omega), traversal_456 f (by omega)]
      change (List.range' 453 3 ++ List.range' (453+3) 1) ++
        [453+(3+1)] = List.range' 453 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 453) (n := 3+1)).symm

private theorem traversal_458 (fuel : Nat) (hf : 458 < fuel) :
    walk nodes fuel 458 = List.range' 458 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 458).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_459 (fuel : Nat) (hf : 459 < fuel) :
    walk nodes fuel 459 = List.range' 453 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 459).rule = .split 1 (15/8) 457 458 := by rfl
      simp only [walk, hr]
      rw [traversal_457 f (by omega), traversal_458 f (by omega)]
      change (List.range' 453 5 ++ List.range' (453+5) 1) ++
        [453+(5+1)] = List.range' 453 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 453) (n := 5+1)).symm

private theorem traversal_460 (fuel : Nat) (hf : 460 < fuel) :
    walk nodes fuel 460 = List.range' 460 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 460).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_461 (fuel : Nat) (hf : 461 < fuel) :
    walk nodes fuel 461 = List.range' 453 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 461).rule = .split 0 (1/5) 459 460 := by rfl
      simp only [walk, hr]
      rw [traversal_459 f (by omega), traversal_460 f (by omega)]
      change (List.range' 453 7 ++ List.range' (453+7) 1) ++
        [453+(7+1)] = List.range' 453 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 453) (n := 7+1)).symm

private theorem traversal_462 (fuel : Nat) (hf : 462 < fuel) :
    walk nodes fuel 462 = List.range' 462 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 462).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_463 (fuel : Nat) (hf : 463 < fuel) :
    walk nodes fuel 463 = List.range' 463 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 463).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_464 (fuel : Nat) (hf : 464 < fuel) :
    walk nodes fuel 464 = List.range' 462 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 464).rule = .split 1 (15/8) 462 463 := by rfl
      simp only [walk, hr]
      rw [traversal_462 f (by omega), traversal_463 f (by omega)]
      change (List.range' 462 1 ++ List.range' (462+1) 1) ++
        [462+(1+1)] = List.range' 462 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 462) (n := 1+1)).symm

private theorem traversal_465 (fuel : Nat) (hf : 465 < fuel) :
    walk nodes fuel 465 = List.range' 465 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 465).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_466 (fuel : Nat) (hf : 466 < fuel) :
    walk nodes fuel 466 = List.range' 462 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 466).rule = .split 0 (1/5) 464 465 := by rfl
      simp only [walk, hr]
      rw [traversal_464 f (by omega), traversal_465 f (by omega)]
      change (List.range' 462 3 ++ List.range' (462+3) 1) ++
        [462+(3+1)] = List.range' 462 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 462) (n := 3+1)).symm

private theorem traversal_467 (fuel : Nat) (hf : 467 < fuel) :
    walk nodes fuel 467 = List.range' 453 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 467).rule = .split 3 (3/4) 461 466 := by rfl
      simp only [walk, hr]
      rw [traversal_461 f (by omega), traversal_466 f (by omega)]
      change (List.range' 453 9 ++ List.range' (453+9) 5) ++
        [453+(9+5)] = List.range' 453 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 453) (n := 9+5)).symm

theorem traversal_468 (fuel : Nat) (hf : 468 < fuel) :
    walk nodes fuel 468 = List.range' 424 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 468).rule = .split 2 (5/4) 452 467 := by rfl
      simp only [walk, hr]
      rw [traversal_452 f (by omega), traversal_467 f (by omega)]
      change (List.range' 424 29 ++ List.range' (424+29) 15) ++
        [424+(29+15)] = List.range' 424 ((29+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 424) (n := 29+15)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
