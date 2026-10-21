/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_563,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_564,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_601,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_602,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_603,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart08.traversal_604
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart07
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_538 (fuel : Nat) (hf : 538 < fuel) :
    walk nodes fuel 538 = List.range' 534 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 538).rule = .split 2 (2213/1024) 536 537 := by rfl
      simp only [walk, hr]
      rw [traversal_536 f (by omega), traversal_537 f (by omega)]
      change (List.range' 534 3 ++ List.range' (534+3) 1) ++
        [534+(3+1)] = List.range' 534 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 534) (n := 3+1)).symm

private theorem traversal_539 (fuel : Nat) (hf : 539 < fuel) :
    walk nodes fuel 539 = List.range' 539 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 539).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_540 (fuel : Nat) (hf : 540 < fuel) :
    walk nodes fuel 540 = List.range' 534 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 540).rule = .split 1 (595/256) 538 539 := by rfl
      simp only [walk, hr]
      rw [traversal_538 f (by omega), traversal_539 f (by omega)]
      change (List.range' 534 5 ++ List.range' (534+5) 1) ++
        [534+(5+1)] = List.range' 534 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 534) (n := 5+1)).symm

private theorem traversal_541 (fuel : Nat) (hf : 541 < fuel) :
    walk nodes fuel 541 = List.range' 541 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 541).rule = .bound .leftEnd 1 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_542 (fuel : Nat) (hf : 542 < fuel) :
    walk nodes fuel 542 = List.range' 534 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 542).rule = .split 0 (1/320) 540 541 := by rfl
      simp only [walk, hr]
      rw [traversal_540 f (by omega), traversal_541 f (by omega)]
      change (List.range' 534 7 ++ List.range' (534+7) 1) ++
        [534+(7+1)] = List.range' 534 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 534) (n := 7+1)).symm

private theorem traversal_543 (fuel : Nat) (hf : 543 < fuel) :
    walk nodes fuel 543 = List.range' 543 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 543).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_544 (fuel : Nat) (hf : 544 < fuel) :
    walk nodes fuel 544 = List.range' 534 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 544).rule = .split 3 (111/128) 542 543 := by rfl
      simp only [walk, hr]
      rw [traversal_542 f (by omega), traversal_543 f (by omega)]
      change (List.range' 534 9 ++ List.range' (534+9) 1) ++
        [534+(9+1)] = List.range' 534 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 534) (n := 9+1)).symm

private theorem traversal_545 (fuel : Nat) (hf : 545 < fuel) :
    walk nodes fuel 545 = List.range' 533 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 545).rule = .split 2 (1097/512) 533 544 := by rfl
      simp only [walk, hr]
      rw [traversal_533 f (by omega), traversal_544 f (by omega)]
      change (List.range' 533 1 ++ List.range' (533+1) 11) ++
        [533+(1+11)] = List.range' 533 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 533) (n := 1+11)).symm

private theorem traversal_546 (fuel : Nat) (hf : 546 < fuel) :
    walk nodes fuel 546 = List.range' 488 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 546).rule = .split 1 (295/128) 532 545 := by rfl
      simp only [walk, hr]
      rw [traversal_532 f (by omega), traversal_545 f (by omega)]
      change (List.range' 488 45 ++ List.range' (488+45) 13) ++
        [488+(45+13)] = List.range' 488 ((45+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 45+13)).symm

private theorem traversal_547 (fuel : Nat) (hf : 547 < fuel) :
    walk nodes fuel 547 = List.range' 547 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 547).rule = .bound .leftEnd 1 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_548 (fuel : Nat) (hf : 548 < fuel) :
    walk nodes fuel 548 = List.range' 548 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 548).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_549 (fuel : Nat) (hf : 549 < fuel) :
    walk nodes fuel 549 = List.range' 549 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 549).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_550 (fuel : Nat) (hf : 550 < fuel) :
    walk nodes fuel 550 = List.range' 548 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 550).rule = .split 3 (111/128) 548 549 := by rfl
      simp only [walk, hr]
      rw [traversal_548 f (by omega), traversal_549 f (by omega)]
      change (List.range' 548 1 ++ List.range' (548+1) 1) ++
        [548+(1+1)] = List.range' 548 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 548) (n := 1+1)).symm

private theorem traversal_551 (fuel : Nat) (hf : 551 < fuel) :
    walk nodes fuel 551 = List.range' 547 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 551).rule = .split 2 (1097/512) 547 550 := by rfl
      simp only [walk, hr]
      rw [traversal_547 f (by omega), traversal_550 f (by omega)]
      change (List.range' 547 1 ++ List.range' (547+1) 3) ++
        [547+(1+3)] = List.range' 547 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 547) (n := 1+3)).symm

private theorem traversal_552 (fuel : Nat) (hf : 552 < fuel) :
    walk nodes fuel 552 = List.range' 552 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 552).rule = .bound .leftEnd 1 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_553 (fuel : Nat) (hf : 553 < fuel) :
    walk nodes fuel 553 = List.range' 547 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 553).rule = .split 1 (295/128) 551 552 := by rfl
      simp only [walk, hr]
      rw [traversal_551 f (by omega), traversal_552 f (by omega)]
      change (List.range' 547 5 ++ List.range' (547+5) 1) ++
        [547+(5+1)] = List.range' 547 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 547) (n := 5+1)).symm

private theorem traversal_554 (fuel : Nat) (hf : 554 < fuel) :
    walk nodes fuel 554 = List.range' 488 67 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 554).rule = .split 0 (1/160) 546 553 := by rfl
      simp only [walk, hr]
      rw [traversal_546 f (by omega), traversal_553 f (by omega)]
      change (List.range' 488 59 ++ List.range' (488+59) 7) ++
        [488+(59+7)] = List.range' 488 ((59+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 59+7)).symm

private theorem traversal_555 (fuel : Nat) (hf : 555 < fuel) :
    walk nodes fuel 555 = List.range' 555 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 555).rule = .bound .leftEnd 1 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_556 (fuel : Nat) (hf : 556 < fuel) :
    walk nodes fuel 556 = List.range' 488 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 556).rule = .split 3 (57/64) 554 555 := by rfl
      simp only [walk, hr]
      rw [traversal_554 f (by omega), traversal_555 f (by omega)]
      change (List.range' 488 67 ++ List.range' (488+67) 1) ++
        [488+(67+1)] = List.range' 488 ((67+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 67+1)).symm

private theorem traversal_557 (fuel : Nat) (hf : 557 < fuel) :
    walk nodes fuel 557 = List.range' 487 71 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 557).rule = .split 2 (539/256) 487 556 := by rfl
      simp only [walk, hr]
      rw [traversal_487 f (by omega), traversal_556 f (by omega)]
      change (List.range' 487 1 ++ List.range' (487+1) 69) ++
        [487+(1+69)] = List.range' 487 ((1+69)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 487) (n := 1+69)).symm

private theorem traversal_558 (fuel : Nat) (hf : 558 < fuel) :
    walk nodes fuel 558 = List.range' 486 73 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 558).rule = .split 1 (145/64) 486 557 := by rfl
      simp only [walk, hr]
      rw [traversal_486 f (by omega), traversal_557 f (by omega)]
      change (List.range' 486 1 ++ List.range' (486+1) 71) ++
        [486+(1+71)] = List.range' 486 ((1+71)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 486) (n := 1+71)).symm

private theorem traversal_559 (fuel : Nat) (hf : 559 < fuel) :
    walk nodes fuel 559 = List.range' 559 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 559).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_560 (fuel : Nat) (hf : 560 < fuel) :
    walk nodes fuel 560 = List.range' 560 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 560).rule = .bound .leftEnd 1 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_561 (fuel : Nat) (hf : 561 < fuel) :
    walk nodes fuel 561 = List.range' 559 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 561).rule = .split 1 (145/64) 559 560 := by rfl
      simp only [walk, hr]
      rw [traversal_559 f (by omega), traversal_560 f (by omega)]
      change (List.range' 559 1 ++ List.range' (559+1) 1) ++
        [559+(1+1)] = List.range' 559 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 559) (n := 1+1)).symm

private theorem traversal_562 (fuel : Nat) (hf : 562 < fuel) :
    walk nodes fuel 562 = List.range' 486 77 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 562).rule = .split 0 (1/80) 558 561 := by rfl
      simp only [walk, hr]
      rw [traversal_558 f (by omega), traversal_561 f (by omega)]
      change (List.range' 486 73 ++ List.range' (486+73) 3) ++
        [486+(73+3)] = List.range' 486 ((73+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 486) (n := 73+3)).symm

theorem traversal_563 (fuel : Nat) (hf : 563 < fuel) :
    walk nodes fuel 563 = List.range' 435 129 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 563).rule = .split 3 (27/32) 485 562 := by rfl
      simp only [walk, hr]
      rw [traversal_485 f (by omega), traversal_562 f (by omega)]
      change (List.range' 435 51 ++ List.range' (435+51) 77) ++
        [435+(51+77)] = List.range' 435 ((51+77)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 51+77)).symm

theorem traversal_564 (fuel : Nat) (hf : 564 < fuel) :
    walk nodes fuel 564 = List.range' 564 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 564).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_565 (fuel : Nat) (hf : 565 < fuel) :
    walk nodes fuel 565 = List.range' 565 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 565).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_566 (fuel : Nat) (hf : 566 < fuel) :
    walk nodes fuel 566 = List.range' 566 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 566).rule = .bound .leftEnd 8 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_567 (fuel : Nat) (hf : 567 < fuel) :
    walk nodes fuel 567 = List.range' 567 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 567).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_568 (fuel : Nat) (hf : 568 < fuel) :
    walk nodes fuel 568 = List.range' 568 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 568).rule = .bound .leftEnd 8 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_569 (fuel : Nat) (hf : 569 < fuel) :
    walk nodes fuel 569 = List.range' 569 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 569).rule = .bound .leftEnd 8 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_570 (fuel : Nat) (hf : 570 < fuel) :
    walk nodes fuel 570 = List.range' 570 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 570).rule = .bound .leftEnd 2 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_571 (fuel : Nat) (hf : 571 < fuel) :
    walk nodes fuel 571 = List.range' 569 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 571).rule = .split 2 (2327/1024) 569 570 := by rfl
      simp only [walk, hr]
      rw [traversal_569 f (by omega), traversal_570 f (by omega)]
      change (List.range' 569 1 ++ List.range' (569+1) 1) ++
        [569+(1+1)] = List.range' 569 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 569) (n := 1+1)).symm

private theorem traversal_572 (fuel : Nat) (hf : 572 < fuel) :
    walk nodes fuel 572 = List.range' 568 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 572).rule = .split 1 (575/256) 568 571 := by rfl
      simp only [walk, hr]
      rw [traversal_568 f (by omega), traversal_571 f (by omega)]
      change (List.range' 568 1 ++ List.range' (568+1) 3) ++
        [568+(1+3)] = List.range' 568 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 568) (n := 1+3)).symm

private theorem traversal_573 (fuel : Nat) (hf : 573 < fuel) :
    walk nodes fuel 573 = List.range' 573 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 573).rule = .bound .leftEnd 2 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_574 (fuel : Nat) (hf : 574 < fuel) :
    walk nodes fuel 574 = List.range' 568 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 574).rule = .split 0 (1/320) 572 573 := by rfl
      simp only [walk, hr]
      rw [traversal_572 f (by omega), traversal_573 f (by omega)]
      change (List.range' 568 5 ++ List.range' (568+5) 1) ++
        [568+(5+1)] = List.range' 568 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 568) (n := 5+1)).symm

private theorem traversal_575 (fuel : Nat) (hf : 575 < fuel) :
    walk nodes fuel 575 = List.range' 567 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 575).rule = .split 3 (111/128) 567 574 := by rfl
      simp only [walk, hr]
      rw [traversal_567 f (by omega), traversal_574 f (by omega)]
      change (List.range' 567 1 ++ List.range' (567+1) 7) ++
        [567+(1+7)] = List.range' 567 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 567) (n := 1+7)).symm

private theorem traversal_576 (fuel : Nat) (hf : 576 < fuel) :
    walk nodes fuel 576 = List.range' 576 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 576).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_577 (fuel : Nat) (hf : 577 < fuel) :
    walk nodes fuel 577 = List.range' 567 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 577).rule = .split 2 (1173/512) 575 576 := by rfl
      simp only [walk, hr]
      rw [traversal_575 f (by omega), traversal_576 f (by omega)]
      change (List.range' 567 9 ++ List.range' (567+9) 1) ++
        [567+(9+1)] = List.range' 567 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 567) (n := 9+1)).symm

private theorem traversal_578 (fuel : Nat) (hf : 578 < fuel) :
    walk nodes fuel 578 = List.range' 566 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 578).rule = .split 1 (285/128) 566 577 := by rfl
      simp only [walk, hr]
      rw [traversal_566 f (by omega), traversal_577 f (by omega)]
      change (List.range' 566 1 ++ List.range' (566+1) 11) ++
        [566+(1+11)] = List.range' 566 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 566) (n := 1+11)).symm

private theorem traversal_579 (fuel : Nat) (hf : 579 < fuel) :
    walk nodes fuel 579 = List.range' 579 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 579).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_580 (fuel : Nat) (hf : 580 < fuel) :
    walk nodes fuel 580 = List.range' 566 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 580).rule = .split 0 (1/160) 578 579 := by rfl
      simp only [walk, hr]
      rw [traversal_578 f (by omega), traversal_579 f (by omega)]
      change (List.range' 566 13 ++ List.range' (566+13) 1) ++
        [566+(13+1)] = List.range' 566 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 566) (n := 13+1)).symm

private theorem traversal_581 (fuel : Nat) (hf : 581 < fuel) :
    walk nodes fuel 581 = List.range' 581 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 581).rule = .bound .leftEnd 8 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_582 (fuel : Nat) (hf : 582 < fuel) :
    walk nodes fuel 582 = List.range' 582 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 582).rule = .bound .leftEnd 8 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_583 (fuel : Nat) (hf : 583 < fuel) :
    walk nodes fuel 583 = List.range' 583 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 583).rule = .bound .leftEnd 8 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_584 (fuel : Nat) (hf : 584 < fuel) :
    walk nodes fuel 584 = List.range' 584 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 584).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_585 (fuel : Nat) (hf : 585 < fuel) :
    walk nodes fuel 585 = List.range' 583 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 585).rule = .split 1 (575/256) 583 584 := by rfl
      simp only [walk, hr]
      rw [traversal_583 f (by omega), traversal_584 f (by omega)]
      change (List.range' 583 1 ++ List.range' (583+1) 1) ++
        [583+(1+1)] = List.range' 583 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 583) (n := 1+1)).symm

private theorem traversal_586 (fuel : Nat) (hf : 586 < fuel) :
    walk nodes fuel 586 = List.range' 586 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 586).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_587 (fuel : Nat) (hf : 587 < fuel) :
    walk nodes fuel 587 = List.range' 583 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 587).rule = .split 0 (1/320) 585 586 := by rfl
      simp only [walk, hr]
      rw [traversal_585 f (by omega), traversal_586 f (by omega)]
      change (List.range' 583 3 ++ List.range' (583+3) 1) ++
        [583+(3+1)] = List.range' 583 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 583) (n := 3+1)).symm

private theorem traversal_588 (fuel : Nat) (hf : 588 < fuel) :
    walk nodes fuel 588 = List.range' 588 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 588).rule = .bound .leftEnd 8 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_589 (fuel : Nat) (hf : 589 < fuel) :
    walk nodes fuel 589 = List.range' 589 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 589).rule = .bound .leftEnd 3 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_590 (fuel : Nat) (hf : 590 < fuel) :
    walk nodes fuel 590 = List.range' 588 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 590).rule = .split 1 (575/256) 588 589 := by rfl
      simp only [walk, hr]
      rw [traversal_588 f (by omega), traversal_589 f (by omega)]
      change (List.range' 588 1 ++ List.range' (588+1) 1) ++
        [588+(1+1)] = List.range' 588 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 588) (n := 1+1)).symm

private theorem traversal_591 (fuel : Nat) (hf : 591 < fuel) :
    walk nodes fuel 591 = List.range' 591 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 591).rule = .bound .leftEnd 3 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_592 (fuel : Nat) (hf : 592 < fuel) :
    walk nodes fuel 592 = List.range' 588 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 592).rule = .split 0 (1/320) 590 591 := by rfl
      simp only [walk, hr]
      rw [traversal_590 f (by omega), traversal_591 f (by omega)]
      change (List.range' 588 3 ++ List.range' (588+3) 1) ++
        [588+(3+1)] = List.range' 588 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 588) (n := 3+1)).symm

private theorem traversal_593 (fuel : Nat) (hf : 593 < fuel) :
    walk nodes fuel 593 = List.range' 583 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 593).rule = .split 3 (117/128) 587 592 := by rfl
      simp only [walk, hr]
      rw [traversal_587 f (by omega), traversal_592 f (by omega)]
      change (List.range' 583 5 ++ List.range' (583+5) 5) ++
        [583+(5+5)] = List.range' 583 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 583) (n := 5+5)).symm

private theorem traversal_594 (fuel : Nat) (hf : 594 < fuel) :
    walk nodes fuel 594 = List.range' 582 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 594).rule = .split 2 (1173/512) 582 593 := by rfl
      simp only [walk, hr]
      rw [traversal_582 f (by omega), traversal_593 f (by omega)]
      change (List.range' 582 1 ++ List.range' (582+1) 11) ++
        [582+(1+11)] = List.range' 582 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 582) (n := 1+11)).symm

private theorem traversal_595 (fuel : Nat) (hf : 595 < fuel) :
    walk nodes fuel 595 = List.range' 581 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 595).rule = .split 1 (285/128) 581 594 := by rfl
      simp only [walk, hr]
      rw [traversal_581 f (by omega), traversal_594 f (by omega)]
      change (List.range' 581 1 ++ List.range' (581+1) 13) ++
        [581+(1+13)] = List.range' 581 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 581) (n := 1+13)).symm

private theorem traversal_596 (fuel : Nat) (hf : 596 < fuel) :
    walk nodes fuel 596 = List.range' 596 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 596).rule = .bound .leftEnd 8 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_597 (fuel : Nat) (hf : 597 < fuel) :
    walk nodes fuel 597 = List.range' 597 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 597).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_598 (fuel : Nat) (hf : 598 < fuel) :
    walk nodes fuel 598 = List.range' 596 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 598).rule = .split 1 (285/128) 596 597 := by rfl
      simp only [walk, hr]
      rw [traversal_596 f (by omega), traversal_597 f (by omega)]
      change (List.range' 596 1 ++ List.range' (596+1) 1) ++
        [596+(1+1)] = List.range' 596 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 596) (n := 1+1)).symm

private theorem traversal_599 (fuel : Nat) (hf : 599 < fuel) :
    walk nodes fuel 599 = List.range' 581 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 599).rule = .split 0 (1/160) 595 598 := by rfl
      simp only [walk, hr]
      rw [traversal_595 f (by omega), traversal_598 f (by omega)]
      change (List.range' 581 15 ++ List.range' (581+15) 3) ++
        [581+(15+3)] = List.range' 581 ((15+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 581) (n := 15+3)).symm

private theorem traversal_600 (fuel : Nat) (hf : 600 < fuel) :
    walk nodes fuel 600 = List.range' 566 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 600).rule = .split 3 (57/64) 580 599 := by rfl
      simp only [walk, hr]
      rw [traversal_580 f (by omega), traversal_599 f (by omega)]
      change (List.range' 566 15 ++ List.range' (566+15) 19) ++
        [566+(15+19)] = List.range' 566 ((15+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 566) (n := 15+19)).symm

theorem traversal_601 (fuel : Nat) (hf : 601 < fuel) :
    walk nodes fuel 601 = List.range' 565 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 601).rule = .split 2 (577/256) 565 600 := by rfl
      simp only [walk, hr]
      rw [traversal_565 f (by omega), traversal_600 f (by omega)]
      change (List.range' 565 1 ++ List.range' (565+1) 35) ++
        [565+(1+35)] = List.range' 565 ((1+35)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 565) (n := 1+35)).symm

theorem traversal_602 (fuel : Nat) (hf : 602 < fuel) :
    walk nodes fuel 602 = List.range' 602 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 602).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_603 (fuel : Nat) (hf : 603 < fuel) :
    walk nodes fuel 603 = List.range' 603 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 603).rule = .bound .leftEnd 8 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_604 (fuel : Nat) (hf : 604 < fuel) :
    walk nodes fuel 604 = List.range' 604 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 604).rule = .bound .leftEnd 8 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
