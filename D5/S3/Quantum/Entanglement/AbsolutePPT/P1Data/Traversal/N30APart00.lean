/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_0,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_1,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_38,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_65,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_66,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart00.traversal_67
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
theorem traversal_0 (fuel : Nat) (hf : 0 < fuel) :
    walk nodes fuel 0 = List.range' 0 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 0).rule = .localRegion := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1 (fuel : Nat) (hf : 1 < fuel) :
    walk nodes fuel 1 = List.range' 1 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1).rule = .bound .leftEnd 5 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2 (fuel : Nat) (hf : 2 < fuel) :
    walk nodes fuel 2 = List.range' 2 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_3 (fuel : Nat) (hf : 3 < fuel) :
    walk nodes fuel 3 = List.range' 3 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 3).rule = .bound .leftEnd 5 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_4 (fuel : Nat) (hf : 4 < fuel) :
    walk nodes fuel 4 = List.range' 4 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 4).rule = .bound .leftEnd 4 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_5 (fuel : Nat) (hf : 5 < fuel) :
    walk nodes fuel 5 = List.range' 5 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 5).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_6 (fuel : Nat) (hf : 6 < fuel) :
    walk nodes fuel 6 = List.range' 4 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 6).rule = .split 3 (3/16) 4 5 := by rfl
      simp only [walk, hr]
      rw [traversal_4 f (by omega), traversal_5 f (by omega)]
      change (List.range' 4 1 ++ List.range' (4+1) 1) ++
        [4+(1+1)] = List.range' 4 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 4) (n := 1+1)).symm

private theorem traversal_7 (fuel : Nat) (hf : 7 < fuel) :
    walk nodes fuel 7 = List.range' 3 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 7).rule = .split 2 (35/64) 3 6 := by rfl
      simp only [walk, hr]
      rw [traversal_3 f (by omega), traversal_6 f (by omega)]
      change (List.range' 3 1 ++ List.range' (3+1) 3) ++
        [3+(1+3)] = List.range' 3 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 3) (n := 1+3)).symm

private theorem traversal_8 (fuel : Nat) (hf : 8 < fuel) :
    walk nodes fuel 8 = List.range' 2 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 8).rule = .split 1 (25/16) 2 7 := by rfl
      simp only [walk, hr]
      rw [traversal_2 f (by omega), traversal_7 f (by omega)]
      change (List.range' 2 1 ++ List.range' (2+1) 5) ++
        [2+(1+5)] = List.range' 2 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 1+5)).symm

private theorem traversal_9 (fuel : Nat) (hf : 9 < fuel) :
    walk nodes fuel 9 = List.range' 9 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 9).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_10 (fuel : Nat) (hf : 10 < fuel) :
    walk nodes fuel 10 = List.range' 10 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 10).rule = .bound .leftEnd 5 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_11 (fuel : Nat) (hf : 11 < fuel) :
    walk nodes fuel 11 = List.range' 11 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 11).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_12 (fuel : Nat) (hf : 12 < fuel) :
    walk nodes fuel 12 = List.range' 12 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 12).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_13 (fuel : Nat) (hf : 13 < fuel) :
    walk nodes fuel 13 = List.range' 11 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 13).rule = .split 3 (3/16) 11 12 := by rfl
      simp only [walk, hr]
      rw [traversal_11 f (by omega), traversal_12 f (by omega)]
      change (List.range' 11 1 ++ List.range' (11+1) 1) ++
        [11+(1+1)] = List.range' 11 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 11) (n := 1+1)).symm

private theorem traversal_14 (fuel : Nat) (hf : 14 < fuel) :
    walk nodes fuel 14 = List.range' 10 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 14).rule = .split 2 (35/64) 10 13 := by rfl
      simp only [walk, hr]
      rw [traversal_10 f (by omega), traversal_13 f (by omega)]
      change (List.range' 10 1 ++ List.range' (10+1) 3) ++
        [10+(1+3)] = List.range' 10 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 10) (n := 1+3)).symm

private theorem traversal_15 (fuel : Nat) (hf : 15 < fuel) :
    walk nodes fuel 15 = List.range' 9 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 15).rule = .split 1 (25/16) 9 14 := by rfl
      simp only [walk, hr]
      rw [traversal_9 f (by omega), traversal_14 f (by omega)]
      change (List.range' 9 1 ++ List.range' (9+1) 5) ++
        [9+(1+5)] = List.range' 9 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 9) (n := 1+5)).symm

private theorem traversal_16 (fuel : Nat) (hf : 16 < fuel) :
    walk nodes fuel 16 = List.range' 2 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 16).rule = .split 0 (1/20) 8 15 := by rfl
      simp only [walk, hr]
      rw [traversal_8 f (by omega), traversal_15 f (by omega)]
      change (List.range' 2 7 ++ List.range' (2+7) 7) ++
        [2+(7+7)] = List.range' 2 ((7+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 7+7)).symm

private theorem traversal_17 (fuel : Nat) (hf : 17 < fuel) :
    walk nodes fuel 17 = List.range' 17 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 17).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_18 (fuel : Nat) (hf : 18 < fuel) :
    walk nodes fuel 18 = List.range' 2 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 18).rule = .split 3 (3/8) 16 17 := by rfl
      simp only [walk, hr]
      rw [traversal_16 f (by omega), traversal_17 f (by omega)]
      change (List.range' 2 15 ++ List.range' (2+15) 1) ++
        [2+(15+1)] = List.range' 2 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 15+1)).symm

private theorem traversal_19 (fuel : Nat) (hf : 19 < fuel) :
    walk nodes fuel 19 = List.range' 19 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 19).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_20 (fuel : Nat) (hf : 20 < fuel) :
    walk nodes fuel 20 = List.range' 20 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 20).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_21 (fuel : Nat) (hf : 21 < fuel) :
    walk nodes fuel 21 = List.range' 21 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 21).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_22 (fuel : Nat) (hf : 22 < fuel) :
    walk nodes fuel 22 = List.range' 20 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 22).rule = .split 3 (3/16) 20 21 := by rfl
      simp only [walk, hr]
      rw [traversal_20 f (by omega), traversal_21 f (by omega)]
      change (List.range' 20 1 ++ List.range' (20+1) 1) ++
        [20+(1+1)] = List.range' 20 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 20) (n := 1+1)).symm

private theorem traversal_23 (fuel : Nat) (hf : 23 < fuel) :
    walk nodes fuel 23 = List.range' 23 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 23).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_24 (fuel : Nat) (hf : 24 < fuel) :
    walk nodes fuel 24 = List.range' 24 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 24).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_25 (fuel : Nat) (hf : 25 < fuel) :
    walk nodes fuel 25 = List.range' 23 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 25).rule = .split 3 (3/16) 23 24 := by rfl
      simp only [walk, hr]
      rw [traversal_23 f (by omega), traversal_24 f (by omega)]
      change (List.range' 23 1 ++ List.range' (23+1) 1) ++
        [23+(1+1)] = List.range' 23 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 23) (n := 1+1)).symm

private theorem traversal_26 (fuel : Nat) (hf : 26 < fuel) :
    walk nodes fuel 26 = List.range' 20 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 26).rule = .split 2 (73/64) 22 25 := by rfl
      simp only [walk, hr]
      rw [traversal_22 f (by omega), traversal_25 f (by omega)]
      change (List.range' 20 3 ++ List.range' (20+3) 3) ++
        [20+(3+3)] = List.range' 20 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 20) (n := 3+3)).symm

private theorem traversal_27 (fuel : Nat) (hf : 27 < fuel) :
    walk nodes fuel 27 = List.range' 19 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 27).rule = .split 1 (25/16) 19 26 := by rfl
      simp only [walk, hr]
      rw [traversal_19 f (by omega), traversal_26 f (by omega)]
      change (List.range' 19 1 ++ List.range' (19+1) 7) ++
        [19+(1+7)] = List.range' 19 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 19) (n := 1+7)).symm

private theorem traversal_28 (fuel : Nat) (hf : 28 < fuel) :
    walk nodes fuel 28 = List.range' 28 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 28).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_29 (fuel : Nat) (hf : 29 < fuel) :
    walk nodes fuel 29 = List.range' 29 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 29).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_30 (fuel : Nat) (hf : 30 < fuel) :
    walk nodes fuel 30 = List.range' 30 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 30).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_31 (fuel : Nat) (hf : 31 < fuel) :
    walk nodes fuel 31 = List.range' 29 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 31).rule = .split 3 (3/16) 29 30 := by rfl
      simp only [walk, hr]
      rw [traversal_29 f (by omega), traversal_30 f (by omega)]
      change (List.range' 29 1 ++ List.range' (29+1) 1) ++
        [29+(1+1)] = List.range' 29 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 29) (n := 1+1)).symm

private theorem traversal_32 (fuel : Nat) (hf : 32 < fuel) :
    walk nodes fuel 32 = List.range' 32 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 32).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_33 (fuel : Nat) (hf : 33 < fuel) :
    walk nodes fuel 33 = List.range' 29 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 33).rule = .split 2 (73/64) 31 32 := by rfl
      simp only [walk, hr]
      rw [traversal_31 f (by omega), traversal_32 f (by omega)]
      change (List.range' 29 3 ++ List.range' (29+3) 1) ++
        [29+(3+1)] = List.range' 29 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 29) (n := 3+1)).symm

private theorem traversal_34 (fuel : Nat) (hf : 34 < fuel) :
    walk nodes fuel 34 = List.range' 28 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 34).rule = .split 1 (25/16) 28 33 := by rfl
      simp only [walk, hr]
      rw [traversal_28 f (by omega), traversal_33 f (by omega)]
      change (List.range' 28 1 ++ List.range' (28+1) 5) ++
        [28+(1+5)] = List.range' 28 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 28) (n := 1+5)).symm

private theorem traversal_35 (fuel : Nat) (hf : 35 < fuel) :
    walk nodes fuel 35 = List.range' 19 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 35).rule = .split 0 (1/20) 27 34 := by rfl
      simp only [walk, hr]
      rw [traversal_27 f (by omega), traversal_34 f (by omega)]
      change (List.range' 19 9 ++ List.range' (19+9) 7) ++
        [19+(9+7)] = List.range' 19 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 19) (n := 9+7)).symm

private theorem traversal_36 (fuel : Nat) (hf : 36 < fuel) :
    walk nodes fuel 36 = List.range' 36 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 36).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_37 (fuel : Nat) (hf : 37 < fuel) :
    walk nodes fuel 37 = List.range' 19 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 37).rule = .split 3 (3/8) 35 36 := by rfl
      simp only [walk, hr]
      rw [traversal_35 f (by omega), traversal_36 f (by omega)]
      change (List.range' 19 17 ++ List.range' (19+17) 1) ++
        [19+(17+1)] = List.range' 19 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 19) (n := 17+1)).symm

theorem traversal_38 (fuel : Nat) (hf : 38 < fuel) :
    walk nodes fuel 38 = List.range' 2 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 38).rule = .split 2 (27/32) 18 37 := by rfl
      simp only [walk, hr]
      rw [traversal_18 f (by omega), traversal_37 f (by omega)]
      change (List.range' 2 17 ++ List.range' (2+17) 19) ++
        [2+(17+19)] = List.range' 2 ((17+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 17+19)).symm

private theorem traversal_39 (fuel : Nat) (hf : 39 < fuel) :
    walk nodes fuel 39 = List.range' 39 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 39).rule = .bound .leftEnd 2 (227023/49152) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_40 (fuel : Nat) (hf : 40 < fuel) :
    walk nodes fuel 40 = List.range' 40 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 40).rule = .bound .leftEnd 8 (23509/12288) (132987/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_41 (fuel : Nat) (hf : 41 < fuel) :
    walk nodes fuel 41 = List.range' 39 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 41).rule = .split 3 (3/64) 39 40 := by rfl
      simp only [walk, hr]
      rw [traversal_39 f (by omega), traversal_40 f (by omega)]
      change (List.range' 39 1 ++ List.range' (39+1) 1) ++
        [39+(1+1)] = List.range' 39 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 1+1)).symm

private theorem traversal_42 (fuel : Nat) (hf : 42 < fuel) :
    walk nodes fuel 42 = List.range' 42 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 42).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_43 (fuel : Nat) (hf : 43 < fuel) :
    walk nodes fuel 43 = List.range' 39 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 43).rule = .split 2 (83/256) 41 42 := by rfl
      simp only [walk, hr]
      rw [traversal_41 f (by omega), traversal_42 f (by omega)]
      change (List.range' 39 3 ++ List.range' (39+3) 1) ++
        [39+(3+1)] = List.range' 39 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 3+1)).symm

private theorem traversal_44 (fuel : Nat) (hf : 44 < fuel) :
    walk nodes fuel 44 = List.range' 44 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 44).rule = .bound .leftEnd 2 (227023/49152) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_45 (fuel : Nat) (hf : 45 < fuel) :
    walk nodes fuel 45 = List.range' 45 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 45).rule = .bound .leftEnd 8 (23509/12288) (132987/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_46 (fuel : Nat) (hf : 46 < fuel) :
    walk nodes fuel 46 = List.range' 44 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 46).rule = .split 3 (3/64) 44 45 := by rfl
      simp only [walk, hr]
      rw [traversal_44 f (by omega), traversal_45 f (by omega)]
      change (List.range' 44 1 ++ List.range' (44+1) 1) ++
        [44+(1+1)] = List.range' 44 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 44) (n := 1+1)).symm

private theorem traversal_47 (fuel : Nat) (hf : 47 < fuel) :
    walk nodes fuel 47 = List.range' 47 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 47).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_48 (fuel : Nat) (hf : 48 < fuel) :
    walk nodes fuel 48 = List.range' 44 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 48).rule = .split 2 (83/256) 46 47 := by rfl
      simp only [walk, hr]
      rw [traversal_46 f (by omega), traversal_47 f (by omega)]
      change (List.range' 44 3 ++ List.range' (44+3) 1) ++
        [44+(3+1)] = List.range' 44 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 44) (n := 3+1)).symm

private theorem traversal_49 (fuel : Nat) (hf : 49 < fuel) :
    walk nodes fuel 49 = List.range' 39 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 49).rule = .split 1 (125/64) 43 48 := by rfl
      simp only [walk, hr]
      rw [traversal_43 f (by omega), traversal_48 f (by omega)]
      change (List.range' 39 5 ++ List.range' (39+5) 5) ++
        [39+(5+5)] = List.range' 39 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 5+5)).symm

private theorem traversal_50 (fuel : Nat) (hf : 50 < fuel) :
    walk nodes fuel 50 = List.range' 50 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 50).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_51 (fuel : Nat) (hf : 51 < fuel) :
    walk nodes fuel 51 = List.range' 39 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 51).rule = .split 0 (1/80) 49 50 := by rfl
      simp only [walk, hr]
      rw [traversal_49 f (by omega), traversal_50 f (by omega)]
      change (List.range' 39 11 ++ List.range' (39+11) 1) ++
        [39+(11+1)] = List.range' 39 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 11+1)).symm

private theorem traversal_52 (fuel : Nat) (hf : 52 < fuel) :
    walk nodes fuel 52 = List.range' 52 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 52).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_53 (fuel : Nat) (hf : 53 < fuel) :
    walk nodes fuel 53 = List.range' 39 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 53).rule = .split 3 (3/32) 51 52 := by rfl
      simp only [walk, hr]
      rw [traversal_51 f (by omega), traversal_52 f (by omega)]
      change (List.range' 39 13 ++ List.range' (39+13) 1) ++
        [39+(13+1)] = List.range' 39 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 13+1)).symm

private theorem traversal_54 (fuel : Nat) (hf : 54 < fuel) :
    walk nodes fuel 54 = List.range' 54 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 54).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_55 (fuel : Nat) (hf : 55 < fuel) :
    walk nodes fuel 55 = List.range' 55 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 55).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_56 (fuel : Nat) (hf : 56 < fuel) :
    walk nodes fuel 56 = List.range' 54 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 56).rule = .split 3 (3/32) 54 55 := by rfl
      simp only [walk, hr]
      rw [traversal_54 f (by omega), traversal_55 f (by omega)]
      change (List.range' 54 1 ++ List.range' (54+1) 1) ++
        [54+(1+1)] = List.range' 54 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 54) (n := 1+1)).symm

private theorem traversal_57 (fuel : Nat) (hf : 57 < fuel) :
    walk nodes fuel 57 = List.range' 39 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 57).rule = .split 2 (51/128) 53 56 := by rfl
      simp only [walk, hr]
      rw [traversal_53 f (by omega), traversal_56 f (by omega)]
      change (List.range' 39 15 ++ List.range' (39+15) 3) ++
        [39+(15+3)] = List.range' 39 ((15+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 15+3)).symm

private theorem traversal_58 (fuel : Nat) (hf : 58 < fuel) :
    walk nodes fuel 58 = List.range' 58 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 58).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_59 (fuel : Nat) (hf : 59 < fuel) :
    walk nodes fuel 59 = List.range' 59 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 59).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_60 (fuel : Nat) (hf : 60 < fuel) :
    walk nodes fuel 60 = List.range' 58 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 60).rule = .split 3 (3/32) 58 59 := by rfl
      simp only [walk, hr]
      rw [traversal_58 f (by omega), traversal_59 f (by omega)]
      change (List.range' 58 1 ++ List.range' (58+1) 1) ++
        [58+(1+1)] = List.range' 58 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 58) (n := 1+1)).symm

private theorem traversal_61 (fuel : Nat) (hf : 61 < fuel) :
    walk nodes fuel 61 = List.range' 61 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 61).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_62 (fuel : Nat) (hf : 62 < fuel) :
    walk nodes fuel 62 = List.range' 62 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 62).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_63 (fuel : Nat) (hf : 63 < fuel) :
    walk nodes fuel 63 = List.range' 61 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 63).rule = .split 3 (3/32) 61 62 := by rfl
      simp only [walk, hr]
      rw [traversal_61 f (by omega), traversal_62 f (by omega)]
      change (List.range' 61 1 ++ List.range' (61+1) 1) ++
        [61+(1+1)] = List.range' 61 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 61) (n := 1+1)).symm

private theorem traversal_64 (fuel : Nat) (hf : 64 < fuel) :
    walk nodes fuel 64 = List.range' 58 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 64).rule = .split 2 (51/128) 60 63 := by rfl
      simp only [walk, hr]
      rw [traversal_60 f (by omega), traversal_63 f (by omega)]
      change (List.range' 58 3 ++ List.range' (58+3) 3) ++
        [58+(3+3)] = List.range' 58 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 58) (n := 3+3)).symm

theorem traversal_65 (fuel : Nat) (hf : 65 < fuel) :
    walk nodes fuel 65 = List.range' 39 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 65).rule = .split 1 (65/32) 57 64 := by rfl
      simp only [walk, hr]
      rw [traversal_57 f (by omega), traversal_64 f (by omega)]
      change (List.range' 39 19 ++ List.range' (39+19) 7) ++
        [39+(19+7)] = List.range' 39 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 19+7)).symm

theorem traversal_66 (fuel : Nat) (hf : 66 < fuel) :
    walk nodes fuel 66 = List.range' 66 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 66).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_67 (fuel : Nat) (hf : 67 < fuel) :
    walk nodes fuel 67 = List.range' 67 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 67).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
