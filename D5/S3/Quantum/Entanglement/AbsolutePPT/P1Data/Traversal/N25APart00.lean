/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_0,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_1,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_40,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_59,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_66,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart00.traversal_67
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
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
      have hr : (node nodes 3).rule = .bound .leftEnd 0 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_4 (fuel : Nat) (hf : 4 < fuel) :
    walk nodes fuel 4 = List.range' 4 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 4).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_5 (fuel : Nat) (hf : 5 < fuel) :
    walk nodes fuel 5 = List.range' 3 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 5).rule = .split 3 (3/16) 3 4 := by rfl
      simp only [walk, hr]
      rw [traversal_3 f (by omega), traversal_4 f (by omega)]
      change (List.range' 3 1 ++ List.range' (3+1) 1) ++
        [3+(1+1)] = List.range' 3 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 3) (n := 1+1)).symm

private theorem traversal_6 (fuel : Nat) (hf : 6 < fuel) :
    walk nodes fuel 6 = List.range' 6 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 6).rule = .bound .leftEnd 4 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_7 (fuel : Nat) (hf : 7 < fuel) :
    walk nodes fuel 7 = List.range' 7 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 7).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_8 (fuel : Nat) (hf : 8 < fuel) :
    walk nodes fuel 8 = List.range' 6 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 8).rule = .split 3 (3/16) 6 7 := by rfl
      simp only [walk, hr]
      rw [traversal_6 f (by omega), traversal_7 f (by omega)]
      change (List.range' 6 1 ++ List.range' (6+1) 1) ++
        [6+(1+1)] = List.range' 6 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 6) (n := 1+1)).symm

private theorem traversal_9 (fuel : Nat) (hf : 9 < fuel) :
    walk nodes fuel 9 = List.range' 3 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 9).rule = .split 2 (35/64) 5 8 := by rfl
      simp only [walk, hr]
      rw [traversal_5 f (by omega), traversal_8 f (by omega)]
      change (List.range' 3 3 ++ List.range' (3+3) 3) ++
        [3+(3+3)] = List.range' 3 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 3) (n := 3+3)).symm

private theorem traversal_10 (fuel : Nat) (hf : 10 < fuel) :
    walk nodes fuel 10 = List.range' 2 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 10).rule = .split 1 (25/16) 2 9 := by rfl
      simp only [walk, hr]
      rw [traversal_2 f (by omega), traversal_9 f (by omega)]
      change (List.range' 2 1 ++ List.range' (2+1) 7) ++
        [2+(1+7)] = List.range' 2 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 1+7)).symm

private theorem traversal_11 (fuel : Nat) (hf : 11 < fuel) :
    walk nodes fuel 11 = List.range' 11 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 11).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_12 (fuel : Nat) (hf : 12 < fuel) :
    walk nodes fuel 12 = List.range' 12 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 12).rule = .bound .leftEnd 5 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_13 (fuel : Nat) (hf : 13 < fuel) :
    walk nodes fuel 13 = List.range' 13 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 13).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_14 (fuel : Nat) (hf : 14 < fuel) :
    walk nodes fuel 14 = List.range' 14 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 14).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_15 (fuel : Nat) (hf : 15 < fuel) :
    walk nodes fuel 15 = List.range' 13 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 15).rule = .split 3 (3/16) 13 14 := by rfl
      simp only [walk, hr]
      rw [traversal_13 f (by omega), traversal_14 f (by omega)]
      change (List.range' 13 1 ++ List.range' (13+1) 1) ++
        [13+(1+1)] = List.range' 13 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 13) (n := 1+1)).symm

private theorem traversal_16 (fuel : Nat) (hf : 16 < fuel) :
    walk nodes fuel 16 = List.range' 12 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 16).rule = .split 2 (35/64) 12 15 := by rfl
      simp only [walk, hr]
      rw [traversal_12 f (by omega), traversal_15 f (by omega)]
      change (List.range' 12 1 ++ List.range' (12+1) 3) ++
        [12+(1+3)] = List.range' 12 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 12) (n := 1+3)).symm

private theorem traversal_17 (fuel : Nat) (hf : 17 < fuel) :
    walk nodes fuel 17 = List.range' 11 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 17).rule = .split 1 (25/16) 11 16 := by rfl
      simp only [walk, hr]
      rw [traversal_11 f (by omega), traversal_16 f (by omega)]
      change (List.range' 11 1 ++ List.range' (11+1) 5) ++
        [11+(1+5)] = List.range' 11 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 11) (n := 1+5)).symm

private theorem traversal_18 (fuel : Nat) (hf : 18 < fuel) :
    walk nodes fuel 18 = List.range' 2 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 18).rule = .split 0 (1/20) 10 17 := by rfl
      simp only [walk, hr]
      rw [traversal_10 f (by omega), traversal_17 f (by omega)]
      change (List.range' 2 9 ++ List.range' (2+9) 7) ++
        [2+(9+7)] = List.range' 2 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 9+7)).symm

private theorem traversal_19 (fuel : Nat) (hf : 19 < fuel) :
    walk nodes fuel 19 = List.range' 19 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 19).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_20 (fuel : Nat) (hf : 20 < fuel) :
    walk nodes fuel 20 = List.range' 2 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 20).rule = .split 3 (3/8) 18 19 := by rfl
      simp only [walk, hr]
      rw [traversal_18 f (by omega), traversal_19 f (by omega)]
      change (List.range' 2 17 ++ List.range' (2+17) 1) ++
        [2+(17+1)] = List.range' 2 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 17+1)).symm

private theorem traversal_21 (fuel : Nat) (hf : 21 < fuel) :
    walk nodes fuel 21 = List.range' 21 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 21).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_22 (fuel : Nat) (hf : 22 < fuel) :
    walk nodes fuel 22 = List.range' 22 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 22).rule = .bound .leftEnd 4 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_23 (fuel : Nat) (hf : 23 < fuel) :
    walk nodes fuel 23 = List.range' 23 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 23).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_24 (fuel : Nat) (hf : 24 < fuel) :
    walk nodes fuel 24 = List.range' 22 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 24).rule = .split 3 (3/16) 22 23 := by rfl
      simp only [walk, hr]
      rw [traversal_22 f (by omega), traversal_23 f (by omega)]
      change (List.range' 22 1 ++ List.range' (22+1) 1) ++
        [22+(1+1)] = List.range' 22 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 22) (n := 1+1)).symm

private theorem traversal_25 (fuel : Nat) (hf : 25 < fuel) :
    walk nodes fuel 25 = List.range' 25 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 25).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_26 (fuel : Nat) (hf : 26 < fuel) :
    walk nodes fuel 26 = List.range' 26 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 26).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_27 (fuel : Nat) (hf : 27 < fuel) :
    walk nodes fuel 27 = List.range' 25 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 27).rule = .split 3 (3/16) 25 26 := by rfl
      simp only [walk, hr]
      rw [traversal_25 f (by omega), traversal_26 f (by omega)]
      change (List.range' 25 1 ++ List.range' (25+1) 1) ++
        [25+(1+1)] = List.range' 25 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 25) (n := 1+1)).symm

private theorem traversal_28 (fuel : Nat) (hf : 28 < fuel) :
    walk nodes fuel 28 = List.range' 22 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 28).rule = .split 2 (73/64) 24 27 := by rfl
      simp only [walk, hr]
      rw [traversal_24 f (by omega), traversal_27 f (by omega)]
      change (List.range' 22 3 ++ List.range' (22+3) 3) ++
        [22+(3+3)] = List.range' 22 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 22) (n := 3+3)).symm

private theorem traversal_29 (fuel : Nat) (hf : 29 < fuel) :
    walk nodes fuel 29 = List.range' 21 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 29).rule = .split 1 (25/16) 21 28 := by rfl
      simp only [walk, hr]
      rw [traversal_21 f (by omega), traversal_28 f (by omega)]
      change (List.range' 21 1 ++ List.range' (21+1) 7) ++
        [21+(1+7)] = List.range' 21 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 21) (n := 1+7)).symm

private theorem traversal_30 (fuel : Nat) (hf : 30 < fuel) :
    walk nodes fuel 30 = List.range' 30 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 30).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_31 (fuel : Nat) (hf : 31 < fuel) :
    walk nodes fuel 31 = List.range' 31 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 31).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_32 (fuel : Nat) (hf : 32 < fuel) :
    walk nodes fuel 32 = List.range' 32 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 32).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_33 (fuel : Nat) (hf : 33 < fuel) :
    walk nodes fuel 33 = List.range' 31 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 33).rule = .split 3 (3/16) 31 32 := by rfl
      simp only [walk, hr]
      rw [traversal_31 f (by omega), traversal_32 f (by omega)]
      change (List.range' 31 1 ++ List.range' (31+1) 1) ++
        [31+(1+1)] = List.range' 31 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 31) (n := 1+1)).symm

private theorem traversal_34 (fuel : Nat) (hf : 34 < fuel) :
    walk nodes fuel 34 = List.range' 34 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 34).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_35 (fuel : Nat) (hf : 35 < fuel) :
    walk nodes fuel 35 = List.range' 31 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 35).rule = .split 2 (73/64) 33 34 := by rfl
      simp only [walk, hr]
      rw [traversal_33 f (by omega), traversal_34 f (by omega)]
      change (List.range' 31 3 ++ List.range' (31+3) 1) ++
        [31+(3+1)] = List.range' 31 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 31) (n := 3+1)).symm

private theorem traversal_36 (fuel : Nat) (hf : 36 < fuel) :
    walk nodes fuel 36 = List.range' 30 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 36).rule = .split 1 (25/16) 30 35 := by rfl
      simp only [walk, hr]
      rw [traversal_30 f (by omega), traversal_35 f (by omega)]
      change (List.range' 30 1 ++ List.range' (30+1) 5) ++
        [30+(1+5)] = List.range' 30 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 30) (n := 1+5)).symm

private theorem traversal_37 (fuel : Nat) (hf : 37 < fuel) :
    walk nodes fuel 37 = List.range' 21 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 37).rule = .split 0 (1/20) 29 36 := by rfl
      simp only [walk, hr]
      rw [traversal_29 f (by omega), traversal_36 f (by omega)]
      change (List.range' 21 9 ++ List.range' (21+9) 7) ++
        [21+(9+7)] = List.range' 21 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 21) (n := 9+7)).symm

private theorem traversal_38 (fuel : Nat) (hf : 38 < fuel) :
    walk nodes fuel 38 = List.range' 38 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 38).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_39 (fuel : Nat) (hf : 39 < fuel) :
    walk nodes fuel 39 = List.range' 21 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 39).rule = .split 3 (3/8) 37 38 := by rfl
      simp only [walk, hr]
      rw [traversal_37 f (by omega), traversal_38 f (by omega)]
      change (List.range' 21 17 ++ List.range' (21+17) 1) ++
        [21+(17+1)] = List.range' 21 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 21) (n := 17+1)).symm

theorem traversal_40 (fuel : Nat) (hf : 40 < fuel) :
    walk nodes fuel 40 = List.range' 2 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 40).rule = .split 2 (27/32) 20 39 := by rfl
      simp only [walk, hr]
      rw [traversal_20 f (by omega), traversal_39 f (by omega)]
      change (List.range' 2 19 ++ List.range' (2+19) 19) ++
        [2+(19+19)] = List.range' 2 ((19+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 19+19)).symm

private theorem traversal_41 (fuel : Nat) (hf : 41 < fuel) :
    walk nodes fuel 41 = List.range' 41 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 41).rule = .bound .leftEnd 4 (227023/49152) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_42 (fuel : Nat) (hf : 42 < fuel) :
    walk nodes fuel 42 = List.range' 42 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 42).rule = .bound .leftEnd 8 (23509/12288) (132987/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_43 (fuel : Nat) (hf : 43 < fuel) :
    walk nodes fuel 43 = List.range' 41 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 43).rule = .split 3 (3/64) 41 42 := by rfl
      simp only [walk, hr]
      rw [traversal_41 f (by omega), traversal_42 f (by omega)]
      change (List.range' 41 1 ++ List.range' (41+1) 1) ++
        [41+(1+1)] = List.range' 41 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 1+1)).symm

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
    walk nodes fuel 47 = List.range' 41 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 47).rule = .split 2 (83/256) 43 46 := by rfl
      simp only [walk, hr]
      rw [traversal_43 f (by omega), traversal_46 f (by omega)]
      change (List.range' 41 3 ++ List.range' (41+3) 3) ++
        [41+(3+3)] = List.range' 41 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 3+3)).symm

private theorem traversal_48 (fuel : Nat) (hf : 48 < fuel) :
    walk nodes fuel 48 = List.range' 48 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 48).rule = .bound .leftEnd 2 (227023/49152) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_49 (fuel : Nat) (hf : 49 < fuel) :
    walk nodes fuel 49 = List.range' 49 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 49).rule = .bound .leftEnd 8 (23509/12288) (132987/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_50 (fuel : Nat) (hf : 50 < fuel) :
    walk nodes fuel 50 = List.range' 48 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 50).rule = .split 3 (3/64) 48 49 := by rfl
      simp only [walk, hr]
      rw [traversal_48 f (by omega), traversal_49 f (by omega)]
      change (List.range' 48 1 ++ List.range' (48+1) 1) ++
        [48+(1+1)] = List.range' 48 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 48) (n := 1+1)).symm

private theorem traversal_51 (fuel : Nat) (hf : 51 < fuel) :
    walk nodes fuel 51 = List.range' 51 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 51).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_52 (fuel : Nat) (hf : 52 < fuel) :
    walk nodes fuel 52 = List.range' 48 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 52).rule = .split 2 (83/256) 50 51 := by rfl
      simp only [walk, hr]
      rw [traversal_50 f (by omega), traversal_51 f (by omega)]
      change (List.range' 48 3 ++ List.range' (48+3) 1) ++
        [48+(3+1)] = List.range' 48 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 48) (n := 3+1)).symm

private theorem traversal_53 (fuel : Nat) (hf : 53 < fuel) :
    walk nodes fuel 53 = List.range' 41 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 53).rule = .split 1 (125/64) 47 52 := by rfl
      simp only [walk, hr]
      rw [traversal_47 f (by omega), traversal_52 f (by omega)]
      change (List.range' 41 7 ++ List.range' (41+7) 5) ++
        [41+(7+5)] = List.range' 41 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 7+5)).symm

private theorem traversal_54 (fuel : Nat) (hf : 54 < fuel) :
    walk nodes fuel 54 = List.range' 54 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 54).rule = .bound .leftEnd 4 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_55 (fuel : Nat) (hf : 55 < fuel) :
    walk nodes fuel 55 = List.range' 55 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 55).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_56 (fuel : Nat) (hf : 56 < fuel) :
    walk nodes fuel 56 = List.range' 54 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 56).rule = .split 1 (125/64) 54 55 := by rfl
      simp only [walk, hr]
      rw [traversal_54 f (by omega), traversal_55 f (by omega)]
      change (List.range' 54 1 ++ List.range' (54+1) 1) ++
        [54+(1+1)] = List.range' 54 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 54) (n := 1+1)).symm

private theorem traversal_57 (fuel : Nat) (hf : 57 < fuel) :
    walk nodes fuel 57 = List.range' 41 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 57).rule = .split 0 (1/80) 53 56 := by rfl
      simp only [walk, hr]
      rw [traversal_53 f (by omega), traversal_56 f (by omega)]
      change (List.range' 41 13 ++ List.range' (41+13) 3) ++
        [41+(13+3)] = List.range' 41 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 13+3)).symm

private theorem traversal_58 (fuel : Nat) (hf : 58 < fuel) :
    walk nodes fuel 58 = List.range' 58 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 58).rule = .bound .leftEnd 8 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_59 (fuel : Nat) (hf : 59 < fuel) :
    walk nodes fuel 59 = List.range' 41 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 59).rule = .split 3 (3/32) 57 58 := by rfl
      simp only [walk, hr]
      rw [traversal_57 f (by omega), traversal_58 f (by omega)]
      change (List.range' 41 17 ++ List.range' (41+17) 1) ++
        [41+(17+1)] = List.range' 41 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 17+1)).symm

private theorem traversal_60 (fuel : Nat) (hf : 60 < fuel) :
    walk nodes fuel 60 = List.range' 60 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 60).rule = .bound .leftEnd 2 (227023/49152) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_61 (fuel : Nat) (hf : 61 < fuel) :
    walk nodes fuel 61 = List.range' 61 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 61).rule = .bound .leftEnd 8 (23509/12288) (132987/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_62 (fuel : Nat) (hf : 62 < fuel) :
    walk nodes fuel 62 = List.range' 60 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 62).rule = .split 3 (3/64) 60 61 := by rfl
      simp only [walk, hr]
      rw [traversal_60 f (by omega), traversal_61 f (by omega)]
      change (List.range' 60 1 ++ List.range' (60+1) 1) ++
        [60+(1+1)] = List.range' 60 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 60) (n := 1+1)).symm

private theorem traversal_63 (fuel : Nat) (hf : 63 < fuel) :
    walk nodes fuel 63 = List.range' 63 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 63).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_64 (fuel : Nat) (hf : 64 < fuel) :
    walk nodes fuel 64 = List.range' 60 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 64).rule = .split 2 (121/256) 62 63 := by rfl
      simp only [walk, hr]
      rw [traversal_62 f (by omega), traversal_63 f (by omega)]
      change (List.range' 60 3 ++ List.range' (60+3) 1) ++
        [60+(3+1)] = List.range' 60 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 60) (n := 3+1)).symm

private theorem traversal_65 (fuel : Nat) (hf : 65 < fuel) :
    walk nodes fuel 65 = List.range' 65 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 65).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_66 (fuel : Nat) (hf : 66 < fuel) :
    walk nodes fuel 66 = List.range' 60 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 66).rule = .split 1 (125/64) 64 65 := by rfl
      simp only [walk, hr]
      rw [traversal_64 f (by omega), traversal_65 f (by omega)]
      change (List.range' 60 5 ++ List.range' (60+5) 1) ++
        [60+(5+1)] = List.range' 60 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 60) (n := 5+1)).symm

theorem traversal_67 (fuel : Nat) (hf : 67 < fuel) :
    walk nodes fuel 67 = List.range' 67 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 67).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
