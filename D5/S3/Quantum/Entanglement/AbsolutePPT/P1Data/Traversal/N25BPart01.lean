/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01.traversal_129,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01.traversal_132,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01.traversal_133,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart01.traversal_134
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart00
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_68 (fuel : Nat) (hf : 68 < fuel) :
    walk nodes fuel 68 = List.range' 60 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 68).rule = .split 0 (1/80) 66 67 := by rfl
      simp only [walk, hr]
      rw [traversal_66 f (by omega), traversal_67 f (by omega)]
      change (List.range' 60 7 ++ List.range' (60+7) 1) ++
        [60+(7+1)] = List.range' 60 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 60) (n := 7+1)).symm

private theorem traversal_69 (fuel : Nat) (hf : 69 < fuel) :
    walk nodes fuel 69 = List.range' 69 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 69).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_70 (fuel : Nat) (hf : 70 < fuel) :
    walk nodes fuel 70 = List.range' 60 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 70).rule = .split 3 (3/32) 68 69 := by rfl
      simp only [walk, hr]
      rw [traversal_68 f (by omega), traversal_69 f (by omega)]
      change (List.range' 60 9 ++ List.range' (60+9) 1) ++
        [60+(9+1)] = List.range' 60 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 60) (n := 9+1)).symm

private theorem traversal_71 (fuel : Nat) (hf : 71 < fuel) :
    walk nodes fuel 71 = List.range' 41 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 71).rule = .split 2 (51/128) 59 70 := by rfl
      simp only [walk, hr]
      rw [traversal_59 f (by omega), traversal_70 f (by omega)]
      change (List.range' 41 19 ++ List.range' (41+19) 11) ++
        [41+(19+11)] = List.range' 41 ((19+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 19+11)).symm

private theorem traversal_72 (fuel : Nat) (hf : 72 < fuel) :
    walk nodes fuel 72 = List.range' 72 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 72).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_73 (fuel : Nat) (hf : 73 < fuel) :
    walk nodes fuel 73 = List.range' 73 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 73).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_74 (fuel : Nat) (hf : 74 < fuel) :
    walk nodes fuel 74 = List.range' 72 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 74).rule = .split 3 (3/32) 72 73 := by rfl
      simp only [walk, hr]
      rw [traversal_72 f (by omega), traversal_73 f (by omega)]
      change (List.range' 72 1 ++ List.range' (72+1) 1) ++
        [72+(1+1)] = List.range' 72 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 72) (n := 1+1)).symm

private theorem traversal_75 (fuel : Nat) (hf : 75 < fuel) :
    walk nodes fuel 75 = List.range' 75 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 75).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_76 (fuel : Nat) (hf : 76 < fuel) :
    walk nodes fuel 76 = List.range' 76 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 76).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_77 (fuel : Nat) (hf : 77 < fuel) :
    walk nodes fuel 77 = List.range' 75 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 77).rule = .split 3 (3/32) 75 76 := by rfl
      simp only [walk, hr]
      rw [traversal_75 f (by omega), traversal_76 f (by omega)]
      change (List.range' 75 1 ++ List.range' (75+1) 1) ++
        [75+(1+1)] = List.range' 75 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 75) (n := 1+1)).symm

private theorem traversal_78 (fuel : Nat) (hf : 78 < fuel) :
    walk nodes fuel 78 = List.range' 72 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 78).rule = .split 2 (51/128) 74 77 := by rfl
      simp only [walk, hr]
      rw [traversal_74 f (by omega), traversal_77 f (by omega)]
      change (List.range' 72 3 ++ List.range' (72+3) 3) ++
        [72+(3+3)] = List.range' 72 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 72) (n := 3+3)).symm

private theorem traversal_79 (fuel : Nat) (hf : 79 < fuel) :
    walk nodes fuel 79 = List.range' 41 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 79).rule = .split 1 (65/32) 71 78 := by rfl
      simp only [walk, hr]
      rw [traversal_71 f (by omega), traversal_78 f (by omega)]
      change (List.range' 41 31 ++ List.range' (41+31) 7) ++
        [41+(31+7)] = List.range' 41 ((31+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 31+7)).symm

private theorem traversal_80 (fuel : Nat) (hf : 80 < fuel) :
    walk nodes fuel 80 = List.range' 80 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 80).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_81 (fuel : Nat) (hf : 81 < fuel) :
    walk nodes fuel 81 = List.range' 81 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 81).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_82 (fuel : Nat) (hf : 82 < fuel) :
    walk nodes fuel 82 = List.range' 80 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 82).rule = .split 3 (3/32) 80 81 := by rfl
      simp only [walk, hr]
      rw [traversal_80 f (by omega), traversal_81 f (by omega)]
      change (List.range' 80 1 ++ List.range' (80+1) 1) ++
        [80+(1+1)] = List.range' 80 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 80) (n := 1+1)).symm

private theorem traversal_83 (fuel : Nat) (hf : 83 < fuel) :
    walk nodes fuel 83 = List.range' 83 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 83).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_84 (fuel : Nat) (hf : 84 < fuel) :
    walk nodes fuel 84 = List.range' 80 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 84).rule = .split 2 (51/128) 82 83 := by rfl
      simp only [walk, hr]
      rw [traversal_82 f (by omega), traversal_83 f (by omega)]
      change (List.range' 80 3 ++ List.range' (80+3) 1) ++
        [80+(3+1)] = List.range' 80 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 80) (n := 3+1)).symm

private theorem traversal_85 (fuel : Nat) (hf : 85 < fuel) :
    walk nodes fuel 85 = List.range' 85 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 85).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_86 (fuel : Nat) (hf : 86 < fuel) :
    walk nodes fuel 86 = List.range' 80 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 86).rule = .split 1 (65/32) 84 85 := by rfl
      simp only [walk, hr]
      rw [traversal_84 f (by omega), traversal_85 f (by omega)]
      change (List.range' 80 5 ++ List.range' (80+5) 1) ++
        [80+(5+1)] = List.range' 80 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 80) (n := 5+1)).symm

private theorem traversal_87 (fuel : Nat) (hf : 87 < fuel) :
    walk nodes fuel 87 = List.range' 41 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 87).rule = .split 0 (1/40) 79 86 := by rfl
      simp only [walk, hr]
      rw [traversal_79 f (by omega), traversal_86 f (by omega)]
      change (List.range' 41 39 ++ List.range' (41+39) 7) ++
        [41+(39+7)] = List.range' 41 ((39+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 39+7)).symm

private theorem traversal_88 (fuel : Nat) (hf : 88 < fuel) :
    walk nodes fuel 88 = List.range' 88 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 88).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_89 (fuel : Nat) (hf : 89 < fuel) :
    walk nodes fuel 89 = List.range' 41 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 89).rule = .split 3 (3/16) 87 88 := by rfl
      simp only [walk, hr]
      rw [traversal_87 f (by omega), traversal_88 f (by omega)]
      change (List.range' 41 47 ++ List.range' (41+47) 1) ++
        [41+(47+1)] = List.range' 41 ((47+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 47+1)).symm

private theorem traversal_90 (fuel : Nat) (hf : 90 < fuel) :
    walk nodes fuel 90 = List.range' 90 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 90).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_91 (fuel : Nat) (hf : 91 < fuel) :
    walk nodes fuel 91 = List.range' 91 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 91).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_92 (fuel : Nat) (hf : 92 < fuel) :
    walk nodes fuel 92 = List.range' 90 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 92).rule = .split 3 (3/32) 90 91 := by rfl
      simp only [walk, hr]
      rw [traversal_90 f (by omega), traversal_91 f (by omega)]
      change (List.range' 90 1 ++ List.range' (90+1) 1) ++
        [90+(1+1)] = List.range' 90 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 90) (n := 1+1)).symm

private theorem traversal_93 (fuel : Nat) (hf : 93 < fuel) :
    walk nodes fuel 93 = List.range' 93 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 93).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_94 (fuel : Nat) (hf : 94 < fuel) :
    walk nodes fuel 94 = List.range' 90 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 94).rule = .split 2 (89/128) 92 93 := by rfl
      simp only [walk, hr]
      rw [traversal_92 f (by omega), traversal_93 f (by omega)]
      change (List.range' 90 3 ++ List.range' (90+3) 1) ++
        [90+(3+1)] = List.range' 90 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 90) (n := 3+1)).symm

private theorem traversal_95 (fuel : Nat) (hf : 95 < fuel) :
    walk nodes fuel 95 = List.range' 95 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 95).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_96 (fuel : Nat) (hf : 96 < fuel) :
    walk nodes fuel 96 = List.range' 90 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 96).rule = .split 1 (65/32) 94 95 := by rfl
      simp only [walk, hr]
      rw [traversal_94 f (by omega), traversal_95 f (by omega)]
      change (List.range' 90 5 ++ List.range' (90+5) 1) ++
        [90+(5+1)] = List.range' 90 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 90) (n := 5+1)).symm

private theorem traversal_97 (fuel : Nat) (hf : 97 < fuel) :
    walk nodes fuel 97 = List.range' 97 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 97).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_98 (fuel : Nat) (hf : 98 < fuel) :
    walk nodes fuel 98 = List.range' 90 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 98).rule = .split 0 (1/40) 96 97 := by rfl
      simp only [walk, hr]
      rw [traversal_96 f (by omega), traversal_97 f (by omega)]
      change (List.range' 90 7 ++ List.range' (90+7) 1) ++
        [90+(7+1)] = List.range' 90 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 90) (n := 7+1)).symm

private theorem traversal_99 (fuel : Nat) (hf : 99 < fuel) :
    walk nodes fuel 99 = List.range' 99 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 99).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_100 (fuel : Nat) (hf : 100 < fuel) :
    walk nodes fuel 100 = List.range' 90 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 100).rule = .split 3 (3/16) 98 99 := by rfl
      simp only [walk, hr]
      rw [traversal_98 f (by omega), traversal_99 f (by omega)]
      change (List.range' 90 9 ++ List.range' (90+9) 1) ++
        [90+(9+1)] = List.range' 90 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 90) (n := 9+1)).symm

private theorem traversal_101 (fuel : Nat) (hf : 101 < fuel) :
    walk nodes fuel 101 = List.range' 41 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 101).rule = .split 2 (35/64) 89 100 := by rfl
      simp only [walk, hr]
      rw [traversal_89 f (by omega), traversal_100 f (by omega)]
      change (List.range' 41 49 ++ List.range' (41+49) 11) ++
        [41+(49+11)] = List.range' 41 ((49+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 49+11)).symm

private theorem traversal_102 (fuel : Nat) (hf : 102 < fuel) :
    walk nodes fuel 102 = List.range' 102 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 102).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_103 (fuel : Nat) (hf : 103 < fuel) :
    walk nodes fuel 103 = List.range' 103 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 103).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_104 (fuel : Nat) (hf : 104 < fuel) :
    walk nodes fuel 104 = List.range' 102 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 104).rule = .split 3 (3/32) 102 103 := by rfl
      simp only [walk, hr]
      rw [traversal_102 f (by omega), traversal_103 f (by omega)]
      change (List.range' 102 1 ++ List.range' (102+1) 1) ++
        [102+(1+1)] = List.range' 102 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 1+1)).symm

private theorem traversal_105 (fuel : Nat) (hf : 105 < fuel) :
    walk nodes fuel 105 = List.range' 105 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 105).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_106 (fuel : Nat) (hf : 106 < fuel) :
    walk nodes fuel 106 = List.range' 102 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 106).rule = .split 2 (51/128) 104 105 := by rfl
      simp only [walk, hr]
      rw [traversal_104 f (by omega), traversal_105 f (by omega)]
      change (List.range' 102 3 ++ List.range' (102+3) 1) ++
        [102+(3+1)] = List.range' 102 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 3+1)).symm

private theorem traversal_107 (fuel : Nat) (hf : 107 < fuel) :
    walk nodes fuel 107 = List.range' 107 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 107).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_108 (fuel : Nat) (hf : 108 < fuel) :
    walk nodes fuel 108 = List.range' 102 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 108).rule = .split 1 (75/32) 106 107 := by rfl
      simp only [walk, hr]
      rw [traversal_106 f (by omega), traversal_107 f (by omega)]
      change (List.range' 102 5 ++ List.range' (102+5) 1) ++
        [102+(5+1)] = List.range' 102 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 5+1)).symm

private theorem traversal_109 (fuel : Nat) (hf : 109 < fuel) :
    walk nodes fuel 109 = List.range' 109 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 109).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_110 (fuel : Nat) (hf : 110 < fuel) :
    walk nodes fuel 110 = List.range' 102 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 110).rule = .split 0 (1/40) 108 109 := by rfl
      simp only [walk, hr]
      rw [traversal_108 f (by omega), traversal_109 f (by omega)]
      change (List.range' 102 7 ++ List.range' (102+7) 1) ++
        [102+(7+1)] = List.range' 102 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 7+1)).symm

private theorem traversal_111 (fuel : Nat) (hf : 111 < fuel) :
    walk nodes fuel 111 = List.range' 111 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 111).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_112 (fuel : Nat) (hf : 112 < fuel) :
    walk nodes fuel 112 = List.range' 102 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 112).rule = .split 3 (3/16) 110 111 := by rfl
      simp only [walk, hr]
      rw [traversal_110 f (by omega), traversal_111 f (by omega)]
      change (List.range' 102 9 ++ List.range' (102+9) 1) ++
        [102+(9+1)] = List.range' 102 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 9+1)).symm

private theorem traversal_113 (fuel : Nat) (hf : 113 < fuel) :
    walk nodes fuel 113 = List.range' 113 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 113).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_114 (fuel : Nat) (hf : 114 < fuel) :
    walk nodes fuel 114 = List.range' 114 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 114).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_115 (fuel : Nat) (hf : 115 < fuel) :
    walk nodes fuel 115 = List.range' 113 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 115).rule = .split 3 (3/16) 113 114 := by rfl
      simp only [walk, hr]
      rw [traversal_113 f (by omega), traversal_114 f (by omega)]
      change (List.range' 113 1 ++ List.range' (113+1) 1) ++
        [113+(1+1)] = List.range' 113 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 113) (n := 1+1)).symm

private theorem traversal_116 (fuel : Nat) (hf : 116 < fuel) :
    walk nodes fuel 116 = List.range' 102 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 116).rule = .split 2 (35/64) 112 115 := by rfl
      simp only [walk, hr]
      rw [traversal_112 f (by omega), traversal_115 f (by omega)]
      change (List.range' 102 11 ++ List.range' (102+11) 3) ++
        [102+(11+3)] = List.range' 102 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 11+3)).symm

private theorem traversal_117 (fuel : Nat) (hf : 117 < fuel) :
    walk nodes fuel 117 = List.range' 41 77 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 117).rule = .split 1 (35/16) 101 116 := by rfl
      simp only [walk, hr]
      rw [traversal_101 f (by omega), traversal_116 f (by omega)]
      change (List.range' 41 61 ++ List.range' (41+61) 15) ++
        [41+(61+15)] = List.range' 41 ((61+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 61+15)).symm

private theorem traversal_118 (fuel : Nat) (hf : 118 < fuel) :
    walk nodes fuel 118 = List.range' 118 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 118).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_119 (fuel : Nat) (hf : 119 < fuel) :
    walk nodes fuel 119 = List.range' 119 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 119).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_120 (fuel : Nat) (hf : 120 < fuel) :
    walk nodes fuel 120 = List.range' 118 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 120).rule = .split 3 (3/16) 118 119 := by rfl
      simp only [walk, hr]
      rw [traversal_118 f (by omega), traversal_119 f (by omega)]
      change (List.range' 118 1 ++ List.range' (118+1) 1) ++
        [118+(1+1)] = List.range' 118 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 118) (n := 1+1)).symm

private theorem traversal_121 (fuel : Nat) (hf : 121 < fuel) :
    walk nodes fuel 121 = List.range' 121 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 121).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_122 (fuel : Nat) (hf : 122 < fuel) :
    walk nodes fuel 122 = List.range' 122 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 122).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_123 (fuel : Nat) (hf : 123 < fuel) :
    walk nodes fuel 123 = List.range' 121 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 123).rule = .split 3 (3/16) 121 122 := by rfl
      simp only [walk, hr]
      rw [traversal_121 f (by omega), traversal_122 f (by omega)]
      change (List.range' 121 1 ++ List.range' (121+1) 1) ++
        [121+(1+1)] = List.range' 121 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 121) (n := 1+1)).symm

private theorem traversal_124 (fuel : Nat) (hf : 124 < fuel) :
    walk nodes fuel 124 = List.range' 118 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 124).rule = .split 2 (35/64) 120 123 := by rfl
      simp only [walk, hr]
      rw [traversal_120 f (by omega), traversal_123 f (by omega)]
      change (List.range' 118 3 ++ List.range' (118+3) 3) ++
        [118+(3+3)] = List.range' 118 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 118) (n := 3+3)).symm

private theorem traversal_125 (fuel : Nat) (hf : 125 < fuel) :
    walk nodes fuel 125 = List.range' 125 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 125).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_126 (fuel : Nat) (hf : 126 < fuel) :
    walk nodes fuel 126 = List.range' 118 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 126).rule = .split 1 (35/16) 124 125 := by rfl
      simp only [walk, hr]
      rw [traversal_124 f (by omega), traversal_125 f (by omega)]
      change (List.range' 118 7 ++ List.range' (118+7) 1) ++
        [118+(7+1)] = List.range' 118 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 118) (n := 7+1)).symm

private theorem traversal_127 (fuel : Nat) (hf : 127 < fuel) :
    walk nodes fuel 127 = List.range' 41 87 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 127).rule = .split 0 (1/20) 117 126 := by rfl
      simp only [walk, hr]
      rw [traversal_117 f (by omega), traversal_126 f (by omega)]
      change (List.range' 41 77 ++ List.range' (41+77) 9) ++
        [41+(77+9)] = List.range' 41 ((77+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 77+9)).symm

private theorem traversal_128 (fuel : Nat) (hf : 128 < fuel) :
    walk nodes fuel 128 = List.range' 128 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 128).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_129 (fuel : Nat) (hf : 129 < fuel) :
    walk nodes fuel 129 = List.range' 41 89 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 129).rule = .split 3 (3/8) 127 128 := by rfl
      simp only [walk, hr]
      rw [traversal_127 f (by omega), traversal_128 f (by omega)]
      change (List.range' 41 87 ++ List.range' (41+87) 1) ++
        [41+(87+1)] = List.range' 41 ((87+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 87+1)).symm

private theorem traversal_130 (fuel : Nat) (hf : 130 < fuel) :
    walk nodes fuel 130 = List.range' 130 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 130).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_131 (fuel : Nat) (hf : 131 < fuel) :
    walk nodes fuel 131 = List.range' 131 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 131).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_132 (fuel : Nat) (hf : 132 < fuel) :
    walk nodes fuel 132 = List.range' 130 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 132).rule = .split 3 (3/16) 130 131 := by rfl
      simp only [walk, hr]
      rw [traversal_130 f (by omega), traversal_131 f (by omega)]
      change (List.range' 130 1 ++ List.range' (130+1) 1) ++
        [130+(1+1)] = List.range' 130 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 130) (n := 1+1)).symm

theorem traversal_133 (fuel : Nat) (hf : 133 < fuel) :
    walk nodes fuel 133 = List.range' 133 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 133).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_134 (fuel : Nat) (hf : 134 < fuel) :
    walk nodes fuel 134 = List.range' 134 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 134).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
