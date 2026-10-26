/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_121,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_130,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_131,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_132,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_133,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart01.traversal_134
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart00
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_68 (fuel : Nat) (hf : 68 < fuel) :
    walk nodes fuel 68 = List.range' 66 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 68).rule = .split 3 (3/32) 66 67 := by rfl
      simp only [walk, hr]
      rw [traversal_66 f (by omega), traversal_67 f (by omega)]
      change (List.range' 66 1 ++ List.range' (66+1) 1) ++
        [66+(1+1)] = List.range' 66 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 66) (n := 1+1)).symm

private theorem traversal_69 (fuel : Nat) (hf : 69 < fuel) :
    walk nodes fuel 69 = List.range' 69 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 69).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_70 (fuel : Nat) (hf : 70 < fuel) :
    walk nodes fuel 70 = List.range' 66 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 70).rule = .split 2 (51/128) 68 69 := by rfl
      simp only [walk, hr]
      rw [traversal_68 f (by omega), traversal_69 f (by omega)]
      change (List.range' 66 3 ++ List.range' (66+3) 1) ++
        [66+(3+1)] = List.range' 66 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 66) (n := 3+1)).symm

private theorem traversal_71 (fuel : Nat) (hf : 71 < fuel) :
    walk nodes fuel 71 = List.range' 71 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 71).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_72 (fuel : Nat) (hf : 72 < fuel) :
    walk nodes fuel 72 = List.range' 66 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 72).rule = .split 1 (65/32) 70 71 := by rfl
      simp only [walk, hr]
      rw [traversal_70 f (by omega), traversal_71 f (by omega)]
      change (List.range' 66 5 ++ List.range' (66+5) 1) ++
        [66+(5+1)] = List.range' 66 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 66) (n := 5+1)).symm

private theorem traversal_73 (fuel : Nat) (hf : 73 < fuel) :
    walk nodes fuel 73 = List.range' 39 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 73).rule = .split 0 (1/40) 65 72 := by rfl
      simp only [walk, hr]
      rw [traversal_65 f (by omega), traversal_72 f (by omega)]
      change (List.range' 39 27 ++ List.range' (39+27) 7) ++
        [39+(27+7)] = List.range' 39 ((27+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 27+7)).symm

private theorem traversal_74 (fuel : Nat) (hf : 74 < fuel) :
    walk nodes fuel 74 = List.range' 74 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 74).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_75 (fuel : Nat) (hf : 75 < fuel) :
    walk nodes fuel 75 = List.range' 39 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 75).rule = .split 3 (3/16) 73 74 := by rfl
      simp only [walk, hr]
      rw [traversal_73 f (by omega), traversal_74 f (by omega)]
      change (List.range' 39 35 ++ List.range' (39+35) 1) ++
        [39+(35+1)] = List.range' 39 ((35+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 35+1)).symm

private theorem traversal_76 (fuel : Nat) (hf : 76 < fuel) :
    walk nodes fuel 76 = List.range' 76 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 76).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_77 (fuel : Nat) (hf : 77 < fuel) :
    walk nodes fuel 77 = List.range' 77 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 77).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_78 (fuel : Nat) (hf : 78 < fuel) :
    walk nodes fuel 78 = List.range' 76 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 78).rule = .split 0 (1/40) 76 77 := by rfl
      simp only [walk, hr]
      rw [traversal_76 f (by omega), traversal_77 f (by omega)]
      change (List.range' 76 1 ++ List.range' (76+1) 1) ++
        [76+(1+1)] = List.range' 76 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 76) (n := 1+1)).symm

private theorem traversal_79 (fuel : Nat) (hf : 79 < fuel) :
    walk nodes fuel 79 = List.range' 79 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 79).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_80 (fuel : Nat) (hf : 80 < fuel) :
    walk nodes fuel 80 = List.range' 76 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 80).rule = .split 3 (3/16) 78 79 := by rfl
      simp only [walk, hr]
      rw [traversal_78 f (by omega), traversal_79 f (by omega)]
      change (List.range' 76 3 ++ List.range' (76+3) 1) ++
        [76+(3+1)] = List.range' 76 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 76) (n := 3+1)).symm

private theorem traversal_81 (fuel : Nat) (hf : 81 < fuel) :
    walk nodes fuel 81 = List.range' 39 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 81).rule = .split 2 (35/64) 75 80 := by rfl
      simp only [walk, hr]
      rw [traversal_75 f (by omega), traversal_80 f (by omega)]
      change (List.range' 39 37 ++ List.range' (39+37) 5) ++
        [39+(37+5)] = List.range' 39 ((37+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 37+5)).symm

private theorem traversal_82 (fuel : Nat) (hf : 82 < fuel) :
    walk nodes fuel 82 = List.range' 82 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 82).rule = .bound .leftEnd 2 (321059/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_83 (fuel : Nat) (hf : 83 < fuel) :
    walk nodes fuel 83 = List.range' 83 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 83).rule = .bound .leftEnd 1 (44329/32768) (23509/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_84 (fuel : Nat) (hf : 84 < fuel) :
    walk nodes fuel 84 = List.range' 82 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 84).rule = .split 3 (3/32) 82 83 := by rfl
      simp only [walk, hr]
      rw [traversal_82 f (by omega), traversal_83 f (by omega)]
      change (List.range' 82 1 ++ List.range' (82+1) 1) ++
        [82+(1+1)] = List.range' 82 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 1+1)).symm

private theorem traversal_85 (fuel : Nat) (hf : 85 < fuel) :
    walk nodes fuel 85 = List.range' 85 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 85).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_86 (fuel : Nat) (hf : 86 < fuel) :
    walk nodes fuel 86 = List.range' 82 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 86).rule = .split 2 (51/128) 84 85 := by rfl
      simp only [walk, hr]
      rw [traversal_84 f (by omega), traversal_85 f (by omega)]
      change (List.range' 82 3 ++ List.range' (82+3) 1) ++
        [82+(3+1)] = List.range' 82 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 3+1)).symm

private theorem traversal_87 (fuel : Nat) (hf : 87 < fuel) :
    walk nodes fuel 87 = List.range' 87 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 87).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_88 (fuel : Nat) (hf : 88 < fuel) :
    walk nodes fuel 88 = List.range' 82 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 88).rule = .split 1 (75/32) 86 87 := by rfl
      simp only [walk, hr]
      rw [traversal_86 f (by omega), traversal_87 f (by omega)]
      change (List.range' 82 5 ++ List.range' (82+5) 1) ++
        [82+(5+1)] = List.range' 82 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 5+1)).symm

private theorem traversal_89 (fuel : Nat) (hf : 89 < fuel) :
    walk nodes fuel 89 = List.range' 89 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 89).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_90 (fuel : Nat) (hf : 90 < fuel) :
    walk nodes fuel 90 = List.range' 82 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 90).rule = .split 0 (1/40) 88 89 := by rfl
      simp only [walk, hr]
      rw [traversal_88 f (by omega), traversal_89 f (by omega)]
      change (List.range' 82 7 ++ List.range' (82+7) 1) ++
        [82+(7+1)] = List.range' 82 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 7+1)).symm

private theorem traversal_91 (fuel : Nat) (hf : 91 < fuel) :
    walk nodes fuel 91 = List.range' 91 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 91).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_92 (fuel : Nat) (hf : 92 < fuel) :
    walk nodes fuel 92 = List.range' 82 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 92).rule = .split 3 (3/16) 90 91 := by rfl
      simp only [walk, hr]
      rw [traversal_90 f (by omega), traversal_91 f (by omega)]
      change (List.range' 82 9 ++ List.range' (82+9) 1) ++
        [82+(9+1)] = List.range' 82 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 9+1)).symm

private theorem traversal_93 (fuel : Nat) (hf : 93 < fuel) :
    walk nodes fuel 93 = List.range' 93 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 93).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_94 (fuel : Nat) (hf : 94 < fuel) :
    walk nodes fuel 94 = List.range' 94 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 94).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_95 (fuel : Nat) (hf : 95 < fuel) :
    walk nodes fuel 95 = List.range' 95 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 95).rule = .bound .leftEnd 2 (34015/32768) (62489/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_96 (fuel : Nat) (hf : 96 < fuel) :
    walk nodes fuel 96 = List.range' 96 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 96).rule = .bound .leftEnd 1 (7169/8192) (298007/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_97 (fuel : Nat) (hf : 97 < fuel) :
    walk nodes fuel 97 = List.range' 95 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 97).rule = .split 3 (9/32) 95 96 := by rfl
      simp only [walk, hr]
      rw [traversal_95 f (by omega), traversal_96 f (by omega)]
      change (List.range' 95 1 ++ List.range' (95+1) 1) ++
        [95+(1+1)] = List.range' 95 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 95) (n := 1+1)).symm

private theorem traversal_98 (fuel : Nat) (hf : 98 < fuel) :
    walk nodes fuel 98 = List.range' 94 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 98).rule = .split 2 (89/128) 94 97 := by rfl
      simp only [walk, hr]
      rw [traversal_94 f (by omega), traversal_97 f (by omega)]
      change (List.range' 94 1 ++ List.range' (94+1) 3) ++
        [94+(1+3)] = List.range' 94 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 94) (n := 1+3)).symm

private theorem traversal_99 (fuel : Nat) (hf : 99 < fuel) :
    walk nodes fuel 99 = List.range' 99 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 99).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_100 (fuel : Nat) (hf : 100 < fuel) :
    walk nodes fuel 100 = List.range' 100 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 100).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_101 (fuel : Nat) (hf : 101 < fuel) :
    walk nodes fuel 101 = List.range' 99 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 101).rule = .split 2 (89/128) 99 100 := by rfl
      simp only [walk, hr]
      rw [traversal_99 f (by omega), traversal_100 f (by omega)]
      change (List.range' 99 1 ++ List.range' (99+1) 1) ++
        [99+(1+1)] = List.range' 99 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 99) (n := 1+1)).symm

private theorem traversal_102 (fuel : Nat) (hf : 102 < fuel) :
    walk nodes fuel 102 = List.range' 94 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 102).rule = .split 1 (75/32) 98 101 := by rfl
      simp only [walk, hr]
      rw [traversal_98 f (by omega), traversal_101 f (by omega)]
      change (List.range' 94 5 ++ List.range' (94+5) 3) ++
        [94+(5+3)] = List.range' 94 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 94) (n := 5+3)).symm

private theorem traversal_103 (fuel : Nat) (hf : 103 < fuel) :
    walk nodes fuel 103 = List.range' 103 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 103).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_104 (fuel : Nat) (hf : 104 < fuel) :
    walk nodes fuel 104 = List.range' 94 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 104).rule = .split 0 (1/40) 102 103 := by rfl
      simp only [walk, hr]
      rw [traversal_102 f (by omega), traversal_103 f (by omega)]
      change (List.range' 94 9 ++ List.range' (94+9) 1) ++
        [94+(9+1)] = List.range' 94 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 94) (n := 9+1)).symm

private theorem traversal_105 (fuel : Nat) (hf : 105 < fuel) :
    walk nodes fuel 105 = List.range' 93 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 105).rule = .split 3 (3/16) 93 104 := by rfl
      simp only [walk, hr]
      rw [traversal_93 f (by omega), traversal_104 f (by omega)]
      change (List.range' 93 1 ++ List.range' (93+1) 11) ++
        [93+(1+11)] = List.range' 93 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 93) (n := 1+11)).symm

private theorem traversal_106 (fuel : Nat) (hf : 106 < fuel) :
    walk nodes fuel 106 = List.range' 82 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 106).rule = .split 2 (35/64) 92 105 := by rfl
      simp only [walk, hr]
      rw [traversal_92 f (by omega), traversal_105 f (by omega)]
      change (List.range' 82 11 ++ List.range' (82+11) 13) ++
        [82+(11+13)] = List.range' 82 ((11+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 82) (n := 11+13)).symm

private theorem traversal_107 (fuel : Nat) (hf : 107 < fuel) :
    walk nodes fuel 107 = List.range' 39 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 107).rule = .split 1 (35/16) 81 106 := by rfl
      simp only [walk, hr]
      rw [traversal_81 f (by omega), traversal_106 f (by omega)]
      change (List.range' 39 43 ++ List.range' (39+43) 25) ++
        [39+(43+25)] = List.range' 39 ((43+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 43+25)).symm

private theorem traversal_108 (fuel : Nat) (hf : 108 < fuel) :
    walk nodes fuel 108 = List.range' 108 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 108).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_109 (fuel : Nat) (hf : 109 < fuel) :
    walk nodes fuel 109 = List.range' 109 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 109).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_110 (fuel : Nat) (hf : 110 < fuel) :
    walk nodes fuel 110 = List.range' 108 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 110).rule = .split 3 (3/16) 108 109 := by rfl
      simp only [walk, hr]
      rw [traversal_108 f (by omega), traversal_109 f (by omega)]
      change (List.range' 108 1 ++ List.range' (108+1) 1) ++
        [108+(1+1)] = List.range' 108 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 108) (n := 1+1)).symm

private theorem traversal_111 (fuel : Nat) (hf : 111 < fuel) :
    walk nodes fuel 111 = List.range' 111 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 111).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_112 (fuel : Nat) (hf : 112 < fuel) :
    walk nodes fuel 112 = List.range' 112 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 112).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_113 (fuel : Nat) (hf : 113 < fuel) :
    walk nodes fuel 113 = List.range' 111 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 113).rule = .split 3 (3/16) 111 112 := by rfl
      simp only [walk, hr]
      rw [traversal_111 f (by omega), traversal_112 f (by omega)]
      change (List.range' 111 1 ++ List.range' (111+1) 1) ++
        [111+(1+1)] = List.range' 111 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 111) (n := 1+1)).symm

private theorem traversal_114 (fuel : Nat) (hf : 114 < fuel) :
    walk nodes fuel 114 = List.range' 108 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 114).rule = .split 2 (35/64) 110 113 := by rfl
      simp only [walk, hr]
      rw [traversal_110 f (by omega), traversal_113 f (by omega)]
      change (List.range' 108 3 ++ List.range' (108+3) 3) ++
        [108+(3+3)] = List.range' 108 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 108) (n := 3+3)).symm

private theorem traversal_115 (fuel : Nat) (hf : 115 < fuel) :
    walk nodes fuel 115 = List.range' 115 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 115).rule = .bound .leftEnd 1 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_116 (fuel : Nat) (hf : 116 < fuel) :
    walk nodes fuel 116 = List.range' 116 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 116).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_117 (fuel : Nat) (hf : 117 < fuel) :
    walk nodes fuel 117 = List.range' 115 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 117).rule = .split 2 (35/64) 115 116 := by rfl
      simp only [walk, hr]
      rw [traversal_115 f (by omega), traversal_116 f (by omega)]
      change (List.range' 115 1 ++ List.range' (115+1) 1) ++
        [115+(1+1)] = List.range' 115 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 115) (n := 1+1)).symm

private theorem traversal_118 (fuel : Nat) (hf : 118 < fuel) :
    walk nodes fuel 118 = List.range' 108 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 118).rule = .split 1 (35/16) 114 117 := by rfl
      simp only [walk, hr]
      rw [traversal_114 f (by omega), traversal_117 f (by omega)]
      change (List.range' 108 7 ++ List.range' (108+7) 3) ++
        [108+(7+3)] = List.range' 108 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 108) (n := 7+3)).symm

private theorem traversal_119 (fuel : Nat) (hf : 119 < fuel) :
    walk nodes fuel 119 = List.range' 39 81 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 119).rule = .split 0 (1/20) 107 118 := by rfl
      simp only [walk, hr]
      rw [traversal_107 f (by omega), traversal_118 f (by omega)]
      change (List.range' 39 69 ++ List.range' (39+69) 11) ++
        [39+(69+11)] = List.range' 39 ((69+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 69+11)).symm

private theorem traversal_120 (fuel : Nat) (hf : 120 < fuel) :
    walk nodes fuel 120 = List.range' 120 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 120).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_121 (fuel : Nat) (hf : 121 < fuel) :
    walk nodes fuel 121 = List.range' 39 83 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 121).rule = .split 3 (3/8) 119 120 := by rfl
      simp only [walk, hr]
      rw [traversal_119 f (by omega), traversal_120 f (by omega)]
      change (List.range' 39 81 ++ List.range' (39+81) 1) ++
        [39+(81+1)] = List.range' 39 ((81+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 81+1)).symm

private theorem traversal_122 (fuel : Nat) (hf : 122 < fuel) :
    walk nodes fuel 122 = List.range' 122 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 122).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_123 (fuel : Nat) (hf : 123 < fuel) :
    walk nodes fuel 123 = List.range' 123 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 123).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_124 (fuel : Nat) (hf : 124 < fuel) :
    walk nodes fuel 124 = List.range' 122 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 124).rule = .split 3 (3/16) 122 123 := by rfl
      simp only [walk, hr]
      rw [traversal_122 f (by omega), traversal_123 f (by omega)]
      change (List.range' 122 1 ++ List.range' (122+1) 1) ++
        [122+(1+1)] = List.range' 122 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 122) (n := 1+1)).symm

private theorem traversal_125 (fuel : Nat) (hf : 125 < fuel) :
    walk nodes fuel 125 = List.range' 125 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 125).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_126 (fuel : Nat) (hf : 126 < fuel) :
    walk nodes fuel 126 = List.range' 122 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 126).rule = .split 2 (73/64) 124 125 := by rfl
      simp only [walk, hr]
      rw [traversal_124 f (by omega), traversal_125 f (by omega)]
      change (List.range' 122 3 ++ List.range' (122+3) 1) ++
        [122+(3+1)] = List.range' 122 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 122) (n := 3+1)).symm

private theorem traversal_127 (fuel : Nat) (hf : 127 < fuel) :
    walk nodes fuel 127 = List.range' 127 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 127).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_128 (fuel : Nat) (hf : 128 < fuel) :
    walk nodes fuel 128 = List.range' 122 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 128).rule = .split 1 (35/16) 126 127 := by rfl
      simp only [walk, hr]
      rw [traversal_126 f (by omega), traversal_127 f (by omega)]
      change (List.range' 122 5 ++ List.range' (122+5) 1) ++
        [122+(5+1)] = List.range' 122 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 122) (n := 5+1)).symm

private theorem traversal_129 (fuel : Nat) (hf : 129 < fuel) :
    walk nodes fuel 129 = List.range' 129 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 129).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_130 (fuel : Nat) (hf : 130 < fuel) :
    walk nodes fuel 130 = List.range' 122 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 130).rule = .split 0 (1/20) 128 129 := by rfl
      simp only [walk, hr]
      rw [traversal_128 f (by omega), traversal_129 f (by omega)]
      change (List.range' 122 7 ++ List.range' (122+7) 1) ++
        [122+(7+1)] = List.range' 122 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 122) (n := 7+1)).symm

theorem traversal_131 (fuel : Nat) (hf : 131 < fuel) :
    walk nodes fuel 131 = List.range' 131 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 131).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_132 (fuel : Nat) (hf : 132 < fuel) :
    walk nodes fuel 132 = List.range' 132 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 132).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_133 (fuel : Nat) (hf : 133 < fuel) :
    walk nodes fuel 133 = List.range' 133 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 133).rule = .bound .leftEnd 8 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_134 (fuel : Nat) (hf : 134 < fuel) :
    walk nodes fuel 134 = List.range' 134 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 134).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
