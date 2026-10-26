/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_150,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_179,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_180,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_187,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_188,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart02.traversal_201
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart01
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_135 (fuel : Nat) (hf : 135 < fuel) :
    walk nodes fuel 135 = List.range' 133 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 135).rule = .split 1 (75/32) 133 134 := by rfl
      simp only [walk, hr]
      rw [traversal_133 f (by omega), traversal_134 f (by omega)]
      change (List.range' 133 1 ++ List.range' (133+1) 1) ++
        [133+(1+1)] = List.range' 133 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 133) (n := 1+1)).symm

private theorem traversal_136 (fuel : Nat) (hf : 136 < fuel) :
    walk nodes fuel 136 = List.range' 136 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 136).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_137 (fuel : Nat) (hf : 137 < fuel) :
    walk nodes fuel 137 = List.range' 133 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 137).rule = .split 0 (1/40) 135 136 := by rfl
      simp only [walk, hr]
      rw [traversal_135 f (by omega), traversal_136 f (by omega)]
      change (List.range' 133 3 ++ List.range' (133+3) 1) ++
        [133+(3+1)] = List.range' 133 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 133) (n := 3+1)).symm

private theorem traversal_138 (fuel : Nat) (hf : 138 < fuel) :
    walk nodes fuel 138 = List.range' 138 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 138).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_139 (fuel : Nat) (hf : 139 < fuel) :
    walk nodes fuel 139 = List.range' 133 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 139).rule = .split 3 (9/16) 137 138 := by rfl
      simp only [walk, hr]
      rw [traversal_137 f (by omega), traversal_138 f (by omega)]
      change (List.range' 133 5 ++ List.range' (133+5) 1) ++
        [133+(5+1)] = List.range' 133 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 133) (n := 5+1)).symm

private theorem traversal_140 (fuel : Nat) (hf : 140 < fuel) :
    walk nodes fuel 140 = List.range' 132 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 140).rule = .split 2 (73/64) 132 139 := by rfl
      simp only [walk, hr]
      rw [traversal_132 f (by omega), traversal_139 f (by omega)]
      change (List.range' 132 1 ++ List.range' (132+1) 7) ++
        [132+(1+7)] = List.range' 132 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 132) (n := 1+7)).symm

private theorem traversal_141 (fuel : Nat) (hf : 141 < fuel) :
    walk nodes fuel 141 = List.range' 131 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 141).rule = .split 1 (35/16) 131 140 := by rfl
      simp only [walk, hr]
      rw [traversal_131 f (by omega), traversal_140 f (by omega)]
      change (List.range' 131 1 ++ List.range' (131+1) 9) ++
        [131+(1+9)] = List.range' 131 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 131) (n := 1+9)).symm

private theorem traversal_142 (fuel : Nat) (hf : 142 < fuel) :
    walk nodes fuel 142 = List.range' 142 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 142).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_143 (fuel : Nat) (hf : 143 < fuel) :
    walk nodes fuel 143 = List.range' 143 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 143).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_144 (fuel : Nat) (hf : 144 < fuel) :
    walk nodes fuel 144 = List.range' 142 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 144).rule = .split 1 (35/16) 142 143 := by rfl
      simp only [walk, hr]
      rw [traversal_142 f (by omega), traversal_143 f (by omega)]
      change (List.range' 142 1 ++ List.range' (142+1) 1) ++
        [142+(1+1)] = List.range' 142 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 142) (n := 1+1)).symm

private theorem traversal_145 (fuel : Nat) (hf : 145 < fuel) :
    walk nodes fuel 145 = List.range' 131 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 145).rule = .split 0 (1/20) 141 144 := by rfl
      simp only [walk, hr]
      rw [traversal_141 f (by omega), traversal_144 f (by omega)]
      change (List.range' 131 11 ++ List.range' (131+11) 3) ++
        [131+(11+3)] = List.range' 131 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 131) (n := 11+3)).symm

private theorem traversal_146 (fuel : Nat) (hf : 146 < fuel) :
    walk nodes fuel 146 = List.range' 122 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 146).rule = .split 3 (3/8) 130 145 := by rfl
      simp only [walk, hr]
      rw [traversal_130 f (by omega), traversal_145 f (by omega)]
      change (List.range' 122 9 ++ List.range' (122+9) 15) ++
        [122+(9+15)] = List.range' 122 ((9+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 122) (n := 9+15)).symm

private theorem traversal_147 (fuel : Nat) (hf : 147 < fuel) :
    walk nodes fuel 147 = List.range' 39 109 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 147).rule = .split 2 (27/32) 121 146 := by rfl
      simp only [walk, hr]
      rw [traversal_121 f (by omega), traversal_146 f (by omega)]
      change (List.range' 39 83 ++ List.range' (39+83) 25) ++
        [39+(83+25)] = List.range' 39 ((83+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 39) (n := 83+25)).symm

private theorem traversal_148 (fuel : Nat) (hf : 148 < fuel) :
    walk nodes fuel 148 = List.range' 2 147 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 148).rule = .split 1 (15/8) 38 147 := by rfl
      simp only [walk, hr]
      rw [traversal_38 f (by omega), traversal_147 f (by omega)]
      change (List.range' 2 37 ++ List.range' (2+37) 109) ++
        [2+(37+109)] = List.range' 2 ((37+109)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 37+109)).symm

private theorem traversal_149 (fuel : Nat) (hf : 149 < fuel) :
    walk nodes fuel 149 = List.range' 149 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 149).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_150 (fuel : Nat) (hf : 150 < fuel) :
    walk nodes fuel 150 = List.range' 2 149 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 150).rule = .split 3 (3/4) 148 149 := by rfl
      simp only [walk, hr]
      rw [traversal_148 f (by omega), traversal_149 f (by omega)]
      change (List.range' 2 147 ++ List.range' (2+147) 1) ++
        [2+(147+1)] = List.range' 2 ((147+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 147+1)).symm

private theorem traversal_151 (fuel : Nat) (hf : 151 < fuel) :
    walk nodes fuel 151 = List.range' 151 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 151).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_152 (fuel : Nat) (hf : 152 < fuel) :
    walk nodes fuel 152 = List.range' 152 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 152).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_153 (fuel : Nat) (hf : 153 < fuel) :
    walk nodes fuel 153 = List.range' 151 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 153).rule = .split 3 (3/8) 151 152 := by rfl
      simp only [walk, hr]
      rw [traversal_151 f (by omega), traversal_152 f (by omega)]
      change (List.range' 151 1 ++ List.range' (151+1) 1) ++
        [151+(1+1)] = List.range' 151 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 151) (n := 1+1)).symm

private theorem traversal_154 (fuel : Nat) (hf : 154 < fuel) :
    walk nodes fuel 154 = List.range' 154 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 154).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_155 (fuel : Nat) (hf : 155 < fuel) :
    walk nodes fuel 155 = List.range' 155 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 155).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_156 (fuel : Nat) (hf : 156 < fuel) :
    walk nodes fuel 156 = List.range' 154 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 156).rule = .split 3 (3/8) 154 155 := by rfl
      simp only [walk, hr]
      rw [traversal_154 f (by omega), traversal_155 f (by omega)]
      change (List.range' 154 1 ++ List.range' (154+1) 1) ++
        [154+(1+1)] = List.range' 154 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 154) (n := 1+1)).symm

private theorem traversal_157 (fuel : Nat) (hf : 157 < fuel) :
    walk nodes fuel 157 = List.range' 151 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 157).rule = .split 2 (65/32) 153 156 := by rfl
      simp only [walk, hr]
      rw [traversal_153 f (by omega), traversal_156 f (by omega)]
      change (List.range' 151 3 ++ List.range' (151+3) 3) ++
        [151+(3+3)] = List.range' 151 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 151) (n := 3+3)).symm

private theorem traversal_158 (fuel : Nat) (hf : 158 < fuel) :
    walk nodes fuel 158 = List.range' 158 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 158).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_159 (fuel : Nat) (hf : 159 < fuel) :
    walk nodes fuel 159 = List.range' 159 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 159).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_160 (fuel : Nat) (hf : 160 < fuel) :
    walk nodes fuel 160 = List.range' 160 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 160).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_161 (fuel : Nat) (hf : 161 < fuel) :
    walk nodes fuel 161 = List.range' 161 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 161).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_162 (fuel : Nat) (hf : 162 < fuel) :
    walk nodes fuel 162 = List.range' 162 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 162).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_163 (fuel : Nat) (hf : 163 < fuel) :
    walk nodes fuel 163 = List.range' 161 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 163).rule = .split 1 (75/32) 161 162 := by rfl
      simp only [walk, hr]
      rw [traversal_161 f (by omega), traversal_162 f (by omega)]
      change (List.range' 161 1 ++ List.range' (161+1) 1) ++
        [161+(1+1)] = List.range' 161 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 1+1)).symm

private theorem traversal_164 (fuel : Nat) (hf : 164 < fuel) :
    walk nodes fuel 164 = List.range' 164 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 164).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_165 (fuel : Nat) (hf : 165 < fuel) :
    walk nodes fuel 165 = List.range' 161 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 165).rule = .split 0 (1/40) 163 164 := by rfl
      simp only [walk, hr]
      rw [traversal_163 f (by omega), traversal_164 f (by omega)]
      change (List.range' 161 3 ++ List.range' (161+3) 1) ++
        [161+(3+1)] = List.range' 161 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 3+1)).symm

private theorem traversal_166 (fuel : Nat) (hf : 166 < fuel) :
    walk nodes fuel 166 = List.range' 160 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 166).rule = .split 3 (9/16) 160 165 := by rfl
      simp only [walk, hr]
      rw [traversal_160 f (by omega), traversal_165 f (by omega)]
      change (List.range' 160 1 ++ List.range' (160+1) 5) ++
        [160+(1+5)] = List.range' 160 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 160) (n := 1+5)).symm

private theorem traversal_167 (fuel : Nat) (hf : 167 < fuel) :
    walk nodes fuel 167 = List.range' 167 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 167).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_168 (fuel : Nat) (hf : 168 < fuel) :
    walk nodes fuel 168 = List.range' 160 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 168).rule = .split 2 (111/64) 166 167 := by rfl
      simp only [walk, hr]
      rw [traversal_166 f (by omega), traversal_167 f (by omega)]
      change (List.range' 160 7 ++ List.range' (160+7) 1) ++
        [160+(7+1)] = List.range' 160 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 160) (n := 7+1)).symm

private theorem traversal_169 (fuel : Nat) (hf : 169 < fuel) :
    walk nodes fuel 169 = List.range' 159 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 169).rule = .split 1 (35/16) 159 168 := by rfl
      simp only [walk, hr]
      rw [traversal_159 f (by omega), traversal_168 f (by omega)]
      change (List.range' 159 1 ++ List.range' (159+1) 9) ++
        [159+(1+9)] = List.range' 159 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 159) (n := 1+9)).symm

private theorem traversal_170 (fuel : Nat) (hf : 170 < fuel) :
    walk nodes fuel 170 = List.range' 170 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 170).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_171 (fuel : Nat) (hf : 171 < fuel) :
    walk nodes fuel 171 = List.range' 171 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 171).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_172 (fuel : Nat) (hf : 172 < fuel) :
    walk nodes fuel 172 = List.range' 170 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 172).rule = .split 2 (111/64) 170 171 := by rfl
      simp only [walk, hr]
      rw [traversal_170 f (by omega), traversal_171 f (by omega)]
      change (List.range' 170 1 ++ List.range' (170+1) 1) ++
        [170+(1+1)] = List.range' 170 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 170) (n := 1+1)).symm

private theorem traversal_173 (fuel : Nat) (hf : 173 < fuel) :
    walk nodes fuel 173 = List.range' 173 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 173).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_174 (fuel : Nat) (hf : 174 < fuel) :
    walk nodes fuel 174 = List.range' 170 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 174).rule = .split 1 (35/16) 172 173 := by rfl
      simp only [walk, hr]
      rw [traversal_172 f (by omega), traversal_173 f (by omega)]
      change (List.range' 170 3 ++ List.range' (170+3) 1) ++
        [170+(3+1)] = List.range' 170 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 170) (n := 3+1)).symm

private theorem traversal_175 (fuel : Nat) (hf : 175 < fuel) :
    walk nodes fuel 175 = List.range' 159 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 175).rule = .split 0 (1/20) 169 174 := by rfl
      simp only [walk, hr]
      rw [traversal_169 f (by omega), traversal_174 f (by omega)]
      change (List.range' 159 11 ++ List.range' (159+11) 5) ++
        [159+(11+5)] = List.range' 159 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 159) (n := 11+5)).symm

private theorem traversal_176 (fuel : Nat) (hf : 176 < fuel) :
    walk nodes fuel 176 = List.range' 158 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 176).rule = .split 3 (3/8) 158 175 := by rfl
      simp only [walk, hr]
      rw [traversal_158 f (by omega), traversal_175 f (by omega)]
      change (List.range' 158 1 ++ List.range' (158+1) 17) ++
        [158+(1+17)] = List.range' 158 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 158) (n := 1+17)).symm

private theorem traversal_177 (fuel : Nat) (hf : 177 < fuel) :
    walk nodes fuel 177 = List.range' 177 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 177).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_178 (fuel : Nat) (hf : 178 < fuel) :
    walk nodes fuel 178 = List.range' 158 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 178).rule = .split 2 (65/32) 176 177 := by rfl
      simp only [walk, hr]
      rw [traversal_176 f (by omega), traversal_177 f (by omega)]
      change (List.range' 158 19 ++ List.range' (158+19) 1) ++
        [158+(19+1)] = List.range' 158 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 158) (n := 19+1)).symm

theorem traversal_179 (fuel : Nat) (hf : 179 < fuel) :
    walk nodes fuel 179 = List.range' 151 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 179).rule = .split 1 (15/8) 157 178 := by rfl
      simp only [walk, hr]
      rw [traversal_157 f (by omega), traversal_178 f (by omega)]
      change (List.range' 151 7 ++ List.range' (151+7) 21) ++
        [151+(7+21)] = List.range' 151 ((7+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 151) (n := 7+21)).symm

theorem traversal_180 (fuel : Nat) (hf : 180 < fuel) :
    walk nodes fuel 180 = List.range' 180 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 180).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_181 (fuel : Nat) (hf : 181 < fuel) :
    walk nodes fuel 181 = List.range' 181 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 181).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_182 (fuel : Nat) (hf : 182 < fuel) :
    walk nodes fuel 182 = List.range' 182 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 182).rule = .bound .leftEnd 1 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_183 (fuel : Nat) (hf : 183 < fuel) :
    walk nodes fuel 183 = List.range' 181 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 183).rule = .split 1 (35/16) 181 182 := by rfl
      simp only [walk, hr]
      rw [traversal_181 f (by omega), traversal_182 f (by omega)]
      change (List.range' 181 1 ++ List.range' (181+1) 1) ++
        [181+(1+1)] = List.range' 181 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 181) (n := 1+1)).symm

private theorem traversal_184 (fuel : Nat) (hf : 184 < fuel) :
    walk nodes fuel 184 = List.range' 184 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 184).rule = .bound .leftEnd 1 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_185 (fuel : Nat) (hf : 185 < fuel) :
    walk nodes fuel 185 = List.range' 181 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 185).rule = .split 0 (1/20) 183 184 := by rfl
      simp only [walk, hr]
      rw [traversal_183 f (by omega), traversal_184 f (by omega)]
      change (List.range' 181 3 ++ List.range' (181+3) 1) ++
        [181+(3+1)] = List.range' 181 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 181) (n := 3+1)).symm

private theorem traversal_186 (fuel : Nat) (hf : 186 < fuel) :
    walk nodes fuel 186 = List.range' 186 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 186).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_187 (fuel : Nat) (hf : 187 < fuel) :
    walk nodes fuel 187 = List.range' 181 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 187).rule = .split 3 (9/8) 185 186 := by rfl
      simp only [walk, hr]
      rw [traversal_185 f (by omega), traversal_186 f (by omega)]
      change (List.range' 181 5 ++ List.range' (181+5) 1) ++
        [181+(5+1)] = List.range' 181 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 181) (n := 5+1)).symm

theorem traversal_188 (fuel : Nat) (hf : 188 < fuel) :
    walk nodes fuel 188 = List.range' 188 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 188).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_189 (fuel : Nat) (hf : 189 < fuel) :
    walk nodes fuel 189 = List.range' 189 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 189).rule = .bound .leftEnd 1 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_190 (fuel : Nat) (hf : 190 < fuel) :
    walk nodes fuel 190 = List.range' 190 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 190).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_191 (fuel : Nat) (hf : 191 < fuel) :
    walk nodes fuel 191 = List.range' 189 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 191).rule = .split 2 (279/128) 189 190 := by rfl
      simp only [walk, hr]
      rw [traversal_189 f (by omega), traversal_190 f (by omega)]
      change (List.range' 189 1 ++ List.range' (189+1) 1) ++
        [189+(1+1)] = List.range' 189 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 189) (n := 1+1)).symm

private theorem traversal_192 (fuel : Nat) (hf : 192 < fuel) :
    walk nodes fuel 192 = List.range' 192 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 192).rule = .bound .leftEnd 1 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_193 (fuel : Nat) (hf : 193 < fuel) :
    walk nodes fuel 193 = List.range' 189 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 193).rule = .split 1 (75/32) 191 192 := by rfl
      simp only [walk, hr]
      rw [traversal_191 f (by omega), traversal_192 f (by omega)]
      change (List.range' 189 3 ++ List.range' (189+3) 1) ++
        [189+(3+1)] = List.range' 189 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 189) (n := 3+1)).symm

private theorem traversal_194 (fuel : Nat) (hf : 194 < fuel) :
    walk nodes fuel 194 = List.range' 194 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 194).rule = .bound .leftEnd 1 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_195 (fuel : Nat) (hf : 195 < fuel) :
    walk nodes fuel 195 = List.range' 189 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 195).rule = .split 0 (1/40) 193 194 := by rfl
      simp only [walk, hr]
      rw [traversal_193 f (by omega), traversal_194 f (by omega)]
      change (List.range' 189 5 ++ List.range' (189+5) 1) ++
        [189+(5+1)] = List.range' 189 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 189) (n := 5+1)).symm

private theorem traversal_196 (fuel : Nat) (hf : 196 < fuel) :
    walk nodes fuel 196 = List.range' 196 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 196).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_197 (fuel : Nat) (hf : 197 < fuel) :
    walk nodes fuel 197 = List.range' 189 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 197).rule = .split 3 (15/16) 195 196 := by rfl
      simp only [walk, hr]
      rw [traversal_195 f (by omega), traversal_196 f (by omega)]
      change (List.range' 189 7 ++ List.range' (189+7) 1) ++
        [189+(7+1)] = List.range' 189 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 189) (n := 7+1)).symm

private theorem traversal_198 (fuel : Nat) (hf : 198 < fuel) :
    walk nodes fuel 198 = List.range' 198 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 198).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_199 (fuel : Nat) (hf : 199 < fuel) :
    walk nodes fuel 199 = List.range' 199 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 199).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_200 (fuel : Nat) (hf : 200 < fuel) :
    walk nodes fuel 200 = List.range' 198 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 200).rule = .split 3 (15/16) 198 199 := by rfl
      simp only [walk, hr]
      rw [traversal_198 f (by omega), traversal_199 f (by omega)]
      change (List.range' 198 1 ++ List.range' (198+1) 1) ++
        [198+(1+1)] = List.range' 198 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 198) (n := 1+1)).symm

theorem traversal_201 (fuel : Nat) (hf : 201 < fuel) :
    walk nodes fuel 201 = List.range' 189 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 201).rule = .split 2 (149/64) 197 200 := by rfl
      simp only [walk, hr]
      rw [traversal_197 f (by omega), traversal_200 f (by omega)]
      change (List.range' 189 9 ++ List.range' (189+9) 3) ++
        [189+(9+3)] = List.range' 189 ((9+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 189) (n := 9+3)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
