/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_149,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_176,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_177,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_184,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_199,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_200,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart02.traversal_201
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart01
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_135 (fuel : Nat) (hf : 135 < fuel) :
    walk nodes fuel 135 = List.range' 117 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 135).rule = .split 3 (3/16) 117 134 := by rfl
      simp only [walk, hr]
      rw [traversal_117 f (by omega), traversal_134 f (by omega)]
      change (List.range' 117 1 ++ List.range' (117+1) 17) ++
        [117+(1+17)] = List.range' 117 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 117) (n := 1+17)).symm

private theorem traversal_136 (fuel : Nat) (hf : 136 < fuel) :
    walk nodes fuel 136 = List.range' 102 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 136).rule = .split 2 (35/64) 116 135 := by rfl
      simp only [walk, hr]
      rw [traversal_116 f (by omega), traversal_135 f (by omega)]
      change (List.range' 102 15 ++ List.range' (102+15) 19) ++
        [102+(15+19)] = List.range' 102 ((15+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 102) (n := 15+19)).symm

private theorem traversal_137 (fuel : Nat) (hf : 137 < fuel) :
    walk nodes fuel 137 = List.range' 41 97 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 137).rule = .split 1 (35/16) 101 136 := by rfl
      simp only [walk, hr]
      rw [traversal_101 f (by omega), traversal_136 f (by omega)]
      change (List.range' 41 61 ++ List.range' (41+61) 35) ++
        [41+(61+35)] = List.range' 41 ((61+35)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 61+35)).symm

private theorem traversal_138 (fuel : Nat) (hf : 138 < fuel) :
    walk nodes fuel 138 = List.range' 138 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 138).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_139 (fuel : Nat) (hf : 139 < fuel) :
    walk nodes fuel 139 = List.range' 139 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 139).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_140 (fuel : Nat) (hf : 140 < fuel) :
    walk nodes fuel 140 = List.range' 138 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 140).rule = .split 3 (3/16) 138 139 := by rfl
      simp only [walk, hr]
      rw [traversal_138 f (by omega), traversal_139 f (by omega)]
      change (List.range' 138 1 ++ List.range' (138+1) 1) ++
        [138+(1+1)] = List.range' 138 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 138) (n := 1+1)).symm

private theorem traversal_141 (fuel : Nat) (hf : 141 < fuel) :
    walk nodes fuel 141 = List.range' 141 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 141).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_142 (fuel : Nat) (hf : 142 < fuel) :
    walk nodes fuel 142 = List.range' 142 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 142).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_143 (fuel : Nat) (hf : 143 < fuel) :
    walk nodes fuel 143 = List.range' 141 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 143).rule = .split 3 (3/16) 141 142 := by rfl
      simp only [walk, hr]
      rw [traversal_141 f (by omega), traversal_142 f (by omega)]
      change (List.range' 141 1 ++ List.range' (141+1) 1) ++
        [141+(1+1)] = List.range' 141 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 141) (n := 1+1)).symm

private theorem traversal_144 (fuel : Nat) (hf : 144 < fuel) :
    walk nodes fuel 144 = List.range' 138 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 144).rule = .split 2 (35/64) 140 143 := by rfl
      simp only [walk, hr]
      rw [traversal_140 f (by omega), traversal_143 f (by omega)]
      change (List.range' 138 3 ++ List.range' (138+3) 3) ++
        [138+(3+3)] = List.range' 138 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 138) (n := 3+3)).symm

private theorem traversal_145 (fuel : Nat) (hf : 145 < fuel) :
    walk nodes fuel 145 = List.range' 145 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 145).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_146 (fuel : Nat) (hf : 146 < fuel) :
    walk nodes fuel 146 = List.range' 138 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 146).rule = .split 1 (35/16) 144 145 := by rfl
      simp only [walk, hr]
      rw [traversal_144 f (by omega), traversal_145 f (by omega)]
      change (List.range' 138 7 ++ List.range' (138+7) 1) ++
        [138+(7+1)] = List.range' 138 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 138) (n := 7+1)).symm

private theorem traversal_147 (fuel : Nat) (hf : 147 < fuel) :
    walk nodes fuel 147 = List.range' 41 107 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 147).rule = .split 0 (1/20) 137 146 := by rfl
      simp only [walk, hr]
      rw [traversal_137 f (by omega), traversal_146 f (by omega)]
      change (List.range' 41 97 ++ List.range' (41+97) 9) ++
        [41+(97+9)] = List.range' 41 ((97+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 97+9)).symm

private theorem traversal_148 (fuel : Nat) (hf : 148 < fuel) :
    walk nodes fuel 148 = List.range' 148 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 148).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_149 (fuel : Nat) (hf : 149 < fuel) :
    walk nodes fuel 149 = List.range' 41 109 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 149).rule = .split 3 (3/8) 147 148 := by rfl
      simp only [walk, hr]
      rw [traversal_147 f (by omega), traversal_148 f (by omega)]
      change (List.range' 41 107 ++ List.range' (41+107) 1) ++
        [41+(107+1)] = List.range' 41 ((107+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 107+1)).symm

private theorem traversal_150 (fuel : Nat) (hf : 150 < fuel) :
    walk nodes fuel 150 = List.range' 150 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 150).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_151 (fuel : Nat) (hf : 151 < fuel) :
    walk nodes fuel 151 = List.range' 151 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 151).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_152 (fuel : Nat) (hf : 152 < fuel) :
    walk nodes fuel 152 = List.range' 150 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 152).rule = .split 3 (3/16) 150 151 := by rfl
      simp only [walk, hr]
      rw [traversal_150 f (by omega), traversal_151 f (by omega)]
      change (List.range' 150 1 ++ List.range' (150+1) 1) ++
        [150+(1+1)] = List.range' 150 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 150) (n := 1+1)).symm

private theorem traversal_153 (fuel : Nat) (hf : 153 < fuel) :
    walk nodes fuel 153 = List.range' 153 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 153).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_154 (fuel : Nat) (hf : 154 < fuel) :
    walk nodes fuel 154 = List.range' 154 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 154).rule = .bound .leftEnd 8 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_155 (fuel : Nat) (hf : 155 < fuel) :
    walk nodes fuel 155 = List.range' 155 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 155).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_156 (fuel : Nat) (hf : 156 < fuel) :
    walk nodes fuel 156 = List.range' 154 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 156).rule = .split 1 (65/32) 154 155 := by rfl
      simp only [walk, hr]
      rw [traversal_154 f (by omega), traversal_155 f (by omega)]
      change (List.range' 154 1 ++ List.range' (154+1) 1) ++
        [154+(1+1)] = List.range' 154 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 154) (n := 1+1)).symm

private theorem traversal_157 (fuel : Nat) (hf : 157 < fuel) :
    walk nodes fuel 157 = List.range' 157 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 157).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_158 (fuel : Nat) (hf : 158 < fuel) :
    walk nodes fuel 158 = List.range' 154 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 158).rule = .split 0 (1/40) 156 157 := by rfl
      simp only [walk, hr]
      rw [traversal_156 f (by omega), traversal_157 f (by omega)]
      change (List.range' 154 3 ++ List.range' (154+3) 1) ++
        [154+(3+1)] = List.range' 154 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 154) (n := 3+1)).symm

private theorem traversal_159 (fuel : Nat) (hf : 159 < fuel) :
    walk nodes fuel 159 = List.range' 153 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 159).rule = .split 3 (3/16) 153 158 := by rfl
      simp only [walk, hr]
      rw [traversal_153 f (by omega), traversal_158 f (by omega)]
      change (List.range' 153 1 ++ List.range' (153+1) 5) ++
        [153+(1+5)] = List.range' 153 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 153) (n := 1+5)).symm

private theorem traversal_160 (fuel : Nat) (hf : 160 < fuel) :
    walk nodes fuel 160 = List.range' 150 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 160).rule = .split 2 (73/64) 152 159 := by rfl
      simp only [walk, hr]
      rw [traversal_152 f (by omega), traversal_159 f (by omega)]
      change (List.range' 150 3 ++ List.range' (150+3) 7) ++
        [150+(3+7)] = List.range' 150 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 150) (n := 3+7)).symm

private theorem traversal_161 (fuel : Nat) (hf : 161 < fuel) :
    walk nodes fuel 161 = List.range' 161 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 161).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_162 (fuel : Nat) (hf : 162 < fuel) :
    walk nodes fuel 162 = List.range' 162 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 162).rule = .bound .leftEnd 2 (34015/32768) (62489/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_163 (fuel : Nat) (hf : 163 < fuel) :
    walk nodes fuel 163 = List.range' 163 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 163).rule = .bound .leftEnd 8 (7169/8192) (298007/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_164 (fuel : Nat) (hf : 164 < fuel) :
    walk nodes fuel 164 = List.range' 162 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 164).rule = .split 3 (9/32) 162 163 := by rfl
      simp only [walk, hr]
      rw [traversal_162 f (by omega), traversal_163 f (by omega)]
      change (List.range' 162 1 ++ List.range' (162+1) 1) ++
        [162+(1+1)] = List.range' 162 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 162) (n := 1+1)).symm

private theorem traversal_165 (fuel : Nat) (hf : 165 < fuel) :
    walk nodes fuel 165 = List.range' 165 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 165).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_166 (fuel : Nat) (hf : 166 < fuel) :
    walk nodes fuel 166 = List.range' 162 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 166).rule = .split 2 (127/128) 164 165 := by rfl
      simp only [walk, hr]
      rw [traversal_164 f (by omega), traversal_165 f (by omega)]
      change (List.range' 162 3 ++ List.range' (162+3) 1) ++
        [162+(3+1)] = List.range' 162 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 162) (n := 3+1)).symm

private theorem traversal_167 (fuel : Nat) (hf : 167 < fuel) :
    walk nodes fuel 167 = List.range' 167 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 167).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_168 (fuel : Nat) (hf : 168 < fuel) :
    walk nodes fuel 168 = List.range' 162 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 168).rule = .split 1 (75/32) 166 167 := by rfl
      simp only [walk, hr]
      rw [traversal_166 f (by omega), traversal_167 f (by omega)]
      change (List.range' 162 5 ++ List.range' (162+5) 1) ++
        [162+(5+1)] = List.range' 162 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 162) (n := 5+1)).symm

private theorem traversal_169 (fuel : Nat) (hf : 169 < fuel) :
    walk nodes fuel 169 = List.range' 169 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 169).rule = .bound .leftEnd 2 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_170 (fuel : Nat) (hf : 170 < fuel) :
    walk nodes fuel 170 = List.range' 162 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 170).rule = .split 0 (1/40) 168 169 := by rfl
      simp only [walk, hr]
      rw [traversal_168 f (by omega), traversal_169 f (by omega)]
      change (List.range' 162 7 ++ List.range' (162+7) 1) ++
        [162+(7+1)] = List.range' 162 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 162) (n := 7+1)).symm

private theorem traversal_171 (fuel : Nat) (hf : 171 < fuel) :
    walk nodes fuel 171 = List.range' 161 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 171).rule = .split 3 (3/16) 161 170 := by rfl
      simp only [walk, hr]
      rw [traversal_161 f (by omega), traversal_170 f (by omega)]
      change (List.range' 161 1 ++ List.range' (161+1) 9) ++
        [161+(1+9)] = List.range' 161 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 1+9)).symm

private theorem traversal_172 (fuel : Nat) (hf : 172 < fuel) :
    walk nodes fuel 172 = List.range' 172 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 172).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_173 (fuel : Nat) (hf : 173 < fuel) :
    walk nodes fuel 173 = List.range' 161 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 173).rule = .split 2 (73/64) 171 172 := by rfl
      simp only [walk, hr]
      rw [traversal_171 f (by omega), traversal_172 f (by omega)]
      change (List.range' 161 11 ++ List.range' (161+11) 1) ++
        [161+(11+1)] = List.range' 161 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 11+1)).symm

private theorem traversal_174 (fuel : Nat) (hf : 174 < fuel) :
    walk nodes fuel 174 = List.range' 150 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 174).rule = .split 1 (35/16) 160 173 := by rfl
      simp only [walk, hr]
      rw [traversal_160 f (by omega), traversal_173 f (by omega)]
      change (List.range' 150 11 ++ List.range' (150+11) 13) ++
        [150+(11+13)] = List.range' 150 ((11+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 150) (n := 11+13)).symm

private theorem traversal_175 (fuel : Nat) (hf : 175 < fuel) :
    walk nodes fuel 175 = List.range' 175 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 175).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_176 (fuel : Nat) (hf : 176 < fuel) :
    walk nodes fuel 176 = List.range' 150 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 176).rule = .split 0 (1/20) 174 175 := by rfl
      simp only [walk, hr]
      rw [traversal_174 f (by omega), traversal_175 f (by omega)]
      change (List.range' 150 25 ++ List.range' (150+25) 1) ++
        [150+(25+1)] = List.range' 150 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 150) (n := 25+1)).symm

theorem traversal_177 (fuel : Nat) (hf : 177 < fuel) :
    walk nodes fuel 177 = List.range' 177 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 177).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_178 (fuel : Nat) (hf : 178 < fuel) :
    walk nodes fuel 178 = List.range' 178 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 178).rule = .bound .leftEnd 8 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_179 (fuel : Nat) (hf : 179 < fuel) :
    walk nodes fuel 179 = List.range' 179 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 179).rule = .bound .leftEnd 1 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_180 (fuel : Nat) (hf : 180 < fuel) :
    walk nodes fuel 180 = List.range' 178 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 180).rule = .split 1 (75/32) 178 179 := by rfl
      simp only [walk, hr]
      rw [traversal_178 f (by omega), traversal_179 f (by omega)]
      change (List.range' 178 1 ++ List.range' (178+1) 1) ++
        [178+(1+1)] = List.range' 178 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 178) (n := 1+1)).symm

private theorem traversal_181 (fuel : Nat) (hf : 181 < fuel) :
    walk nodes fuel 181 = List.range' 181 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 181).rule = .bound .leftEnd 1 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_182 (fuel : Nat) (hf : 182 < fuel) :
    walk nodes fuel 182 = List.range' 178 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 182).rule = .split 0 (1/40) 180 181 := by rfl
      simp only [walk, hr]
      rw [traversal_180 f (by omega), traversal_181 f (by omega)]
      change (List.range' 178 3 ++ List.range' (178+3) 1) ++
        [178+(3+1)] = List.range' 178 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 178) (n := 3+1)).symm

private theorem traversal_183 (fuel : Nat) (hf : 183 < fuel) :
    walk nodes fuel 183 = List.range' 183 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 183).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_184 (fuel : Nat) (hf : 184 < fuel) :
    walk nodes fuel 184 = List.range' 178 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 184).rule = .split 3 (9/16) 182 183 := by rfl
      simp only [walk, hr]
      rw [traversal_182 f (by omega), traversal_183 f (by omega)]
      change (List.range' 178 5 ++ List.range' (178+5) 1) ++
        [178+(5+1)] = List.range' 178 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 178) (n := 5+1)).symm

private theorem traversal_185 (fuel : Nat) (hf : 185 < fuel) :
    walk nodes fuel 185 = List.range' 185 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 185).rule = .bound .leftEnd 2 (75791/98304) (338955/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_186 (fuel : Nat) (hf : 186 < fuel) :
    walk nodes fuel 186 = List.range' 186 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 186).rule = .bound .leftEnd 8 (34261/49152) (93825/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_187 (fuel : Nat) (hf : 187 < fuel) :
    walk nodes fuel 187 = List.range' 185 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 187).rule = .split 3 (15/32) 185 186 := by rfl
      simp only [walk, hr]
      rw [traversal_185 f (by omega), traversal_186 f (by omega)]
      change (List.range' 185 1 ++ List.range' (185+1) 1) ++
        [185+(1+1)] = List.range' 185 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 185) (n := 1+1)).symm

private theorem traversal_188 (fuel : Nat) (hf : 188 < fuel) :
    walk nodes fuel 188 = List.range' 188 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 188).rule = .bound .leftEnd 2 (75791/98304) (338955/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_189 (fuel : Nat) (hf : 189 < fuel) :
    walk nodes fuel 189 = List.range' 189 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 189).rule = .bound .leftEnd 8 (34261/49152) (93825/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_190 (fuel : Nat) (hf : 190 < fuel) :
    walk nodes fuel 190 = List.range' 188 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 190).rule = .split 3 (15/32) 188 189 := by rfl
      simp only [walk, hr]
      rw [traversal_188 f (by omega), traversal_189 f (by omega)]
      change (List.range' 188 1 ++ List.range' (188+1) 1) ++
        [188+(1+1)] = List.range' 188 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 188) (n := 1+1)).symm

private theorem traversal_191 (fuel : Nat) (hf : 191 < fuel) :
    walk nodes fuel 191 = List.range' 185 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 191).rule = .split 2 (165/128) 187 190 := by rfl
      simp only [walk, hr]
      rw [traversal_187 f (by omega), traversal_190 f (by omega)]
      change (List.range' 185 3 ++ List.range' (185+3) 3) ++
        [185+(3+3)] = List.range' 185 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 185) (n := 3+3)).symm

private theorem traversal_192 (fuel : Nat) (hf : 192 < fuel) :
    walk nodes fuel 192 = List.range' 192 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 192).rule = .bound .leftEnd 2 (75791/98304) (338955/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_193 (fuel : Nat) (hf : 193 < fuel) :
    walk nodes fuel 193 = List.range' 193 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 193).rule = .bound .leftEnd 1 (34261/49152) (93825/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_194 (fuel : Nat) (hf : 194 < fuel) :
    walk nodes fuel 194 = List.range' 192 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 194).rule = .split 3 (15/32) 192 193 := by rfl
      simp only [walk, hr]
      rw [traversal_192 f (by omega), traversal_193 f (by omega)]
      change (List.range' 192 1 ++ List.range' (192+1) 1) ++
        [192+(1+1)] = List.range' 192 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 192) (n := 1+1)).symm

private theorem traversal_195 (fuel : Nat) (hf : 195 < fuel) :
    walk nodes fuel 195 = List.range' 195 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 195).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_196 (fuel : Nat) (hf : 196 < fuel) :
    walk nodes fuel 196 = List.range' 192 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 196).rule = .split 2 (165/128) 194 195 := by rfl
      simp only [walk, hr]
      rw [traversal_194 f (by omega), traversal_195 f (by omega)]
      change (List.range' 192 3 ++ List.range' (192+3) 1) ++
        [192+(3+1)] = List.range' 192 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 192) (n := 3+1)).symm

private theorem traversal_197 (fuel : Nat) (hf : 197 < fuel) :
    walk nodes fuel 197 = List.range' 185 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 197).rule = .split 1 (75/32) 191 196 := by rfl
      simp only [walk, hr]
      rw [traversal_191 f (by omega), traversal_196 f (by omega)]
      change (List.range' 185 7 ++ List.range' (185+7) 5) ++
        [185+(7+5)] = List.range' 185 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 185) (n := 7+5)).symm

private theorem traversal_198 (fuel : Nat) (hf : 198 < fuel) :
    walk nodes fuel 198 = List.range' 198 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 198).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_199 (fuel : Nat) (hf : 199 < fuel) :
    walk nodes fuel 199 = List.range' 185 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 199).rule = .split 0 (1/40) 197 198 := by rfl
      simp only [walk, hr]
      rw [traversal_197 f (by omega), traversal_198 f (by omega)]
      change (List.range' 185 13 ++ List.range' (185+13) 1) ++
        [185+(13+1)] = List.range' 185 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 185) (n := 13+1)).symm

theorem traversal_200 (fuel : Nat) (hf : 200 < fuel) :
    walk nodes fuel 200 = List.range' 200 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 200).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_201 (fuel : Nat) (hf : 201 < fuel) :
    walk nodes fuel 201 = List.range' 201 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 201).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
