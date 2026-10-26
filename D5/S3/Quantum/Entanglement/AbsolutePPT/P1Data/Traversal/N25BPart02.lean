/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02.traversal_160,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02.traversal_181,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02.traversal_182,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart02.traversal_201
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart01
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_135 (fuel : Nat) (hf : 135 < fuel) :
    walk nodes fuel 135 = List.range' 135 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 135).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_136 (fuel : Nat) (hf : 136 < fuel) :
    walk nodes fuel 136 = List.range' 134 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 136).rule = .split 1 (65/32) 134 135 := by rfl
      simp only [walk, hr]
      rw [traversal_134 f (by omega), traversal_135 f (by omega)]
      change (List.range' 134 1 ++ List.range' (134+1) 1) ++
        [134+(1+1)] = List.range' 134 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 134) (n := 1+1)).symm

private theorem traversal_137 (fuel : Nat) (hf : 137 < fuel) :
    walk nodes fuel 137 = List.range' 137 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 137).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_138 (fuel : Nat) (hf : 138 < fuel) :
    walk nodes fuel 138 = List.range' 134 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 138).rule = .split 0 (1/40) 136 137 := by rfl
      simp only [walk, hr]
      rw [traversal_136 f (by omega), traversal_137 f (by omega)]
      change (List.range' 134 3 ++ List.range' (134+3) 1) ++
        [134+(3+1)] = List.range' 134 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 134) (n := 3+1)).symm

private theorem traversal_139 (fuel : Nat) (hf : 139 < fuel) :
    walk nodes fuel 139 = List.range' 133 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 139).rule = .split 3 (3/16) 133 138 := by rfl
      simp only [walk, hr]
      rw [traversal_133 f (by omega), traversal_138 f (by omega)]
      change (List.range' 133 1 ++ List.range' (133+1) 5) ++
        [133+(1+5)] = List.range' 133 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 133) (n := 1+5)).symm

private theorem traversal_140 (fuel : Nat) (hf : 140 < fuel) :
    walk nodes fuel 140 = List.range' 130 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 140).rule = .split 2 (73/64) 132 139 := by rfl
      simp only [walk, hr]
      rw [traversal_132 f (by omega), traversal_139 f (by omega)]
      change (List.range' 130 3 ++ List.range' (130+3) 7) ++
        [130+(3+7)] = List.range' 130 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 130) (n := 3+7)).symm

private theorem traversal_141 (fuel : Nat) (hf : 141 < fuel) :
    walk nodes fuel 141 = List.range' 141 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 141).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_142 (fuel : Nat) (hf : 142 < fuel) :
    walk nodes fuel 142 = List.range' 142 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 142).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_143 (fuel : Nat) (hf : 143 < fuel) :
    walk nodes fuel 143 = List.range' 143 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 143).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_144 (fuel : Nat) (hf : 144 < fuel) :
    walk nodes fuel 144 = List.range' 142 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 144).rule = .split 2 (127/128) 142 143 := by rfl
      simp only [walk, hr]
      rw [traversal_142 f (by omega), traversal_143 f (by omega)]
      change (List.range' 142 1 ++ List.range' (142+1) 1) ++
        [142+(1+1)] = List.range' 142 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 142) (n := 1+1)).symm

private theorem traversal_145 (fuel : Nat) (hf : 145 < fuel) :
    walk nodes fuel 145 = List.range' 145 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 145).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_146 (fuel : Nat) (hf : 146 < fuel) :
    walk nodes fuel 146 = List.range' 142 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 146).rule = .split 1 (75/32) 144 145 := by rfl
      simp only [walk, hr]
      rw [traversal_144 f (by omega), traversal_145 f (by omega)]
      change (List.range' 142 3 ++ List.range' (142+3) 1) ++
        [142+(3+1)] = List.range' 142 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 142) (n := 3+1)).symm

private theorem traversal_147 (fuel : Nat) (hf : 147 < fuel) :
    walk nodes fuel 147 = List.range' 147 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 147).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_148 (fuel : Nat) (hf : 148 < fuel) :
    walk nodes fuel 148 = List.range' 142 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 148).rule = .split 0 (1/40) 146 147 := by rfl
      simp only [walk, hr]
      rw [traversal_146 f (by omega), traversal_147 f (by omega)]
      change (List.range' 142 5 ++ List.range' (142+5) 1) ++
        [142+(5+1)] = List.range' 142 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 142) (n := 5+1)).symm

private theorem traversal_149 (fuel : Nat) (hf : 149 < fuel) :
    walk nodes fuel 149 = List.range' 141 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 149).rule = .split 3 (3/16) 141 148 := by rfl
      simp only [walk, hr]
      rw [traversal_141 f (by omega), traversal_148 f (by omega)]
      change (List.range' 141 1 ++ List.range' (141+1) 7) ++
        [141+(1+7)] = List.range' 141 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 141) (n := 1+7)).symm

private theorem traversal_150 (fuel : Nat) (hf : 150 < fuel) :
    walk nodes fuel 150 = List.range' 150 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 150).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_151 (fuel : Nat) (hf : 151 < fuel) :
    walk nodes fuel 151 = List.range' 141 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 151).rule = .split 2 (73/64) 149 150 := by rfl
      simp only [walk, hr]
      rw [traversal_149 f (by omega), traversal_150 f (by omega)]
      change (List.range' 141 9 ++ List.range' (141+9) 1) ++
        [141+(9+1)] = List.range' 141 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 141) (n := 9+1)).symm

private theorem traversal_152 (fuel : Nat) (hf : 152 < fuel) :
    walk nodes fuel 152 = List.range' 130 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 152).rule = .split 1 (35/16) 140 151 := by rfl
      simp only [walk, hr]
      rw [traversal_140 f (by omega), traversal_151 f (by omega)]
      change (List.range' 130 11 ++ List.range' (130+11) 11) ++
        [130+(11+11)] = List.range' 130 ((11+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 130) (n := 11+11)).symm

private theorem traversal_153 (fuel : Nat) (hf : 153 < fuel) :
    walk nodes fuel 153 = List.range' 153 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 153).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_154 (fuel : Nat) (hf : 154 < fuel) :
    walk nodes fuel 154 = List.range' 130 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 154).rule = .split 0 (1/20) 152 153 := by rfl
      simp only [walk, hr]
      rw [traversal_152 f (by omega), traversal_153 f (by omega)]
      change (List.range' 130 23 ++ List.range' (130+23) 1) ++
        [130+(23+1)] = List.range' 130 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 130) (n := 23+1)).symm

private theorem traversal_155 (fuel : Nat) (hf : 155 < fuel) :
    walk nodes fuel 155 = List.range' 155 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 155).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_156 (fuel : Nat) (hf : 156 < fuel) :
    walk nodes fuel 156 = List.range' 130 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 156).rule = .split 3 (3/8) 154 155 := by rfl
      simp only [walk, hr]
      rw [traversal_154 f (by omega), traversal_155 f (by omega)]
      change (List.range' 130 25 ++ List.range' (130+25) 1) ++
        [130+(25+1)] = List.range' 130 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 130) (n := 25+1)).symm

private theorem traversal_157 (fuel : Nat) (hf : 157 < fuel) :
    walk nodes fuel 157 = List.range' 41 117 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 157).rule = .split 2 (27/32) 129 156 := by rfl
      simp only [walk, hr]
      rw [traversal_129 f (by omega), traversal_156 f (by omega)]
      change (List.range' 41 89 ++ List.range' (41+89) 27) ++
        [41+(89+27)] = List.range' 41 ((89+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 89+27)).symm

private theorem traversal_158 (fuel : Nat) (hf : 158 < fuel) :
    walk nodes fuel 158 = List.range' 2 157 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 158).rule = .split 1 (15/8) 40 157 := by rfl
      simp only [walk, hr]
      rw [traversal_40 f (by omega), traversal_157 f (by omega)]
      change (List.range' 2 39 ++ List.range' (2+39) 117) ++
        [2+(39+117)] = List.range' 2 ((39+117)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 39+117)).symm

private theorem traversal_159 (fuel : Nat) (hf : 159 < fuel) :
    walk nodes fuel 159 = List.range' 159 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 159).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_160 (fuel : Nat) (hf : 160 < fuel) :
    walk nodes fuel 160 = List.range' 2 159 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 160).rule = .split 3 (3/4) 158 159 := by rfl
      simp only [walk, hr]
      rw [traversal_158 f (by omega), traversal_159 f (by omega)]
      change (List.range' 2 157 ++ List.range' (2+157) 1) ++
        [2+(157+1)] = List.range' 2 ((157+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 157+1)).symm

private theorem traversal_161 (fuel : Nat) (hf : 161 < fuel) :
    walk nodes fuel 161 = List.range' 161 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 161).rule = .bound .leftEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_162 (fuel : Nat) (hf : 162 < fuel) :
    walk nodes fuel 162 = List.range' 162 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 162).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_163 (fuel : Nat) (hf : 163 < fuel) :
    walk nodes fuel 163 = List.range' 161 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 163).rule = .split 1 (25/16) 161 162 := by rfl
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
      have hr : (node nodes 164).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_165 (fuel : Nat) (hf : 165 < fuel) :
    walk nodes fuel 165 = List.range' 161 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 165).rule = .split 0 (1/20) 163 164 := by rfl
      simp only [walk, hr]
      rw [traversal_163 f (by omega), traversal_164 f (by omega)]
      change (List.range' 161 3 ++ List.range' (161+3) 1) ++
        [161+(3+1)] = List.range' 161 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 3+1)).symm

private theorem traversal_166 (fuel : Nat) (hf : 166 < fuel) :
    walk nodes fuel 166 = List.range' 166 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 166).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_167 (fuel : Nat) (hf : 167 < fuel) :
    walk nodes fuel 167 = List.range' 161 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 167).rule = .split 3 (3/8) 165 166 := by rfl
      simp only [walk, hr]
      rw [traversal_165 f (by omega), traversal_166 f (by omega)]
      change (List.range' 161 5 ++ List.range' (161+5) 1) ++
        [161+(5+1)] = List.range' 161 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 5+1)).symm

private theorem traversal_168 (fuel : Nat) (hf : 168 < fuel) :
    walk nodes fuel 168 = List.range' 168 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 168).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_169 (fuel : Nat) (hf : 169 < fuel) :
    walk nodes fuel 169 = List.range' 169 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 169).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_170 (fuel : Nat) (hf : 170 < fuel) :
    walk nodes fuel 170 = List.range' 170 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 170).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_171 (fuel : Nat) (hf : 171 < fuel) :
    walk nodes fuel 171 = List.range' 171 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 171).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_172 (fuel : Nat) (hf : 172 < fuel) :
    walk nodes fuel 172 = List.range' 170 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 172).rule = .split 3 (9/16) 170 171 := by rfl
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
      have hr : (node nodes 173).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_174 (fuel : Nat) (hf : 174 < fuel) :
    walk nodes fuel 174 = List.range' 170 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 174).rule = .split 2 (149/64) 172 173 := by rfl
      simp only [walk, hr]
      rw [traversal_172 f (by omega), traversal_173 f (by omega)]
      change (List.range' 170 3 ++ List.range' (170+3) 1) ++
        [170+(3+1)] = List.range' 170 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 170) (n := 3+1)).symm

private theorem traversal_175 (fuel : Nat) (hf : 175 < fuel) :
    walk nodes fuel 175 = List.range' 169 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 175).rule = .split 1 (25/16) 169 174 := by rfl
      simp only [walk, hr]
      rw [traversal_169 f (by omega), traversal_174 f (by omega)]
      change (List.range' 169 1 ++ List.range' (169+1) 5) ++
        [169+(1+5)] = List.range' 169 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 169) (n := 1+5)).symm

private theorem traversal_176 (fuel : Nat) (hf : 176 < fuel) :
    walk nodes fuel 176 = List.range' 176 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 176).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_177 (fuel : Nat) (hf : 177 < fuel) :
    walk nodes fuel 177 = List.range' 177 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 177).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_178 (fuel : Nat) (hf : 178 < fuel) :
    walk nodes fuel 178 = List.range' 176 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 178).rule = .split 1 (25/16) 176 177 := by rfl
      simp only [walk, hr]
      rw [traversal_176 f (by omega), traversal_177 f (by omega)]
      change (List.range' 176 1 ++ List.range' (176+1) 1) ++
        [176+(1+1)] = List.range' 176 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 176) (n := 1+1)).symm

private theorem traversal_179 (fuel : Nat) (hf : 179 < fuel) :
    walk nodes fuel 179 = List.range' 169 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 179).rule = .split 0 (1/20) 175 178 := by rfl
      simp only [walk, hr]
      rw [traversal_175 f (by omega), traversal_178 f (by omega)]
      change (List.range' 169 7 ++ List.range' (169+7) 3) ++
        [169+(7+3)] = List.range' 169 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 169) (n := 7+3)).symm

private theorem traversal_180 (fuel : Nat) (hf : 180 < fuel) :
    walk nodes fuel 180 = List.range' 168 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 180).rule = .split 3 (3/8) 168 179 := by rfl
      simp only [walk, hr]
      rw [traversal_168 f (by omega), traversal_179 f (by omega)]
      change (List.range' 168 1 ++ List.range' (168+1) 11) ++
        [168+(1+11)] = List.range' 168 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 168) (n := 1+11)).symm

theorem traversal_181 (fuel : Nat) (hf : 181 < fuel) :
    walk nodes fuel 181 = List.range' 161 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 181).rule = .split 2 (65/32) 167 180 := by rfl
      simp only [walk, hr]
      rw [traversal_167 f (by omega), traversal_180 f (by omega)]
      change (List.range' 161 7 ++ List.range' (161+7) 13) ++
        [161+(7+13)] = List.range' 161 ((7+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 7+13)).symm

theorem traversal_182 (fuel : Nat) (hf : 182 < fuel) :
    walk nodes fuel 182 = List.range' 182 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 182).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_183 (fuel : Nat) (hf : 183 < fuel) :
    walk nodes fuel 183 = List.range' 183 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 183).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_184 (fuel : Nat) (hf : 184 < fuel) :
    walk nodes fuel 184 = List.range' 184 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 184).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_185 (fuel : Nat) (hf : 185 < fuel) :
    walk nodes fuel 185 = List.range' 185 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 185).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_186 (fuel : Nat) (hf : 186 < fuel) :
    walk nodes fuel 186 = List.range' 184 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 186).rule = .split 3 (9/16) 184 185 := by rfl
      simp only [walk, hr]
      rw [traversal_184 f (by omega), traversal_185 f (by omega)]
      change (List.range' 184 1 ++ List.range' (184+1) 1) ++
        [184+(1+1)] = List.range' 184 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 184) (n := 1+1)).symm

private theorem traversal_187 (fuel : Nat) (hf : 187 < fuel) :
    walk nodes fuel 187 = List.range' 183 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 187).rule = .split 2 (111/64) 183 186 := by rfl
      simp only [walk, hr]
      rw [traversal_183 f (by omega), traversal_186 f (by omega)]
      change (List.range' 183 1 ++ List.range' (183+1) 3) ++
        [183+(1+3)] = List.range' 183 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 183) (n := 1+3)).symm

private theorem traversal_188 (fuel : Nat) (hf : 188 < fuel) :
    walk nodes fuel 188 = List.range' 188 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 188).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_189 (fuel : Nat) (hf : 189 < fuel) :
    walk nodes fuel 189 = List.range' 189 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 189).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_190 (fuel : Nat) (hf : 190 < fuel) :
    walk nodes fuel 190 = List.range' 188 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 190).rule = .split 3 (9/16) 188 189 := by rfl
      simp only [walk, hr]
      rw [traversal_188 f (by omega), traversal_189 f (by omega)]
      change (List.range' 188 1 ++ List.range' (188+1) 1) ++
        [188+(1+1)] = List.range' 188 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 188) (n := 1+1)).symm

private theorem traversal_191 (fuel : Nat) (hf : 191 < fuel) :
    walk nodes fuel 191 = List.range' 191 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 191).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_192 (fuel : Nat) (hf : 192 < fuel) :
    walk nodes fuel 192 = List.range' 192 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 192).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_193 (fuel : Nat) (hf : 193 < fuel) :
    walk nodes fuel 193 = List.range' 193 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 193).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_194 (fuel : Nat) (hf : 194 < fuel) :
    walk nodes fuel 194 = List.range' 194 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 194).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_195 (fuel : Nat) (hf : 195 < fuel) :
    walk nodes fuel 195 = List.range' 193 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 195).rule = .split 2 (241/128) 193 194 := by rfl
      simp only [walk, hr]
      rw [traversal_193 f (by omega), traversal_194 f (by omega)]
      change (List.range' 193 1 ++ List.range' (193+1) 1) ++
        [193+(1+1)] = List.range' 193 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 193) (n := 1+1)).symm

private theorem traversal_196 (fuel : Nat) (hf : 196 < fuel) :
    walk nodes fuel 196 = List.range' 192 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 196).rule = .split 1 (75/32) 192 195 := by rfl
      simp only [walk, hr]
      rw [traversal_192 f (by omega), traversal_195 f (by omega)]
      change (List.range' 192 1 ++ List.range' (192+1) 3) ++
        [192+(1+3)] = List.range' 192 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 192) (n := 1+3)).symm

private theorem traversal_197 (fuel : Nat) (hf : 197 < fuel) :
    walk nodes fuel 197 = List.range' 197 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 197).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_198 (fuel : Nat) (hf : 198 < fuel) :
    walk nodes fuel 198 = List.range' 192 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 198).rule = .split 0 (1/40) 196 197 := by rfl
      simp only [walk, hr]
      rw [traversal_196 f (by omega), traversal_197 f (by omega)]
      change (List.range' 192 5 ++ List.range' (192+5) 1) ++
        [192+(5+1)] = List.range' 192 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 192) (n := 5+1)).symm

private theorem traversal_199 (fuel : Nat) (hf : 199 < fuel) :
    walk nodes fuel 199 = List.range' 191 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 199).rule = .split 3 (9/16) 191 198 := by rfl
      simp only [walk, hr]
      rw [traversal_191 f (by omega), traversal_198 f (by omega)]
      change (List.range' 191 1 ++ List.range' (191+1) 7) ++
        [191+(1+7)] = List.range' 191 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 191) (n := 1+7)).symm

private theorem traversal_200 (fuel : Nat) (hf : 200 < fuel) :
    walk nodes fuel 200 = List.range' 188 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 200).rule = .split 2 (111/64) 190 199 := by rfl
      simp only [walk, hr]
      rw [traversal_190 f (by omega), traversal_199 f (by omega)]
      change (List.range' 188 3 ++ List.range' (188+3) 9) ++
        [188+(3+9)] = List.range' 188 ((3+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 188) (n := 3+9)).symm

theorem traversal_201 (fuel : Nat) (hf : 201 < fuel) :
    walk nodes fuel 201 = List.range' 183 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 201).rule = .split 1 (35/16) 187 200 := by rfl
      simp only [walk, hr]
      rw [traversal_187 f (by omega), traversal_200 f (by omega)]
      change (List.range' 183 5 ++ List.range' (183+5) 13) ++
        [183+(5+13)] = List.range' 183 ((5+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 183) (n := 5+13)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
