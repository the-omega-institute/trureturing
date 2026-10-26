/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_216,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_227,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_228,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_233,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_262,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_263,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_264,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_265,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_266,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_267,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_268,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart03.traversal_269
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart02
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_202 (fuel : Nat) (hf : 202 < fuel) :
    walk nodes fuel 202 = List.range' 200 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 202).rule = .split 1 (75/32) 200 201 := by rfl
      simp only [walk, hr]
      rw [traversal_200 f (by omega), traversal_201 f (by omega)]
      change (List.range' 200 1 ++ List.range' (200+1) 1) ++
        [200+(1+1)] = List.range' 200 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 200) (n := 1+1)).symm

private theorem traversal_203 (fuel : Nat) (hf : 203 < fuel) :
    walk nodes fuel 203 = List.range' 203 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 203).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_204 (fuel : Nat) (hf : 204 < fuel) :
    walk nodes fuel 204 = List.range' 200 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 204).rule = .split 0 (1/40) 202 203 := by rfl
      simp only [walk, hr]
      rw [traversal_202 f (by omega), traversal_203 f (by omega)]
      change (List.range' 200 3 ++ List.range' (200+3) 1) ++
        [200+(3+1)] = List.range' 200 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 200) (n := 3+1)).symm

private theorem traversal_205 (fuel : Nat) (hf : 205 < fuel) :
    walk nodes fuel 205 = List.range' 185 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 205).rule = .split 3 (9/16) 199 204 := by rfl
      simp only [walk, hr]
      rw [traversal_199 f (by omega), traversal_204 f (by omega)]
      change (List.range' 185 15 ++ List.range' (185+15) 5) ++
        [185+(15+5)] = List.range' 185 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 185) (n := 15+5)).symm

private theorem traversal_206 (fuel : Nat) (hf : 206 < fuel) :
    walk nodes fuel 206 = List.range' 178 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 206).rule = .split 2 (73/64) 184 205 := by rfl
      simp only [walk, hr]
      rw [traversal_184 f (by omega), traversal_205 f (by omega)]
      change (List.range' 178 7 ++ List.range' (178+7) 21) ++
        [178+(7+21)] = List.range' 178 ((7+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 178) (n := 7+21)).symm

private theorem traversal_207 (fuel : Nat) (hf : 207 < fuel) :
    walk nodes fuel 207 = List.range' 177 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 207).rule = .split 1 (35/16) 177 206 := by rfl
      simp only [walk, hr]
      rw [traversal_177 f (by omega), traversal_206 f (by omega)]
      change (List.range' 177 1 ++ List.range' (177+1) 29) ++
        [177+(1+29)] = List.range' 177 ((1+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 177) (n := 1+29)).symm

private theorem traversal_208 (fuel : Nat) (hf : 208 < fuel) :
    walk nodes fuel 208 = List.range' 208 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 208).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_209 (fuel : Nat) (hf : 209 < fuel) :
    walk nodes fuel 209 = List.range' 209 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 209).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_210 (fuel : Nat) (hf : 210 < fuel) :
    walk nodes fuel 210 = List.range' 208 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 210).rule = .split 1 (35/16) 208 209 := by rfl
      simp only [walk, hr]
      rw [traversal_208 f (by omega), traversal_209 f (by omega)]
      change (List.range' 208 1 ++ List.range' (208+1) 1) ++
        [208+(1+1)] = List.range' 208 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 208) (n := 1+1)).symm

private theorem traversal_211 (fuel : Nat) (hf : 211 < fuel) :
    walk nodes fuel 211 = List.range' 177 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 211).rule = .split 0 (1/20) 207 210 := by rfl
      simp only [walk, hr]
      rw [traversal_207 f (by omega), traversal_210 f (by omega)]
      change (List.range' 177 31 ++ List.range' (177+31) 3) ++
        [177+(31+3)] = List.range' 177 ((31+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 177) (n := 31+3)).symm

private theorem traversal_212 (fuel : Nat) (hf : 212 < fuel) :
    walk nodes fuel 212 = List.range' 150 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 212).rule = .split 3 (3/8) 176 211 := by rfl
      simp only [walk, hr]
      rw [traversal_176 f (by omega), traversal_211 f (by omega)]
      change (List.range' 150 27 ++ List.range' (150+27) 35) ++
        [150+(27+35)] = List.range' 150 ((27+35)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 150) (n := 27+35)).symm

private theorem traversal_213 (fuel : Nat) (hf : 213 < fuel) :
    walk nodes fuel 213 = List.range' 41 173 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 213).rule = .split 2 (27/32) 149 212 := by rfl
      simp only [walk, hr]
      rw [traversal_149 f (by omega), traversal_212 f (by omega)]
      change (List.range' 41 109 ++ List.range' (41+109) 63) ++
        [41+(109+63)] = List.range' 41 ((109+63)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 41) (n := 109+63)).symm

private theorem traversal_214 (fuel : Nat) (hf : 214 < fuel) :
    walk nodes fuel 214 = List.range' 2 213 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 214).rule = .split 1 (15/8) 40 213 := by rfl
      simp only [walk, hr]
      rw [traversal_40 f (by omega), traversal_213 f (by omega)]
      change (List.range' 2 39 ++ List.range' (2+39) 173) ++
        [2+(39+173)] = List.range' 2 ((39+173)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 39+173)).symm

private theorem traversal_215 (fuel : Nat) (hf : 215 < fuel) :
    walk nodes fuel 215 = List.range' 215 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 215).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_216 (fuel : Nat) (hf : 216 < fuel) :
    walk nodes fuel 216 = List.range' 2 215 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 216).rule = .split 3 (3/4) 214 215 := by rfl
      simp only [walk, hr]
      rw [traversal_214 f (by omega), traversal_215 f (by omega)]
      change (List.range' 2 213 ++ List.range' (2+213) 1) ++
        [2+(213+1)] = List.range' 2 ((213+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 213+1)).symm

private theorem traversal_217 (fuel : Nat) (hf : 217 < fuel) :
    walk nodes fuel 217 = List.range' 217 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 217).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_218 (fuel : Nat) (hf : 218 < fuel) :
    walk nodes fuel 218 = List.range' 218 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 218).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_219 (fuel : Nat) (hf : 219 < fuel) :
    walk nodes fuel 219 = List.range' 217 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 219).rule = .split 1 (25/16) 217 218 := by rfl
      simp only [walk, hr]
      rw [traversal_217 f (by omega), traversal_218 f (by omega)]
      change (List.range' 217 1 ++ List.range' (217+1) 1) ++
        [217+(1+1)] = List.range' 217 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 1+1)).symm

private theorem traversal_220 (fuel : Nat) (hf : 220 < fuel) :
    walk nodes fuel 220 = List.range' 220 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 220).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_221 (fuel : Nat) (hf : 221 < fuel) :
    walk nodes fuel 221 = List.range' 217 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 221).rule = .split 0 (1/20) 219 220 := by rfl
      simp only [walk, hr]
      rw [traversal_219 f (by omega), traversal_220 f (by omega)]
      change (List.range' 217 3 ++ List.range' (217+3) 1) ++
        [217+(3+1)] = List.range' 217 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 3+1)).symm

private theorem traversal_222 (fuel : Nat) (hf : 222 < fuel) :
    walk nodes fuel 222 = List.range' 222 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 222).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_223 (fuel : Nat) (hf : 223 < fuel) :
    walk nodes fuel 223 = List.range' 217 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 223).rule = .split 3 (3/8) 221 222 := by rfl
      simp only [walk, hr]
      rw [traversal_221 f (by omega), traversal_222 f (by omega)]
      change (List.range' 217 5 ++ List.range' (217+5) 1) ++
        [217+(5+1)] = List.range' 217 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 5+1)).symm

private theorem traversal_224 (fuel : Nat) (hf : 224 < fuel) :
    walk nodes fuel 224 = List.range' 224 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 224).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_225 (fuel : Nat) (hf : 225 < fuel) :
    walk nodes fuel 225 = List.range' 225 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 225).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_226 (fuel : Nat) (hf : 226 < fuel) :
    walk nodes fuel 226 = List.range' 224 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 226).rule = .split 3 (3/8) 224 225 := by rfl
      simp only [walk, hr]
      rw [traversal_224 f (by omega), traversal_225 f (by omega)]
      change (List.range' 224 1 ++ List.range' (224+1) 1) ++
        [224+(1+1)] = List.range' 224 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 224) (n := 1+1)).symm

theorem traversal_227 (fuel : Nat) (hf : 227 < fuel) :
    walk nodes fuel 227 = List.range' 217 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 227).rule = .split 2 (65/32) 223 226 := by rfl
      simp only [walk, hr]
      rw [traversal_223 f (by omega), traversal_226 f (by omega)]
      change (List.range' 217 7 ++ List.range' (217+7) 3) ++
        [217+(7+3)] = List.range' 217 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 7+3)).symm

theorem traversal_228 (fuel : Nat) (hf : 228 < fuel) :
    walk nodes fuel 228 = List.range' 228 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 228).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_229 (fuel : Nat) (hf : 229 < fuel) :
    walk nodes fuel 229 = List.range' 229 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 229).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_230 (fuel : Nat) (hf : 230 < fuel) :
    walk nodes fuel 230 = List.range' 230 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 230).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_231 (fuel : Nat) (hf : 231 < fuel) :
    walk nodes fuel 231 = List.range' 231 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 231).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_232 (fuel : Nat) (hf : 232 < fuel) :
    walk nodes fuel 232 = List.range' 230 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 232).rule = .split 3 (9/16) 230 231 := by rfl
      simp only [walk, hr]
      rw [traversal_230 f (by omega), traversal_231 f (by omega)]
      change (List.range' 230 1 ++ List.range' (230+1) 1) ++
        [230+(1+1)] = List.range' 230 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 230) (n := 1+1)).symm

theorem traversal_233 (fuel : Nat) (hf : 233 < fuel) :
    walk nodes fuel 233 = List.range' 229 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 233).rule = .split 2 (111/64) 229 232 := by rfl
      simp only [walk, hr]
      rw [traversal_229 f (by omega), traversal_232 f (by omega)]
      change (List.range' 229 1 ++ List.range' (229+1) 3) ++
        [229+(1+3)] = List.range' 229 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 229) (n := 1+3)).symm

private theorem traversal_234 (fuel : Nat) (hf : 234 < fuel) :
    walk nodes fuel 234 = List.range' 234 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 234).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_235 (fuel : Nat) (hf : 235 < fuel) :
    walk nodes fuel 235 = List.range' 235 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 235).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_236 (fuel : Nat) (hf : 236 < fuel) :
    walk nodes fuel 236 = List.range' 236 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 236).rule = .bound .leftEnd 8 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_237 (fuel : Nat) (hf : 237 < fuel) :
    walk nodes fuel 237 = List.range' 237 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 237).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_238 (fuel : Nat) (hf : 238 < fuel) :
    walk nodes fuel 238 = List.range' 236 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 238).rule = .split 1 (145/64) 236 237 := by rfl
      simp only [walk, hr]
      rw [traversal_236 f (by omega), traversal_237 f (by omega)]
      change (List.range' 236 1 ++ List.range' (236+1) 1) ++
        [236+(1+1)] = List.range' 236 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 236) (n := 1+1)).symm

private theorem traversal_239 (fuel : Nat) (hf : 239 < fuel) :
    walk nodes fuel 239 = List.range' 239 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 239).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_240 (fuel : Nat) (hf : 240 < fuel) :
    walk nodes fuel 240 = List.range' 236 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 240).rule = .split 0 (1/80) 238 239 := by rfl
      simp only [walk, hr]
      rw [traversal_238 f (by omega), traversal_239 f (by omega)]
      change (List.range' 236 3 ++ List.range' (236+3) 1) ++
        [236+(3+1)] = List.range' 236 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 236) (n := 3+1)).symm

private theorem traversal_241 (fuel : Nat) (hf : 241 < fuel) :
    walk nodes fuel 241 = List.range' 241 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 241).rule = .bound .leftEnd 8 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_242 (fuel : Nat) (hf : 242 < fuel) :
    walk nodes fuel 242 = List.range' 236 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 242).rule = .split 3 (21/32) 240 241 := by rfl
      simp only [walk, hr]
      rw [traversal_240 f (by omega), traversal_241 f (by omega)]
      change (List.range' 236 5 ++ List.range' (236+5) 1) ++
        [236+(5+1)] = List.range' 236 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 236) (n := 5+1)).symm

private theorem traversal_243 (fuel : Nat) (hf : 243 < fuel) :
    walk nodes fuel 243 = List.range' 235 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 243).rule = .split 2 (203/128) 235 242 := by rfl
      simp only [walk, hr]
      rw [traversal_235 f (by omega), traversal_242 f (by omega)]
      change (List.range' 235 1 ++ List.range' (235+1) 7) ++
        [235+(1+7)] = List.range' 235 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 235) (n := 1+7)).symm

private theorem traversal_244 (fuel : Nat) (hf : 244 < fuel) :
    walk nodes fuel 244 = List.range' 244 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 244).rule = .bound .leftEnd 1 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_245 (fuel : Nat) (hf : 245 < fuel) :
    walk nodes fuel 245 = List.range' 245 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 245).rule = .bound .leftEnd 1 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_246 (fuel : Nat) (hf : 246 < fuel) :
    walk nodes fuel 246 = List.range' 244 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 246).rule = .split 0 (1/80) 244 245 := by rfl
      simp only [walk, hr]
      rw [traversal_244 f (by omega), traversal_245 f (by omega)]
      change (List.range' 244 1 ++ List.range' (244+1) 1) ++
        [244+(1+1)] = List.range' 244 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 244) (n := 1+1)).symm

private theorem traversal_247 (fuel : Nat) (hf : 247 < fuel) :
    walk nodes fuel 247 = List.range' 247 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 247).rule = .bound .leftEnd 1 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_248 (fuel : Nat) (hf : 248 < fuel) :
    walk nodes fuel 248 = List.range' 244 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 248).rule = .split 3 (21/32) 246 247 := by rfl
      simp only [walk, hr]
      rw [traversal_246 f (by omega), traversal_247 f (by omega)]
      change (List.range' 244 3 ++ List.range' (244+3) 1) ++
        [244+(3+1)] = List.range' 244 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 244) (n := 3+1)).symm

private theorem traversal_249 (fuel : Nat) (hf : 249 < fuel) :
    walk nodes fuel 249 = List.range' 249 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 249).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_250 (fuel : Nat) (hf : 250 < fuel) :
    walk nodes fuel 250 = List.range' 250 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 250).rule = .bound .leftEnd 1 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_251 (fuel : Nat) (hf : 251 < fuel) :
    walk nodes fuel 251 = List.range' 249 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 251).rule = .split 3 (21/32) 249 250 := by rfl
      simp only [walk, hr]
      rw [traversal_249 f (by omega), traversal_250 f (by omega)]
      change (List.range' 249 1 ++ List.range' (249+1) 1) ++
        [249+(1+1)] = List.range' 249 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 249) (n := 1+1)).symm

private theorem traversal_252 (fuel : Nat) (hf : 252 < fuel) :
    walk nodes fuel 252 = List.range' 244 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 252).rule = .split 2 (203/128) 248 251 := by rfl
      simp only [walk, hr]
      rw [traversal_248 f (by omega), traversal_251 f (by omega)]
      change (List.range' 244 5 ++ List.range' (244+5) 3) ++
        [244+(5+3)] = List.range' 244 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 244) (n := 5+3)).symm

private theorem traversal_253 (fuel : Nat) (hf : 253 < fuel) :
    walk nodes fuel 253 = List.range' 235 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 253).rule = .split 1 (75/32) 243 252 := by rfl
      simp only [walk, hr]
      rw [traversal_243 f (by omega), traversal_252 f (by omega)]
      change (List.range' 235 9 ++ List.range' (235+9) 9) ++
        [235+(9+9)] = List.range' 235 ((9+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 235) (n := 9+9)).symm

private theorem traversal_254 (fuel : Nat) (hf : 254 < fuel) :
    walk nodes fuel 254 = List.range' 254 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 254).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_255 (fuel : Nat) (hf : 255 < fuel) :
    walk nodes fuel 255 = List.range' 255 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 255).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_256 (fuel : Nat) (hf : 256 < fuel) :
    walk nodes fuel 256 = List.range' 256 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 256).rule = .bound .leftEnd 1 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_257 (fuel : Nat) (hf : 257 < fuel) :
    walk nodes fuel 257 = List.range' 255 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 257).rule = .split 3 (21/32) 255 256 := by rfl
      simp only [walk, hr]
      rw [traversal_255 f (by omega), traversal_256 f (by omega)]
      change (List.range' 255 1 ++ List.range' (255+1) 1) ++
        [255+(1+1)] = List.range' 255 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 255) (n := 1+1)).symm

private theorem traversal_258 (fuel : Nat) (hf : 258 < fuel) :
    walk nodes fuel 258 = List.range' 254 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 258).rule = .split 2 (203/128) 254 257 := by rfl
      simp only [walk, hr]
      rw [traversal_254 f (by omega), traversal_257 f (by omega)]
      change (List.range' 254 1 ++ List.range' (254+1) 3) ++
        [254+(1+3)] = List.range' 254 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 254) (n := 1+3)).symm

private theorem traversal_259 (fuel : Nat) (hf : 259 < fuel) :
    walk nodes fuel 259 = List.range' 259 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 259).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_260 (fuel : Nat) (hf : 260 < fuel) :
    walk nodes fuel 260 = List.range' 254 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 260).rule = .split 1 (75/32) 258 259 := by rfl
      simp only [walk, hr]
      rw [traversal_258 f (by omega), traversal_259 f (by omega)]
      change (List.range' 254 5 ++ List.range' (254+5) 1) ++
        [254+(5+1)] = List.range' 254 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 254) (n := 5+1)).symm

private theorem traversal_261 (fuel : Nat) (hf : 261 < fuel) :
    walk nodes fuel 261 = List.range' 235 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 261).rule = .split 0 (1/40) 253 260 := by rfl
      simp only [walk, hr]
      rw [traversal_253 f (by omega), traversal_260 f (by omega)]
      change (List.range' 235 19 ++ List.range' (235+19) 7) ++
        [235+(19+7)] = List.range' 235 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 235) (n := 19+7)).symm

theorem traversal_262 (fuel : Nat) (hf : 262 < fuel) :
    walk nodes fuel 262 = List.range' 234 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 262).rule = .split 3 (9/16) 234 261 := by rfl
      simp only [walk, hr]
      rw [traversal_234 f (by omega), traversal_261 f (by omega)]
      change (List.range' 234 1 ++ List.range' (234+1) 27) ++
        [234+(1+27)] = List.range' 234 ((1+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 234) (n := 1+27)).symm

theorem traversal_263 (fuel : Nat) (hf : 263 < fuel) :
    walk nodes fuel 263 = List.range' 263 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 263).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_264 (fuel : Nat) (hf : 264 < fuel) :
    walk nodes fuel 264 = List.range' 264 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 264).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_265 (fuel : Nat) (hf : 265 < fuel) :
    walk nodes fuel 265 = List.range' 265 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 265).rule = .bound .leftEnd 8 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_266 (fuel : Nat) (hf : 266 < fuel) :
    walk nodes fuel 266 = List.range' 266 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 266).rule = .bound .leftEnd 8 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_267 (fuel : Nat) (hf : 267 < fuel) :
    walk nodes fuel 267 = List.range' 267 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 267).rule = .bound .leftEnd 2 (4969/8192) (432047/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_268 (fuel : Nat) (hf : 268 < fuel) :
    walk nodes fuel 268 = List.range' 268 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 268).rule = .bound .leftEnd 8 (2403/4096) (446717/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_269 (fuel : Nat) (hf : 269 < fuel) :
    walk nodes fuel 269 = List.range' 269 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 269).rule = .bound .leftEnd 1 (2403/4096) (446717/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
