/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03.traversal_227,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03.traversal_228,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03.traversal_229,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart03.traversal_268
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart02
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_202 (fuel : Nat) (hf : 202 < fuel) :
    walk nodes fuel 202 = List.range' 202 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 202).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_203 (fuel : Nat) (hf : 203 < fuel) :
    walk nodes fuel 203 = List.range' 203 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 203).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_204 (fuel : Nat) (hf : 204 < fuel) :
    walk nodes fuel 204 = List.range' 204 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 204).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_205 (fuel : Nat) (hf : 205 < fuel) :
    walk nodes fuel 205 = List.range' 203 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 205).rule = .split 3 (9/16) 203 204 := by rfl
      simp only [walk, hr]
      rw [traversal_203 f (by omega), traversal_204 f (by omega)]
      change (List.range' 203 1 ++ List.range' (203+1) 1) ++
        [203+(1+1)] = List.range' 203 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 203) (n := 1+1)).symm

private theorem traversal_206 (fuel : Nat) (hf : 206 < fuel) :
    walk nodes fuel 206 = List.range' 202 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 206).rule = .split 2 (111/64) 202 205 := by rfl
      simp only [walk, hr]
      rw [traversal_202 f (by omega), traversal_205 f (by omega)]
      change (List.range' 202 1 ++ List.range' (202+1) 3) ++
        [202+(1+3)] = List.range' 202 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 202) (n := 1+3)).symm

private theorem traversal_207 (fuel : Nat) (hf : 207 < fuel) :
    walk nodes fuel 207 = List.range' 207 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 207).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_208 (fuel : Nat) (hf : 208 < fuel) :
    walk nodes fuel 208 = List.range' 202 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 208).rule = .split 1 (35/16) 206 207 := by rfl
      simp only [walk, hr]
      rw [traversal_206 f (by omega), traversal_207 f (by omega)]
      change (List.range' 202 5 ++ List.range' (202+5) 1) ++
        [202+(5+1)] = List.range' 202 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 202) (n := 5+1)).symm

private theorem traversal_209 (fuel : Nat) (hf : 209 < fuel) :
    walk nodes fuel 209 = List.range' 183 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 209).rule = .split 0 (1/20) 201 208 := by rfl
      simp only [walk, hr]
      rw [traversal_201 f (by omega), traversal_208 f (by omega)]
      change (List.range' 183 19 ++ List.range' (183+19) 7) ++
        [183+(19+7)] = List.range' 183 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 183) (n := 19+7)).symm

private theorem traversal_210 (fuel : Nat) (hf : 210 < fuel) :
    walk nodes fuel 210 = List.range' 182 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 210).rule = .split 3 (3/8) 182 209 := by rfl
      simp only [walk, hr]
      rw [traversal_182 f (by omega), traversal_209 f (by omega)]
      change (List.range' 182 1 ++ List.range' (182+1) 27) ++
        [182+(1+27)] = List.range' 182 ((1+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 182) (n := 1+27)).symm

private theorem traversal_211 (fuel : Nat) (hf : 211 < fuel) :
    walk nodes fuel 211 = List.range' 211 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 211).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_212 (fuel : Nat) (hf : 212 < fuel) :
    walk nodes fuel 212 = List.range' 212 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 212).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_213 (fuel : Nat) (hf : 213 < fuel) :
    walk nodes fuel 213 = List.range' 213 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 213).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_214 (fuel : Nat) (hf : 214 < fuel) :
    walk nodes fuel 214 = List.range' 214 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 214).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_215 (fuel : Nat) (hf : 215 < fuel) :
    walk nodes fuel 215 = List.range' 213 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 215).rule = .split 1 (65/32) 213 214 := by rfl
      simp only [walk, hr]
      rw [traversal_213 f (by omega), traversal_214 f (by omega)]
      change (List.range' 213 1 ++ List.range' (213+1) 1) ++
        [213+(1+1)] = List.range' 213 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 213) (n := 1+1)).symm

private theorem traversal_216 (fuel : Nat) (hf : 216 < fuel) :
    walk nodes fuel 216 = List.range' 216 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 216).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_217 (fuel : Nat) (hf : 217 < fuel) :
    walk nodes fuel 217 = List.range' 213 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 217).rule = .split 0 (1/40) 215 216 := by rfl
      simp only [walk, hr]
      rw [traversal_215 f (by omega), traversal_216 f (by omega)]
      change (List.range' 213 3 ++ List.range' (213+3) 1) ++
        [213+(3+1)] = List.range' 213 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 213) (n := 3+1)).symm

private theorem traversal_218 (fuel : Nat) (hf : 218 < fuel) :
    walk nodes fuel 218 = List.range' 212 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 218).rule = .split 3 (9/16) 212 217 := by rfl
      simp only [walk, hr]
      rw [traversal_212 f (by omega), traversal_217 f (by omega)]
      change (List.range' 212 1 ++ List.range' (212+1) 5) ++
        [212+(1+5)] = List.range' 212 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 212) (n := 1+5)).symm

private theorem traversal_219 (fuel : Nat) (hf : 219 < fuel) :
    walk nodes fuel 219 = List.range' 219 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 219).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_220 (fuel : Nat) (hf : 220 < fuel) :
    walk nodes fuel 220 = List.range' 212 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 220).rule = .split 2 (149/64) 218 219 := by rfl
      simp only [walk, hr]
      rw [traversal_218 f (by omega), traversal_219 f (by omega)]
      change (List.range' 212 7 ++ List.range' (212+7) 1) ++
        [212+(7+1)] = List.range' 212 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 212) (n := 7+1)).symm

private theorem traversal_221 (fuel : Nat) (hf : 221 < fuel) :
    walk nodes fuel 221 = List.range' 221 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 221).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_222 (fuel : Nat) (hf : 222 < fuel) :
    walk nodes fuel 222 = List.range' 212 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 222).rule = .split 1 (35/16) 220 221 := by rfl
      simp only [walk, hr]
      rw [traversal_220 f (by omega), traversal_221 f (by omega)]
      change (List.range' 212 9 ++ List.range' (212+9) 1) ++
        [212+(9+1)] = List.range' 212 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 212) (n := 9+1)).symm

private theorem traversal_223 (fuel : Nat) (hf : 223 < fuel) :
    walk nodes fuel 223 = List.range' 223 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 223).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_224 (fuel : Nat) (hf : 224 < fuel) :
    walk nodes fuel 224 = List.range' 212 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 224).rule = .split 0 (1/20) 222 223 := by rfl
      simp only [walk, hr]
      rw [traversal_222 f (by omega), traversal_223 f (by omega)]
      change (List.range' 212 11 ++ List.range' (212+11) 1) ++
        [212+(11+1)] = List.range' 212 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 212) (n := 11+1)).symm

private theorem traversal_225 (fuel : Nat) (hf : 225 < fuel) :
    walk nodes fuel 225 = List.range' 211 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 225).rule = .split 3 (3/8) 211 224 := by rfl
      simp only [walk, hr]
      rw [traversal_211 f (by omega), traversal_224 f (by omega)]
      change (List.range' 211 1 ++ List.range' (211+1) 13) ++
        [211+(1+13)] = List.range' 211 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 211) (n := 1+13)).symm

private theorem traversal_226 (fuel : Nat) (hf : 226 < fuel) :
    walk nodes fuel 226 = List.range' 182 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 226).rule = .split 2 (65/32) 210 225 := by rfl
      simp only [walk, hr]
      rw [traversal_210 f (by omega), traversal_225 f (by omega)]
      change (List.range' 182 29 ++ List.range' (182+29) 15) ++
        [182+(29+15)] = List.range' 182 ((29+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 182) (n := 29+15)).symm

theorem traversal_227 (fuel : Nat) (hf : 227 < fuel) :
    walk nodes fuel 227 = List.range' 161 67 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 227).rule = .split 1 (15/8) 181 226 := by rfl
      simp only [walk, hr]
      rw [traversal_181 f (by omega), traversal_226 f (by omega)]
      change (List.range' 161 21 ++ List.range' (161+21) 45) ++
        [161+(21+45)] = List.range' 161 ((21+45)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 21+45)).symm

theorem traversal_228 (fuel : Nat) (hf : 228 < fuel) :
    walk nodes fuel 228 = List.range' 228 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 228).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_229 (fuel : Nat) (hf : 229 < fuel) :
    walk nodes fuel 229 = List.range' 229 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 229).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_230 (fuel : Nat) (hf : 230 < fuel) :
    walk nodes fuel 230 = List.range' 230 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 230).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_231 (fuel : Nat) (hf : 231 < fuel) :
    walk nodes fuel 231 = List.range' 231 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 231).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_232 (fuel : Nat) (hf : 232 < fuel) :
    walk nodes fuel 232 = List.range' 232 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 232).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_233 (fuel : Nat) (hf : 233 < fuel) :
    walk nodes fuel 233 = List.range' 233 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 233).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_234 (fuel : Nat) (hf : 234 < fuel) :
    walk nodes fuel 234 = List.range' 234 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 234).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_235 (fuel : Nat) (hf : 235 < fuel) :
    walk nodes fuel 235 = List.range' 233 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 235).rule = .split 3 (27/32) 233 234 := by rfl
      simp only [walk, hr]
      rw [traversal_233 f (by omega), traversal_234 f (by omega)]
      change (List.range' 233 1 ++ List.range' (233+1) 1) ++
        [233+(1+1)] = List.range' 233 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 233) (n := 1+1)).symm

private theorem traversal_236 (fuel : Nat) (hf : 236 < fuel) :
    walk nodes fuel 236 = List.range' 232 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 236).rule = .split 2 (317/128) 232 235 := by rfl
      simp only [walk, hr]
      rw [traversal_232 f (by omega), traversal_235 f (by omega)]
      change (List.range' 232 1 ++ List.range' (232+1) 3) ++
        [232+(1+3)] = List.range' 232 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 232) (n := 1+3)).symm

private theorem traversal_237 (fuel : Nat) (hf : 237 < fuel) :
    walk nodes fuel 237 = List.range' 231 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 237).rule = .split 1 (65/32) 231 236 := by rfl
      simp only [walk, hr]
      rw [traversal_231 f (by omega), traversal_236 f (by omega)]
      change (List.range' 231 1 ++ List.range' (231+1) 5) ++
        [231+(1+5)] = List.range' 231 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 231) (n := 1+5)).symm

private theorem traversal_238 (fuel : Nat) (hf : 238 < fuel) :
    walk nodes fuel 238 = List.range' 238 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 238).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_239 (fuel : Nat) (hf : 239 < fuel) :
    walk nodes fuel 239 = List.range' 239 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 239).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_240 (fuel : Nat) (hf : 240 < fuel) :
    walk nodes fuel 240 = List.range' 238 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 240).rule = .split 1 (65/32) 238 239 := by rfl
      simp only [walk, hr]
      rw [traversal_238 f (by omega), traversal_239 f (by omega)]
      change (List.range' 238 1 ++ List.range' (238+1) 1) ++
        [238+(1+1)] = List.range' 238 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 238) (n := 1+1)).symm

private theorem traversal_241 (fuel : Nat) (hf : 241 < fuel) :
    walk nodes fuel 241 = List.range' 231 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 241).rule = .split 0 (1/40) 237 240 := by rfl
      simp only [walk, hr]
      rw [traversal_237 f (by omega), traversal_240 f (by omega)]
      change (List.range' 231 7 ++ List.range' (231+7) 3) ++
        [231+(7+3)] = List.range' 231 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 231) (n := 7+3)).symm

private theorem traversal_242 (fuel : Nat) (hf : 242 < fuel) :
    walk nodes fuel 242 = List.range' 242 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 242).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_243 (fuel : Nat) (hf : 243 < fuel) :
    walk nodes fuel 243 = List.range' 231 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 243).rule = .split 3 (15/16) 241 242 := by rfl
      simp only [walk, hr]
      rw [traversal_241 f (by omega), traversal_242 f (by omega)]
      change (List.range' 231 11 ++ List.range' (231+11) 1) ++
        [231+(11+1)] = List.range' 231 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 231) (n := 11+1)).symm

private theorem traversal_244 (fuel : Nat) (hf : 244 < fuel) :
    walk nodes fuel 244 = List.range' 230 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 244).rule = .split 2 (149/64) 230 243 := by rfl
      simp only [walk, hr]
      rw [traversal_230 f (by omega), traversal_243 f (by omega)]
      change (List.range' 230 1 ++ List.range' (230+1) 13) ++
        [230+(1+13)] = List.range' 230 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 230) (n := 1+13)).symm

private theorem traversal_245 (fuel : Nat) (hf : 245 < fuel) :
    walk nodes fuel 245 = List.range' 245 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 245).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_246 (fuel : Nat) (hf : 246 < fuel) :
    walk nodes fuel 246 = List.range' 246 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 246).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_247 (fuel : Nat) (hf : 247 < fuel) :
    walk nodes fuel 247 = List.range' 247 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 247).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_248 (fuel : Nat) (hf : 248 < fuel) :
    walk nodes fuel 248 = List.range' 246 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 248).rule = .split 3 (27/32) 246 247 := by rfl
      simp only [walk, hr]
      rw [traversal_246 f (by omega), traversal_247 f (by omega)]
      change (List.range' 246 1 ++ List.range' (246+1) 1) ++
        [246+(1+1)] = List.range' 246 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 246) (n := 1+1)).symm

private theorem traversal_249 (fuel : Nat) (hf : 249 < fuel) :
    walk nodes fuel 249 = List.range' 249 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 249).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_250 (fuel : Nat) (hf : 250 < fuel) :
    walk nodes fuel 250 = List.range' 246 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 250).rule = .split 2 (317/128) 248 249 := by rfl
      simp only [walk, hr]
      rw [traversal_248 f (by omega), traversal_249 f (by omega)]
      change (List.range' 246 3 ++ List.range' (246+3) 1) ++
        [246+(3+1)] = List.range' 246 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 246) (n := 3+1)).symm

private theorem traversal_251 (fuel : Nat) (hf : 251 < fuel) :
    walk nodes fuel 251 = List.range' 251 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 251).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_252 (fuel : Nat) (hf : 252 < fuel) :
    walk nodes fuel 252 = List.range' 246 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 252).rule = .split 1 (75/32) 250 251 := by rfl
      simp only [walk, hr]
      rw [traversal_250 f (by omega), traversal_251 f (by omega)]
      change (List.range' 246 5 ++ List.range' (246+5) 1) ++
        [246+(5+1)] = List.range' 246 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 246) (n := 5+1)).symm

private theorem traversal_253 (fuel : Nat) (hf : 253 < fuel) :
    walk nodes fuel 253 = List.range' 253 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 253).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_254 (fuel : Nat) (hf : 254 < fuel) :
    walk nodes fuel 254 = List.range' 246 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 254).rule = .split 0 (1/40) 252 253 := by rfl
      simp only [walk, hr]
      rw [traversal_252 f (by omega), traversal_253 f (by omega)]
      change (List.range' 246 7 ++ List.range' (246+7) 1) ++
        [246+(7+1)] = List.range' 246 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 246) (n := 7+1)).symm

private theorem traversal_255 (fuel : Nat) (hf : 255 < fuel) :
    walk nodes fuel 255 = List.range' 255 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 255).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_256 (fuel : Nat) (hf : 256 < fuel) :
    walk nodes fuel 256 = List.range' 256 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 256).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_257 (fuel : Nat) (hf : 257 < fuel) :
    walk nodes fuel 257 = List.range' 255 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 257).rule = .split 1 (75/32) 255 256 := by rfl
      simp only [walk, hr]
      rw [traversal_255 f (by omega), traversal_256 f (by omega)]
      change (List.range' 255 1 ++ List.range' (255+1) 1) ++
        [255+(1+1)] = List.range' 255 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 255) (n := 1+1)).symm

private theorem traversal_258 (fuel : Nat) (hf : 258 < fuel) :
    walk nodes fuel 258 = List.range' 258 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 258).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_259 (fuel : Nat) (hf : 259 < fuel) :
    walk nodes fuel 259 = List.range' 255 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 259).rule = .split 0 (1/40) 257 258 := by rfl
      simp only [walk, hr]
      rw [traversal_257 f (by omega), traversal_258 f (by omega)]
      change (List.range' 255 3 ++ List.range' (255+3) 1) ++
        [255+(3+1)] = List.range' 255 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 255) (n := 3+1)).symm

private theorem traversal_260 (fuel : Nat) (hf : 260 < fuel) :
    walk nodes fuel 260 = List.range' 246 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 260).rule = .split 3 (15/16) 254 259 := by rfl
      simp only [walk, hr]
      rw [traversal_254 f (by omega), traversal_259 f (by omega)]
      change (List.range' 246 9 ++ List.range' (246+9) 5) ++
        [246+(9+5)] = List.range' 246 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 246) (n := 9+5)).symm

private theorem traversal_261 (fuel : Nat) (hf : 261 < fuel) :
    walk nodes fuel 261 = List.range' 245 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 261).rule = .split 2 (149/64) 245 260 := by rfl
      simp only [walk, hr]
      rw [traversal_245 f (by omega), traversal_260 f (by omega)]
      change (List.range' 245 1 ++ List.range' (245+1) 15) ++
        [245+(1+15)] = List.range' 245 ((1+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 245) (n := 1+15)).symm

private theorem traversal_262 (fuel : Nat) (hf : 262 < fuel) :
    walk nodes fuel 262 = List.range' 230 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 262).rule = .split 1 (35/16) 244 261 := by rfl
      simp only [walk, hr]
      rw [traversal_244 f (by omega), traversal_261 f (by omega)]
      change (List.range' 230 15 ++ List.range' (230+15) 17) ++
        [230+(15+17)] = List.range' 230 ((15+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 230) (n := 15+17)).symm

private theorem traversal_263 (fuel : Nat) (hf : 263 < fuel) :
    walk nodes fuel 263 = List.range' 263 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 263).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_264 (fuel : Nat) (hf : 264 < fuel) :
    walk nodes fuel 264 = List.range' 264 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 264).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_265 (fuel : Nat) (hf : 265 < fuel) :
    walk nodes fuel 265 = List.range' 263 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 265).rule = .split 2 (149/64) 263 264 := by rfl
      simp only [walk, hr]
      rw [traversal_263 f (by omega), traversal_264 f (by omega)]
      change (List.range' 263 1 ++ List.range' (263+1) 1) ++
        [263+(1+1)] = List.range' 263 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 263) (n := 1+1)).symm

private theorem traversal_266 (fuel : Nat) (hf : 266 < fuel) :
    walk nodes fuel 266 = List.range' 266 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 266).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_267 (fuel : Nat) (hf : 267 < fuel) :
    walk nodes fuel 267 = List.range' 263 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 267).rule = .split 1 (35/16) 265 266 := by rfl
      simp only [walk, hr]
      rw [traversal_265 f (by omega), traversal_266 f (by omega)]
      change (List.range' 263 3 ++ List.range' (263+3) 1) ++
        [263+(3+1)] = List.range' 263 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 263) (n := 3+1)).symm

theorem traversal_268 (fuel : Nat) (hf : 268 < fuel) :
    walk nodes fuel 268 = List.range' 230 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 268).rule = .split 0 (1/20) 262 267 := by rfl
      simp only [walk, hr]
      rw [traversal_262 f (by omega), traversal_267 f (by omega)]
      change (List.range' 230 33 ++ List.range' (230+33) 5) ++
        [230+(33+5)] = List.range' 230 ((33+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 230) (n := 33+5)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
