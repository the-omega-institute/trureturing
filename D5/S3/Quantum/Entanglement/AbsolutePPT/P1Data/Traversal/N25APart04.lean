/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart04
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart04
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart04.traversal_334
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart03
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_270 (fuel : Nat) (hf : 270 < fuel) :
    walk nodes fuel 270 = List.range' 270 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 270).rule = .bound .leftEnd 2 (2403/4096) (446717/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_271 (fuel : Nat) (hf : 271 < fuel) :
    walk nodes fuel 271 = List.range' 269 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 271).rule = .split 2 (945/512) 269 270 := by rfl
      simp only [walk, hr]
      rw [traversal_269 f (by omega), traversal_270 f (by omega)]
      change (List.range' 269 1 ++ List.range' (269+1) 1) ++
        [269+(1+1)] = List.range' 269 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 269) (n := 1+1)).symm

private theorem traversal_272 (fuel : Nat) (hf : 272 < fuel) :
    walk nodes fuel 272 = List.range' 268 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 272).rule = .split 1 (295/128) 268 271 := by rfl
      simp only [walk, hr]
      rw [traversal_268 f (by omega), traversal_271 f (by omega)]
      change (List.range' 268 1 ++ List.range' (268+1) 3) ++
        [268+(1+3)] = List.range' 268 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 268) (n := 1+3)).symm

private theorem traversal_273 (fuel : Nat) (hf : 273 < fuel) :
    walk nodes fuel 273 = List.range' 273 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 273).rule = .bound .leftEnd 2 (2403/4096) (446717/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_274 (fuel : Nat) (hf : 274 < fuel) :
    walk nodes fuel 274 = List.range' 268 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 274).rule = .split 0 (1/160) 272 273 := by rfl
      simp only [walk, hr]
      rw [traversal_272 f (by omega), traversal_273 f (by omega)]
      change (List.range' 268 5 ++ List.range' (268+5) 1) ++
        [268+(5+1)] = List.range' 268 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 268) (n := 5+1)).symm

private theorem traversal_275 (fuel : Nat) (hf : 275 < fuel) :
    walk nodes fuel 275 = List.range' 267 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 275).rule = .split 3 (45/64) 267 274 := by rfl
      simp only [walk, hr]
      rw [traversal_267 f (by omega), traversal_274 f (by omega)]
      change (List.range' 267 1 ++ List.range' (267+1) 7) ++
        [267+(1+7)] = List.range' 267 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 267) (n := 1+7)).symm

private theorem traversal_276 (fuel : Nat) (hf : 276 < fuel) :
    walk nodes fuel 276 = List.range' 266 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 276).rule = .split 2 (463/256) 266 275 := by rfl
      simp only [walk, hr]
      rw [traversal_266 f (by omega), traversal_275 f (by omega)]
      change (List.range' 266 1 ++ List.range' (266+1) 9) ++
        [266+(1+9)] = List.range' 266 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 266) (n := 1+9)).symm

private theorem traversal_277 (fuel : Nat) (hf : 277 < fuel) :
    walk nodes fuel 277 = List.range' 265 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 277).rule = .split 1 (145/64) 265 276 := by rfl
      simp only [walk, hr]
      rw [traversal_265 f (by omega), traversal_276 f (by omega)]
      change (List.range' 265 1 ++ List.range' (265+1) 11) ++
        [265+(1+11)] = List.range' 265 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 265) (n := 1+11)).symm

private theorem traversal_278 (fuel : Nat) (hf : 278 < fuel) :
    walk nodes fuel 278 = List.range' 278 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 278).rule = .bound .leftEnd 8 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_279 (fuel : Nat) (hf : 279 < fuel) :
    walk nodes fuel 279 = List.range' 279 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 279).rule = .bound .leftEnd 2 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_280 (fuel : Nat) (hf : 280 < fuel) :
    walk nodes fuel 280 = List.range' 278 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 280).rule = .split 1 (145/64) 278 279 := by rfl
      simp only [walk, hr]
      rw [traversal_278 f (by omega), traversal_279 f (by omega)]
      change (List.range' 278 1 ++ List.range' (278+1) 1) ++
        [278+(1+1)] = List.range' 278 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 278) (n := 1+1)).symm

private theorem traversal_281 (fuel : Nat) (hf : 281 < fuel) :
    walk nodes fuel 281 = List.range' 265 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 281).rule = .split 0 (1/80) 277 280 := by rfl
      simp only [walk, hr]
      rw [traversal_277 f (by omega), traversal_280 f (by omega)]
      change (List.range' 265 13 ++ List.range' (265+13) 3) ++
        [265+(13+3)] = List.range' 265 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 265) (n := 13+3)).symm

private theorem traversal_282 (fuel : Nat) (hf : 282 < fuel) :
    walk nodes fuel 282 = List.range' 264 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 282).rule = .split 3 (21/32) 264 281 := by rfl
      simp only [walk, hr]
      rw [traversal_264 f (by omega), traversal_281 f (by omega)]
      change (List.range' 264 1 ++ List.range' (264+1) 17) ++
        [264+(1+17)] = List.range' 264 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 264) (n := 1+17)).symm

private theorem traversal_283 (fuel : Nat) (hf : 283 < fuel) :
    walk nodes fuel 283 = List.range' 283 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 283).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_284 (fuel : Nat) (hf : 284 < fuel) :
    walk nodes fuel 284 = List.range' 284 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 284).rule = .bound .leftEnd 8 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_285 (fuel : Nat) (hf : 285 < fuel) :
    walk nodes fuel 285 = List.range' 285 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 285).rule = .bound .leftEnd 2 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_286 (fuel : Nat) (hf : 286 < fuel) :
    walk nodes fuel 286 = List.range' 284 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 286).rule = .split 1 (145/64) 284 285 := by rfl
      simp only [walk, hr]
      rw [traversal_284 f (by omega), traversal_285 f (by omega)]
      change (List.range' 284 1 ++ List.range' (284+1) 1) ++
        [284+(1+1)] = List.range' 284 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 284) (n := 1+1)).symm

private theorem traversal_287 (fuel : Nat) (hf : 287 < fuel) :
    walk nodes fuel 287 = List.range' 287 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 287).rule = .bound .leftEnd 2 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_288 (fuel : Nat) (hf : 288 < fuel) :
    walk nodes fuel 288 = List.range' 284 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 288).rule = .split 0 (1/80) 286 287 := by rfl
      simp only [walk, hr]
      rw [traversal_286 f (by omega), traversal_287 f (by omega)]
      change (List.range' 284 3 ++ List.range' (284+3) 1) ++
        [284+(3+1)] = List.range' 284 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 284) (n := 3+1)).symm

private theorem traversal_289 (fuel : Nat) (hf : 289 < fuel) :
    walk nodes fuel 289 = List.range' 283 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 289).rule = .split 3 (21/32) 283 288 := by rfl
      simp only [walk, hr]
      rw [traversal_283 f (by omega), traversal_288 f (by omega)]
      change (List.range' 283 1 ++ List.range' (283+1) 5) ++
        [283+(1+5)] = List.range' 283 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 283) (n := 1+5)).symm

private theorem traversal_290 (fuel : Nat) (hf : 290 < fuel) :
    walk nodes fuel 290 = List.range' 264 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 290).rule = .split 2 (241/128) 282 289 := by rfl
      simp only [walk, hr]
      rw [traversal_282 f (by omega), traversal_289 f (by omega)]
      change (List.range' 264 19 ++ List.range' (264+19) 7) ++
        [264+(19+7)] = List.range' 264 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 264) (n := 19+7)).symm

private theorem traversal_291 (fuel : Nat) (hf : 291 < fuel) :
    walk nodes fuel 291 = List.range' 291 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 291).rule = .bound .leftEnd 2 (63011/98304) (204183/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_292 (fuel : Nat) (hf : 292 < fuel) :
    walk nodes fuel 292 = List.range' 292 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 292).rule = .bound .leftEnd 2 (4969/8192) (432047/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_293 (fuel : Nat) (hf : 293 < fuel) :
    walk nodes fuel 293 = List.range' 293 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 293).rule = .bound .leftEnd 1 (2403/4096) (446717/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_294 (fuel : Nat) (hf : 294 < fuel) :
    walk nodes fuel 294 = List.range' 292 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 294).rule = .split 3 (45/64) 292 293 := by rfl
      simp only [walk, hr]
      rw [traversal_292 f (by omega), traversal_293 f (by omega)]
      change (List.range' 292 1 ++ List.range' (292+1) 1) ++
        [292+(1+1)] = List.range' 292 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 292) (n := 1+1)).symm

private theorem traversal_295 (fuel : Nat) (hf : 295 < fuel) :
    walk nodes fuel 295 = List.range' 295 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 295).rule = .bound .leftEnd 2 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_296 (fuel : Nat) (hf : 296 < fuel) :
    walk nodes fuel 296 = List.range' 292 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 296).rule = .split 2 (463/256) 294 295 := by rfl
      simp only [walk, hr]
      rw [traversal_294 f (by omega), traversal_295 f (by omega)]
      change (List.range' 292 3 ++ List.range' (292+3) 1) ++
        [292+(3+1)] = List.range' 292 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 292) (n := 3+1)).symm

private theorem traversal_297 (fuel : Nat) (hf : 297 < fuel) :
    walk nodes fuel 297 = List.range' 297 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 297).rule = .bound .leftEnd 2 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_298 (fuel : Nat) (hf : 298 < fuel) :
    walk nodes fuel 298 = List.range' 292 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 298).rule = .split 1 (155/64) 296 297 := by rfl
      simp only [walk, hr]
      rw [traversal_296 f (by omega), traversal_297 f (by omega)]
      change (List.range' 292 5 ++ List.range' (292+5) 1) ++
        [292+(5+1)] = List.range' 292 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 292) (n := 5+1)).symm

private theorem traversal_299 (fuel : Nat) (hf : 299 < fuel) :
    walk nodes fuel 299 = List.range' 299 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 299).rule = .bound .leftEnd 1 (9775/16384) (438893/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_300 (fuel : Nat) (hf : 300 < fuel) :
    walk nodes fuel 300 = List.range' 292 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 300).rule = .split 0 (1/80) 298 299 := by rfl
      simp only [walk, hr]
      rw [traversal_298 f (by omega), traversal_299 f (by omega)]
      change (List.range' 292 7 ++ List.range' (292+7) 1) ++
        [292+(7+1)] = List.range' 292 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 292) (n := 7+1)).symm

private theorem traversal_301 (fuel : Nat) (hf : 301 < fuel) :
    walk nodes fuel 301 = List.range' 291 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 301).rule = .split 3 (21/32) 291 300 := by rfl
      simp only [walk, hr]
      rw [traversal_291 f (by omega), traversal_300 f (by omega)]
      change (List.range' 291 1 ++ List.range' (291+1) 9) ++
        [291+(1+9)] = List.range' 291 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 291) (n := 1+9)).symm

private theorem traversal_302 (fuel : Nat) (hf : 302 < fuel) :
    walk nodes fuel 302 = List.range' 302 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 302).rule = .bound .leftEnd 2 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_303 (fuel : Nat) (hf : 303 < fuel) :
    walk nodes fuel 303 = List.range' 291 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 303).rule = .split 2 (241/128) 301 302 := by rfl
      simp only [walk, hr]
      rw [traversal_301 f (by omega), traversal_302 f (by omega)]
      change (List.range' 291 11 ++ List.range' (291+11) 1) ++
        [291+(11+1)] = List.range' 291 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 291) (n := 11+1)).symm

private theorem traversal_304 (fuel : Nat) (hf : 304 < fuel) :
    walk nodes fuel 304 = List.range' 264 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 304).rule = .split 1 (75/32) 290 303 := by rfl
      simp only [walk, hr]
      rw [traversal_290 f (by omega), traversal_303 f (by omega)]
      change (List.range' 264 27 ++ List.range' (264+27) 13) ++
        [264+(27+13)] = List.range' 264 ((27+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 264) (n := 27+13)).symm

private theorem traversal_305 (fuel : Nat) (hf : 305 < fuel) :
    walk nodes fuel 305 = List.range' 305 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 305).rule = .bound .leftEnd 2 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_306 (fuel : Nat) (hf : 306 < fuel) :
    walk nodes fuel 306 = List.range' 264 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 306).rule = .split 0 (1/40) 304 305 := by rfl
      simp only [walk, hr]
      rw [traversal_304 f (by omega), traversal_305 f (by omega)]
      change (List.range' 264 41 ++ List.range' (264+41) 1) ++
        [264+(41+1)] = List.range' 264 ((41+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 264) (n := 41+1)).symm

private theorem traversal_307 (fuel : Nat) (hf : 307 < fuel) :
    walk nodes fuel 307 = List.range' 263 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 307).rule = .split 3 (9/16) 263 306 := by rfl
      simp only [walk, hr]
      rw [traversal_263 f (by omega), traversal_306 f (by omega)]
      change (List.range' 263 1 ++ List.range' (263+1) 43) ++
        [263+(1+43)] = List.range' 263 ((1+43)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 263) (n := 1+43)).symm

private theorem traversal_308 (fuel : Nat) (hf : 308 < fuel) :
    walk nodes fuel 308 = List.range' 234 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 308).rule = .split 2 (111/64) 262 307 := by rfl
      simp only [walk, hr]
      rw [traversal_262 f (by omega), traversal_307 f (by omega)]
      change (List.range' 234 29 ++ List.range' (234+29) 45) ++
        [234+(29+45)] = List.range' 234 ((29+45)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 234) (n := 29+45)).symm

private theorem traversal_309 (fuel : Nat) (hf : 309 < fuel) :
    walk nodes fuel 309 = List.range' 229 81 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 309).rule = .split 1 (35/16) 233 308 := by rfl
      simp only [walk, hr]
      rw [traversal_233 f (by omega), traversal_308 f (by omega)]
      change (List.range' 229 5 ++ List.range' (229+5) 75) ++
        [229+(5+75)] = List.range' 229 ((5+75)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 229) (n := 5+75)).symm

private theorem traversal_310 (fuel : Nat) (hf : 310 < fuel) :
    walk nodes fuel 310 = List.range' 310 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 310).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_311 (fuel : Nat) (hf : 311 < fuel) :
    walk nodes fuel 311 = List.range' 311 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 311).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_312 (fuel : Nat) (hf : 312 < fuel) :
    walk nodes fuel 312 = List.range' 312 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 312).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_313 (fuel : Nat) (hf : 313 < fuel) :
    walk nodes fuel 313 = List.range' 311 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 313).rule = .split 3 (9/16) 311 312 := by rfl
      simp only [walk, hr]
      rw [traversal_311 f (by omega), traversal_312 f (by omega)]
      change (List.range' 311 1 ++ List.range' (311+1) 1) ++
        [311+(1+1)] = List.range' 311 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 311) (n := 1+1)).symm

private theorem traversal_314 (fuel : Nat) (hf : 314 < fuel) :
    walk nodes fuel 314 = List.range' 310 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 314).rule = .split 2 (111/64) 310 313 := by rfl
      simp only [walk, hr]
      rw [traversal_310 f (by omega), traversal_313 f (by omega)]
      change (List.range' 310 1 ++ List.range' (310+1) 3) ++
        [310+(1+3)] = List.range' 310 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 310) (n := 1+3)).symm

private theorem traversal_315 (fuel : Nat) (hf : 315 < fuel) :
    walk nodes fuel 315 = List.range' 315 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 315).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_316 (fuel : Nat) (hf : 316 < fuel) :
    walk nodes fuel 316 = List.range' 310 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 316).rule = .split 1 (35/16) 314 315 := by rfl
      simp only [walk, hr]
      rw [traversal_314 f (by omega), traversal_315 f (by omega)]
      change (List.range' 310 5 ++ List.range' (310+5) 1) ++
        [310+(5+1)] = List.range' 310 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 310) (n := 5+1)).symm

private theorem traversal_317 (fuel : Nat) (hf : 317 < fuel) :
    walk nodes fuel 317 = List.range' 229 89 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 317).rule = .split 0 (1/20) 309 316 := by rfl
      simp only [walk, hr]
      rw [traversal_309 f (by omega), traversal_316 f (by omega)]
      change (List.range' 229 81 ++ List.range' (229+81) 7) ++
        [229+(81+7)] = List.range' 229 ((81+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 229) (n := 81+7)).symm

private theorem traversal_318 (fuel : Nat) (hf : 318 < fuel) :
    walk nodes fuel 318 = List.range' 228 91 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 318).rule = .split 3 (3/8) 228 317 := by rfl
      simp only [walk, hr]
      rw [traversal_228 f (by omega), traversal_317 f (by omega)]
      change (List.range' 228 1 ++ List.range' (228+1) 89) ++
        [228+(1+89)] = List.range' 228 ((1+89)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 228) (n := 1+89)).symm

private theorem traversal_319 (fuel : Nat) (hf : 319 < fuel) :
    walk nodes fuel 319 = List.range' 319 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 319).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_320 (fuel : Nat) (hf : 320 < fuel) :
    walk nodes fuel 320 = List.range' 320 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 320).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_321 (fuel : Nat) (hf : 321 < fuel) :
    walk nodes fuel 321 = List.range' 321 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 321).rule = .bound .leftEnd 8 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_322 (fuel : Nat) (hf : 322 < fuel) :
    walk nodes fuel 322 = List.range' 322 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 322).rule = .bound .leftEnd 2 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_323 (fuel : Nat) (hf : 323 < fuel) :
    walk nodes fuel 323 = List.range' 321 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 323).rule = .split 1 (65/32) 321 322 := by rfl
      simp only [walk, hr]
      rw [traversal_321 f (by omega), traversal_322 f (by omega)]
      change (List.range' 321 1 ++ List.range' (321+1) 1) ++
        [321+(1+1)] = List.range' 321 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 321) (n := 1+1)).symm

private theorem traversal_324 (fuel : Nat) (hf : 324 < fuel) :
    walk nodes fuel 324 = List.range' 324 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 324).rule = .bound .leftEnd 2 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_325 (fuel : Nat) (hf : 325 < fuel) :
    walk nodes fuel 325 = List.range' 321 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 325).rule = .split 0 (1/40) 323 324 := by rfl
      simp only [walk, hr]
      rw [traversal_323 f (by omega), traversal_324 f (by omega)]
      change (List.range' 321 3 ++ List.range' (321+3) 1) ++
        [321+(3+1)] = List.range' 321 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 321) (n := 3+1)).symm

private theorem traversal_326 (fuel : Nat) (hf : 326 < fuel) :
    walk nodes fuel 326 = List.range' 320 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 326).rule = .split 3 (9/16) 320 325 := by rfl
      simp only [walk, hr]
      rw [traversal_320 f (by omega), traversal_325 f (by omega)]
      change (List.range' 320 1 ++ List.range' (320+1) 5) ++
        [320+(1+5)] = List.range' 320 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 320) (n := 1+5)).symm

private theorem traversal_327 (fuel : Nat) (hf : 327 < fuel) :
    walk nodes fuel 327 = List.range' 327 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 327).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_328 (fuel : Nat) (hf : 328 < fuel) :
    walk nodes fuel 328 = List.range' 320 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 328).rule = .split 2 (149/64) 326 327 := by rfl
      simp only [walk, hr]
      rw [traversal_326 f (by omega), traversal_327 f (by omega)]
      change (List.range' 320 7 ++ List.range' (320+7) 1) ++
        [320+(7+1)] = List.range' 320 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 320) (n := 7+1)).symm

private theorem traversal_329 (fuel : Nat) (hf : 329 < fuel) :
    walk nodes fuel 329 = List.range' 329 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 329).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_330 (fuel : Nat) (hf : 330 < fuel) :
    walk nodes fuel 330 = List.range' 320 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 330).rule = .split 1 (35/16) 328 329 := by rfl
      simp only [walk, hr]
      rw [traversal_328 f (by omega), traversal_329 f (by omega)]
      change (List.range' 320 9 ++ List.range' (320+9) 1) ++
        [320+(9+1)] = List.range' 320 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 320) (n := 9+1)).symm

private theorem traversal_331 (fuel : Nat) (hf : 331 < fuel) :
    walk nodes fuel 331 = List.range' 331 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 331).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_332 (fuel : Nat) (hf : 332 < fuel) :
    walk nodes fuel 332 = List.range' 320 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 332).rule = .split 0 (1/20) 330 331 := by rfl
      simp only [walk, hr]
      rw [traversal_330 f (by omega), traversal_331 f (by omega)]
      change (List.range' 320 11 ++ List.range' (320+11) 1) ++
        [320+(11+1)] = List.range' 320 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 320) (n := 11+1)).symm

private theorem traversal_333 (fuel : Nat) (hf : 333 < fuel) :
    walk nodes fuel 333 = List.range' 319 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 333).rule = .split 3 (3/8) 319 332 := by rfl
      simp only [walk, hr]
      rw [traversal_319 f (by omega), traversal_332 f (by omega)]
      change (List.range' 319 1 ++ List.range' (319+1) 13) ++
        [319+(1+13)] = List.range' 319 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 319) (n := 1+13)).symm

theorem traversal_334 (fuel : Nat) (hf : 334 < fuel) :
    walk nodes fuel 334 = List.range' 228 107 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 334).rule = .split 2 (65/32) 318 333 := by rfl
      simp only [walk, hr]
      rw [traversal_318 f (by omega), traversal_333 f (by omega)]
      change (List.range' 228 91 ++ List.range' (228+91) 15) ++
        [228+(91+15)] = List.range' 228 ((91+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 228) (n := 91+15)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
