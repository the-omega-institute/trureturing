/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_283,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_296,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_297,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_322,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_329,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_334,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart04.traversal_335
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart02
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart03
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_269 (fuel : Nat) (hf : 269 < fuel) :
    walk nodes fuel 269 = List.range' 269 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 269).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_270 (fuel : Nat) (hf : 270 < fuel) :
    walk nodes fuel 270 = List.range' 230 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 270).rule = .split 3 (9/8) 268 269 := by rfl
      simp only [walk, hr]
      rw [traversal_268 f (by omega), traversal_269 f (by omega)]
      change (List.range' 230 39 ++ List.range' (230+39) 1) ++
        [230+(39+1)] = List.range' 230 ((39+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 230) (n := 39+1)).symm

private theorem traversal_271 (fuel : Nat) (hf : 271 < fuel) :
    walk nodes fuel 271 = List.range' 229 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 271).rule = .split 2 (65/32) 229 270 := by rfl
      simp only [walk, hr]
      rw [traversal_229 f (by omega), traversal_270 f (by omega)]
      change (List.range' 229 1 ++ List.range' (229+1) 41) ++
        [229+(1+41)] = List.range' 229 ((1+41)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 229) (n := 1+41)).symm

private theorem traversal_272 (fuel : Nat) (hf : 272 < fuel) :
    walk nodes fuel 272 = List.range' 228 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 272).rule = .split 1 (15/8) 228 271 := by rfl
      simp only [walk, hr]
      rw [traversal_228 f (by omega), traversal_271 f (by omega)]
      change (List.range' 228 1 ++ List.range' (228+1) 43) ++
        [228+(1+43)] = List.range' 228 ((1+43)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 228) (n := 1+43)).symm

private theorem traversal_273 (fuel : Nat) (hf : 273 < fuel) :
    walk nodes fuel 273 = List.range' 161 113 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 273).rule = .split 3 (3/4) 227 272 := by rfl
      simp only [walk, hr]
      rw [traversal_227 f (by omega), traversal_272 f (by omega)]
      change (List.range' 161 67 ++ List.range' (161+67) 45) ++
        [161+(67+45)] = List.range' 161 ((67+45)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 161) (n := 67+45)).symm

private theorem traversal_274 (fuel : Nat) (hf : 274 < fuel) :
    walk nodes fuel 274 = List.range' 2 273 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 274).rule = .split 2 (23/16) 160 273 := by rfl
      simp only [walk, hr]
      rw [traversal_160 f (by omega), traversal_273 f (by omega)]
      change (List.range' 2 159 ++ List.range' (2+159) 113) ++
        [2+(159+113)] = List.range' 2 ((159+113)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 159+113)).symm

private theorem traversal_275 (fuel : Nat) (hf : 275 < fuel) :
    walk nodes fuel 275 = List.range' 1 275 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 275).rule = .split 1 (5/4) 1 274 := by rfl
      simp only [walk, hr]
      rw [traversal_1 f (by omega), traversal_274 f (by omega)]
      change (List.range' 1 1 ++ List.range' (1+1) 273) ++
        [1+(1+273)] = List.range' 1 ((1+273)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 1+273)).symm

private theorem traversal_276 (fuel : Nat) (hf : 276 < fuel) :
    walk nodes fuel 276 = List.range' 276 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 276).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_277 (fuel : Nat) (hf : 277 < fuel) :
    walk nodes fuel 277 = List.range' 277 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 277).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_278 (fuel : Nat) (hf : 278 < fuel) :
    walk nodes fuel 278 = List.range' 278 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 278).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_279 (fuel : Nat) (hf : 279 < fuel) :
    walk nodes fuel 279 = List.range' 277 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 279).rule = .split 3 (9/4) 277 278 := by rfl
      simp only [walk, hr]
      rw [traversal_277 f (by omega), traversal_278 f (by omega)]
      change (List.range' 277 1 ++ List.range' (277+1) 1) ++
        [277+(1+1)] = List.range' 277 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 277) (n := 1+1)).symm

private theorem traversal_280 (fuel : Nat) (hf : 280 < fuel) :
    walk nodes fuel 280 = List.range' 276 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 280).rule = .split 2 (23/16) 276 279 := by rfl
      simp only [walk, hr]
      rw [traversal_276 f (by omega), traversal_279 f (by omega)]
      change (List.range' 276 1 ++ List.range' (276+1) 3) ++
        [276+(1+3)] = List.range' 276 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 276) (n := 1+3)).symm

private theorem traversal_281 (fuel : Nat) (hf : 281 < fuel) :
    walk nodes fuel 281 = List.range' 281 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 281).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_282 (fuel : Nat) (hf : 282 < fuel) :
    walk nodes fuel 282 = List.range' 276 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 282).rule = .split 1 (5/4) 280 281 := by rfl
      simp only [walk, hr]
      rw [traversal_280 f (by omega), traversal_281 f (by omega)]
      change (List.range' 276 5 ++ List.range' (276+5) 1) ++
        [276+(5+1)] = List.range' 276 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 276) (n := 5+1)).symm

theorem traversal_283 (fuel : Nat) (hf : 283 < fuel) :
    walk nodes fuel 283 = List.range' 1 283 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 283).rule = .split 3 (3/2) 275 282 := by rfl
      simp only [walk, hr]
      rw [traversal_275 f (by omega), traversal_282 f (by omega)]
      change (List.range' 1 275 ++ List.range' (1+275) 7) ++
        [1+(275+7)] = List.range' 1 ((275+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 275+7)).symm

private theorem traversal_284 (fuel : Nat) (hf : 284 < fuel) :
    walk nodes fuel 284 = List.range' 284 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 284).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_285 (fuel : Nat) (hf : 285 < fuel) :
    walk nodes fuel 285 = List.range' 285 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 285).rule = .infeasible 1 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_286 (fuel : Nat) (hf : 286 < fuel) :
    walk nodes fuel 286 = List.range' 286 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 286).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_287 (fuel : Nat) (hf : 287 < fuel) :
    walk nodes fuel 287 = List.range' 287 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 287).rule = .bound .vertex 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_288 (fuel : Nat) (hf : 288 < fuel) :
    walk nodes fuel 288 = List.range' 288 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 288).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_289 (fuel : Nat) (hf : 289 < fuel) :
    walk nodes fuel 289 = List.range' 289 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 289).rule = .bound .vertex 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_290 (fuel : Nat) (hf : 290 < fuel) :
    walk nodes fuel 290 = List.range' 288 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 290).rule = .split 0 (1/20) 288 289 := by rfl
      simp only [walk, hr]
      rw [traversal_288 f (by omega), traversal_289 f (by omega)]
      change (List.range' 288 1 ++ List.range' (288+1) 1) ++
        [288+(1+1)] = List.range' 288 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 288) (n := 1+1)).symm

private theorem traversal_291 (fuel : Nat) (hf : 291 < fuel) :
    walk nodes fuel 291 = List.range' 287 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 291).rule = .split 3 (9/8) 287 290 := by rfl
      simp only [walk, hr]
      rw [traversal_287 f (by omega), traversal_290 f (by omega)]
      change (List.range' 287 1 ++ List.range' (287+1) 3) ++
        [287+(1+3)] = List.range' 287 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 287) (n := 1+3)).symm

private theorem traversal_292 (fuel : Nat) (hf : 292 < fuel) :
    walk nodes fuel 292 = List.range' 292 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 292).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_293 (fuel : Nat) (hf : 293 < fuel) :
    walk nodes fuel 293 = List.range' 287 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 293).rule = .split 2 (141/32) 291 292 := by rfl
      simp only [walk, hr]
      rw [traversal_291 f (by omega), traversal_292 f (by omega)]
      change (List.range' 287 5 ++ List.range' (287+5) 1) ++
        [287+(5+1)] = List.range' 287 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 287) (n := 5+1)).symm

private theorem traversal_294 (fuel : Nat) (hf : 294 < fuel) :
    walk nodes fuel 294 = List.range' 286 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 294).rule = .split 1 (5/8) 286 293 := by rfl
      simp only [walk, hr]
      rw [traversal_286 f (by omega), traversal_293 f (by omega)]
      change (List.range' 286 1 ++ List.range' (286+1) 7) ++
        [286+(1+7)] = List.range' 286 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 286) (n := 1+7)).symm

private theorem traversal_295 (fuel : Nat) (hf : 295 < fuel) :
    walk nodes fuel 295 = List.range' 285 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 295).rule = .split 3 (3/4) 285 294 := by rfl
      simp only [walk, hr]
      rw [traversal_285 f (by omega), traversal_294 f (by omega)]
      change (List.range' 285 1 ++ List.range' (285+1) 9) ++
        [285+(1+9)] = List.range' 285 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 285) (n := 1+9)).symm

theorem traversal_296 (fuel : Nat) (hf : 296 < fuel) :
    walk nodes fuel 296 = List.range' 284 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 296).rule = .split 2 (61/16) 284 295 := by rfl
      simp only [walk, hr]
      rw [traversal_284 f (by omega), traversal_295 f (by omega)]
      change (List.range' 284 1 ++ List.range' (284+1) 11) ++
        [284+(1+11)] = List.range' 284 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 284) (n := 1+11)).symm

theorem traversal_297 (fuel : Nat) (hf : 297 < fuel) :
    walk nodes fuel 297 = List.range' 297 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 297).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_298 (fuel : Nat) (hf : 298 < fuel) :
    walk nodes fuel 298 = List.range' 298 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 298).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_299 (fuel : Nat) (hf : 299 < fuel) :
    walk nodes fuel 299 = List.range' 299 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 299).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_300 (fuel : Nat) (hf : 300 < fuel) :
    walk nodes fuel 300 = List.range' 300 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 300).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_301 (fuel : Nat) (hf : 301 < fuel) :
    walk nodes fuel 301 = List.range' 299 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 301).rule = .split 1 (55/32) 299 300 := by rfl
      simp only [walk, hr]
      rw [traversal_299 f (by omega), traversal_300 f (by omega)]
      change (List.range' 299 1 ++ List.range' (299+1) 1) ++
        [299+(1+1)] = List.range' 299 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 1+1)).symm

private theorem traversal_302 (fuel : Nat) (hf : 302 < fuel) :
    walk nodes fuel 302 = List.range' 302 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 302).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_303 (fuel : Nat) (hf : 303 < fuel) :
    walk nodes fuel 303 = List.range' 303 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 303).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_304 (fuel : Nat) (hf : 304 < fuel) :
    walk nodes fuel 304 = List.range' 302 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 304).rule = .split 1 (55/32) 302 303 := by rfl
      simp only [walk, hr]
      rw [traversal_302 f (by omega), traversal_303 f (by omega)]
      change (List.range' 302 1 ++ List.range' (302+1) 1) ++
        [302+(1+1)] = List.range' 302 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 302) (n := 1+1)).symm

private theorem traversal_305 (fuel : Nat) (hf : 305 < fuel) :
    walk nodes fuel 305 = List.range' 299 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 305).rule = .split 0 (1/40) 301 304 := by rfl
      simp only [walk, hr]
      rw [traversal_301 f (by omega), traversal_304 f (by omega)]
      change (List.range' 299 3 ++ List.range' (299+3) 3) ++
        [299+(3+3)] = List.range' 299 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 3+3)).symm

private theorem traversal_306 (fuel : Nat) (hf : 306 < fuel) :
    walk nodes fuel 306 = List.range' 306 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 306).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_307 (fuel : Nat) (hf : 307 < fuel) :
    walk nodes fuel 307 = List.range' 299 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 307).rule = .split 3 (15/16) 305 306 := by rfl
      simp only [walk, hr]
      rw [traversal_305 f (by omega), traversal_306 f (by omega)]
      change (List.range' 299 7 ++ List.range' (299+7) 1) ++
        [299+(7+1)] = List.range' 299 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 7+1)).symm

private theorem traversal_308 (fuel : Nat) (hf : 308 < fuel) :
    walk nodes fuel 308 = List.range' 308 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 308).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_309 (fuel : Nat) (hf : 309 < fuel) :
    walk nodes fuel 309 = List.range' 309 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 309).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_310 (fuel : Nat) (hf : 310 < fuel) :
    walk nodes fuel 310 = List.range' 310 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 310).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_311 (fuel : Nat) (hf : 311 < fuel) :
    walk nodes fuel 311 = List.range' 309 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 311).rule = .split 1 (55/32) 309 310 := by rfl
      simp only [walk, hr]
      rw [traversal_309 f (by omega), traversal_310 f (by omega)]
      change (List.range' 309 1 ++ List.range' (309+1) 1) ++
        [309+(1+1)] = List.range' 309 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 309) (n := 1+1)).symm

private theorem traversal_312 (fuel : Nat) (hf : 312 < fuel) :
    walk nodes fuel 312 = List.range' 312 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 312).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_313 (fuel : Nat) (hf : 313 < fuel) :
    walk nodes fuel 313 = List.range' 309 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 313).rule = .split 0 (1/40) 311 312 := by rfl
      simp only [walk, hr]
      rw [traversal_311 f (by omega), traversal_312 f (by omega)]
      change (List.range' 309 3 ++ List.range' (309+3) 1) ++
        [309+(3+1)] = List.range' 309 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 309) (n := 3+1)).symm

private theorem traversal_314 (fuel : Nat) (hf : 314 < fuel) :
    walk nodes fuel 314 = List.range' 308 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 314).rule = .split 3 (15/16) 308 313 := by rfl
      simp only [walk, hr]
      rw [traversal_308 f (by omega), traversal_313 f (by omega)]
      change (List.range' 308 1 ++ List.range' (308+1) 5) ++
        [308+(1+5)] = List.range' 308 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 308) (n := 1+5)).symm

private theorem traversal_315 (fuel : Nat) (hf : 315 < fuel) :
    walk nodes fuel 315 = List.range' 299 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 315).rule = .split 2 (187/64) 307 314 := by rfl
      simp only [walk, hr]
      rw [traversal_307 f (by omega), traversal_314 f (by omega)]
      change (List.range' 299 9 ++ List.range' (299+9) 7) ++
        [299+(9+7)] = List.range' 299 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 9+7)).symm

private theorem traversal_316 (fuel : Nat) (hf : 316 < fuel) :
    walk nodes fuel 316 = List.range' 298 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 316).rule = .split 1 (25/16) 298 315 := by rfl
      simp only [walk, hr]
      rw [traversal_298 f (by omega), traversal_315 f (by omega)]
      change (List.range' 298 1 ++ List.range' (298+1) 17) ++
        [298+(1+17)] = List.range' 298 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 298) (n := 1+17)).symm

private theorem traversal_317 (fuel : Nat) (hf : 317 < fuel) :
    walk nodes fuel 317 = List.range' 317 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 317).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_318 (fuel : Nat) (hf : 318 < fuel) :
    walk nodes fuel 318 = List.range' 318 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 318).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_319 (fuel : Nat) (hf : 319 < fuel) :
    walk nodes fuel 319 = List.range' 317 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 319).rule = .split 1 (25/16) 317 318 := by rfl
      simp only [walk, hr]
      rw [traversal_317 f (by omega), traversal_318 f (by omega)]
      change (List.range' 317 1 ++ List.range' (317+1) 1) ++
        [317+(1+1)] = List.range' 317 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 317) (n := 1+1)).symm

private theorem traversal_320 (fuel : Nat) (hf : 320 < fuel) :
    walk nodes fuel 320 = List.range' 298 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 320).rule = .split 0 (1/20) 316 319 := by rfl
      simp only [walk, hr]
      rw [traversal_316 f (by omega), traversal_319 f (by omega)]
      change (List.range' 298 19 ++ List.range' (298+19) 3) ++
        [298+(19+3)] = List.range' 298 ((19+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 298) (n := 19+3)).symm

private theorem traversal_321 (fuel : Nat) (hf : 321 < fuel) :
    walk nodes fuel 321 = List.range' 321 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 321).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_322 (fuel : Nat) (hf : 322 < fuel) :
    walk nodes fuel 322 = List.range' 298 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 322).rule = .split 3 (9/8) 320 321 := by rfl
      simp only [walk, hr]
      rw [traversal_320 f (by omega), traversal_321 f (by omega)]
      change (List.range' 298 23 ++ List.range' (298+23) 1) ++
        [298+(23+1)] = List.range' 298 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 298) (n := 23+1)).symm

private theorem traversal_323 (fuel : Nat) (hf : 323 < fuel) :
    walk nodes fuel 323 = List.range' 323 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 323).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_324 (fuel : Nat) (hf : 324 < fuel) :
    walk nodes fuel 324 = List.range' 324 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 324).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_325 (fuel : Nat) (hf : 325 < fuel) :
    walk nodes fuel 325 = List.range' 323 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 325).rule = .split 2 (225/64) 323 324 := by rfl
      simp only [walk, hr]
      rw [traversal_323 f (by omega), traversal_324 f (by omega)]
      change (List.range' 323 1 ++ List.range' (323+1) 1) ++
        [323+(1+1)] = List.range' 323 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 323) (n := 1+1)).symm

private theorem traversal_326 (fuel : Nat) (hf : 326 < fuel) :
    walk nodes fuel 326 = List.range' 326 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 326).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_327 (fuel : Nat) (hf : 327 < fuel) :
    walk nodes fuel 327 = List.range' 323 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 327).rule = .split 1 (25/16) 325 326 := by rfl
      simp only [walk, hr]
      rw [traversal_325 f (by omega), traversal_326 f (by omega)]
      change (List.range' 323 3 ++ List.range' (323+3) 1) ++
        [323+(3+1)] = List.range' 323 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 323) (n := 3+1)).symm

private theorem traversal_328 (fuel : Nat) (hf : 328 < fuel) :
    walk nodes fuel 328 = List.range' 328 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 328).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_329 (fuel : Nat) (hf : 329 < fuel) :
    walk nodes fuel 329 = List.range' 323 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 329).rule = .split 0 (1/20) 327 328 := by rfl
      simp only [walk, hr]
      rw [traversal_327 f (by omega), traversal_328 f (by omega)]
      change (List.range' 323 5 ++ List.range' (323+5) 1) ++
        [323+(5+1)] = List.range' 323 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 323) (n := 5+1)).symm

private theorem traversal_330 (fuel : Nat) (hf : 330 < fuel) :
    walk nodes fuel 330 = List.range' 330 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 330).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_331 (fuel : Nat) (hf : 331 < fuel) :
    walk nodes fuel 331 = List.range' 331 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 331).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_332 (fuel : Nat) (hf : 332 < fuel) :
    walk nodes fuel 332 = List.range' 330 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 332).rule = .split 2 (225/64) 330 331 := by rfl
      simp only [walk, hr]
      rw [traversal_330 f (by omega), traversal_331 f (by omega)]
      change (List.range' 330 1 ++ List.range' (330+1) 1) ++
        [330+(1+1)] = List.range' 330 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 330) (n := 1+1)).symm

private theorem traversal_333 (fuel : Nat) (hf : 333 < fuel) :
    walk nodes fuel 333 = List.range' 333 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 333).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_334 (fuel : Nat) (hf : 334 < fuel) :
    walk nodes fuel 334 = List.range' 330 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 334).rule = .split 1 (25/16) 332 333 := by rfl
      simp only [walk, hr]
      rw [traversal_332 f (by omega), traversal_333 f (by omega)]
      change (List.range' 330 3 ++ List.range' (330+3) 1) ++
        [330+(3+1)] = List.range' 330 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 330) (n := 3+1)).symm

theorem traversal_335 (fuel : Nat) (hf : 335 < fuel) :
    walk nodes fuel 335 = List.range' 335 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 335).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
