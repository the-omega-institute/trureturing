/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart04
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart04
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart04.traversal_331,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart04.traversal_332,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart04.traversal_335
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart03
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_269 (fuel : Nat) (hf : 269 < fuel) :
    walk nodes fuel 269 = List.range' 269 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 269).rule = .bound .leftEnd 1 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_270 (fuel : Nat) (hf : 270 < fuel) :
    walk nodes fuel 270 = List.range' 270 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 270).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_271 (fuel : Nat) (hf : 271 < fuel) :
    walk nodes fuel 271 = List.range' 269 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 271).rule = .split 3 (39/16) 269 270 := by rfl
      simp only [walk, hr]
      rw [traversal_269 f (by omega), traversal_270 f (by omega)]
      change (List.range' 269 1 ++ List.range' (269+1) 1) ++
        [269+(1+1)] = List.range' 269 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 269) (n := 1+1)).symm

private theorem traversal_272 (fuel : Nat) (hf : 272 < fuel) :
    walk nodes fuel 272 = List.range' 272 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 272).rule = .bound .leftEnd 1 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_273 (fuel : Nat) (hf : 273 < fuel) :
    walk nodes fuel 273 = List.range' 273 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 273).rule = .bound .leftEnd 6 (61799/196608) (833701/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_274 (fuel : Nat) (hf : 274 < fuel) :
    walk nodes fuel 274 = List.range' 274 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 274).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_275 (fuel : Nat) (hf : 275 < fuel) :
    walk nodes fuel 275 = List.range' 273 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 275).rule = .split 1 (35/32) 273 274 := by rfl
      simp only [walk, hr]
      rw [traversal_273 f (by omega), traversal_274 f (by omega)]
      change (List.range' 273 1 ++ List.range' (273+1) 1) ++
        [273+(1+1)] = List.range' 273 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 273) (n := 1+1)).symm

private theorem traversal_276 (fuel : Nat) (hf : 276 < fuel) :
    walk nodes fuel 276 = List.range' 276 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 276).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_277 (fuel : Nat) (hf : 277 < fuel) :
    walk nodes fuel 277 = List.range' 273 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 277).rule = .split 0 (1/40) 275 276 := by rfl
      simp only [walk, hr]
      rw [traversal_275 f (by omega), traversal_276 f (by omega)]
      change (List.range' 273 3 ++ List.range' (273+3) 1) ++
        [273+(3+1)] = List.range' 273 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 273) (n := 3+1)).symm

private theorem traversal_278 (fuel : Nat) (hf : 278 < fuel) :
    walk nodes fuel 278 = List.range' 272 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 278).rule = .split 3 (39/16) 272 277 := by rfl
      simp only [walk, hr]
      rw [traversal_272 f (by omega), traversal_277 f (by omega)]
      change (List.range' 272 1 ++ List.range' (272+1) 5) ++
        [272+(1+5)] = List.range' 272 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 272) (n := 1+5)).symm

private theorem traversal_279 (fuel : Nat) (hf : 279 < fuel) :
    walk nodes fuel 279 = List.range' 269 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 279).rule = .split 2 (225/64) 271 278 := by rfl
      simp only [walk, hr]
      rw [traversal_271 f (by omega), traversal_278 f (by omega)]
      change (List.range' 269 3 ++ List.range' (269+3) 7) ++
        [269+(3+7)] = List.range' 269 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 269) (n := 3+7)).symm

private theorem traversal_280 (fuel : Nat) (hf : 280 < fuel) :
    walk nodes fuel 280 = List.range' 268 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 280).rule = .split 1 (15/16) 268 279 := by rfl
      simp only [walk, hr]
      rw [traversal_268 f (by omega), traversal_279 f (by omega)]
      change (List.range' 268 1 ++ List.range' (268+1) 11) ++
        [268+(1+11)] = List.range' 268 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 268) (n := 1+11)).symm

private theorem traversal_281 (fuel : Nat) (hf : 281 < fuel) :
    walk nodes fuel 281 = List.range' 281 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 281).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_282 (fuel : Nat) (hf : 282 < fuel) :
    walk nodes fuel 282 = List.range' 282 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 282).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_283 (fuel : Nat) (hf : 283 < fuel) :
    walk nodes fuel 283 = List.range' 281 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 283).rule = .split 1 (15/16) 281 282 := by rfl
      simp only [walk, hr]
      rw [traversal_281 f (by omega), traversal_282 f (by omega)]
      change (List.range' 281 1 ++ List.range' (281+1) 1) ++
        [281+(1+1)] = List.range' 281 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 281) (n := 1+1)).symm

private theorem traversal_284 (fuel : Nat) (hf : 284 < fuel) :
    walk nodes fuel 284 = List.range' 268 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 284).rule = .split 0 (1/20) 280 283 := by rfl
      simp only [walk, hr]
      rw [traversal_280 f (by omega), traversal_283 f (by omega)]
      change (List.range' 268 13 ++ List.range' (268+13) 3) ++
        [268+(13+3)] = List.range' 268 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 268) (n := 13+3)).symm

private theorem traversal_285 (fuel : Nat) (hf : 285 < fuel) :
    walk nodes fuel 285 = List.range' 285 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 285).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_286 (fuel : Nat) (hf : 286 < fuel) :
    walk nodes fuel 286 = List.range' 268 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 286).rule = .split 3 (21/8) 284 285 := by rfl
      simp only [walk, hr]
      rw [traversal_284 f (by omega), traversal_285 f (by omega)]
      change (List.range' 268 17 ++ List.range' (268+17) 1) ++
        [268+(17+1)] = List.range' 268 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 268) (n := 17+1)).symm

private theorem traversal_287 (fuel : Nat) (hf : 287 < fuel) :
    walk nodes fuel 287 = List.range' 267 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 287).rule = .split 2 (103/32) 267 286 := by rfl
      simp only [walk, hr]
      rw [traversal_267 f (by omega), traversal_286 f (by omega)]
      change (List.range' 267 1 ++ List.range' (267+1) 19) ++
        [267+(1+19)] = List.range' 267 ((1+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 267) (n := 1+19)).symm

private theorem traversal_288 (fuel : Nat) (hf : 288 < fuel) :
    walk nodes fuel 288 = List.range' 262 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 288).rule = .split 1 (5/8) 266 287 := by rfl
      simp only [walk, hr]
      rw [traversal_266 f (by omega), traversal_287 f (by omega)]
      change (List.range' 262 5 ++ List.range' (262+5) 21) ++
        [262+(5+21)] = List.range' 262 ((5+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 262) (n := 5+21)).symm

private theorem traversal_289 (fuel : Nat) (hf : 289 < fuel) :
    walk nodes fuel 289 = List.range' 261 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 289).rule = .split 3 (9/4) 261 288 := by rfl
      simp only [walk, hr]
      rw [traversal_261 f (by omega), traversal_288 f (by omega)]
      change (List.range' 261 1 ++ List.range' (261+1) 27) ++
        [261+(1+27)] = List.range' 261 ((1+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 261) (n := 1+27)).symm

private theorem traversal_290 (fuel : Nat) (hf : 290 < fuel) :
    walk nodes fuel 290 = List.range' 290 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 290).rule = .bound .vertex 0 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_291 (fuel : Nat) (hf : 291 < fuel) :
    walk nodes fuel 291 = List.range' 291 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 291).rule = .bound .vertex 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_292 (fuel : Nat) (hf : 292 < fuel) :
    walk nodes fuel 292 = List.range' 292 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 292).rule = .bound .vertex 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_293 (fuel : Nat) (hf : 293 < fuel) :
    walk nodes fuel 293 = List.range' 293 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 293).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_294 (fuel : Nat) (hf : 294 < fuel) :
    walk nodes fuel 294 = List.range' 292 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 294).rule = .split 0 (1/20) 292 293 := by rfl
      simp only [walk, hr]
      rw [traversal_292 f (by omega), traversal_293 f (by omega)]
      change (List.range' 292 1 ++ List.range' (292+1) 1) ++
        [292+(1+1)] = List.range' 292 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 292) (n := 1+1)).symm

private theorem traversal_295 (fuel : Nat) (hf : 295 < fuel) :
    walk nodes fuel 295 = List.range' 291 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 295).rule = .split 3 (15/8) 291 294 := by rfl
      simp only [walk, hr]
      rw [traversal_291 f (by omega), traversal_294 f (by omega)]
      change (List.range' 291 1 ++ List.range' (291+1) 3) ++
        [291+(1+3)] = List.range' 291 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 291) (n := 1+3)).symm

private theorem traversal_296 (fuel : Nat) (hf : 296 < fuel) :
    walk nodes fuel 296 = List.range' 296 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 296).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_297 (fuel : Nat) (hf : 297 < fuel) :
    walk nodes fuel 297 = List.range' 291 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 297).rule = .split 2 (141/32) 295 296 := by rfl
      simp only [walk, hr]
      rw [traversal_295 f (by omega), traversal_296 f (by omega)]
      change (List.range' 291 5 ++ List.range' (291+5) 1) ++
        [291+(5+1)] = List.range' 291 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 291) (n := 5+1)).symm

private theorem traversal_298 (fuel : Nat) (hf : 298 < fuel) :
    walk nodes fuel 298 = List.range' 290 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 298).rule = .split 1 (5/8) 290 297 := by rfl
      simp only [walk, hr]
      rw [traversal_290 f (by omega), traversal_297 f (by omega)]
      change (List.range' 290 1 ++ List.range' (290+1) 7) ++
        [290+(1+7)] = List.range' 290 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 290) (n := 1+7)).symm

private theorem traversal_299 (fuel : Nat) (hf : 299 < fuel) :
    walk nodes fuel 299 = List.range' 299 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 299).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_300 (fuel : Nat) (hf : 300 < fuel) :
    walk nodes fuel 300 = List.range' 300 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 300).rule = .bound .rightEnd 6 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_301 (fuel : Nat) (hf : 301 < fuel) :
    walk nodes fuel 301 = List.range' 301 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 301).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_302 (fuel : Nat) (hf : 302 < fuel) :
    walk nodes fuel 302 = List.range' 302 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 302).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_303 (fuel : Nat) (hf : 303 < fuel) :
    walk nodes fuel 303 = List.range' 301 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 303).rule = .split 3 (45/16) 301 302 := by rfl
      simp only [walk, hr]
      rw [traversal_301 f (by omega), traversal_302 f (by omega)]
      change (List.range' 301 1 ++ List.range' (301+1) 1) ++
        [301+(1+1)] = List.range' 301 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 301) (n := 1+1)).symm

private theorem traversal_304 (fuel : Nat) (hf : 304 < fuel) :
    walk nodes fuel 304 = List.range' 304 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 304).rule = .bound .rightEnd 3 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_305 (fuel : Nat) (hf : 305 < fuel) :
    walk nodes fuel 305 = List.range' 301 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 305).rule = .split 2 (263/64) 303 304 := by rfl
      simp only [walk, hr]
      rw [traversal_303 f (by omega), traversal_304 f (by omega)]
      change (List.range' 301 3 ++ List.range' (301+3) 1) ++
        [301+(3+1)] = List.range' 301 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 301) (n := 3+1)).symm

private theorem traversal_306 (fuel : Nat) (hf : 306 < fuel) :
    walk nodes fuel 306 = List.range' 306 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 306).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_307 (fuel : Nat) (hf : 307 < fuel) :
    walk nodes fuel 307 = List.range' 301 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 307).rule = .split 1 (5/16) 305 306 := by rfl
      simp only [walk, hr]
      rw [traversal_305 f (by omega), traversal_306 f (by omega)]
      change (List.range' 301 5 ++ List.range' (301+5) 1) ++
        [301+(5+1)] = List.range' 301 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 301) (n := 5+1)).symm

private theorem traversal_308 (fuel : Nat) (hf : 308 < fuel) :
    walk nodes fuel 308 = List.range' 300 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 308).rule = .split 0 (1/20) 300 307 := by rfl
      simp only [walk, hr]
      rw [traversal_300 f (by omega), traversal_307 f (by omega)]
      change (List.range' 300 1 ++ List.range' (300+1) 7) ++
        [300+(1+7)] = List.range' 300 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 300) (n := 1+7)).symm

private theorem traversal_309 (fuel : Nat) (hf : 309 < fuel) :
    walk nodes fuel 309 = List.range' 299 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 309).rule = .split 3 (21/8) 299 308 := by rfl
      simp only [walk, hr]
      rw [traversal_299 f (by omega), traversal_308 f (by omega)]
      change (List.range' 299 1 ++ List.range' (299+1) 9) ++
        [299+(1+9)] = List.range' 299 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 1+9)).symm

private theorem traversal_310 (fuel : Nat) (hf : 310 < fuel) :
    walk nodes fuel 310 = List.range' 310 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 310).rule = .bound .rightEnd 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_311 (fuel : Nat) (hf : 311 < fuel) :
    walk nodes fuel 311 = List.range' 311 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 311).rule = .bound .rightEnd 6 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_312 (fuel : Nat) (hf : 312 < fuel) :
    walk nodes fuel 312 = List.range' 312 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 312).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_313 (fuel : Nat) (hf : 313 < fuel) :
    walk nodes fuel 313 = List.range' 311 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 313).rule = .split 0 (1/20) 311 312 := by rfl
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
      have hr : (node nodes 314).rule = .split 3 (21/8) 310 313 := by rfl
      simp only [walk, hr]
      rw [traversal_310 f (by omega), traversal_313 f (by omega)]
      change (List.range' 310 1 ++ List.range' (310+1) 3) ++
        [310+(1+3)] = List.range' 310 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 310) (n := 1+3)).symm

private theorem traversal_315 (fuel : Nat) (hf : 315 < fuel) :
    walk nodes fuel 315 = List.range' 299 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 315).rule = .split 2 (141/32) 309 314 := by rfl
      simp only [walk, hr]
      rw [traversal_309 f (by omega), traversal_314 f (by omega)]
      change (List.range' 299 11 ++ List.range' (299+11) 5) ++
        [299+(11+5)] = List.range' 299 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 11+5)).symm

private theorem traversal_316 (fuel : Nat) (hf : 316 < fuel) :
    walk nodes fuel 316 = List.range' 316 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 316).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_317 (fuel : Nat) (hf : 317 < fuel) :
    walk nodes fuel 317 = List.range' 317 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 317).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_318 (fuel : Nat) (hf : 318 < fuel) :
    walk nodes fuel 318 = List.range' 316 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 318).rule = .split 1 (15/16) 316 317 := by rfl
      simp only [walk, hr]
      rw [traversal_316 f (by omega), traversal_317 f (by omega)]
      change (List.range' 316 1 ++ List.range' (316+1) 1) ++
        [316+(1+1)] = List.range' 316 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 316) (n := 1+1)).symm

private theorem traversal_319 (fuel : Nat) (hf : 319 < fuel) :
    walk nodes fuel 319 = List.range' 319 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 319).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_320 (fuel : Nat) (hf : 320 < fuel) :
    walk nodes fuel 320 = List.range' 316 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 320).rule = .split 0 (1/20) 318 319 := by rfl
      simp only [walk, hr]
      rw [traversal_318 f (by omega), traversal_319 f (by omega)]
      change (List.range' 316 3 ++ List.range' (316+3) 1) ++
        [316+(3+1)] = List.range' 316 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 316) (n := 3+1)).symm

private theorem traversal_321 (fuel : Nat) (hf : 321 < fuel) :
    walk nodes fuel 321 = List.range' 321 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 321).rule = .bound .vertex 6 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_322 (fuel : Nat) (hf : 322 < fuel) :
    walk nodes fuel 322 = List.range' 322 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 322).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_323 (fuel : Nat) (hf : 323 < fuel) :
    walk nodes fuel 323 = List.range' 321 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 323).rule = .split 1 (15/16) 321 322 := by rfl
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
      have hr : (node nodes 324).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_325 (fuel : Nat) (hf : 325 < fuel) :
    walk nodes fuel 325 = List.range' 321 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 325).rule = .split 0 (1/20) 323 324 := by rfl
      simp only [walk, hr]
      rw [traversal_323 f (by omega), traversal_324 f (by omega)]
      change (List.range' 321 3 ++ List.range' (321+3) 1) ++
        [321+(3+1)] = List.range' 321 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 321) (n := 3+1)).symm

private theorem traversal_326 (fuel : Nat) (hf : 326 < fuel) :
    walk nodes fuel 326 = List.range' 316 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 326).rule = .split 3 (21/8) 320 325 := by rfl
      simp only [walk, hr]
      rw [traversal_320 f (by omega), traversal_325 f (by omega)]
      change (List.range' 316 5 ++ List.range' (316+5) 5) ++
        [316+(5+5)] = List.range' 316 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 316) (n := 5+5)).symm

private theorem traversal_327 (fuel : Nat) (hf : 327 < fuel) :
    walk nodes fuel 327 = List.range' 327 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 327).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_328 (fuel : Nat) (hf : 328 < fuel) :
    walk nodes fuel 328 = List.range' 316 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 328).rule = .split 2 (141/32) 326 327 := by rfl
      simp only [walk, hr]
      rw [traversal_326 f (by omega), traversal_327 f (by omega)]
      change (List.range' 316 11 ++ List.range' (316+11) 1) ++
        [316+(11+1)] = List.range' 316 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 316) (n := 11+1)).symm

private theorem traversal_329 (fuel : Nat) (hf : 329 < fuel) :
    walk nodes fuel 329 = List.range' 299 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 329).rule = .split 1 (5/8) 315 328 := by rfl
      simp only [walk, hr]
      rw [traversal_315 f (by omega), traversal_328 f (by omega)]
      change (List.range' 299 17 ++ List.range' (299+17) 13) ++
        [299+(17+13)] = List.range' 299 ((17+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 299) (n := 17+13)).symm

private theorem traversal_330 (fuel : Nat) (hf : 330 < fuel) :
    walk nodes fuel 330 = List.range' 290 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 330).rule = .split 3 (9/4) 298 329 := by rfl
      simp only [walk, hr]
      rw [traversal_298 f (by omega), traversal_329 f (by omega)]
      change (List.range' 290 9 ++ List.range' (290+9) 31) ++
        [290+(9+31)] = List.range' 290 ((9+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 290) (n := 9+31)).symm

theorem traversal_331 (fuel : Nat) (hf : 331 < fuel) :
    walk nodes fuel 331 = List.range' 261 71 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 331).rule = .split 2 (61/16) 289 330 := by rfl
      simp only [walk, hr]
      rw [traversal_289 f (by omega), traversal_330 f (by omega)]
      change (List.range' 261 29 ++ List.range' (261+29) 41) ++
        [261+(29+41)] = List.range' 261 ((29+41)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 261) (n := 29+41)).symm

theorem traversal_332 (fuel : Nat) (hf : 332 < fuel) :
    walk nodes fuel 332 = List.range' 332 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 332).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_333 (fuel : Nat) (hf : 333 < fuel) :
    walk nodes fuel 333 = List.range' 333 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 333).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_334 (fuel : Nat) (hf : 334 < fuel) :
    walk nodes fuel 334 = List.range' 334 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 334).rule = .bound .leftEnd 1 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_335 (fuel : Nat) (hf : 335 < fuel) :
    walk nodes fuel 335 = List.range' 333 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 335).rule = .split 1 (25/16) 333 334 := by rfl
      simp only [walk, hr]
      rw [traversal_333 f (by omega), traversal_334 f (by omega)]
      change (List.range' 333 1 ++ List.range' (333+1) 1) ++
        [333+(1+1)] = List.range' 333 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 333) (n := 1+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
