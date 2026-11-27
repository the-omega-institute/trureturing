/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of the finite lower near-Gibbs Wu cubic certificate. -/

import D5.S3.Quantum.Semigroups.WuCubicLowerFocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowerReplay

open Matrix
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicLowerCells (check)
open WuCubicLowerPartition (root tree)
open WuCubicUpperPartition (Box)

private def boxes : List Box := tree.leaves root

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The first replay cell, checked separately so that its cost can be measured. -/
theorem first_cell_checked : ((boxes.take 1).all check) = true := by
  decide +kernel

private theorem all_of_parts (xs : List Box) (n : ℕ)
    (hfirst : ((xs.take n).all check) = true) (hrest : ((xs.drop n).all check) = true) :
    (xs.all check) = true := by
  calc
    xs.all check = ((xs.take n ++ xs.drop n).all check) :=
      congrArg (fun ys => ys.all check) (List.take_append_drop n xs).symm
    _ = true := by simp [List.all_append, hfirst, hrest]

private def segment (start count : ℕ) : List Box := (boxes.drop start).take count

private theorem all_from_segment (start count : ℕ) (h : ((segment start count).all check) = true)
    (htail : ((boxes.drop (start + count)).all check) = true) :
    ((boxes.drop start).all check) = true := by
  apply all_of_parts (boxes.drop start) count h
  simpa only [List.drop_drop, Nat.add_comm] using htail

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private theorem segment_1 : ((segment 1 4).all check) = true := by
  decide +kernel

private theorem segment_5 : ((segment 5 4).all check) = true := by
  decide +kernel

private theorem segment_9 : ((segment 9 4).all check) = true := by
  decide +kernel

private theorem segment_13 : ((segment 13 4).all check) = true := by
  decide +kernel

private theorem segment_17 : ((segment 17 4).all check) = true := by
  decide +kernel

private theorem segment_21 : ((segment 21 4).all check) = true := by
  decide +kernel

private theorem segment_25 : ((segment 25 4).all check) = true := by
  decide +kernel

private theorem segment_29 : ((segment 29 4).all check) = true := by
  decide +kernel

private theorem segment_33 : ((segment 33 4).all check) = true := by
  decide +kernel

private theorem segment_37 : ((segment 37 4).all check) = true := by
  decide +kernel

private theorem segment_41 : ((segment 41 4).all check) = true := by
  decide +kernel

private theorem segment_45 : ((segment 45 4).all check) = true := by
  decide +kernel

private theorem segment_49 : ((segment 49 4).all check) = true := by
  decide +kernel

private theorem segment_53 : ((segment 53 4).all check) = true := by
  decide +kernel

private theorem segment_57 : ((segment 57 4).all check) = true := by
  decide +kernel

private theorem segment_61 : ((segment 61 4).all check) = true := by
  decide +kernel

private theorem segment_65 : ((segment 65 4).all check) = true := by
  decide +kernel

private theorem segment_69 : ((segment 69 4).all check) = true := by
  decide +kernel

private theorem segment_73 : ((segment 73 4).all check) = true := by
  decide +kernel

private theorem segment_77 : ((segment 77 4).all check) = true := by
  decide +kernel

private theorem segment_81 : ((segment 81 4).all check) = true := by
  decide +kernel

private theorem segment_85 : ((segment 85 4).all check) = true := by
  decide +kernel

private theorem segment_89 : ((segment 89 4).all check) = true := by
  decide +kernel

private theorem segment_93 : ((segment 93 4).all check) = true := by
  decide +kernel

private theorem segment_97 : ((segment 97 4).all check) = true := by
  decide +kernel

private theorem segment_101 : ((segment 101 4).all check) = true := by
  decide +kernel

private theorem segment_105 : ((segment 105 4).all check) = true := by
  decide +kernel

private theorem segment_109 : ((segment 109 4).all check) = true := by
  decide +kernel

private theorem segment_113 : ((segment 113 4).all check) = true := by
  decide +kernel

private theorem segment_117 : ((segment 117 4).all check) = true := by
  decide +kernel

private theorem segment_121 : ((segment 121 4).all check) = true := by
  decide +kernel

private theorem segment_125 : ((segment 125 4).all check) = true := by
  decide +kernel

private theorem segment_129 : ((segment 129 4).all check) = true := by
  decide +kernel

private theorem segment_133 : ((segment 133 4).all check) = true := by
  decide +kernel

private theorem segment_137 : ((segment 137 4).all check) = true := by
  decide +kernel

private theorem segment_141 : ((segment 141 4).all check) = true := by
  decide +kernel

private theorem segment_145 : ((segment 145 4).all check) = true := by
  decide +kernel

private theorem segment_149 : ((segment 149 4).all check) = true := by
  decide +kernel

private theorem segment_153 : ((segment 153 4).all check) = true := by
  decide +kernel

private theorem segment_157 : ((segment 157 4).all check) = true := by
  decide +kernel

private theorem segment_161 : ((segment 161 4).all check) = true := by
  decide +kernel

private theorem segment_165 : ((segment 165 4).all check) = true := by
  decide +kernel

private theorem segment_169 : ((segment 169 4).all check) = true := by
  decide +kernel

private theorem segment_173 : ((segment 173 4).all check) = true := by
  decide +kernel

private theorem segment_177 : ((segment 177 4).all check) = true := by
  decide +kernel

private theorem segment_181 : ((segment 181 4).all check) = true := by
  decide +kernel

private theorem segment_185 : ((segment 185 4).all check) = true := by
  decide +kernel

private theorem segment_189 : ((segment 189 4).all check) = true := by
  decide +kernel

private theorem segment_193 : ((segment 193 4).all check) = true := by
  decide +kernel

private theorem segment_197 : ((segment 197 4).all check) = true := by
  decide +kernel

private theorem segment_201 : ((segment 201 4).all check) = true := by
  decide +kernel

private theorem segment_205 : ((segment 205 4).all check) = true := by
  decide +kernel

private theorem segment_209 : ((segment 209 4).all check) = true := by
  decide +kernel

private theorem segment_213 : ((segment 213 4).all check) = true := by
  decide +kernel

private theorem segment_217 : ((segment 217 4).all check) = true := by
  decide +kernel

private theorem segment_221 : ((segment 221 4).all check) = true := by
  decide +kernel

private theorem segment_225 : ((segment 225 4).all check) = true := by
  decide +kernel

private theorem segment_229 : ((segment 229 4).all check) = true := by
  decide +kernel

private theorem segment_233 : ((segment 233 4).all check) = true := by
  decide +kernel

private theorem segment_237 : ((segment 237 4).all check) = true := by
  decide +kernel

private theorem segment_241 : ((segment 241 4).all check) = true := by
  decide +kernel

private theorem segment_245 : ((segment 245 4).all check) = true := by
  decide +kernel

private theorem segment_249 : ((segment 249 4).all check) = true := by
  decide +kernel

private theorem segment_253 : ((segment 253 4).all check) = true := by
  decide +kernel

private theorem segment_257 : ((segment 257 4).all check) = true := by
  decide +kernel

private theorem segment_261 : ((segment 261 4).all check) = true := by
  decide +kernel

private theorem segment_265 : ((segment 265 4).all check) = true := by
  decide +kernel

private theorem segment_269 : ((segment 269 4).all check) = true := by
  decide +kernel

private theorem segment_273 : ((segment 273 4).all check) = true := by
  decide +kernel

private theorem segment_277 : ((segment 277 4).all check) = true := by
  decide +kernel

private theorem segment_281 : ((segment 281 4).all check) = true := by
  decide +kernel

private theorem segment_285 : ((segment 285 4).all check) = true := by
  decide +kernel

private theorem segment_289 : ((segment 289 4).all check) = true := by
  decide +kernel

private theorem segment_293 : ((segment 293 4).all check) = true := by
  decide +kernel

private theorem segment_297 : ((segment 297 4).all check) = true := by
  decide +kernel

private theorem segment_301 : ((segment 301 4).all check) = true := by
  decide +kernel

private theorem segment_305 : ((segment 305 4).all check) = true := by
  decide +kernel

private theorem segment_309 : ((segment 309 4).all check) = true := by
  decide +kernel

private theorem segment_313 : ((segment 313 4).all check) = true := by
  decide +kernel

private theorem segment_317 : ((segment 317 4).all check) = true := by
  decide +kernel

private theorem segment_321 : ((segment 321 4).all check) = true := by
  decide +kernel

private theorem segment_325 : ((segment 325 4).all check) = true := by
  decide +kernel

private theorem segment_329 : ((segment 329 4).all check) = true := by
  decide +kernel

private theorem segment_333 : ((segment 333 4).all check) = true := by
  decide +kernel

private theorem segment_337 : ((segment 337 4).all check) = true := by
  decide +kernel

private theorem segment_341 : ((segment 341 4).all check) = true := by
  decide +kernel

private theorem segment_345 : ((segment 345 4).all check) = true := by
  decide +kernel

private theorem segment_349 : ((segment 349 4).all check) = true := by
  decide +kernel

private theorem segment_353 : ((segment 353 4).all check) = true := by
  decide +kernel

private theorem segment_357 : ((segment 357 4).all check) = true := by
  decide +kernel

private theorem segment_361 : ((segment 361 4).all check) = true := by
  decide +kernel

private theorem segment_365 : ((segment 365 4).all check) = true := by
  decide +kernel

private theorem segment_369 : ((segment 369 4).all check) = true := by
  decide +kernel

private theorem segment_373 : ((segment 373 4).all check) = true := by
  decide +kernel

private theorem segment_377 : ((segment 377 4).all check) = true := by
  decide +kernel

private theorem segment_381 : ((segment 381 4).all check) = true := by
  decide +kernel

private theorem segment_385 : ((segment 385 4).all check) = true := by
  decide +kernel

private theorem segment_389 : ((segment 389 4).all check) = true := by
  decide +kernel

private theorem segment_393 : ((segment 393 4).all check) = true := by
  decide +kernel

private theorem segment_397 : ((segment 397 4).all check) = true := by
  decide +kernel

private theorem segment_401 : ((segment 401 4).all check) = true := by
  decide +kernel

private theorem segment_405 : ((segment 405 4).all check) = true := by
  decide +kernel

private theorem segment_409 : ((segment 409 4).all check) = true := by
  decide +kernel

private theorem segment_413 : ((segment 413 4).all check) = true := by
  decide +kernel

private theorem segment_417 : ((segment 417 4).all check) = true := by
  decide +kernel

private theorem segment_421 : ((segment 421 4).all check) = true := by
  decide +kernel

private theorem segment_425 : ((segment 425 4).all check) = true := by
  decide +kernel

private theorem segment_429 : ((segment 429 4).all check) = true := by
  decide +kernel

private theorem segment_433 : ((segment 433 4).all check) = true := by
  decide +kernel

private theorem segment_437 : ((segment 437 4).all check) = true := by
  decide +kernel

private theorem segment_441 : ((segment 441 4).all check) = true := by
  decide +kernel

private theorem segment_445 : ((segment 445 4).all check) = true := by
  decide +kernel

private theorem segment_449 : ((segment 449 4).all check) = true := by
  decide +kernel

private theorem segment_453 : ((segment 453 4).all check) = true := by
  decide +kernel

private theorem segment_457 : ((segment 457 4).all check) = true := by
  decide +kernel

private theorem segment_461 : ((segment 461 4).all check) = true := by
  decide +kernel

private theorem segment_465 : ((segment 465 4).all check) = true := by
  decide +kernel

private theorem segment_469 : ((segment 469 4).all check) = true := by
  decide +kernel

private theorem segment_473 : ((segment 473 4).all check) = true := by
  decide +kernel

private theorem segment_477 : ((segment 477 4).all check) = true := by
  decide +kernel

private theorem segment_481 : ((segment 481 4).all check) = true := by
  decide +kernel

private theorem segment_485 : ((segment 485 4).all check) = true := by
  decide +kernel

private theorem segment_489 : ((segment 489 4).all check) = true := by
  decide +kernel

private theorem segment_493 : ((segment 493 4).all check) = true := by
  decide +kernel

private theorem segment_497 : ((segment 497 4).all check) = true := by
  decide +kernel

private theorem segment_501 : ((segment 501 4).all check) = true := by
  decide +kernel

private theorem segment_505 : ((segment 505 4).all check) = true := by
  decide +kernel

private theorem segment_509 : ((segment 509 4).all check) = true := by
  decide +kernel

private theorem segment_513 : ((segment 513 4).all check) = true := by
  decide +kernel

private theorem segment_517 : ((segment 517 4).all check) = true := by
  decide +kernel

private theorem segment_521 : ((segment 521 4).all check) = true := by
  decide +kernel

private theorem segment_525 : ((segment 525 4).all check) = true := by
  decide +kernel

private theorem segment_529 : ((segment 529 4).all check) = true := by
  decide +kernel

private theorem segment_533 : ((segment 533 4).all check) = true := by
  decide +kernel

private theorem segment_537 : ((segment 537 4).all check) = true := by
  decide +kernel

private theorem segment_541 : ((segment 541 4).all check) = true := by
  decide +kernel

private theorem segment_545 : ((segment 545 4).all check) = true := by
  decide +kernel

private theorem segment_549 : ((segment 549 4).all check) = true := by
  decide +kernel

private theorem segment_553 : ((segment 553 4).all check) = true := by
  decide +kernel

private theorem segment_557 : ((segment 557 4).all check) = true := by
  decide +kernel

private theorem segment_561 : ((segment 561 4).all check) = true := by
  decide +kernel

private theorem segment_565 : ((segment 565 4).all check) = true := by
  decide +kernel

private theorem segment_569 : ((segment 569 4).all check) = true := by
  decide +kernel

private theorem segment_573 : ((segment 573 4).all check) = true := by
  decide +kernel

private theorem segment_577 : ((segment 577 4).all check) = true := by
  decide +kernel

private theorem segment_581 : ((segment 581 4).all check) = true := by
  decide +kernel

private theorem segment_585 : ((segment 585 4).all check) = true := by
  decide +kernel

private theorem segment_589 : ((segment 589 4).all check) = true := by
  decide +kernel

private theorem segment_593 : ((segment 593 4).all check) = true := by
  decide +kernel

private theorem segment_597 : ((segment 597 4).all check) = true := by
  decide +kernel

private theorem segment_601 : ((segment 601 4).all check) = true := by
  decide +kernel

private theorem segment_605 : ((segment 605 4).all check) = true := by
  decide +kernel

private theorem segment_609 : ((segment 609 4).all check) = true := by
  decide +kernel

private theorem segment_613 : ((segment 613 4).all check) = true := by
  decide +kernel

private theorem segment_617 : ((segment 617 4).all check) = true := by
  decide +kernel

private theorem segment_621 : ((segment 621 4).all check) = true := by
  decide +kernel

private theorem segment_625 : ((segment 625 4).all check) = true := by
  decide +kernel

private theorem segment_629 : ((segment 629 4).all check) = true := by
  decide +kernel

private theorem segment_633 : ((segment 633 4).all check) = true := by
  decide +kernel

private theorem segment_637 : ((segment 637 4).all check) = true := by
  decide +kernel

private theorem segment_641 : ((segment 641 4).all check) = true := by
  decide +kernel

private theorem segment_645 : ((segment 645 4).all check) = true := by
  decide +kernel

private theorem segment_649 : ((segment 649 4).all check) = true := by
  decide +kernel

private theorem segment_653 : ((segment 653 4).all check) = true := by
  decide +kernel

private theorem segment_657 : ((segment 657 4).all check) = true := by
  decide +kernel

private theorem segment_661 : ((segment 661 4).all check) = true := by
  decide +kernel

private theorem segment_665 : ((segment 665 4).all check) = true := by
  decide +kernel

private theorem segment_669 : ((segment 669 4).all check) = true := by
  decide +kernel

private theorem segment_673 : ((segment 673 4).all check) = true := by
  decide +kernel

private theorem segment_677 : ((segment 677 4).all check) = true := by
  decide +kernel

private theorem segment_681 : ((segment 681 4).all check) = true := by
  decide +kernel

private theorem segment_685 : ((segment 685 4).all check) = true := by
  decide +kernel

private theorem segment_689 : ((segment 689 4).all check) = true := by
  decide +kernel

private theorem segment_693 : ((segment 693 4).all check) = true := by
  decide +kernel

private theorem segment_697 : ((segment 697 4).all check) = true := by
  decide +kernel

private theorem segment_701 : ((segment 701 4).all check) = true := by
  decide +kernel

private theorem segment_705 : ((segment 705 4).all check) = true := by
  decide +kernel

private theorem segment_709 : ((segment 709 4).all check) = true := by
  decide +kernel

private theorem segment_713 : ((segment 713 4).all check) = true := by
  decide +kernel

private theorem segment_717 : ((segment 717 4).all check) = true := by
  decide +kernel

private theorem segment_721 : ((segment 721 1).all check) = true := by
  decide +kernel

private theorem tail_empty : ((boxes.drop 722).all check) = true := by decide +kernel

/-- Every closed leaf of the lower root passes the rational checker. -/
theorem checked : tree.check root check = true := by
  change (boxes.all check) = true
  refine all_of_parts boxes 1 first_cell_checked ?_
  refine all_from_segment 1 4 segment_1 ?_
  refine all_from_segment 5 4 segment_5 ?_
  refine all_from_segment 9 4 segment_9 ?_
  refine all_from_segment 13 4 segment_13 ?_
  refine all_from_segment 17 4 segment_17 ?_
  refine all_from_segment 21 4 segment_21 ?_
  refine all_from_segment 25 4 segment_25 ?_
  refine all_from_segment 29 4 segment_29 ?_
  refine all_from_segment 33 4 segment_33 ?_
  refine all_from_segment 37 4 segment_37 ?_
  refine all_from_segment 41 4 segment_41 ?_
  refine all_from_segment 45 4 segment_45 ?_
  refine all_from_segment 49 4 segment_49 ?_
  refine all_from_segment 53 4 segment_53 ?_
  refine all_from_segment 57 4 segment_57 ?_
  refine all_from_segment 61 4 segment_61 ?_
  refine all_from_segment 65 4 segment_65 ?_
  refine all_from_segment 69 4 segment_69 ?_
  refine all_from_segment 73 4 segment_73 ?_
  refine all_from_segment 77 4 segment_77 ?_
  refine all_from_segment 81 4 segment_81 ?_
  refine all_from_segment 85 4 segment_85 ?_
  refine all_from_segment 89 4 segment_89 ?_
  refine all_from_segment 93 4 segment_93 ?_
  refine all_from_segment 97 4 segment_97 ?_
  refine all_from_segment 101 4 segment_101 ?_
  refine all_from_segment 105 4 segment_105 ?_
  refine all_from_segment 109 4 segment_109 ?_
  refine all_from_segment 113 4 segment_113 ?_
  refine all_from_segment 117 4 segment_117 ?_
  refine all_from_segment 121 4 segment_121 ?_
  refine all_from_segment 125 4 segment_125 ?_
  refine all_from_segment 129 4 segment_129 ?_
  refine all_from_segment 133 4 segment_133 ?_
  refine all_from_segment 137 4 segment_137 ?_
  refine all_from_segment 141 4 segment_141 ?_
  refine all_from_segment 145 4 segment_145 ?_
  refine all_from_segment 149 4 segment_149 ?_
  refine all_from_segment 153 4 segment_153 ?_
  refine all_from_segment 157 4 segment_157 ?_
  refine all_from_segment 161 4 segment_161 ?_
  refine all_from_segment 165 4 segment_165 ?_
  refine all_from_segment 169 4 segment_169 ?_
  refine all_from_segment 173 4 segment_173 ?_
  refine all_from_segment 177 4 segment_177 ?_
  refine all_from_segment 181 4 segment_181 ?_
  refine all_from_segment 185 4 segment_185 ?_
  refine all_from_segment 189 4 segment_189 ?_
  refine all_from_segment 193 4 segment_193 ?_
  refine all_from_segment 197 4 segment_197 ?_
  refine all_from_segment 201 4 segment_201 ?_
  refine all_from_segment 205 4 segment_205 ?_
  refine all_from_segment 209 4 segment_209 ?_
  refine all_from_segment 213 4 segment_213 ?_
  refine all_from_segment 217 4 segment_217 ?_
  refine all_from_segment 221 4 segment_221 ?_
  refine all_from_segment 225 4 segment_225 ?_
  refine all_from_segment 229 4 segment_229 ?_
  refine all_from_segment 233 4 segment_233 ?_
  refine all_from_segment 237 4 segment_237 ?_
  refine all_from_segment 241 4 segment_241 ?_
  refine all_from_segment 245 4 segment_245 ?_
  refine all_from_segment 249 4 segment_249 ?_
  refine all_from_segment 253 4 segment_253 ?_
  refine all_from_segment 257 4 segment_257 ?_
  refine all_from_segment 261 4 segment_261 ?_
  refine all_from_segment 265 4 segment_265 ?_
  refine all_from_segment 269 4 segment_269 ?_
  refine all_from_segment 273 4 segment_273 ?_
  refine all_from_segment 277 4 segment_277 ?_
  refine all_from_segment 281 4 segment_281 ?_
  refine all_from_segment 285 4 segment_285 ?_
  refine all_from_segment 289 4 segment_289 ?_
  refine all_from_segment 293 4 segment_293 ?_
  refine all_from_segment 297 4 segment_297 ?_
  refine all_from_segment 301 4 segment_301 ?_
  refine all_from_segment 305 4 segment_305 ?_
  refine all_from_segment 309 4 segment_309 ?_
  refine all_from_segment 313 4 segment_313 ?_
  refine all_from_segment 317 4 segment_317 ?_
  refine all_from_segment 321 4 segment_321 ?_
  refine all_from_segment 325 4 segment_325 ?_
  refine all_from_segment 329 4 segment_329 ?_
  refine all_from_segment 333 4 segment_333 ?_
  refine all_from_segment 337 4 segment_337 ?_
  refine all_from_segment 341 4 segment_341 ?_
  refine all_from_segment 345 4 segment_345 ?_
  refine all_from_segment 349 4 segment_349 ?_
  refine all_from_segment 353 4 segment_353 ?_
  refine all_from_segment 357 4 segment_357 ?_
  refine all_from_segment 361 4 segment_361 ?_
  refine all_from_segment 365 4 segment_365 ?_
  refine all_from_segment 369 4 segment_369 ?_
  refine all_from_segment 373 4 segment_373 ?_
  refine all_from_segment 377 4 segment_377 ?_
  refine all_from_segment 381 4 segment_381 ?_
  refine all_from_segment 385 4 segment_385 ?_
  refine all_from_segment 389 4 segment_389 ?_
  refine all_from_segment 393 4 segment_393 ?_
  refine all_from_segment 397 4 segment_397 ?_
  refine all_from_segment 401 4 segment_401 ?_
  refine all_from_segment 405 4 segment_405 ?_
  refine all_from_segment 409 4 segment_409 ?_
  refine all_from_segment 413 4 segment_413 ?_
  refine all_from_segment 417 4 segment_417 ?_
  refine all_from_segment 421 4 segment_421 ?_
  refine all_from_segment 425 4 segment_425 ?_
  refine all_from_segment 429 4 segment_429 ?_
  refine all_from_segment 433 4 segment_433 ?_
  refine all_from_segment 437 4 segment_437 ?_
  refine all_from_segment 441 4 segment_441 ?_
  refine all_from_segment 445 4 segment_445 ?_
  refine all_from_segment 449 4 segment_449 ?_
  refine all_from_segment 453 4 segment_453 ?_
  refine all_from_segment 457 4 segment_457 ?_
  refine all_from_segment 461 4 segment_461 ?_
  refine all_from_segment 465 4 segment_465 ?_
  refine all_from_segment 469 4 segment_469 ?_
  refine all_from_segment 473 4 segment_473 ?_
  refine all_from_segment 477 4 segment_477 ?_
  refine all_from_segment 481 4 segment_481 ?_
  refine all_from_segment 485 4 segment_485 ?_
  refine all_from_segment 489 4 segment_489 ?_
  refine all_from_segment 493 4 segment_493 ?_
  refine all_from_segment 497 4 segment_497 ?_
  refine all_from_segment 501 4 segment_501 ?_
  refine all_from_segment 505 4 segment_505 ?_
  refine all_from_segment 509 4 segment_509 ?_
  refine all_from_segment 513 4 segment_513 ?_
  refine all_from_segment 517 4 segment_517 ?_
  refine all_from_segment 521 4 segment_521 ?_
  refine all_from_segment 525 4 segment_525 ?_
  refine all_from_segment 529 4 segment_529 ?_
  refine all_from_segment 533 4 segment_533 ?_
  refine all_from_segment 537 4 segment_537 ?_
  refine all_from_segment 541 4 segment_541 ?_
  refine all_from_segment 545 4 segment_545 ?_
  refine all_from_segment 549 4 segment_549 ?_
  refine all_from_segment 553 4 segment_553 ?_
  refine all_from_segment 557 4 segment_557 ?_
  refine all_from_segment 561 4 segment_561 ?_
  refine all_from_segment 565 4 segment_565 ?_
  refine all_from_segment 569 4 segment_569 ?_
  refine all_from_segment 573 4 segment_573 ?_
  refine all_from_segment 577 4 segment_577 ?_
  refine all_from_segment 581 4 segment_581 ?_
  refine all_from_segment 585 4 segment_585 ?_
  refine all_from_segment 589 4 segment_589 ?_
  refine all_from_segment 593 4 segment_593 ?_
  refine all_from_segment 597 4 segment_597 ?_
  refine all_from_segment 601 4 segment_601 ?_
  refine all_from_segment 605 4 segment_605 ?_
  refine all_from_segment 609 4 segment_609 ?_
  refine all_from_segment 613 4 segment_613 ?_
  refine all_from_segment 617 4 segment_617 ?_
  refine all_from_segment 621 4 segment_621 ?_
  refine all_from_segment 625 4 segment_625 ?_
  refine all_from_segment 629 4 segment_629 ?_
  refine all_from_segment 633 4 segment_633 ?_
  refine all_from_segment 637 4 segment_637 ?_
  refine all_from_segment 641 4 segment_641 ?_
  refine all_from_segment 645 4 segment_645 ?_
  refine all_from_segment 649 4 segment_649 ?_
  refine all_from_segment 653 4 segment_653 ?_
  refine all_from_segment 657 4 segment_657 ?_
  refine all_from_segment 661 4 segment_661 ?_
  refine all_from_segment 665 4 segment_665 ?_
  refine all_from_segment 669 4 segment_669 ?_
  refine all_from_segment 673 4 segment_673 ?_
  refine all_from_segment 677 4 segment_677 ?_
  refine all_from_segment 681 4 segment_681 ?_
  refine all_from_segment 685 4 segment_685 ?_
  refine all_from_segment 689 4 segment_689 ?_
  refine all_from_segment 693 4 segment_693 ?_
  refine all_from_segment 697 4 segment_697 ?_
  refine all_from_segment 701 4 segment_701 ?_
  refine all_from_segment 705 4 segment_705 ?_
  refine all_from_segment 709 4 segment_709 ?_
  refine all_from_segment 713 4 segment_713 ?_
  refine all_from_segment 717 4 segment_717 ?_
  refine all_from_segment 721 1 segment_721 ?_
  exact tail_empty

/-- In the lower focal spectrum, Wu's normalized cubic deficit dominates
the squared displacement from Gibbs with coefficient 1/1024. -/
theorem normalized_deficit_ge (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : -(1 / 256) ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 0)
    (hn₀ : -(1 / 256) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 256) :
    ((m - (r ^ 2)⁻¹) ^ 2 + (n - r⁻¹) ^ 2 + (q - r⁻¹) ^ 2) / 1024 ≤
      normalizedDeficit r U m n q :=
  WuCubicLowerFocal.normalized_deficit_ge_of_check checked U hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁

#print axioms normalized_deficit_ge

end D5.S3.Quantum.Semigroups.WuCubicLowerReplay
