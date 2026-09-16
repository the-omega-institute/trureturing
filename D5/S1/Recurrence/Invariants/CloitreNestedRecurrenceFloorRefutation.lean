/- GID: D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Topology.Instances.Real.Lemmas]
   digest: At n = 1167, the literal nested recurrence is 664 while the conjectured cubic-root floor is 665. -/

import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S1.Recurrence.Invariants.CloitreNestedRecurrenceFloorRefutation

/-!
OEIS A076502, entered by Benoit Cloitre on 2002-11-08, defines
`a(1)=1, a(n)=n-a(n-a(n-a(n-1))).`  The value at zero below is only a
sentinel outside the offset-one sequence.

The recursive implementation clamps the two computed inner indices below the
current input.  A strong-induction invariant proves that both clamps are
identities, so the public sequence satisfies the literal recurrence without a
fuel convention.
-/

/-- The offset-one A076502 sequence, extended by the disclosed sentinel `a 0 = 0`. -/
def a : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let i2 := min (n + 2 - a (n + 1)) (n + 1)
      let i3 := min (n + 2 - a i2) (n + 1)
      n + 2 - a i3
termination_by n => n
decreasing_by all_goals omega

private theorem a_bounds (N : ℕ) : a N <= N /\ (0 < N -> 0 < a N) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      rcases N with _ | _ | n
      · simp [a]
      · simp [a]
      · rw [a]
        let i2 := min (n + 2 - a (n + 1)) (n + 1)
        let i3 := min (n + 2 - a i2) (n + 1)
        have h1 := ih (n + 1) (by omega)
        have hi2le : i2 <= n + 1 := min_le_right _ _
        have hi2pos : 0 < i2 := by
          have hraw : 0 < n + 2 - a (n + 1) := by omega
          simp only [i2, lt_min_iff]
          omega
        have h2 := ih i2 (by omega)
        have hi3le : i3 <= n + 1 := min_le_right _ _
        have hi3pos : 0 < i3 := by
          have hraw : 0 < n + 2 - a i2 := by omega
          simp only [i3, lt_min_iff]
          omega
        have h3 := ih i3 (by omega)
        change n + 2 - a i3 <= n + 2 /\ (0 < n + 2 -> 0 < n + 2 - a i3)
        omega

theorem a_succ : ∀ n : ℕ, 2 <= n ->
    a n = n - a (n - a (n - a (n - 1))) := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [a]
  have h1 := a_bounds (n + 1)
  have hi2le : n + 2 - a (n + 1) <= n + 1 := by omega
  rw [min_eq_left hi2le]
  have hi2pos : 0 < n + 2 - a (n + 1) := by omega
  have h2 := a_bounds (n + 2 - a (n + 1))
  have hi3le : n + 2 - a (n + 2 - a (n + 1)) <= n + 1 := by omega
  rw [min_eq_left hi3le]
  have hpred : n + 2 - 1 = n + 1 := by omega
  rw [hpred]

private def P (x : ℝ) : ℝ := x ^ 3 - x ^ 2 + 2 * x - 1

private theorem P_strictMono : StrictMono P := by
  intro x y hxy
  have hfactor : 0 < y ^ 2 + y * x + x ^ 2 - y - x + 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y - 1)]
  have hdiff : P y - P x =
      (y - x) * (y ^ 2 + y * x + x ^ 2 - y - x + 2) := by
    simp only [P]
    ring
  have hprod : 0 < (y - x) * (y ^ 2 + y * x + x ^ 2 - y - x + 2) :=
    mul_pos (sub_pos.mpr hxy) hfactor
  linarith

theorem cubic_positiveRoot_existsUnique :
    ∃! x : ℝ, 0 < x /\ x ^ 3 - x ^ 2 + 2 * x - 1 = 0 := by
  have hroot : ∃! x : ℝ, 0 < x /\ P x = 0 := by
    have hcontinuous : Continuous P := by
      unfold P
      exact ((((continuous_id.pow 3).sub (continuous_id.pow 2)).add
        (continuous_const.mul continuous_id)).sub continuous_const)
    have hzero : (0 : ℝ) ∈ Set.Icc (P 0) (P 1) := by
      norm_num [P]
    obtain ⟨x, hx, hPx⟩ :=
      intermediate_value_Icc (show (0 : ℝ) <= 1 by norm_num)
        hcontinuous.continuousOn hzero
    have hxpos : 0 < x := by
      rcases hx with ⟨hxnonneg, _⟩
      by_contra hnot
      have : x = 0 := by linarith
      subst x
      norm_num [P] at hPx
    refine ⟨x, ⟨hxpos, hPx⟩, ?_⟩
    intro y hy
    apply P_strictMono.injective
    exact hy.2.trans hPx.symm
  simpa only [P] using hroot

/-- The unique positive real root of `x^3 - x^2 + 2*x - 1`. -/
noncomputable def c : ℝ := Classical.choose cubic_positiveRoot_existsUnique

/-- Cloitre's literal 2002 comment: bounded real error and floor offset in `{0,1,2}`. -/
def claim : Prop :=
  (∃ M : ℝ, ∀ n : ℕ, 1 <= n -> |(a n : ℝ) - c * n| <= M) /\
    ∀ n : ℕ, 1 <= n -> ∃ j ∈ ({0, 1, 2} : Finset ℤ),
      (a n : ℤ) = ⌊c * n⌋ + j

private inductive PrefixTable where
  | empty
  | branch (index value : ℕ) (left right : PrefixTable)

private def PrefixTable.lookup (index : ℕ) : PrefixTable -> Option ℕ
  | .empty => none
  | .branch key value left right =>
      if index = key then some value
      else if index < key then left.lookup index
      else right.lookup index

private def PrefixTable.value (table : PrefixTable) (index : ℕ) : ℕ :=
  (table.lookup index).getD 0

private def entryChecks (table : PrefixTable) (index : ℕ) : Bool :=
  (table.lookup index).isSome &&
    match index with
    | 0 => table.value 0 == 0
    | 1 => table.value 1 == 1
    | n + 2 => table.value (n + 2) ==
        n + 2 - table.value (n + 2 - table.value
          (n + 2 - table.value (n + 1)))

private def prefixChecks (table : PrefixTable) (last : ℕ) : Bool :=
  (List.range (last + 1)).all (entryChecks table)

private theorem prefixChecks_sound (table : PrefixTable) (last : ℕ)
    (hchecks : prefixChecks table last = true) :
    ∀ index, index <= last -> a index = table.value index := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index ih =>
      intro hindex
      have hentryBool := List.all_eq_true.mp hchecks index (by simp; omega)
      simp only [entryChecks, Bool.and_eq_true] at hentryBool
      rcases index with _ | _ | n
      · have heq : table.value 0 = 0 := by simpa using hentryBool.2
        simpa [a] using heq.symm
      · have heq : table.value 1 = 1 := by simpa using hentryBool.2
        simpa [a] using heq.symm
      · have heq : table.value (n + 2) =
            n + 2 - table.value (n + 2 - table.value
              (n + 2 - table.value (n + 1))) := by
          simpa using hentryBool.2
        have hpred : n + 2 - 1 = n + 1 := by omega
        rw [a_succ (n + 2) (by omega), hpred]
        have ha1 := a_bounds (n + 1)
        have h1 := ih (n + 1) (by omega) (by omega)
        rw [h1]
        have hi2pos : 0 < n + 2 - table.value (n + 1) := by
          rw [← h1]
          omega
        have hi2lt : n + 2 - table.value (n + 1) < n + 2 := by
          rw [← h1]
          omega
        have h2 := ih (n + 2 - table.value (n + 1)) hi2lt (by omega)
        rw [h2]
        have ha2 := a_bounds (n + 2 - table.value (n + 1))
        have hi3lt :
            n + 2 - table.value (n + 2 - table.value (n + 1)) < n + 2 := by
          rw [← h2]
          have ha2pos := ha2.2 hi2pos
          omega
        have h3 := ih
          (n + 2 - table.value (n + 2 - table.value (n + 1))) hi3lt (by omega)
        rw [h3]
        exact heq.symm

-- Candidate data only: every entry is checked against the literal recurrence.
-- The balanced shape gives logarithmic lookup without entering the soundness proof.
private def certificate : PrefixTable :=
  (.branch 584 333 (.branch 292 166 (.branch 146 84 (.branch 73 42 (.branch 36 21 (.branch 18 10 (.branch 9 5 (.branch 4 2 (.branch 2 1 (.branch 1 1 (.branch 0 0 .empty .empty) .empty) (.branch 3 2 .empty .empty)) (.branch 7 4 (.branch 6 4 (.branch 5 3 .empty .empty) .empty) (.branch 8 4 .empty .empty))) (.branch 14 8 (.branch 12 7 (.branch 11 7 (.branch 10 6 .empty .empty) .empty) (.branch 13 8 .empty .empty)) (.branch 16 9 (.branch 15 8 .empty .empty) (.branch 17 9 .empty .empty)))) (.branch 27 15 (.branch 23 14 (.branch 21 12 (.branch 20 12 (.branch 19 11 .empty .empty) .empty) (.branch 22 13 .empty .empty)) (.branch 25 15 (.branch 24 14 .empty .empty) (.branch 26 15 .empty .empty))) (.branch 32 18 (.branch 30 17 (.branch 29 17 (.branch 28 16 .empty .empty) .empty) (.branch 31 17 .empty .empty)) (.branch 34 19 (.branch 33 18 .empty .empty) (.branch 35 20 .empty .empty))))) (.branch 55 31 (.branch 46 27 (.branch 41 24 (.branch 39 22 (.branch 38 21 (.branch 37 21 .empty .empty) .empty) (.branch 40 23 .empty .empty)) (.branch 44 26 (.branch 43 25 (.branch 42 24 .empty .empty) .empty) (.branch 45 26 .empty .empty))) (.branch 51 30 (.branch 49 28 (.branch 48 27 (.branch 47 27 .empty .empty) .empty) (.branch 50 29 .empty .empty)) (.branch 53 31 (.branch 52 30 .empty .empty) (.branch 54 31 .empty .empty)))) (.branch 64 37 (.branch 60 34 (.branch 58 33 (.branch 57 33 (.branch 56 32 .empty .empty) .empty) (.branch 59 33 .empty .empty)) (.branch 62 35 (.branch 61 34 .empty .empty) (.branch 63 36 .empty .empty))) (.branch 69 39 (.branch 67 38 (.branch 66 38 (.branch 65 37 .empty .empty) .empty) (.branch 68 38 .empty .empty)) (.branch 71 40 (.branch 70 39 .empty .empty) (.branch 72 41 .empty .empty)))))) (.branch 110 62 (.branch 92 53 (.branch 83 48 (.branch 78 45 (.branch 76 43 (.branch 75 42 (.branch 74 42 .empty .empty) .empty) (.branch 77 44 .empty .empty)) (.branch 81 47 (.branch 80 46 (.branch 79 45 .empty .empty) .empty) (.branch 82 47 .empty .empty))) (.branch 88 50 (.branch 86 49 (.branch 85 48 (.branch 84 48 .empty .empty) .empty) (.branch 87 49 .empty .empty)) (.branch 90 52 (.branch 89 51 .empty .empty) (.branch 91 52 .empty .empty)))) (.branch 101 58 (.branch 97 55 (.branch 95 55 (.branch 94 54 (.branch 93 54 .empty .empty) .empty) (.branch 96 55 .empty .empty)) (.branch 99 57 (.branch 98 56 .empty .empty) (.branch 100 58 .empty .empty))) (.branch 106 61 (.branch 104 59 (.branch 103 59 (.branch 102 59 .empty .empty) .empty) (.branch 105 60 .empty .empty)) (.branch 108 61 (.branch 107 61 .empty .empty) (.branch 109 62 .empty .empty))))) (.branch 128 73 (.branch 119 68 (.branch 115 66 (.branch 113 65 (.branch 112 64 (.branch 111 63 .empty .empty) .empty) (.branch 114 65 .empty .empty)) (.branch 117 67 (.branch 116 67 .empty .empty) (.branch 118 68 .empty .empty))) (.branch 124 70 (.branch 122 70 (.branch 121 69 (.branch 120 68 .empty .empty) .empty) (.branch 123 70 .empty .empty)) (.branch 126 71 (.branch 125 71 .empty .empty) (.branch 127 72 .empty .empty)))) (.branch 137 78 (.branch 133 75 (.branch 131 75 (.branch 130 74 (.branch 129 74 .empty .empty) .empty) (.branch 132 75 .empty .empty)) (.branch 135 76 (.branch 134 76 .empty .empty) (.branch 136 77 .empty .empty))) (.branch 142 81 (.branch 140 79 (.branch 139 79 (.branch 138 79 .empty .empty) .empty) (.branch 141 80 .empty .empty)) (.branch 144 82 (.branch 143 82 .empty .empty) (.branch 145 83 .empty .empty))))))) (.branch 219 125 (.branch 183 104 (.branch 165 94 (.branch 156 88 (.branch 151 86 (.branch 149 85 (.branch 148 85 (.branch 147 84 .empty .empty) .empty) (.branch 150 85 .empty .empty)) (.branch 154 87 (.branch 153 87 (.branch 152 87 .empty .empty) .empty) (.branch 155 88 .empty .empty))) (.branch 161 91 (.branch 159 91 (.branch 158 90 (.branch 157 89 .empty .empty) .empty) (.branch 160 91 .empty .empty)) (.branch 163 93 (.branch 162 92 .empty .empty) (.branch 164 94 .empty .empty)))) (.branch 174 99 (.branch 170 97 (.branch 168 96 (.branch 167 96 (.branch 166 95 .empty .empty) .empty) (.branch 169 97 .empty .empty)) (.branch 172 98 (.branch 171 97 .empty .empty) (.branch 173 98 .empty .empty))) (.branch 179 103 (.branch 177 101 (.branch 176 101 (.branch 175 100 .empty .empty) .empty) (.branch 178 102 .empty .empty)) (.branch 181 104 (.branch 180 103 .empty .empty) (.branch 182 104 .empty .empty))))) (.branch 201 114 (.branch 192 110 (.branch 188 108 (.branch 186 107 (.branch 185 106 (.branch 184 105 .empty .empty) .empty) (.branch 187 107 .empty .empty)) (.branch 190 108 (.branch 189 108 .empty .empty) (.branch 191 109 .empty .empty))) (.branch 197 112 (.branch 195 111 (.branch 194 110 (.branch 193 110 .empty .empty) .empty) (.branch 196 111 .empty .empty)) (.branch 199 114 (.branch 198 113 .empty .empty) (.branch 200 114 .empty .empty)))) (.branch 210 120 (.branch 206 118 (.branch 204 117 (.branch 203 116 (.branch 202 115 .empty .empty) .empty) (.branch 205 117 .empty .empty)) (.branch 208 119 (.branch 207 119 .empty .empty) (.branch 209 120 .empty .empty))) (.branch 215 123 (.branch 213 122 (.branch 212 121 (.branch 211 120 .empty .empty) .empty) (.branch 214 123 .empty .empty)) (.branch 217 124 (.branch 216 124 .empty .empty) (.branch 218 124 .empty .empty)))))) (.branch 256 146 (.branch 238 135 (.branch 229 131 (.branch 224 127 (.branch 222 126 (.branch 221 126 (.branch 220 126 .empty .empty) .empty) (.branch 223 127 .empty .empty)) (.branch 227 130 (.branch 226 129 (.branch 225 128 .empty .empty) .empty) (.branch 228 130 .empty .empty))) (.branch 234 133 (.branch 232 133 (.branch 231 132 (.branch 230 132 .empty .empty) .empty) (.branch 233 133 .empty .empty)) (.branch 236 135 (.branch 235 134 .empty .empty) (.branch 237 135 .empty .empty)))) (.branch 247 140 (.branch 243 139 (.branch 241 137 (.branch 240 136 (.branch 239 136 .empty .empty) .empty) (.branch 242 138 .empty .empty)) (.branch 245 140 (.branch 244 139 .empty .empty) (.branch 246 140 .empty .empty))) (.branch 252 144 (.branch 250 142 (.branch 249 141 (.branch 248 141 .empty .empty) .empty) (.branch 251 143 .empty .empty)) (.branch 254 144 (.branch 253 144 .empty .empty) (.branch 255 145 .empty .empty))))) (.branch 274 156 (.branch 265 151 (.branch 261 149 (.branch 259 148 (.branch 258 147 (.branch 257 147 .empty .empty) .empty) (.branch 260 149 .empty .empty)) (.branch 263 150 (.branch 262 150 .empty .empty) (.branch 264 150 .empty .empty))) (.branch 270 154 (.branch 268 153 (.branch 267 153 (.branch 266 152 .empty .empty) .empty) (.branch 269 154 .empty .empty)) (.branch 272 155 (.branch 271 154 .empty .empty) (.branch 273 156 .empty .empty)))) (.branch 283 161 (.branch 279 159 (.branch 277 157 (.branch 276 157 (.branch 275 156 .empty .empty) .empty) (.branch 278 158 .empty .empty)) (.branch 281 160 (.branch 280 160 .empty .empty) (.branch 282 161 .empty .empty))) (.branch 288 164 (.branch 286 162 (.branch 285 162 (.branch 284 161 .empty .empty) .empty) (.branch 287 163 .empty .empty)) (.branch 290 165 (.branch 289 165 .empty .empty) (.branch 291 165 .empty .empty)))))))) (.branch 438 249 (.branch 365 208 (.branch 329 188 (.branch 311 177 (.branch 302 172 (.branch 297 170 (.branch 295 168 (.branch 294 168 (.branch 293 167 .empty .empty) .empty) (.branch 296 169 .empty .empty)) (.branch 300 171 (.branch 299 171 (.branch 298 170 .empty .empty) .empty) (.branch 301 171 .empty .empty))) (.branch 307 174 (.branch 305 173 (.branch 304 173 (.branch 303 173 .empty .empty) .empty) (.branch 306 174 .empty .empty)) (.branch 309 176 (.branch 308 175 .empty .empty) (.branch 310 177 .empty .empty)))) (.branch 320 183 (.branch 316 180 (.branch 314 179 (.branch 313 178 (.branch 312 177 .empty .empty) .empty) (.branch 315 180 .empty .empty)) (.branch 318 182 (.branch 317 181 .empty .empty) (.branch 319 182 .empty .empty))) (.branch 325 185 (.branch 323 184 (.branch 322 183 (.branch 321 183 .empty .empty) .empty) (.branch 324 184 .empty .empty)) (.branch 327 187 (.branch 326 186 .empty .empty) (.branch 328 187 .empty .empty))))) (.branch 347 197 (.branch 338 193 (.branch 334 190 (.branch 332 190 (.branch 331 189 (.branch 330 189 .empty .empty) .empty) (.branch 333 190 .empty .empty)) (.branch 336 192 (.branch 335 191 .empty .empty) (.branch 337 193 .empty .empty))) (.branch 343 196 (.branch 341 194 (.branch 340 194 (.branch 339 194 .empty .empty) .empty) (.branch 342 195 .empty .empty)) (.branch 345 196 (.branch 344 196 .empty .empty) (.branch 346 197 .empty .empty)))) (.branch 356 202 (.branch 352 201 (.branch 350 200 (.branch 349 199 (.branch 348 198 .empty .empty) .empty) (.branch 351 200 .empty .empty)) (.branch 354 201 (.branch 353 201 .empty .empty) (.branch 355 202 .empty .empty))) (.branch 361 205 (.branch 359 205 (.branch 358 204 (.branch 357 203 .empty .empty) .empty) (.branch 360 205 .empty .empty)) (.branch 363 207 (.branch 362 206 .empty .empty) (.branch 364 208 .empty .empty)))))) (.branch 402 229 (.branch 384 219 (.branch 375 214 (.branch 370 211 (.branch 368 210 (.branch 367 210 (.branch 366 209 .empty .empty) .empty) (.branch 369 211 .empty .empty)) (.branch 373 212 (.branch 372 212 (.branch 371 211 .empty .empty) .empty) (.branch 374 213 .empty .empty))) (.branch 380 217 (.branch 378 216 (.branch 377 215 (.branch 376 215 .empty .empty) .empty) (.branch 379 217 .empty .empty)) (.branch 382 218 (.branch 381 218 .empty .empty) (.branch 383 218 .empty .empty)))) (.branch 393 224 (.branch 389 222 (.branch 387 221 (.branch 386 221 (.branch 385 220 .empty .empty) .empty) (.branch 388 222 .empty .empty)) (.branch 391 223 (.branch 390 222 .empty .empty) (.branch 392 224 .empty .empty))) (.branch 398 227 (.branch 396 225 (.branch 395 225 (.branch 394 224 .empty .empty) .empty) (.branch 397 226 .empty .empty)) (.branch 400 228 (.branch 399 228 .empty .empty) (.branch 401 228 .empty .empty))))) (.branch 420 240 (.branch 411 234 (.branch 407 233 (.branch 405 231 (.branch 404 231 (.branch 403 230 .empty .empty) .empty) (.branch 406 232 .empty .empty)) (.branch 409 234 (.branch 408 233 .empty .empty) (.branch 410 234 .empty .empty))) (.branch 416 238 (.branch 414 237 (.branch 413 236 (.branch 412 235 .empty .empty) .empty) (.branch 415 237 .empty .empty)) (.branch 418 238 (.branch 417 238 .empty .empty) (.branch 419 239 .empty .empty)))) (.branch 429 245 (.branch 425 242 (.branch 423 241 (.branch 422 240 (.branch 421 240 .empty .empty) .empty) (.branch 424 241 .empty .empty)) (.branch 427 244 (.branch 426 243 .empty .empty) (.branch 428 244 .empty .empty))) (.branch 434 247 (.branch 432 247 (.branch 431 246 (.branch 430 246 .empty .empty) .empty) (.branch 433 247 .empty .empty)) (.branch 436 249 (.branch 435 248 .empty .empty) (.branch 437 249 .empty .empty))))))) (.branch 511 291 (.branch 475 271 (.branch 457 261 (.branch 448 255 (.branch 443 253 (.branch 441 251 (.branch 440 250 (.branch 439 250 .empty .empty) .empty) (.branch 442 252 .empty .empty)) (.branch 446 254 (.branch 445 254 (.branch 444 253 .empty .empty) .empty) (.branch 447 254 .empty .empty))) (.branch 453 258 (.branch 451 257 (.branch 450 256 (.branch 449 255 .empty .empty) .empty) (.branch 452 258 .empty .empty)) (.branch 455 259 (.branch 454 258 .empty .empty) (.branch 456 260 .empty .empty)))) (.branch 466 265 (.branch 462 264 (.branch 460 263 (.branch 459 262 (.branch 458 261 .empty .empty) .empty) (.branch 461 263 .empty .empty)) (.branch 464 264 (.branch 463 264 .empty .empty) (.branch 465 265 .empty .empty))) (.branch 471 269 (.branch 469 268 (.branch 468 267 (.branch 467 266 .empty .empty) .empty) (.branch 470 268 .empty .empty)) (.branch 473 270 (.branch 472 270 .empty .empty) (.branch 474 271 .empty .empty))))) (.branch 493 281 (.branch 484 276 (.branch 480 274 (.branch 478 273 (.branch 477 272 (.branch 476 271 .empty .empty) .empty) (.branch 479 274 .empty .empty)) (.branch 482 275 (.branch 481 275 .empty .empty) (.branch 483 275 .empty .empty))) (.branch 489 278 (.branch 487 277 (.branch 486 277 (.branch 485 277 .empty .empty) .empty) (.branch 488 278 .empty .empty)) (.branch 491 280 (.branch 490 279 .empty .empty) (.branch 492 281 .empty .empty)))) (.branch 502 286 (.branch 498 284 (.branch 496 283 (.branch 495 283 (.branch 494 282 .empty .empty) .empty) (.branch 497 284 .empty .empty)) (.branch 500 285 (.branch 499 284 .empty .empty) (.branch 501 286 .empty .empty))) (.branch 507 289 (.branch 505 287 (.branch 504 287 (.branch 503 286 .empty .empty) .empty) (.branch 506 288 .empty .empty)) (.branch 509 290 (.branch 508 290 .empty .empty) (.branch 510 291 .empty .empty)))))) (.branch 548 312 (.branch 530 302 (.branch 521 297 (.branch 516 294 (.branch 514 292 (.branch 513 292 (.branch 512 291 .empty .empty) .empty) (.branch 515 293 .empty .empty)) (.branch 519 295 (.branch 518 295 (.branch 517 295 .empty .empty) .empty) (.branch 520 296 .empty .empty))) (.branch 526 300 (.branch 524 299 (.branch 523 298 (.branch 522 298 .empty .empty) .empty) (.branch 525 300 .empty .empty)) (.branch 528 301 (.branch 527 301 .empty .empty) (.branch 529 301 .empty .empty)))) (.branch 539 307 (.branch 535 305 (.branch 533 304 (.branch 532 304 (.branch 531 303 .empty .empty) .empty) (.branch 534 305 .empty .empty)) (.branch 537 306 (.branch 536 305 .empty .empty) (.branch 538 307 .empty .empty))) (.branch 544 310 (.branch 542 308 (.branch 541 308 (.branch 540 307 .empty .empty) .empty) (.branch 543 309 .empty .empty)) (.branch 546 311 (.branch 545 311 .empty .empty) (.branch 547 312 .empty .empty))))) (.branch 566 322 (.branch 557 317 (.branch 553 315 (.branch 551 313 (.branch 550 313 (.branch 549 312 .empty .empty) .empty) (.branch 552 314 .empty .empty)) (.branch 555 316 (.branch 554 316 .empty .empty) (.branch 556 316 .empty .empty))) (.branch 562 321 (.branch 560 319 (.branch 559 319 (.branch 558 318 .empty .empty) .empty) (.branch 561 320 .empty .empty)) (.branch 564 322 (.branch 563 321 .empty .empty) (.branch 565 322 .empty .empty)))) (.branch 575 328 (.branch 571 325 (.branch 569 324 (.branch 568 324 (.branch 567 323 .empty .empty) .empty) (.branch 570 324 .empty .empty)) (.branch 573 326 (.branch 572 325 .empty .empty) (.branch 574 327 .empty .empty))) (.branch 580 331 (.branch 578 329 (.branch 577 328 (.branch 576 328 .empty .empty) .empty) (.branch 579 330 .empty .empty)) (.branch 582 332 (.branch 581 331 .empty .empty) (.branch 583 333 .empty .empty))))))))) (.branch 876 499 (.branch 730 417 (.branch 657 374 (.branch 621 354 (.branch 603 344 (.branch 594 339 (.branch 589 335 (.branch 587 334 (.branch 586 334 (.branch 585 334 .empty .empty) .empty) (.branch 588 335 .empty .empty)) (.branch 592 338 (.branch 591 337 (.branch 590 336 .empty .empty) .empty) (.branch 593 338 .empty .empty))) (.branch 599 341 (.branch 597 341 (.branch 596 340 (.branch 595 340 .empty .empty) .empty) (.branch 598 341 .empty .empty)) (.branch 601 343 (.branch 600 342 .empty .empty) (.branch 602 344 .empty .empty)))) (.branch 612 348 (.branch 608 347 (.branch 606 345 (.branch 605 345 (.branch 604 345 .empty .empty) .empty) (.branch 607 346 .empty .empty)) (.branch 610 347 (.branch 609 347 .empty .empty) (.branch 611 348 .empty .empty))) (.branch 617 352 (.branch 615 351 (.branch 614 350 (.branch 613 349 .empty .empty) .empty) (.branch 616 351 .empty .empty)) (.branch 619 353 (.branch 618 353 .empty .empty) (.branch 620 354 .empty .empty))))) (.branch 639 364 (.branch 630 359 (.branch 626 356 (.branch 624 356 (.branch 623 355 (.branch 622 354 .empty .empty) .empty) (.branch 625 356 .empty .empty)) (.branch 628 357 (.branch 627 357 .empty .empty) (.branch 629 358 .empty .empty))) (.branch 635 361 (.branch 633 361 (.branch 632 360 (.branch 631 360 .empty .empty) .empty) (.branch 634 361 .empty .empty)) (.branch 637 362 (.branch 636 362 .empty .empty) (.branch 638 363 .empty .empty)))) (.branch 648 370 (.branch 644 367 (.branch 642 365 (.branch 641 365 (.branch 640 365 .empty .empty) .empty) (.branch 643 366 .empty .empty)) (.branch 646 368 (.branch 645 368 .empty .empty) (.branch 647 369 .empty .empty))) (.branch 653 372 (.branch 651 371 (.branch 650 371 (.branch 649 370 .empty .empty) .empty) (.branch 652 371 .empty .empty)) (.branch 655 373 (.branch 654 373 .empty .empty) (.branch 656 373 .empty .empty)))))) (.branch 694 396 (.branch 676 385 (.branch 667 380 (.branch 662 377 (.branch 660 376 (.branch 659 375 (.branch 658 374 .empty .empty) .empty) (.branch 661 377 .empty .empty)) (.branch 665 379 (.branch 664 378 (.branch 663 377 .empty .empty) .empty) (.branch 666 380 .empty .empty))) (.branch 672 383 (.branch 670 382 (.branch 669 382 (.branch 668 381 .empty .empty) .empty) (.branch 671 383 .empty .empty)) (.branch 674 384 (.branch 673 383 .empty .empty) (.branch 675 384 .empty .empty)))) (.branch 685 390 (.branch 681 389 (.branch 679 387 (.branch 678 387 (.branch 677 386 .empty .empty) .empty) (.branch 680 388 .empty .empty)) (.branch 683 390 (.branch 682 389 .empty .empty) (.branch 684 390 .empty .empty))) (.branch 690 394 (.branch 688 393 (.branch 687 392 (.branch 686 391 .empty .empty) .empty) (.branch 689 393 .empty .empty)) (.branch 692 394 (.branch 691 394 .empty .empty) (.branch 693 395 .empty .empty))))) (.branch 712 405 (.branch 703 401 (.branch 699 398 (.branch 697 397 (.branch 696 396 (.branch 695 396 .empty .empty) .empty) (.branch 698 397 .empty .empty)) (.branch 701 400 (.branch 700 399 .empty .empty) (.branch 702 400 .empty .empty))) (.branch 708 403 (.branch 706 402 (.branch 705 401 (.branch 704 401 .empty .empty) .empty) (.branch 707 402 .empty .empty)) (.branch 710 405 (.branch 709 404 .empty .empty) (.branch 711 405 .empty .empty)))) (.branch 721 411 (.branch 717 409 (.branch 715 408 (.branch 714 407 (.branch 713 406 .empty .empty) .empty) (.branch 716 408 .empty .empty)) (.branch 719 410 (.branch 718 410 .empty .empty) (.branch 720 411 .empty .empty))) (.branch 726 414 (.branch 724 412 (.branch 723 412 (.branch 722 411 .empty .empty) .empty) (.branch 725 413 .empty .empty)) (.branch 728 415 (.branch 727 415 .empty .empty) (.branch 729 416 .empty .empty))))))) (.branch 803 458 (.branch 767 438 (.branch 749 427 (.branch 740 422 (.branch 735 419 (.branch 733 418 (.branch 732 418 (.branch 731 417 .empty .empty) .empty) (.branch 734 418 .empty .empty)) (.branch 738 421 (.branch 737 421 (.branch 736 420 .empty .empty) .empty) (.branch 739 422 .empty .empty))) (.branch 745 424 (.branch 743 424 (.branch 742 423 (.branch 741 422 .empty .empty) .empty) (.branch 744 424 .empty .empty)) (.branch 747 425 (.branch 746 425 .empty .empty) (.branch 748 426 .empty .empty)))) (.branch 758 433 (.branch 754 430 (.branch 752 428 (.branch 751 428 (.branch 750 428 .empty .empty) .empty) (.branch 753 429 .empty .empty)) (.branch 756 431 (.branch 755 431 .empty .empty) (.branch 757 432 .empty .empty))) (.branch 763 435 (.branch 761 434 (.branch 760 434 (.branch 759 433 .empty .empty) .empty) (.branch 762 434 .empty .empty)) (.branch 765 437 (.branch 764 436 .empty .empty) (.branch 766 437 .empty .empty))))) (.branch 785 447 (.branch 776 442 (.branch 772 440 (.branch 770 439 (.branch 769 438 (.branch 768 438 .empty .empty) .empty) (.branch 771 440 .empty .empty)) (.branch 774 441 (.branch 773 440 .empty .empty) (.branch 775 441 .empty .empty))) (.branch 781 446 (.branch 779 444 (.branch 778 444 (.branch 777 443 .empty .empty) .empty) (.branch 780 445 .empty .empty)) (.branch 783 447 (.branch 782 446 .empty .empty) (.branch 784 447 .empty .empty)))) (.branch 794 453 (.branch 790 450 (.branch 788 449 (.branch 787 449 (.branch 786 448 .empty .empty) .empty) (.branch 789 449 .empty .empty)) (.branch 792 451 (.branch 791 450 .empty .empty) (.branch 793 452 .empty .empty))) (.branch 799 455 (.branch 797 454 (.branch 796 454 (.branch 795 453 .empty .empty) .empty) (.branch 798 454 .empty .empty)) (.branch 801 456 (.branch 800 455 .empty .empty) (.branch 802 457 .empty .empty)))))) (.branch 840 479 (.branch 822 468 (.branch 813 464 (.branch 808 461 (.branch 806 459 (.branch 805 458 (.branch 804 458 .empty .empty) .empty) (.branch 807 460 .empty .empty)) (.branch 811 463 (.branch 810 462 (.branch 809 461 .empty .empty) .empty) (.branch 812 463 .empty .empty))) (.branch 818 466 (.branch 816 465 (.branch 815 464 (.branch 814 464 .empty .empty) .empty) (.branch 817 466 .empty .empty)) (.branch 820 467 (.branch 819 466 .empty .empty) (.branch 821 467 .empty .empty)))) (.branch 831 474 (.branch 827 471 (.branch 825 470 (.branch 824 470 (.branch 823 469 .empty .empty) .empty) (.branch 826 470 .empty .empty)) (.branch 829 473 (.branch 828 472 .empty .empty) (.branch 830 473 .empty .empty))) (.branch 836 476 (.branch 834 476 (.branch 833 475 (.branch 832 475 .empty .empty) .empty) (.branch 835 476 .empty .empty)) (.branch 838 477 (.branch 837 477 .empty .empty) (.branch 839 478 .empty .empty))))) (.branch 858 489 (.branch 849 484 (.branch 845 482 (.branch 843 481 (.branch 842 480 (.branch 841 480 .empty .empty) .empty) (.branch 844 482 .empty .empty)) (.branch 847 483 (.branch 846 483 .empty .empty) (.branch 848 483 .empty .empty))) (.branch 854 487 (.branch 852 486 (.branch 851 486 (.branch 850 485 .empty .empty) .empty) (.branch 853 487 .empty .empty)) (.branch 856 488 (.branch 855 487 .empty .empty) (.branch 857 489 .empty .empty)))) (.branch 867 494 (.branch 863 492 (.branch 861 490 (.branch 860 490 (.branch 859 489 .empty .empty) .empty) (.branch 862 491 .empty .empty)) (.branch 865 493 (.branch 864 493 .empty .empty) (.branch 866 493 .empty .empty))) (.branch 872 498 (.branch 870 496 (.branch 869 496 (.branch 868 495 .empty .empty) .empty) (.branch 871 497 .empty .empty)) (.branch 874 499 (.branch 873 498 .empty .empty) (.branch 875 499 .empty .empty)))))))) (.branch 1022 582 (.branch 949 541 (.branch 913 520 (.branch 895 511 (.branch 886 505 (.branch 881 503 (.branch 879 502 (.branch 878 501 (.branch 877 500 .empty .empty) .empty) (.branch 880 502 .empty .empty)) (.branch 884 504 (.branch 883 503 (.branch 882 503 .empty .empty) .empty) (.branch 885 505 .empty .empty))) (.branch 891 508 (.branch 889 506 (.branch 888 506 (.branch 887 505 .empty .empty) .empty) (.branch 890 507 .empty .empty)) (.branch 893 509 (.branch 892 509 .empty .empty) (.branch 894 510 .empty .empty)))) (.branch 904 515 (.branch 900 513 (.branch 898 512 (.branch 897 512 (.branch 896 511 .empty .empty) .empty) (.branch 899 512 .empty .empty)) (.branch 902 514 (.branch 901 514 .empty .empty) (.branch 903 514 .empty .empty))) (.branch 909 518 (.branch 907 517 (.branch 906 516 (.branch 905 515 .empty .empty) .empty) (.branch 908 518 .empty .empty)) (.branch 911 519 (.branch 910 519 .empty .empty) (.branch 912 519 .empty .empty))))) (.branch 931 530 (.branch 922 526 (.branch 918 523 (.branch 916 522 (.branch 915 521 (.branch 914 520 .empty .empty) .empty) (.branch 917 523 .empty .empty)) (.branch 920 524 (.branch 919 523 .empty .empty) (.branch 921 525 .empty .empty))) (.branch 927 529 (.branch 925 528 (.branch 924 527 (.branch 923 526 .empty .empty) .empty) (.branch 926 528 .empty .empty)) (.branch 929 529 (.branch 928 529 .empty .empty) (.branch 930 530 .empty .empty)))) (.branch 940 536 (.branch 936 534 (.branch 934 533 (.branch 933 532 (.branch 932 531 .empty .empty) .empty) (.branch 935 533 .empty .empty)) (.branch 938 535 (.branch 937 535 .empty .empty) (.branch 939 536 .empty .empty))) (.branch 945 539 (.branch 943 538 (.branch 942 537 (.branch 941 536 .empty .empty) .empty) (.branch 944 539 .empty .empty)) (.branch 947 540 (.branch 946 540 .empty .empty) (.branch 948 540 .empty .empty)))))) (.branch 986 562 (.branch 968 551 (.branch 959 547 (.branch 954 543 (.branch 952 542 (.branch 951 542 (.branch 950 542 .empty .empty) .empty) (.branch 953 543 .empty .empty)) (.branch 957 546 (.branch 956 545 (.branch 955 544 .empty .empty) .empty) (.branch 958 546 .empty .empty))) (.branch 964 549 (.branch 962 549 (.branch 961 548 (.branch 960 548 .empty .empty) .empty) (.branch 963 549 .empty .empty)) (.branch 966 551 (.branch 965 550 .empty .empty) (.branch 967 551 .empty .empty)))) (.branch 977 556 (.branch 973 555 (.branch 971 553 (.branch 970 552 (.branch 969 552 .empty .empty) .empty) (.branch 972 554 .empty .empty)) (.branch 975 556 (.branch 974 555 .empty .empty) (.branch 976 556 .empty .empty))) (.branch 982 560 (.branch 980 558 (.branch 979 557 (.branch 978 557 .empty .empty) .empty) (.branch 981 559 .empty .empty)) (.branch 984 560 (.branch 983 560 .empty .empty) (.branch 985 561 .empty .empty))))) (.branch 1004 572 (.branch 995 567 (.branch 991 565 (.branch 989 564 (.branch 988 563 (.branch 987 563 .empty .empty) .empty) (.branch 990 565 .empty .empty)) (.branch 993 566 (.branch 992 566 .empty .empty) (.branch 994 566 .empty .empty))) (.branch 1000 570 (.branch 998 569 (.branch 997 569 (.branch 996 568 .empty .empty) .empty) (.branch 999 570 .empty .empty)) (.branch 1002 571 (.branch 1001 570 .empty .empty) (.branch 1003 572 .empty .empty)))) (.branch 1013 577 (.branch 1009 575 (.branch 1007 573 (.branch 1006 573 (.branch 1005 572 .empty .empty) .empty) (.branch 1008 574 .empty .empty)) (.branch 1011 576 (.branch 1010 576 .empty .empty) (.branch 1012 577 .empty .empty))) (.branch 1018 580 (.branch 1016 578 (.branch 1015 578 (.branch 1014 577 .empty .empty) .empty) (.branch 1017 579 .empty .empty)) (.branch 1020 581 (.branch 1019 581 .empty .empty) (.branch 1021 581 .empty .empty))))))) (.branch 1095 625 (.branch 1059 604 (.branch 1041 593 (.branch 1032 588 (.branch 1027 586 (.branch 1025 584 (.branch 1024 584 (.branch 1023 583 .empty .empty) .empty) (.branch 1026 585 .empty .empty)) (.branch 1030 587 (.branch 1029 587 (.branch 1028 586 .empty .empty) .empty) (.branch 1031 587 .empty .empty))) (.branch 1037 590 (.branch 1035 589 (.branch 1034 589 (.branch 1033 589 .empty .empty) .empty) (.branch 1036 590 .empty .empty)) (.branch 1039 592 (.branch 1038 591 .empty .empty) (.branch 1040 593 .empty .empty)))) (.branch 1050 599 (.branch 1046 596 (.branch 1044 595 (.branch 1043 594 (.branch 1042 593 .empty .empty) .empty) (.branch 1045 596 .empty .empty)) (.branch 1048 598 (.branch 1047 597 .empty .empty) (.branch 1049 598 .empty .empty))) (.branch 1055 601 (.branch 1053 600 (.branch 1052 599 (.branch 1051 599 .empty .empty) .empty) (.branch 1054 600 .empty .empty)) (.branch 1057 603 (.branch 1056 602 .empty .empty) (.branch 1058 603 .empty .empty))))) (.branch 1077 613 (.branch 1068 609 (.branch 1064 606 (.branch 1062 606 (.branch 1061 605 (.branch 1060 605 .empty .empty) .empty) (.branch 1063 606 .empty .empty)) (.branch 1066 608 (.branch 1065 607 .empty .empty) (.branch 1067 609 .empty .empty))) (.branch 1073 612 (.branch 1071 610 (.branch 1070 610 (.branch 1069 610 .empty .empty) .empty) (.branch 1072 611 .empty .empty)) (.branch 1075 612 (.branch 1074 612 .empty .empty) (.branch 1076 613 .empty .empty)))) (.branch 1086 619 (.branch 1082 616 (.branch 1080 616 (.branch 1079 615 (.branch 1078 614 .empty .empty) .empty) (.branch 1081 616 .empty .empty)) (.branch 1084 618 (.branch 1083 617 .empty .empty) (.branch 1085 619 .empty .empty))) (.branch 1091 622 (.branch 1089 621 (.branch 1088 621 (.branch 1087 620 .empty .empty) .empty) (.branch 1090 622 .empty .empty)) (.branch 1093 623 (.branch 1092 622 .empty .empty) (.branch 1094 624 .empty .empty)))))) (.branch 1132 645 (.branch 1114 635 (.branch 1105 629 (.branch 1100 627 (.branch 1098 626 (.branch 1097 626 (.branch 1096 625 .empty .empty) .empty) (.branch 1099 626 .empty .empty)) (.branch 1103 628 (.branch 1102 628 (.branch 1101 628 .empty .empty) .empty) (.branch 1104 629 .empty .empty))) (.branch 1110 633 (.branch 1108 632 (.branch 1107 631 (.branch 1106 630 .empty .empty) .empty) (.branch 1109 632 .empty .empty)) (.branch 1112 634 (.branch 1111 634 .empty .empty) (.branch 1113 635 .empty .empty)))) (.branch 1123 640 (.branch 1119 637 (.branch 1117 637 (.branch 1116 636 (.branch 1115 635 .empty .empty) .empty) (.branch 1118 637 .empty .empty)) (.branch 1121 638 (.branch 1120 638 .empty .empty) (.branch 1122 639 .empty .empty))) (.branch 1128 642 (.branch 1126 642 (.branch 1125 641 (.branch 1124 641 .empty .empty) .empty) (.branch 1127 642 .empty .empty)) (.branch 1130 643 (.branch 1129 643 .empty .empty) (.branch 1131 644 .empty .empty))))) (.branch 1150 656 (.branch 1141 651 (.branch 1137 648 (.branch 1135 646 (.branch 1134 646 (.branch 1133 646 .empty .empty) .empty) (.branch 1136 647 .empty .empty)) (.branch 1139 649 (.branch 1138 649 .empty .empty) (.branch 1140 650 .empty .empty))) (.branch 1146 653 (.branch 1144 652 (.branch 1143 652 (.branch 1142 651 .empty .empty) .empty) (.branch 1145 652 .empty .empty)) (.branch 1148 655 (.branch 1147 654 .empty .empty) (.branch 1149 655 .empty .empty)))) (.branch 1159 660 (.branch 1155 658 (.branch 1153 657 (.branch 1152 656 (.branch 1151 656 .empty .empty) .empty) (.branch 1154 658 .empty .empty)) (.branch 1157 659 (.branch 1156 658 .empty .empty) (.branch 1158 659 .empty .empty))) (.branch 1164 663 (.branch 1162 662 (.branch 1161 662 (.branch 1160 661 .empty .empty) .empty) (.branch 1163 663 .empty .empty)) (.branch 1166 664 (.branch 1165 663 .empty .empty) (.branch 1167 664 .empty .empty))))))))))

set_option maxHeartbeats 4000000 in
/-- At `n = 1167`, the literal recurrence is 664 but the asserted floor is 665. -/
theorem result : ¬ claim := by
  have hchecked : prefixChecks certificate 1167 = true := by decide +kernel
  have ha : a 1167 = 664 := by
    calc
      a 1167 = certificate.value 1167 :=
        prefixChecks_sound certificate 1167 hchecked 1167 (by omega)
      _ = 664 := by decide +kernel
  have hc : 0 < c /\ P c = 0 := by
    simpa only [c, P] using (Classical.choose_spec cubic_positiveRoot_existsUnique).1
  have hPlow : P ((665 : ℝ) / 1167) < 0 := by norm_num [P]
  have hPupper : 0 < P ((666 : ℝ) / 1167) := by norm_num [P]
  have hlower : (665 : ℝ) / 1167 < c := by
    apply (P_strictMono.lt_iff_lt).mp
    rw [hc.2]
    exact hPlow
  have hupper : c < (666 : ℝ) / 1167 := by
    apply (P_strictMono.lt_iff_lt).mp
    rw [hc.2]
    exact hPupper
  have hscaled : (665 : ℝ) < c * 1167 /\ c * 1167 < 666 := by
    constructor <;> nlinarith
  have hfloor : ⌊c * (1167 : ℕ)⌋ = (665 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num
    exact ⟨hscaled.1.le, hscaled.2⟩
  intro hclaim
  obtain ⟨j, hj, heq⟩ := hclaim.2 1167 (by omega)
  rw [ha, hfloor] at heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  omega

#print axioms a
#print axioms a_succ
#print axioms cubic_positiveRoot_existsUnique
#print axioms c
#print axioms claim
#print axioms result

end D5.S1.Recurrence.Invariants.CloitreNestedRecurrenceFloorRefutation
