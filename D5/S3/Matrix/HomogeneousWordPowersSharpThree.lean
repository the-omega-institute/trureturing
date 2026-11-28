/- GID: D5/S3/Matrix/HomogeneousWordPowersSharpThree
   generality: G
   mirror-B: none(waiver:covered-by-shitov-size-three-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp exact word length in size three. -/

import D5.S3.Matrix.HomogeneousWordPowersInvertible
import D5.S3.Matrix.HomogeneousWordPowersCompression
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

/-! Omega original.

The sharp exact word length in size three. The lower witness is the size-three
case of Yi Yu's Theorem 1.2 (https://zenodo.org/records/24562446). -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

/-- A size-three matrix subspace with a positive full power has full seventh power. -/
theorem pow_seven_eq_top [Infinite K] [NeZero (2 : K)]
    (L : Submodule K Mat) (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    L ^ 7 = ⊤ := by
  by_cases hsing : ∀ A ∈ L, A.det = 0
  · exact all_singular_pow_seven_eq_top L hfull hsing
  · push Not at hsing
    obtain ⟨A, hA, hdet⟩ := hsing
    obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet)
    exact invertible_pow_seven_eq_top L U hA hfull

private def yuLetter (R : Type*) [Zero R] [One R] : Bool → Matrix (Fin 3) (Fin 3) R
  | false => !![0, 0, 1; 1, 0, 1; 0, 0, 0]
  | true => !![0, 0, 0; 0, 0, 0; 0, 1, 0]

private def yuWord (R : Type*) [Semiring R] {n : ℕ} (w : Fin n → Bool) :
    Matrix (Fin 3) (Fin 3) R :=
  (List.ofFn (yuLetter R ∘ w)).prod

private theorem yuWord_cast {n : ℕ} (w : Fin n → Bool) :
    (Int.castRingHom K).mapMatrix (yuWord ℤ w) = yuWord K w := by
  unfold yuWord
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  change (Int.castRingHom K).mapMatrix (yuLetter ℤ (w i)) = yuLetter K (w i)
  cases w i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [yuLetter, RingHom.mapMatrix_apply]

private def yuFunctional (R : Type*) [Ring R] (X : Matrix (Fin 3) (Fin 3) R) : R :=
  X 0 0 - X 0 2 - X 1 0 + X 1 2

set_option maxRecDepth 4096 in
private theorem yu_six_integer :
    ∀ w : Fin 6 → Bool, yuFunctional ℤ (yuWord ℤ w) = 0 := by
  decide +kernel

private def yuColumns (R : Type*) [Zero R] [One R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 0, 1, 1; 1, 0, 0]

private def yuRows (R : Type*) [Zero R] [One R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 1, 0, 1; 0, 0, 1]

-- The (i,j) word gives A^i B A^j, padded by the identities BAB = B and BA²B = B.
private def yuSpanningWord : Fin 3 → Fin 3 → Fin 7 → Bool :=
  ![
    ![![true, false, false, true, false, false, true],
      ![true, false, true, false, false, true, false],
      ![true, false, true, false, true, false, false]],
    ![![false, true, false, true, false, false, true],
      ![false, true, false, true, false, true, false],
      ![false, true, false, false, true, false, false]],
    ![![false, false, true, false, true, false, true],
      ![false, false, true, false, false, true, false],
      ![false, false, true, false, true, false, false]]
  ]

set_option maxRecDepth 4096 in
private theorem yu_seven_integer (i j : Fin 3) :
    yuWord ℤ (yuSpanningWord i j) = yuColumns ℤ * Matrix.single i j (1 : ℤ) * yuRows ℤ := by
  have h : ∀ p : Fin 4 → Fin 3, yuWord ℤ (yuSpanningWord (p 0) (p 1)) (p 2) (p 3) =
      (yuColumns ℤ * Matrix.single (p 0) (p 1) (1 : ℤ) * yuRows ℤ :
        Matrix (Fin 3) (Fin 3) ℤ) (p 2) (p 3) := by
    decide +kernel
  exact Matrix.ext fun a b => h ![i, j, a, b]

/-- Yu's size-three pair has proper exact sixth span and full exact seventh span. -/
theorem yu_word_span_three :
    let A : Mat := !![0, 0, 1; 1, 0, 1; 0, 0, 0]
    let B : Mat := !![0, 0, 0; 0, 0, 0; 0, 1, 0]
    let S : Set Mat := {A, B}
    Submodule.span K (S ^ 6) ≠ ⊤ ∧ Submodule.span K (S ^ 7) = ⊤ := by
  classical
  let S := Set.range (yuLetter K)
  have hS : S = ({yuLetter K false, yuLetter K true} : Set Mat) := by
    ext X
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  change Submodule.span K (({yuLetter K false, yuLetter K true} : Set Mat) ^ 6) ≠ ⊤ ∧
    Submodule.span K (({yuLetter K false, yuLetter K true} : Set Mat) ^ 7) = ⊤
  rw [← hS]
  constructor
  · let entry (i j : Fin 3) : Mat →ₗ[K] K := Matrix.entryLinearMap K K i j
    let p := entry 0 0 - entry 0 2 - entry 1 0 + entry 1 2
    have hle : Submodule.span K (S ^ 6) ≤ p.ker := by
      apply Submodule.span_le.2
      intro X hX
      obtain ⟨f, rfl⟩ := Set.mem_pow.1 hX
      choose w hw using fun i => (f i).property
      have he : (List.ofFn fun i ↦ (f i : Mat)).prod = yuWord K w := by
        unfold yuWord
        simp only [Function.comp_def, hw]
      rw [he, ← yuWord_cast]
      change yuFunctional K ((Int.castRingHom K).mapMatrix (yuWord ℤ w)) = 0
      have h := congrArg (Int.castRingHom K) (yu_six_integer w)
      simpa only [yuFunctional, RingHom.mapMatrix_apply, Matrix.map_apply,
        map_add, map_sub, map_zero] using h
    intro htop
    rw [htop] at hle
    have hh : (Matrix.single 1 2 1 : Mat) ∈ p.ker := hle Submodule.mem_top
    change yuFunctional K (Matrix.single 1 2 1) = 0 at hh
    simp [yuFunctional, Matrix.single_apply] at hh
  · have hU : IsUnit (yuColumns K) := by
      apply (Matrix.isUnit_iff_isUnit_det _).2
      rw [isUnit_iff_ne_zero]
      simp [yuColumns, Matrix.det_fin_three]
    have hV : IsUnit (yuRows K) := by
      apply (Matrix.isUnit_iff_isUnit_det _).2
      rw [isUnit_iff_ne_zero]
      simp [yuRows, Matrix.det_fin_three]
    obtain ⟨U, hU⟩ := hU
    obtain ⟨V, hV⟩ := hV
    let e := (U.mulLeftLinearEquiv K Mat).trans (V.mulRightLinearEquiv K)
    let basis := (Matrix.stdBasis K (Fin 3) (Fin 3)).map e
    apply top_unique
    rw [← basis.span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply Submodule.subset_span
    apply Set.mem_pow.2
    let w := yuSpanningWord i j
    refine ⟨fun k => ⟨yuLetter K (w k), ⟨w k, rfl⟩⟩, ?_⟩
    change yuWord K w = e (Matrix.stdBasis K (Fin 3) (Fin 3) (i, j))
    rw [← yuWord_cast, yu_seven_integer, map_mul, map_mul, Matrix.stdBasis_eq_single]
    change _ = (U : Mat) * Matrix.single i j 1 * (V : Mat)
    rw [hU, hV]
    congr 1
    · congr 1
      · ext a b
        fin_cases a <;> fin_cases b <;> simp [yuColumns, RingHom.mapMatrix_apply]
      · ext a b
        by_cases ha : a = i <;> by_cases hb : b = j <;>
          simp [Matrix.single_apply, RingHom.mapMatrix_apply, ha, hb]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [yuRows, RingHom.mapMatrix_apply]

/-- Seven is the least positive universal length for exact words in size three.
In particular this gives `w(3) = 7` in Shitov's Question 2 over the complex field. -/
theorem isLeast_full_word_length_three [Infinite K] [NeZero (2 : K)] :
    IsLeast {k : ℕ | 0 < k ∧ ∀ S : Set Mat,
        (∃ m : ℕ, 0 < m ∧ Submodule.span K (S ^ m) = ⊤) →
        Submodule.span K (S ^ k) = ⊤} 7 := by
  constructor
  · refine ⟨by decide, fun S hfull => ?_⟩
    simp_rw [← Submodule.span_pow] at hfull ⊢
    exact pow_seven_eq_top (Submodule.span K S) hfull
  · intro k hk
    by_contra! hlt
    obtain ⟨hk, hall⟩ := hk
    obtain ⟨hsix, hseven⟩ := yu_word_span_three (K := K)
    have hpower := hall _ ⟨7, by decide, hseven⟩
    rw [← Submodule.span_pow] at hsix hpower
    exact hsix (pow_eq_top_of_le _ hk hpower (by omega))

end OmegaMath.HomogeneousWordPowers
