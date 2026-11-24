/- GID: D5/S3/Quantum/Analysis/RefinedBMV67
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV67
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hägele's refined BMV lower bounds with six and seven copies of the first factor. -/

import D5.S3.Quantum.Analysis.RefinedBMV54
import Mathlib.Algebra.Star.Rat
import Mathlib.Data.Rat.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Weighted Gram certificates for the balanced fourth traces at degrees six and seven

The data are those of equations (15)–(25) in the supplied certificate. The
coefficient check keeps rotations as the equivalence relation, so the identities
are equalities of complex traces for Hermitian inputs. The positivity proof
allows singular weights. The integer-balanced bounds feed into the separate
comparison with the fractional fourth trace.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV

open private evalWord_append43 from D5.S3.Quantum.Analysis.RefinedBMV43
open private evalWord_reverse from D5.S3.Quantum.Analysis.RefinedBMV44
open private Algebra54.rotations from D5.S3.Quantum.Analysis.RefinedBMV54

namespace WeightedGram67

local notation "𝔞" => true
local notation "𝔟" => false

private abbrev Word := List Bool
private abbrev Terms := List (ℚ × Word)

private def cyclicRep (w : Word) : Word :=
  (Algebra54.rotations w).min?.getD w

private def addTerm (u : ℚ × Word) : Terms → Terms
  | [] => [u]
  | t :: ts =>
      if t.2 = u.2 then (u.1 + t.1, t.2) :: ts else t :: addTerm u ts

private def coefficients : Terms → Terms
  | [] => []
  | t :: ts => addTerm (t.1, cyclicRep t.2) (coefficients ts)

private def scaleTerms {α : Type*} (c : ℚ) (p : List (ℚ × α)) : List (ℚ × α) :=
  p.map fun t => (c * t.1, t.2)

private def pairTerms (l r : Word) (p q : Terms) : Terms :=
  p.flatMap fun u => q.map fun v => (u.1 * v.1, u.2.reverse ++ l ++ v.2 ++ r)

private def gramTerms {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ)
    (l r : Word) (P : Fin k → Terms) : Terms :=
  (List.finRange k).flatMap fun i =>
    (List.finRange k).flatMap fun j => scaleTerms (G i j) (pairTerms l r (P i) (P j))

private def v : Fin 10 → Word :=
  ![[𝔟, 𝔟, 𝔞, 𝔞, 𝔞], [𝔟, 𝔞, 𝔟, 𝔞, 𝔞], [𝔟, 𝔞, 𝔞, 𝔟, 𝔞], [𝔟, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔟, 𝔟, 𝔞, 𝔞], [𝔞, 𝔟, 𝔞, 𝔟, 𝔞], [𝔞, 𝔟, 𝔞, 𝔞, 𝔟], [𝔞, 𝔞, 𝔟, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔟], [𝔞, 𝔞, 𝔞, 𝔟, 𝔟]]

private def P : Fin 7 → Terms :=
  ![[(1, v 0), (1, v 1), (-1, v 8), (-1, v 9)],
    [(1, v 2), (-1/2, v 8), (-1/2, v 9)],
    [(1, v 3), (-1/2, v 8), (-1/2, v 9)],
    [(1, v 4), (-1/2, v 8), (-1/2, v 9)],
    [(1, v 5), (-1/2, v 8), (-1/2, v 9)],
    [(1, v 6), (-1/2, v 8), (-1/2, v 9)],
    [(1, v 7), (-1/2, v 8), (-1/2, v 9)]]

private def w : Fin 6 → Word :=
  ![[𝔟, 𝔟, 𝔞, 𝔞], [𝔟, 𝔞, 𝔟, 𝔞], [𝔟, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔟, 𝔟, 𝔞], [𝔞, 𝔟, 𝔞, 𝔟], [𝔞, 𝔞, 𝔟, 𝔟]]

private def Q (i : Fin 5) : Terms := [(1, w i.castSucc), (-1, w 5)]

private def u : Fin 4 → Word :=
  ![[𝔟, 𝔞, 𝔞, 𝔞], [𝔞, 𝔟, 𝔞, 𝔞], [𝔞, 𝔞, 𝔟, 𝔞], [𝔞, 𝔞, 𝔞, 𝔟]]

private def R (i : Fin 3) : Terms := [(1, u i.castSucc), (-1, u 3)]

private def G₀ : Matrix (Fin 7) (Fin 7) ℚ :=
  !![4, 4, -2, -2, -4, -2, -4;
     4, 52, 9, 6, -47, -5, -19;
     -2, 9, 18, 0, -28, 9, 0;
     -2, 6, 0, 16, 12, -19, -3;
     -4, -47, -28, 12, 114, -47, 12;
     -2, -5, 9, -19, -47, 52, 6;
     -4, -19, 0, -3, 12, 6, 16]

private def G₁ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![4, 5, 0, -1, -6;
     5, 20, -2, 1, -18;
     0, -2, 9, -5, -2;
     -1, 1, -5, 5, 1;
     -6, -18, -2, 1, 20]

private def G₂ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4, 1, -2;
     1, 55, -54;
     -2, -54, 55]

private def H : Matrix (Fin 7) (Fin 7) ℚ :=
  !![4, 8, 0, 0, -7, -5, -2;
     8, 154, -29, 33, -72, -58, -24;
     0, -29, 38, -17, -10, 10, 0;
     0, 33, -17, 22, -14, -10, -6;
     -7, -72, -10, -14, 78, 16, 16;
     -5, -58, 10, -10, 16, 38, 6;
     -2, -24, 0, -6, 16, 6, 12]

private def comparator6 : Word := [𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟]
private def comparator7 : Word := [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟]

private def gapTerms (p : ℕ) (c : ℚ) (target : Word) : Terms :=
  scaleTerms (1 / ((p + 4 : ℕ) : ℚ)) ((balancedWords p 4).map fun w => (1, w)) ++
    [(-c, target)]

private def certificate6 : Terms :=
  scaleTerms (1/8) (gramTerms G₀ [] [] P) ++
    scaleTerms (1/4) (gramTerms G₁ [𝔞] [𝔞] Q) ++
    scaleTerms (1/4) (gramTerms G₂ [𝔟] [𝔟] R)

private def certificate7 : Terms :=
  scaleTerms (1/4) (gramTerms H [𝔞] [] P)

private def coefficientsVanish (p : Terms) : Bool :=
  (coefficients p).all fun t => decide (t.1 = 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem coefficients6 :
    coefficientsVanish (gapTerms 6 21 comparator6 ++ scaleTerms (-1) certificate6) = true := by
  simp only [gapTerms, balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem coefficients7 :
    coefficientsVanish (gapTerms 7 30 comparator7 ++ scaleTerms (-1) certificate7) = true := by
  simp only [gapTerms, balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

noncomputable section

private def weightedSum {α M : Type*} [AddCommMonoid M] [Module ℂ M] (f : α → M) :
    List (ℚ × α) → M
  | [] => 0
  | t :: ts => (t.1 : ℂ) • f t.2 + weightedSum f ts

private theorem weightedSum_eq_map {α M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : α → M) (p : List (ℚ × α)) :
    weightedSum f p = (p.map fun t => (t.1 : ℂ) • f t.2).sum := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp only [weightedSum, List.map_cons, List.sum_cons, ih]

private theorem weightedSum_append {α M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : α → M) (p q : List (ℚ × α)) :
    weightedSum f (p ++ q) = weightedSum f p + weightedSum f q := by
  simp only [weightedSum_eq_map, List.map_append, List.sum_append]

private theorem weightedSum_scale {α M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : α → M) (c : ℚ) (p : List (ℚ × α)) :
    weightedSum f (scaleTerms c p) = (c : ℂ) • weightedSum f p := by
  induction p with
  | nil => simp [scaleTerms, weightedSum]
  | cons t ts ih =>
    change (↑(c * t.1) : ℂ) • f t.2 + weightedSum f (scaleTerms c ts) =
      (c : ℂ) • ((t.1 : ℂ) • f t.2 + weightedSum f ts)
    rw [ih, Rat.cast_mul, mul_smul, smul_add]

private theorem weightedSum_flatMap {α β M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : β → M) (xs : List α) (terms : α → List (ℚ × β)) :
    weightedSum f (xs.flatMap terms) = (xs.map fun x => weightedSum f (terms x)).sum := by
  simp only [weightedSum_eq_map, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]

private theorem weightedSum_addTerm (f : Word → ℂ) (u : ℚ × Word) (p : Terms) :
    weightedSum f (addTerm u p) = (u.1 : ℂ) • f u.2 + weightedSum f p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2 = u.2
    · rw [addTerm, ite_eq_left h]
      simp only [weightedSum, Rat.cast_add, add_smul, h, add_assoc]
    · simp only [addTerm, if_neg h, weightedSum, ih]
      exact add_left_comm _ _ _

private theorem coefficients_sound (f : Word → ℂ) (hf : ∀ w, f (cyclicRep w) = f w)
    (p : Terms) (h : coefficientsVanish p = true) : weightedSum f p = 0 := by
  have heval : weightedSum f (coefficients p) = weightedSum f p := by
    clear h
    induction p with
    | nil => rfl
    | cons t ts ih =>
      simp only [coefficients, weightedSum_addTerm, hf, ih, weightedSum]
  rw [← heval]
  have hz : ∀ t ∈ coefficients p, t.1 = 0 := fun t ht =>
    of_decide_eq_true (List.all_eq_true.mp h t ht)
  generalize coefficients p = terms at hz ⊢
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [weightedSum, hz t (List.mem_cons_self), Rat.cast_zero, zero_smul, zero_add]
    exact ih fun s hs => hz s (List.mem_cons_of_mem t hs)

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

private def traceWord (A B : Mat) (w : Word) : ℂ := trace (evalWord A B w)

private theorem traceWord_cyclicRep (A B : Mat) (w : Word) :
    traceWord A B (cyclicRep w) = traceWord A B w := by
  unfold cyclicRep
  cases h : (Algebra54.rotations w).min? with
  | none => rfl
  | some z =>
    simp only [Option.getD_some]
    have hz := List.min?_mem h
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    exact evalWord_rotate_trace43 A B w k

/-- The polarized expansion used both for the word identity and for the LDL coordinates. -/
private theorem trace_weighted_pair {α : Type*} (f : α → Mat) (p q : List (ℚ × α))
    (L R : Mat) :
    trace ((weightedSum f p)ᴴ * L * weightedSum f q * R) =
      (p.map fun u => (q.map fun v =>
        (((u.1 * v.1 : ℚ)) : ℂ) * trace ((f u.2)ᴴ * L * f v.2 * R)).sum).sum := by
  have right (Z : Mat) (qs : List (ℚ × α)) :
      trace (Z * L * weightedSum f qs * R) =
        (qs.map fun v => (v.1 : ℂ) * trace (Z * L * f v.2 * R)).sum := by
    induction qs with
    | nil => simp [weightedSum]
    | cons v vs ih =>
      simp only [weightedSum, List.map_cons, List.sum_cons, mul_add, add_mul,
        Matrix.mul_smul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul, ih]
  induction p with
  | nil => simp [weightedSum]
  | cons u us ih =>
    have head : trace (((u.1 : ℂ) • f u.2)ᴴ * L * weightedSum f q * R) =
        (q.map fun v =>
          (((u.1 * v.1 : ℚ)) : ℂ) * trace ((f u.2)ᴴ * L * f v.2 * R)).sum := by
      simp only [conjTranspose_smul, star_ratCast, Matrix.smul_mul, trace_smul, smul_eq_mul]
      rw [right]
      simp only [← List.sum_map_mul_left, Rat.cast_mul, mul_assoc]
    simp only [weightedSum, List.map_cons, List.sum_cons, conjTranspose_add, add_mul,
      trace_add, head, ih]

private theorem eval_pairTerms (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (l r : Word) (p q : Terms) :
    weightedSum (traceWord A B) (pairTerms l r p q) =
      trace ((weightedSum (evalWord A B) p)ᴴ * evalWord A B l *
        weightedSum (evalWord A B) q * evalWord A B r) := by
  rw [trace_weighted_pair, pairTerms, weightedSum_flatMap]
  simp only [weightedSum_eq_map, List.map_map, Function.comp_def,
    smul_eq_mul, traceWord, evalWord_append43, evalWord_reverse A B hA hB, mul_assoc]

/-- The weighted trace pairing of a rational coefficient matrix and a word vector. -/
def weightedGram {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ) (Z : Fin k → Mat) (L R : Mat) : ℂ :=
  ∑ i, ∑ j, (G i j : ℂ) * trace ((Z i)ᴴ * L * Z j * R)

private theorem eval_gramTerms (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ) (l r : Word) (Z : Fin k → Terms) :
    weightedSum (traceWord A B) (gramTerms G l r Z) =
      weightedGram G (fun i => weightedSum (evalWord A B) (Z i))
        (evalWord A B l) (evalWord A B r) := by
  simp only [gramTerms, weightedSum_flatMap, weightedSum_scale, eval_pairTerms A B hA hB,
    smul_eq_mul, ← Fin.sum_univ_def, weightedGram]

private theorem trace_pair_nonneg (L R U : Mat) (hL : L.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (trace (Uᴴ * L * U * R)).re := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  rw [star_eq_conjTranspose] at hS
  rw [hS, ← mul_assoc (Uᴴ * L * U) Sᴴ S, trace_mul_cycle (Uᴴ * L * U) Sᴴ S]
  exact (Complex.le_def.mp
    ((hL.conjTranspose_mul_mul_same U).mul_mul_conjTranspose_same S).trace_nonneg).1

private theorem real_rat_mul (a : ℚ) (z : ℂ) : ((a : ℂ) * z).re = (a : ℝ) * z.re := by
  simp [Complex.mul_re]

private theorem weightedGram_nonneg_of_ldl {k : ℕ} (G : Matrix (Fin k) (Fin k) ℚ)
    (Z : Fin k → Mat) (L R : Mat) (hL : L.PosSemidef) (hR : R.PosSemidef)
    (d : Fin k → ℚ) (F : Matrix (Fin k) (Fin k) ℚ)
    (hd : ∀ t, 0 ≤ d t) (hG : ∀ i j, G i j = ∑ t, d t * (F i t * F j t)) :
    0 ≤ (weightedGram G Z L R).re := by
  let row (t : Fin k) := (List.finRange k).map fun i => (F i t, Z i)
  let U (t : Fin k) := weightedSum id (row t)
  have htrace (t : Fin k) : trace ((U t)ᴴ * L * U t * R) =
      ∑ i, ∑ j, (F i t : ℂ) * (F j t : ℂ) * trace ((Z i)ᴴ * L * Z j * R) := by
    dsimp only [U]
    rw [trace_weighted_pair]
    simp only [row, List.map_map, Function.comp_def, id_eq, Rat.cast_mul, ← Fin.sum_univ_def]
  have hdecomp : weightedGram G Z L R =
      ∑ t, (d t : ℂ) * trace ((U t)ᴴ * L * U t * R) := by
    simp only [weightedGram, hG, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul,
      htrace, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ t, ∑ j, (d t : ℂ) * ((F i t : ℂ) * (F j t : ℂ)) *
          trace ((Z i)ᴴ * L * Z j * R) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  change 0 ≤ Complex.reCLM (weightedGram G Z L R)
  rw [hdecomp, map_sum]
  apply Finset.sum_nonneg
  intro t _
  simp only [Complex.reCLM_apply, real_rat_mul]
  exact mul_nonneg (Rat.cast_nonneg.mpr (hd t)) (trace_pair_nonneg L R (U t) hL hR)

-- The rational LDL coordinates witness positivity of the supplied matrices.
private theorem G₀_nonneg (Z : Fin 7 → Mat) (L R : Mat)
    (hL : L.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (weightedGram G₀ Z L R).re := by
  let d : Fin 7 → ℚ := ![4, 48, 695 / 48, 9113 / 695, 21108 / 701, 1611667 / 274404, 10103868 / 1611667]
  let F : Matrix (Fin 7) (Fin 7) ℚ :=
    !![1, 0, 0, 0, 0, 0, 0;
       1, 1, 0, 0, 0, 0, 0;
       -1 / 2, 11 / 48, 1, 0, 0, 0, 0;
       -1 / 2, 1 / 6, -136 / 695, 1, 0, 0, 0;
       -1, -43 / 48, -967 / 695, 707 / 701, 1, 0, 0;
       -1 / 2, -1 / 16, 3 / 5, -12371 / 9113, -15175 / 21108, 1, 0;
       -1, -5 / 16, 69 / 695, -1542 / 9113, -841 / 21108, -459467 / 1611667, 1]
  exact weightedGram_nonneg_of_ldl G₀ Z L R hL hR d F
    (by intro t; fin_cases t <;> norm_num [d])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [G₀, d, F, Fin.sum_univ_succ])

private theorem G₁_nonneg (Z : Fin 5 → Mat) (L R : Mat)
    (hL : L.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (weightedGram G₁ Z L R).re := by
  let d : Fin 5 → ℚ := ![4, 55 / 4, 479 / 55, 898 / 479, 1177 / 898]
  let F : Matrix (Fin 5) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0;
       5 / 4, 1, 0, 0, 0;
       0, -8 / 55, 1, 0, 0;
       -1 / 4, 9 / 55, -257 / 479, 1, 0;
       -3 / 2, -42 / 55, -194 / 479, -323 / 898, 1]
  exact weightedGram_nonneg_of_ldl G₁ Z L R hL hR d F
    (by intro t; fin_cases t <;> norm_num [d])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [G₁, d, F, Fin.sum_univ_succ])

private theorem G₂_nonneg (Z : Fin 3 → Mat) (L R : Mat)
    (hL : L.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (weightedGram G₂ Z L R).re := by
  let d : Fin 3 → ℚ := ![4, 219 / 4, 377 / 219]
  let F : Matrix (Fin 3) (Fin 3) ℚ :=
    !![1, 0, 0;
       1 / 4, 1, 0;
       -1 / 2, -214 / 219, 1]
  exact weightedGram_nonneg_of_ldl G₂ Z L R hL hR d F
    (by intro t; fin_cases t <;> norm_num [d])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [G₂, d, F, Fin.sum_univ_succ])

private theorem H_nonneg (Z : Fin 7 → Mat) (L R : Mat)
    (hL : L.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (weightedGram H Z L R).re := by
  let d : Fin 7 → ℚ := ![4, 138, 4403 / 138, 48140 / 4403, 1025033 / 48140, 8257207 / 1025033, 45455976 / 8257207]
  let F : Matrix (Fin 7) (Fin 7) ℚ :=
    !![1, 0, 0, 0, 0, 0, 0;
       2, 1, 0, 0, 0, 0, 0;
       0, -29 / 138, 1, 0, 0, 0, 0;
       0, 11 / 46, -1389 / 4403, 1, 0, 0, 0;
       -7 / 4, -29 / 69, -3062 / 4403, -15697 / 24070, 1, 0, 0;
       -5 / 4, -8 / 23, -12 / 4403, 1597 / 12035, -579521 / 1025033, 1, 0;
       -1 / 2, -10 / 69, -580 / 4403, -5599 / 24070, -23454 / 1025033, -3491205 / 8257207, 1]
  exact weightedGram_nonneg_of_ldl H Z L R hL hR d F
    (by intro t; fin_cases t <;> norm_num [d])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [H, d, F, Fin.sum_univ_succ])

private abbrev evalVector (A B : Mat) {k : ℕ} (Z : Fin k → Terms) (i : Fin k) : Mat :=
  weightedSum (evalWord A B) (Z i)

/-- Sum of the complex traces of the ordered words with four copies of B. -/
def orderedTraceSum (A B : Mat) (p : ℕ) : ℂ :=
  ((balancedWords p 4).map (traceWord A B)).sum

private theorem eval_gapTerms (A B : Mat) (p : ℕ) (c : ℚ) (target : Word) :
    weightedSum (traceWord A B) (gapTerms p c target) =
      ((1 / ((p + 4 : ℕ) : ℚ) : ℚ) : ℂ) * orderedTraceSum A B p -
        (c : ℂ) * traceWord A B target := by
  rw [gapTerms, weightedSum_append, weightedSum_scale]
  simp only [weightedSum_eq_map, List.map_map, Function.comp_def, smul_eq_mul,
    Rat.cast_one, one_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Rat.cast_neg, neg_mul, sub_eq_add_neg, orderedTraceSum]

private theorem comparator6_eval (A B : Mat) :
    traceWord A B comparator6 = trace ((A ^ 2 * B * A * B) ^ 2) := by
  simp only [traceWord, comparator6, evalWord, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]

private theorem comparator7_eval (A B : Mat) :
    traceWord A B comparator7 = trace ((A ^ 2 * B) ^ 3 * (A * B)) := by
  simp only [traceWord, comparator7, evalWord, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]

/-- Equation (20) for complex traces. The third block has a B on each side. -/
private theorem trace_gap64 (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((1 / 10 : ℚ) : ℂ) * orderedTraceSum A B 6 -
      ((21 : ℚ) : ℂ) * trace ((A ^ 2 * B * A * B) ^ 2) =
        ((1 / 8 : ℚ) : ℂ) * weightedGram G₀ (evalVector A B P) 1 1 +
          (((1 / 4 : ℚ) : ℂ) * weightedGram G₁ (evalVector A B Q) A A +
            ((1 / 4 : ℚ) : ℂ) * weightedGram G₂ (evalVector A B R) B B) := by
  have checked := coefficients_sound (traceWord A B) (traceWord_cyclicRep A B) _ coefficients6
  apply eq_of_sub_eq_zero
  simp only [weightedSum_append, weightedSum_scale, eval_gapTerms, certificate6,
    eval_gramTerms A B hA hB, smul_eq_mul, Rat.cast_neg, Rat.cast_one, neg_one_mul,
    evalWord, mul_one, comparator6_eval, sub_eq_add_neg, evalVector] at checked ⊢
  norm_num at checked ⊢
  simpa only [add_assoc, evalVector] using checked

/-- Equation (24) for complex traces. -/
private theorem trace_gap74 (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((1 / 11 : ℚ) : ℂ) * orderedTraceSum A B 7 -
      ((30 : ℚ) : ℂ) * trace ((A ^ 2 * B) ^ 3 * (A * B)) =
        ((1 / 4 : ℚ) : ℂ) * weightedGram H (evalVector A B P) A 1 := by
  have checked := coefficients_sound (traceWord A B) (traceWord_cyclicRep A B) _ coefficients7
  apply eq_of_sub_eq_zero
  simp only [weightedSum_append, weightedSum_scale, eval_gapTerms, certificate7,
    eval_gramTerms A B hA hB, smul_eq_mul, Rat.cast_neg, Rat.cast_one, neg_one_mul,
    evalWord, mul_one, comparator7_eval, sub_eq_add_neg, evalVector] at checked ⊢
  norm_num at checked ⊢
  exact checked

private theorem orderedTraceSum_re (A B : Mat) (p : ℕ) :
    (orderedTraceSum A B p).re =
      ((balancedWords p 4).map fun w => (trace (evalWord A B w)).re).sum := by
  simpa only [orderedTraceSum, traceWord, List.map_map, Function.comp_def, Complex.reCLM_apply]
    using (map_list_sum Complex.reCLM ((balancedWords p 4).map (traceWord A B)))

/-- The integer-balanced bound at bidegree (6,4), including singular A and B. -/
theorem balanced_bound64 (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    210 * (trace ((A ^ 2 * B * A * B) ^ 2)).re ≤
      ((balancedWords 6 4).map fun w => (trace (evalWord A B w)).re).sum := by
  have h := congrArg Complex.re (trace_gap64 A B hA.isHermitian hB.isHermitian)
  simp only [Complex.sub_re, Complex.add_re, real_rat_mul, orderedTraceSum_re] at h
  norm_num at h
  have h₀ := G₀_nonneg (evalVector A B P) 1 1 Matrix.PosSemidef.one Matrix.PosSemidef.one
  have h₁ := G₁_nonneg (evalVector A B Q) A A hA hA
  have h₂ := G₂_nonneg (evalVector A B R) B B hB hB
  linarith only [h, h₀, h₁, h₂]

/-- The integer-balanced bound at bidegree (7,4) with Hermitian B. -/
theorem balanced_bound74 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    330 * (trace ((A ^ 2 * B) ^ 3 * (A * B))).re ≤
      ((balancedWords 7 4).map fun w => (trace (evalWord A B w)).re).sum := by
  have h := congrArg Complex.re (trace_gap74 A B hA.isHermitian hB)
  simp only [Complex.sub_re, real_rat_mul, orderedTraceSum_re] at h
  norm_num at h
  have hH := H_nonneg (evalVector A B P) A 1 hA Matrix.PosSemidef.one
  linarith only [h, hH]

end


end WeightedGram67
end RefinedBMV

open Matrix
open scoped MatrixOrder

noncomputable section

namespace RefinedBMV

open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower
open private re_trace_sq_le_gram44 square_gram_le_gram_square44
  from D5.S3.Quantum.Analysis.RefinedBMV44

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem fourth_trace_le_gram_square (M : Mat) :
    (trace (M ^ 4)).re ≤ (trace ((M * Mᴴ) ^ 2)).re := by
  have h := re_trace_sq_le_gram44 (M ^ 2)
  rw [← pow_mul] at h
  exact h.trans (square_gram_le_gram_square44 M)

/-- The alternating balanced word controls the fourth trace at first count six. -/
private theorem balanced6_of_root (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    (trace ((X ^ 6 * B) ^ 4)).re ≤ (trace ((X ^ 8 * B * X ^ 4 * B) ^ 2)).re := by
  let M := X ^ 4 * B * X ^ 2
  have ht : trace ((X ^ 6 * B) ^ 4) = trace (M ^ 4) := by
    calc
      _ = trace ((X ^ 2 * (X ^ 4 * B)) ^ 4) := congrArg trace (by noncomm_ring)
      _ = _ := trace_cycle_power _ _ _
  have hg : trace ((M * Mᴴ) ^ 2) = trace ((X ^ 8 * B * X ^ 4 * B) ^ 2) := by
    simp only [M, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X ^ 4 * B * X ^ 4 * B * X ^ 8 * B * X ^ 4 * B) * X ^ 4) :=
        congrArg trace (by noncomm_ring)
      _ = trace (X ^ 4 * (X ^ 4 * B * X ^ 4 * B * X ^ 8 * B * X ^ 4 * B)) :=
        trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  rw [ht, ← hg]
  exact fourth_trace_le_gram_square M

/-- The balanced word controls the fourth trace at first count seven. -/
private theorem balanced7_of_root (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    (trace ((X ^ 7 * B) ^ 4)).re ≤
      (trace (X ^ 4 * B * (X ^ 8 * B) ^ 3)).re := by
  let M := X ^ 3 * B * X ^ 4
  let Q := X ^ 2 * B * X ^ 8 * B * X ^ 4
  have ht : trace ((X ^ 7 * B) ^ 4) = trace (M ^ 4) := by
    calc
      _ = trace ((X ^ 4 * (X ^ 3 * B)) ^ 4) := congrArg trace (by noncomm_ring)
      _ = _ := trace_cycle_power _ _ _
  have hg : trace ((M * Mᴴ) ^ 2) = trace (Q ^ 2) := by
    simp only [M, Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace (X ^ 3 * (B * X ^ 8 * B * X ^ 6 * B * X ^ 8 * B * X ^ 3)) :=
        congrArg trace (by noncomm_ring)
      _ = trace ((B * X ^ 8 * B * X ^ 6 * B * X ^ 8 * B * X ^ 3) * X ^ 3) :=
        trace_mul_comm _ _
      _ = trace ((B * X ^ 8 * B * X ^ 6 * B * X ^ 8 * B * X ^ 4) * X ^ 2) :=
        congrArg trace (by noncomm_ring)
      _ = trace (X ^ 2 * (B * X ^ 8 * B * X ^ 6 * B * X ^ 8 * B * X ^ 4)) :=
        trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have hq : trace (Qᴴ * Q) = trace (X ^ 4 * B * (X ^ 8 * B) ^ 3) := by
    simp only [Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X ^ 4 * B * X ^ 8 * B) * (X ^ 4 * B * X ^ 8 * B * X ^ 4)) :=
        congrArg trace (by noncomm_ring)
      _ = trace ((X ^ 4 * B * X ^ 8 * B * X ^ 4) * (X ^ 4 * B * X ^ 8 * B)) :=
        trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  rw [ht, ← hq]
  have h := fourth_trace_le_gram_square M
  rw [hg] at h
  exact h.trans (re_trace_sq_le_gram44 Q)


end RefinedBMV

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV

open private trace_exp_sum_le_fourth
  from D5.S3.Quantum.Analysis.RefinedBMV44

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private def fourthWordTraceSum (p : ℕ) (A B : Mat) : ℝ :=
  ((balancedWords p 4).map fun w ↦ (trace (evalWord A B w)).re).sum

private theorem bound64_root (X B : Mat) (hX : X.PosSemidef) (hB : B.PosSemidef) :
    210 * (trace ((X ^ 6 * B) ^ 4)).re ≤ fourthWordTraceSum 6 (X ^ 4) B := by
  have h := balanced6_of_root X B hX.isHermitian hB.isHermitian
  have hg := WeightedGram67.balanced_bound64 (X ^ 4) B (hX.pow 4) hB
  rw [← pow_mul] at hg
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans hg

private theorem bound74_root (X B : Mat) (hX : X.PosSemidef) (hB : B.IsHermitian) :
    330 * (trace ((X ^ 7 * B) ^ 4)).re ≤ fourthWordTraceSum 7 (X ^ 4) B := by
  have h := balanced7_of_root X B hX.isHermitian hB
  rw [trace_mul_comm] at h
  have hg := WeightedGram67.balanced_bound74 (X ^ 4) B (hX.pow 4) hB
  rw [← pow_mul] at hg
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans hg

private theorem fourthRoot_rpow (A : Mat) (hA : A.PosSemidef) (p : ℕ) :
    (A ^ (1 / 4 : ℝ)) ^ p = A ^ ((p : ℝ) / 4) := by
  rw [← CFC.rpow_natCast _ _ (CFC.rpow_nonneg (a := A))]
  rw [CFC.rpow_rpow_of_exponent_nonneg A (1 / 4) p (by norm_num) (by positivity) hA.nonneg]
  congr 1
  ring

private theorem fourthRoot_four (A : Mat) (hA : A.PosSemidef) :
    (A ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = A := by
  rw [fourthRoot_rpow A hA, show (↑(4 : ℕ) : ℝ) / 4 = 1 by norm_num, CFC.rpow_one A hA.nonneg]

/-- The refined product lower bound with six copies of A and four copies of B. -/
theorem product_bound64 (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    210 * (trace (((A ^ (6 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 6 4).map fun w ↦ (trace (evalWord A B w)).re).sum := by
  have hX : 0 ≤ A ^ (1 / 4 : ℝ) := CFC.rpow_nonneg
  simpa only [fourthRoot_four A hA, fourthRoot_rpow A hA, Nat.cast_ofNat, fourthWordTraceSum]
    using bound64_root (A ^ (1 / 4 : ℝ)) B hX.posSemidef hB

/-- The refined product lower bound with seven copies of A and four copies of B. -/
theorem product_bound74 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    330 * (trace (((A ^ (7 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 7 4).map fun w ↦ (trace (evalWord A B w)).re).sum := by
  have hX : 0 ≤ A ^ (1 / 4 : ℝ) := CFC.rpow_nonneg
  simpa only [fourthRoot_four A hA, fourthRoot_rpow A hA, Nat.cast_ofNat, fourthWordTraceSum]
    using bound74_root (A ^ (1 / 4 : ℝ)) B hX.posSemidef hB

private theorem exponentialLowerOfRoot (p c : ℕ) (H K : Mat)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hprod : ∀ X B : Mat, X.PosSemidef → B.PosSemidef →
      (c : ℝ) * (trace ((X ^ p * B) ^ 4)).re ≤ fourthWordTraceSum p (X ^ 4) B) :
    (c : ℝ) * (trace (exp ((p : ℝ) • H + (4 : ℝ) • K))).re ≤
      fourthWordTraceSum p (exp H) (exp K) := by
  by_cases hn : n = 0
  · subst n
    simp [fourthWordTraceSum, trace_eq_zero_of_isEmpty]
  letI : NeZero n := ⟨hn⟩
  let T : Mat := (1 / 4 : ℝ) • H
  have hT : T.IsHermitian := hermitian_real_smul hH _
  have hpow (k : ℕ) : (exp T) ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h4 : (exp T) ^ (4 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have hscale : (4 : ℝ) • ((p : ℝ) • T) = (p : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hb := hprod (exp T) (exp K) (exp_posDef hT).posSemidef (exp_posDef hK).posSemidef
  rw [h4, hpow p] at hb
  have ht := trace_exp_sum_le_fourth ((p : ℝ) • T) K (hermitian_real_smul hT _) hK
  rw [hscale] at ht
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans hb

/-- The refined exponential lower bound at bidegree (6,4). -/
theorem exponential_bound64 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    210 * (trace (exp ((6 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 6 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum := by
  simpa only [Nat.cast_ofNat, fourthWordTraceSum] using
    exponentialLowerOfRoot 6 210 H K hH hK bound64_root

/-- The refined exponential lower bound at bidegree (7,4). -/
theorem exponential_bound74 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    330 * (trace (exp ((7 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 7 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum := by
  simpa only [Nat.cast_ofNat, fourthWordTraceSum] using
    exponentialLowerOfRoot 7 330 H K hH hK
      (fun X B hX hB ↦ bound74_root X B hX hB.isHermitian)

#print axioms product_bound64
#print axioms product_bound74
#print axioms exponential_bound64
#print axioms exponential_bound74

end RefinedBMV
