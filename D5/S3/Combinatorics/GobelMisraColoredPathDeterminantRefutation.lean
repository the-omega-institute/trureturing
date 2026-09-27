/- GID: D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.claim; result=D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.result; claim=D5/S3/Combinatorics/GobelMisraColoredPathDeterminantRefutation.claim
   digest: Conjecture 5.3 on colored-path determinants is false at m = 7. -/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GobelMisraColoredPathDeterminantRefutation

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #8621)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- A labelled colored path on `m` vertices: vertex colours in `V`, edge colours in `E`
(the disjoint colour sets are two types); position `r ∈ {1,...,m}` is `i : Fin m` with
`r = i.val + 1`, edge position `r ∈ {1,...,m-1}` is `i : Fin (m-1)`. -/
structure ColoredPath (V E : Type) (m : ℕ) where
  vertexColor : Fin m → V
  edgeColor : Fin (m - 1) → E
  deriving DecidableEq

/-- The generic concentration matrix `K_P`: `k_ii = X (inl (λ(i)))`,
`k_{i,i+1} = k_{i+1,i} = X (inr (λ({i,i+1})))`, `0` elsewhere
(colour constraints (1)-(3), page 5). -/
noncomputable def concentration {V E : Type} {m : ℕ} (P : ColoredPath V E m) :
    Matrix (Fin m) (Fin m) (MvPolynomial (V ⊕ E) ℤ) := by
  classical
  exact fun i j =>
    if i = j then
      MvPolynomial.X (Sum.inl (P.vertexColor i))
    else if hRight : i.val + 1 = j.val then
      MvPolynomial.X (Sum.inr (P.edgeColor ⟨i.val, by omega⟩))
    else if hLeft : j.val + 1 = i.val then
      MvPolynomial.X (Sum.inr (P.edgeColor ⟨j.val, by omega⟩))
    else
      0

/-- The reflection of `P`: position `r ↦ m+1-r` on vertices, `r ↦ m-r` on edges,
colour labels preserved. -/
def reflect {V E : Type} {m : ℕ} (P : ColoredPath V E m) : ColoredPath V E m where
  vertexColor i := P.vertexColor ⟨m - 1 - i.val, by omega⟩
  edgeColor i := P.edgeColor ⟨m - 2 - i.val, by omega⟩

/-- Theorem 3.6 (1)-(4) (`m` even): equal edge colourings; odd positions monochrome
in each path; even positions monochrome in each path; `λ(p₁) = λ(q₂)`,
`λ(p₂) = λ(q₁)`. One-based odd position iff `i.val % 2 = 0`. -/
def Config36 {V E : Type} {m : ℕ} (P Q : ColoredPath V E m) : Prop :=
  (∀ i, P.edgeColor i = Q.edgeColor i) ∧
  (∀ i j, i.val % 2 = 0 → j.val % 2 = 0 →
    P.vertexColor i = P.vertexColor j ∧ Q.vertexColor i = Q.vertexColor j) ∧
  (∀ i j, i.val % 2 = 1 → j.val % 2 = 1 →
    P.vertexColor i = P.vertexColor j ∧ Q.vertexColor i = Q.vertexColor j) ∧
  (∀ i j, i.val % 2 = 0 → j.val % 2 = 1 →
    P.vertexColor i = Q.vertexColor j ∧ P.vertexColor j = Q.vertexColor i)

/-- Theorem 3.8 (1)-(3) (`m` odd): all odd-position vertices of `P` and `Q`
share one colour; even-position vertex colours agree; every odd-position edge of `P`
equals every even-position edge of `Q` and vice versa (edge positions `1..m-1`). -/
def Config38 {V E : Type} {m : ℕ} (P Q : ColoredPath V E m) : Prop :=
  (∀ i j, i.val % 2 = 0 → j.val % 2 = 0 →
    P.vertexColor i = P.vertexColor j ∧
    P.vertexColor i = Q.vertexColor j ∧
    Q.vertexColor i = Q.vertexColor j) ∧
  (∀ i, i.val % 2 = 1 → P.vertexColor i = Q.vertexColor i) ∧
  (∀ i j : Fin (m - 1), i.val % 2 = 0 → j.val % 2 = 1 →
    P.edgeColor i = Q.edgeColor j) ∧
  (∀ i j : Fin (m - 1), i.val % 2 = 0 → j.val % 2 = 1 →
    P.edgeColor j = Q.edgeColor i)

/-- Conjecture 5.3 of arXiv:2506.23936v1, with "or is a reflection of the same"
read as widely as possible (reflect neither, `P`, `Q`, or both). -/
def claim : Prop := ∀ (V E : Type) (m : ℕ) (P Q : ColoredPath V E m),
  (concentration P).det = (concentration Q).det →
    Q = P ∨ Q = reflect P ∨
    (Even m ∧ (Config36 P Q ∨ Config36 (reflect P) Q ∨
      Config36 P (reflect Q) ∨ Config36 (reflect P) (reflect Q))) ∨
    (Odd m ∧ (Config38 P Q ∨ Config38 (reflect P) Q ∨
      Config38 P (reflect Q) ∨ Config38 (reflect P) (reflect Q)))

private def counterexampleP : ColoredPath Unit Bool 7 where
  vertexColor := fun _ => ()
  edgeColor := ![false, true, true, false, false, true]

private def counterexampleQ : ColoredPath Unit Bool 7 where
  vertexColor := fun _ => ()
  edgeColor := ![false, false, true, false, true, true]

private def theorem38P : ColoredPath Unit Bool 5 where
  vertexColor := fun _ => ()
  edgeColor := ![false, true, false, true]

private def theorem38Q : ColoredPath Unit Bool 5 where
  vertexColor := fun _ => ()
  edgeColor := ![true, false, true, false]

private def tri2 {R : Type} [CommRing R] (a e0 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, e0;
     e0, a]

private def tri3 {R : Type} [CommRing R] (a e0 e1 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, e0, 0;
     e0, a, e1;
     0, e1, a]

private def tri4 {R : Type} [CommRing R] (a e0 e1 e2 : R) : Matrix (Fin 4) (Fin 4) R :=
  !![a, e0, 0, 0;
     e0, a, e1, 0;
     0, e1, a, e2;
     0, 0, e2, a]

private def tri5 {R : Type} [CommRing R] (a e0 e1 e2 e3 : R) : Matrix (Fin 5) (Fin 5) R :=
  !![a, e0, 0, 0, 0;
     e0, a, e1, 0, 0;
     0, e1, a, e2, 0;
     0, 0, e2, a, e3;
     0, 0, 0, e3, a]

private def tri6 {R : Type} [CommRing R] (a e0 e1 e2 e3 e4 : R) :
    Matrix (Fin 6) (Fin 6) R :=
  !![a, e0, 0, 0, 0, 0;
     e0, a, e1, 0, 0, 0;
     0, e1, a, e2, 0, 0;
     0, 0, e2, a, e3, 0;
     0, 0, 0, e3, a, e4;
     0, 0, 0, 0, e4, a]

private def tri7 {R : Type} [CommRing R] (a e0 e1 e2 e3 e4 e5 : R) :
    Matrix (Fin 7) (Fin 7) R :=
  !![a, e0, 0, 0, 0, 0, 0;
     e0, a, e1, 0, 0, 0, 0;
     0, e1, a, e2, 0, 0, 0;
     0, 0, e2, a, e3, 0, 0;
     0, 0, 0, e3, a, e4, 0;
     0, 0, 0, 0, e4, a, e5;
     0, 0, 0, 0, 0, e5, a]

example : (reflect counterexampleP).edgeColor =
    ![true, false, false, true, true, false] := by
  funext i
  fin_cases i <;> rfl

example : Config38 theorem38P theorem38Q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j _ _
    exact ⟨rfl, rfl, rfl⟩
  · intro i _
    rfl
  · intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      simp [theorem38P, theorem38Q] at hi hj ⊢
  · intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      simp [theorem38P, theorem38Q] at hi hj ⊢

example : (concentration theorem38P).det = (concentration theorem38Q).det := by
  classical
  let a : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inl ())
  let u : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inr false)
  let v : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inr true)
  have h2 (x y : MvPolynomial (Unit ⊕ Bool) ℤ) :
      (tri2 x y).det = x ^ 2 - y ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [tri2]
    ring
  have h3 (x y z : MvPolynomial (Unit ⊕ Bool) ℤ) :
      (tri3 x y z).det = x ^ 3 - x * y ^ 2 - x * z ^ 2 := by
    rw [Matrix.det_fin_three]
    simp [tri3]
    ring
  have h4 (x y z w : MvPolynomial (Unit ⊕ Bool) ℤ) :
      (tri4 x y z w).det = x * (tri3 x z w).det - y ^ 2 * (tri2 x w).det := by
    have h0 : (tri4 x y z w).submatrix Fin.succ (0 : Fin 4).succAbove =
        tri3 x z w := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have h1 : ((tri4 x y z w).submatrix Fin.succ
        (Fin.succ (0 : Fin 3) : Fin 4).succAbove).det = y * (tri2 x w).det := by
      rw [Matrix.det_fin_three, Matrix.det_fin_two]
      simp [tri4, tri2, Fin.succAbove]
      ring
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
    rw [h0, h1]
    simp [tri4]
    ring
  have h5 (x y z w t : MvPolynomial (Unit ⊕ Bool) ℤ) :
      (tri5 x y z w t).det = x * (tri4 x z w t).det - y ^ 2 * (tri3 x w t).det := by
    have h0 : (tri5 x y z w t).submatrix Fin.succ (0 : Fin 5).succAbove =
        tri4 x z w t := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have h1 : ((tri5 x y z w t).submatrix Fin.succ
        (Fin.succ (0 : Fin 4) : Fin 5).succAbove).det = y * (tri3 x w t).det := by
      have h10 : ((tri5 x y z w t).submatrix Fin.succ
          (Fin.succ (0 : Fin 4) : Fin 5).succAbove).submatrix
            (0 : Fin 4).succAbove Fin.succ = tri3 x w t := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [Matrix.det_succ_column_zero]
      simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
      rw [h10]
      simp [tri5]
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
    rw [h0, h1]
    simp [tri5]
    ring
  have hp : concentration theorem38P = tri5 a u v u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [concentration, theorem38P, tri5, a, u, v]
  have hq : concentration theorem38Q = tri5 a v u v u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [concentration, theorem38Q, tri5, a, u, v]
  rw [hp, hq]
  simp only [h5, h4, h3, h2]
  ring

/-- Conjecture 5.3 is false at `m = 7`. -/
theorem result : ¬ claim := by
  intro h
  have hdet : (concentration counterexampleP).det =
      (concentration counterexampleQ).det := by
    classical
    let a : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inl ())
    let u : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inr false)
    let v : MvPolynomial (Unit ⊕ Bool) ℤ := MvPolynomial.X (Sum.inr true)
    have h2 (x y : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri2 x y).det = x ^ 2 - y ^ 2 := by
      rw [Matrix.det_fin_two]
      simp [tri2]
      ring
    have h3 (x y z : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri3 x y z).det = x ^ 3 - x * y ^ 2 - x * z ^ 2 := by
      rw [Matrix.det_fin_three]
      simp [tri3]
      ring
    have h4 (x y z w : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri4 x y z w).det = x * (tri3 x z w).det - y ^ 2 * (tri2 x w).det := by
      have h0 : (tri4 x y z w).submatrix Fin.succ (0 : Fin 4).succAbove =
          tri3 x z w := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have h1 : ((tri4 x y z w).submatrix Fin.succ
          (Fin.succ (0 : Fin 3) : Fin 4).succAbove).det = y * (tri2 x w).det := by
        rw [Matrix.det_fin_three, Matrix.det_fin_two]
        simp [tri4, tri2, Fin.succAbove]
        ring
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
      rw [h0, h1]
      simp [tri4]
      ring
    have h5 (x y z w t : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri5 x y z w t).det = x * (tri4 x z w t).det - y ^ 2 * (tri3 x w t).det := by
      have h0 : (tri5 x y z w t).submatrix Fin.succ (0 : Fin 5).succAbove =
          tri4 x z w t := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have h1 : ((tri5 x y z w t).submatrix Fin.succ
          (Fin.succ (0 : Fin 4) : Fin 5).succAbove).det = y * (tri3 x w t).det := by
        have h10 : ((tri5 x y z w t).submatrix Fin.succ
            (Fin.succ (0 : Fin 4) : Fin 5).succAbove).submatrix
              (0 : Fin 4).succAbove Fin.succ = tri3 x w t := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        rw [Matrix.det_succ_column_zero]
        simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
        rw [h10]
        simp [tri5]
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
      rw [h0, h1]
      simp [tri5]
      ring
    have h6 (x y z w t s : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri6 x y z w t s).det = x * (tri5 x z w t s).det - y ^ 2 * (tri4 x w t s).det := by
      have h0 : (tri6 x y z w t s).submatrix Fin.succ (0 : Fin 6).succAbove =
          tri5 x z w t s := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have h1 : ((tri6 x y z w t s).submatrix Fin.succ
          (Fin.succ (0 : Fin 5) : Fin 6).succAbove).det = y * (tri4 x w t s).det := by
        have h10 : ((tri6 x y z w t s).submatrix Fin.succ
            (Fin.succ (0 : Fin 5) : Fin 6).succAbove).submatrix
              (0 : Fin 5).succAbove Fin.succ = tri4 x w t s := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        rw [Matrix.det_succ_column_zero]
        simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
        rw [h10]
        simp [tri6]
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
      rw [h0, h1]
      simp [tri6]
      ring
    have h7 (x y z w t s r : MvPolynomial (Unit ⊕ Bool) ℤ) :
        (tri7 x y z w t s r).det =
          x * (tri6 x z w t s r).det - y ^ 2 * (tri5 x w t s r).det := by
      have h0 : (tri7 x y z w t s r).submatrix Fin.succ (0 : Fin 7).succAbove =
          tri6 x z w t s r := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have h1 : ((tri7 x y z w t s r).submatrix Fin.succ
          (Fin.succ (0 : Fin 6) : Fin 7).succAbove).det = y * (tri5 x w t s r).det := by
        have h10 : ((tri7 x y z w t s r).submatrix Fin.succ
            (Fin.succ (0 : Fin 6) : Fin 7).succAbove).submatrix
              (0 : Fin 6).succAbove Fin.succ = tri5 x w t s r := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        rw [Matrix.det_succ_column_zero]
        simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
        rw [h10]
        simp [tri7]
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
      rw [h0, h1]
      simp [tri7]
      ring
    have hp : concentration counterexampleP = tri7 a u v v u u v := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [concentration, counterexampleP, tri7, a, u, v]
    have hq : concentration counterexampleQ = tri7 a u u v u v v := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [concentration, counterexampleQ, tri7, a, u, v]
    have hpdet : (tri7 a u v v u u v).det =
        a ^ 7 - 3 * a ^ 5 * u ^ 2 - 3 * a ^ 5 * v ^ 2 +
          2 * a ^ 3 * u ^ 4 + 6 * a ^ 3 * u ^ 2 * v ^ 2 + 2 * a ^ 3 * v ^ 4 -
          2 * a * u ^ 4 * v ^ 2 - 2 * a * u ^ 2 * v ^ 4 := by
      simp only [h7, h6, h5, h4, h3, h2]
      ring
    have hqdet : (tri7 a u u v u v v).det =
        a ^ 7 - 3 * a ^ 5 * u ^ 2 - 3 * a ^ 5 * v ^ 2 +
          2 * a ^ 3 * u ^ 4 + 6 * a ^ 3 * u ^ 2 * v ^ 2 + 2 * a ^ 3 * v ^ 4 -
          2 * a * u ^ 4 * v ^ 2 - 2 * a * u ^ 2 * v ^ 4 := by
      simp only [h7, h6, h5, h4, h3, h2]
      ring
    rw [hp, hq]
    exact hpdet.trans hqdet.symm
  have hconclusion := h Unit Bool 7 counterexampleP counterexampleQ hdet
  have himpossible : ¬ (
      counterexampleQ = counterexampleP ∨
      counterexampleQ = reflect counterexampleP ∨
      (Even 7 ∧
        (Config36 counterexampleP counterexampleQ ∨
          Config36 (reflect counterexampleP) counterexampleQ ∨
          Config36 counterexampleP (reflect counterexampleQ) ∨
          Config36 (reflect counterexampleP) (reflect counterexampleQ))) ∨
      (Odd 7 ∧
        (Config38 counterexampleP counterexampleQ ∨
          Config38 (reflect counterexampleP) counterexampleQ ∨
          Config38 counterexampleP (reflect counterexampleQ) ∨
          Config38 (reflect counterexampleP) (reflect counterexampleQ)))) := by
    intro hbad
    rcases hbad with heq | href | ⟨heven, _⟩ | ⟨_, hcfg⟩
    · exact (by decide : counterexampleQ ≠ counterexampleP) heq
    · exact (by decide : counterexampleQ ≠ reflect counterexampleP) href
    · exact (by decide : ¬ Even 7) heven
    · rcases hcfg with hcfg | hcfg | hcfg | hcfg
      · have hfalse := hcfg.2.2.1 (0 : Fin 6) (5 : Fin 6) (by rfl) (by rfl)
        simp [counterexampleP, counterexampleQ] at hfalse
      · have hfalse := hcfg.2.2.1 (0 : Fin 6) (1 : Fin 6) (by rfl) (by rfl)
        simp [counterexampleP, counterexampleQ, reflect] at hfalse
      · have hfalse := hcfg.2.2.1 (2 : Fin 6) (5 : Fin 6) (by rfl) (by rfl)
        simp [counterexampleP, counterexampleQ, reflect] at hfalse
      · have hfalse := hcfg.2.2.1 (0 : Fin 6) (5 : Fin 6) (by rfl) (by rfl)
        simp [counterexampleP, counterexampleQ, reflect] at hfalse
  exact himpossible hconclusion

#print axioms result

end D5.S3.Combinatorics.GobelMisraColoredPathDeterminantRefutation
