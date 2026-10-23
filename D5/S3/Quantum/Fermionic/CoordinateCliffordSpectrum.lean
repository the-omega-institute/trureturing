/- GID: D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/CoordinateCliffordSpectrum
   mirror-E: none(waiver:uniform-coordinate-spectrum)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Prod]
   utility: none
   digest: Coordinate fibers turn the conference coupling into a flat skew matrix. -/

/-
coordinate_skew_flat:
  proof_shape: content
  escape_witness: an explicit equivalence splits a labeled vertex into its selected
    coordinate and the complementary fiber, giving a block conference matrix.
admission_basis: escape-witness
Same-delivery inlined content: ConferenceMatrices, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  none; remaining prerequisites are pinned Mathlib declarations.
computational_content.kind: none; the construction is uniform in dimension and order.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import D5.S3.Quantum.Fermionic.ConferenceMatrices
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Real.Basic

open Matrix
open scoped BigOperators
open D5.S3.Quantum.Fermionic.ConferenceMatrices
noncomputable section
namespace D5.S3.Quantum.Fermionic.CoordinateCliffordSpectrum

open Classical in
def coordinateSkew (q r : ℕ) :
    Matrix ((Fin q → Index r) × Fin q) ((Fin q → Index r) × Fin q) ℝ := fun p t =>
  if p.2 = t.2 ∧ ∀ b, b ≠ p.2 → p.1 b = t.1 b
  then (conference r (p.1 p.2) (t.1 t.2) : ℝ) else 0

theorem coordinate_skew_flat (q r : ℕ) :
    (coordinateSkew q r).transpose = -coordinateSkew q r ∧
    coordinateSkew q r * coordinateSkew q r =
      (-((Fintype.card (Index r) : ℝ) - 1)) • 1 := by
  classical
  let X := Fin q → Index r
  let Fib := (a : Fin q) × ({b : Fin q // b ≠ a} → Index r)
  let f : (X × Fin q) ≃ (Index r × Fib) :=
    { toFun := fun p => (p.1 p.2, ⟨p.2, fun b => p.1 b.val⟩)
      invFun := fun t => ((Equiv.funSplitAt t.2.1 (Index r)).symm (t.1,t.2.2),t.2.1)
      left_inv := by
        rintro ⟨x,a⟩
        apply Prod.ext
        · exact (Equiv.funSplitAt a (Index r)).symm_apply_apply x
        · rfl
      right_inv := by
        rintro ⟨u,⟨a,x⟩⟩
        apply Prod.ext
        · change ((Equiv.funSplitAt a (Index r)).symm (u,x)) a = u
          exact congrArg Prod.fst ((Equiv.funSplitAt a (Index r)).apply_symm_apply (u,x))
        · change (⟨a,fun b => ((Equiv.funSplitAt a (Index r)).symm (u,x)) b.val⟩ : Fib) = ⟨a,x⟩
          exact congrArg (fun t => (⟨a,t⟩ : Fib))
            (congrArg Prod.snd ((Equiv.funSplitAt a (Index r)).apply_symm_apply (u,x))) }
  let C : Matrix (Index r) (Index r) ℝ := (conference r).map (Int.castRingHom ℝ)
  let B := Matrix.blockDiagonal (fun _ : Fib => C)
  have hCskew : C.transpose = -C := by
    have hc := (conference_properties r).2.1
    ext i j
    have hh := congrArg (fun M : Matrix (Index r) (Index r) ℤ => M i j) hc
    change (conference r j i : ℝ) = -(conference r i j : ℝ)
    exact_mod_cast hh
  have hCsq : C*C = (-((Fintype.card (Index r) : ℝ) - 1)) • 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (Index r) (Index r) ℤ => M i j)
      (conference_properties r).2.2.2.2
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
    change (∑ k, (conference r i k : ℝ) * (conference r k j : ℝ)) =
      -((Fintype.card (Index r) : ℝ) - 1) * (if i = j then 1 else 0)
    exact_mod_cast h
  have hBskew : B.transpose = -B := by
    dsimp only [B]
    rw [Matrix.blockDiagonal_transpose]
    simp_rw [hCskew]
    exact Matrix.blockDiagonal_neg _
  have hBsq : B*B = (-((Fintype.card (Index r) : ℝ) - 1)) • 1 := by
    dsimp only [B]
    rw [← Matrix.blockDiagonal_mul]
    simp_rw [hCsq]
    ext ⟨i,u⟩ ⟨j,v⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  have heq : coordinateSkew q r = B.submatrix f f := by
    ext p t
    change (if p.2 = t.2 ∧ ∀ b, b ≠ p.2 → p.1 b = t.1 b
      then (conference r (p.1 p.2) (t.1 t.2) : ℝ) else 0) =
      if (f p).2 = (f t).2 then C (f p).1 (f t).1 else 0
    have hfib : (f p).2 = (f t).2 ↔ p.2 = t.2 ∧ ∀ b, b ≠ p.2 → p.1 b = t.1 b := by
      constructor
      · intro h
        have ha : p.2 = t.2 := congrArg Sigma.fst h
        refine ⟨ha,?_⟩
        rcases p with ⟨x,a⟩
        rcases t with ⟨y,c⟩
        change a = c at ha
        subst c
        have hx : (fun b : {b : Fin q // b ≠ a} => x b.val) = fun b => y b.val :=
          eq_of_heq (Sigma.ext_iff.mp h).2
        intro b hb
        exact congrFun hx ⟨b,hb⟩
      · rintro ⟨ha,hh⟩
        rcases p with ⟨x,a⟩
        rcases t with ⟨y,c⟩
        change a = c at ha
        subst c
        change (⟨a,fun b : {b : Fin q // b ≠ a} => x b.val⟩ : Fib) = ⟨a,fun b => y b.val⟩
        apply congrArg (fun t => (⟨a,t⟩ : Fib))
        funext b
        exact hh b.val b.property
    simp only [hfib]
    rfl
  rw [heq]
  constructor
  · have h := congrArg (fun M : Matrix (Index r × Fib) (Index r × Fib) ℝ => M.submatrix f f) hBskew
    exact h
  · rw [Matrix.submatrix_mul_equiv, hBsq]
    change (-((Fintype.card (Index r) : ℝ) - 1)) •
      ((1 : Matrix (Index r × Fib) (Index r × Fib) ℝ).submatrix f f) = _
    rw [Matrix.submatrix_one_equiv]

end D5.S3.Quantum.Fermionic.CoordinateCliffordSpectrum
