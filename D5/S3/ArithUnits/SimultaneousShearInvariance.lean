/- GID: D5/S3/ArithUnits/SimultaneousShearInvariance
   generality: G
   mirror-B: D5/B/S3/ArithUnits/SimultaneousShearInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two independent simultaneous translations force a polynomial to be constant. -/

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
Translation invariance in two distinguished variables, with arbitrary auxiliary
variables allowed in the coefficient domain. The determinant hypothesis is an
inequality in that domain; it does not assert nonvanishing at every evaluation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ArithUnits.SimultaneousShearInvariance

open MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Substitution by a simultaneous translation of all polynomial variables. -/
def translate {σ : Type*} (v : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (v i))

private def linePolynomial {σ : Type*} (F : MvPolynomial σ R) (x v : σ → R) :
    Polynomial R :=
  eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F

private theorem eval_linePolynomial {σ : Type*}
    (F : MvPolynomial σ R) (x v : σ → R) (t : R) :
    (linePolynomial F x v).eval t = eval (fun i => x i + t * v i) F := by
  let L := eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)
  have h : (Polynomial.evalRingHom t).comp L =
      eval (fun i => x i + t * v i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [L]
    · intro i
      rw [RingHom.comp_apply, show L (X i) =
        Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X from
          eval₂Hom_X' _ _ i, MvPolynomial.eval_X]
      change (Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X).eval t =
        x i + t * v i
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_C, Polynomial.eval_X, mul_comm]
  exact DFunLike.congr_fun h F

/-- Integer iteration is promoted to every scalar parameter by an infinite
root argument. No degree bound or nonzero coordinate of the direction is needed. -/
private theorem eval_line_of_translation {σ : Type*}
    (F : MvPolynomial σ R) (v : σ → R) (hF : translate v F = F)
    (x : σ → R) (t : R) :
    eval (fun i => x i + t * v i) F = eval x F := by
  have hstep (z : σ → R) : eval (fun i => z i + v i) F = eval z F := by
    have he : (eval z).comp (translate v) = eval (fun i => z i + v i) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [translate]
      · intro i
        simp [translate]
    have hz := congrArg (eval z) hF
    change ((eval z).comp (translate v)) F = eval z F at hz
    rw [he] at hz
    exact hz
  have hn : ∀ n : ℕ, eval (fun i => x i + (n : R) * v i) F = eval x F := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [Nat.cast_succ, add_mul, one_mul, add_assoc] using
        (hstep (fun i => x i + (n : R) * v i)).trans ih
  have hline : linePolynomial F x v = Polynomial.C (eval x F) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := R))).mono
    rintro z ⟨n, rfl⟩
    simpa only [Set.mem_ofPred_eq, eval_linePolynomial, Polynomial.eval_C] using hn n
  simpa only [eval_linePolynomial, Polynomial.eval_C] using
    congrArg (fun P : Polynomial R => P.eval t) hline

/-- A polynomial fixed by two translations whose determinant is nonzero is
constant in both variables. The coefficient ring can itself be a polynomial
ring, so the directions and all auxiliary variables remain formal parameters. -/
private theorem eq_constant_of_two_translations
    (F : MvPolynomial (Fin 2) R) (v w : Fin 2 → R)
    (hdet : v 0 * w 1 - w 0 * v 1 ≠ 0)
    (hv : translate v F = F) (hw : translate w F = F) :
    F = C (constantCoeff F) := by
  classical
  let delta : R := v 0 * w 1 - w 0 * v 1
  have hdelta : delta ≠ 0 := hdet
  have hinj : Function.Injective (fun z : R => delta * z) := by
    intro x y hxy
    exact mul_left_cancel₀ hdelta hxy
  apply MvPolynomial.funext_set (fun _ => Set.range (fun z : R => delta * z))
    (fun _ => Set.infinite_range_of_injective hinj)
  intro x hx
  obtain ⟨d, hd⟩ := hx 0 (Set.mem_univ _)
  obtain ⟨u, hu⟩ := hx 1 (Set.mem_univ _)
  let alpha : R := w 1 * d - w 0 * u
  let beta : R := v 0 * u - v 1 * d
  have hpoint : (fun i => (0 + alpha * v i) + beta * w i) = x := by
    funext i
    fin_cases i
    · calc
        (0 + alpha * v 0) + beta * w 0 = delta * d := by
          dsimp [alpha, beta, delta]
          ring
        _ = x 0 := hd
    · calc
        (0 + alpha * v 1) + beta * w 1 = delta * u := by
          dsimp [alpha, beta, delta]
          ring
        _ = x 1 := hu
  calc
    eval x F = eval (fun i => (0 + alpha * v i) + beta * w i) F :=
      congrArg (fun z => eval z F) hpoint.symm
    _ = eval (fun i => 0 + alpha * v i) F :=
      eval_line_of_translation F w hw _ beta
    _ = eval (0 : Fin 2 → R) F :=
      eval_line_of_translation F v hv (0 : Fin 2 → R) alpha
    _ = eval x (C (constantCoeff F)) := by simp [MvPolynomial.eval_zero]

/-- Independent coefficient indeterminates give two simultaneous shear
directions with nonzero polynomial determinant. All other indeterminates are
retained in the coefficient ring, with no restriction on their number or degrees. -/
theorem eq_constant_of_two_shears {σ : Type*}
    (ι : Fin 4 → σ) (hι : Function.Injective ι)
    (F : MvPolynomial (Fin 2) (MvPolynomial σ R))
    (ha : translate (fun i : Fin 2 =>
      if i = 0 then X (ι 0) else X (ι 2)) F = F)
    (hb : translate (fun i : Fin 2 =>
      if i = 0 then X (ι 1) else X (ι 3)) F = F) :
    F = C (constantCoeff F) := by
  classical
  have hdet : (X (ι 0) : MvPolynomial σ R) * X (ι 3) -
      X (ι 1) * X (ι 2) ≠ 0 := by
    intro hz
    have he := congrArg
      (eval (fun j : σ => if j = ι 0 ∨ j = ι 3 then (1 : R) else 0)) hz
    simp [hι.eq_iff] at he
  apply eq_constant_of_two_translations F
    (fun i : Fin 2 => if i = 0 then X (ι 0) else X (ι 2))
    (fun i : Fin 2 => if i = 0 then X (ι 1) else X (ι 3))
    _ ha hb
  simpa using hdet

#print axioms eq_constant_of_two_shears

end D5.S3.ArithUnits.SimultaneousShearInvariance
