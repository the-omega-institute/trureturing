import OmegaBuild.Commands
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
Omega original.

Quadratic normal form and universal evaluation for a four-generator resonant coordinate ring.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Polynomial

namespace Omega.PaisPoisson

-- The polynomial coordinates in order of adjoining are c = u - v, v, x.
abbrev CPoly := Polynomial ℝ
abbrev UV := Polynomial CPoly
abbrev B := Polynomial UV
abbrev cx : CPoly := X
abbrev vv : UV := X
abbrev uu : UV := C cx + vv
abbrev xb : B := X
abbrev rad (n m : ℕ) : B := C (uu ^ n * vv ^ m) - xb ^ 2
abbrev A (n m : ℕ) := QuadraticAlgebra B (rad n m) 0

variable {n m : ℕ}

def incl : B →ₐ[ℝ] A n m := IsScalarTower.toAlgHom ℝ B (A n m)
def inclV : UV →ₐ[ℝ] A n m := incl.comp CAlgHom
def inclC : CPoly →ₐ[ℝ] A n m := inclV.comp CAlgHom

def u : A n m := inclV uu
def v : A n m := inclV vv
def x : A n m := incl xb
def y : A n m := QuadraticAlgebra.omega

@[simp] theorem incl_C (p : UV) : incl (n := n) (m := m) (C p) = inclV p := rfl

theorem inclC_X : inclC (n := n) (m := m) X = u - v := by
  symm
  change inclV (C cx + vv) - inclV vv = inclV (C cx)
  rw [map_add]
  abel

theorem normal (a : A n m) : a = incl a.re + incl a.im * y := by
  have he (p : B) (z : A n m) : p • z = incl p * z := Algebra.smul_def p z
  simpa only [y, he, mul_one] using (QuadraticAlgebra.re_smul_add_im_smul a).symm

theorem y_sq : (y (n := n) (m := m)) ^ 2 = incl (rad n m) := by
  rw [pow_two]
  exact QuadraticAlgebra.omega_mul_omega_eq_mk (R := B) (a := rad n m) (b := 0)

theorem relation : (x (n := n) (m := m)) ^ 2 + y ^ 2 = u ^ n * v ^ m := by
  rw [y_sq]
  change incl xb ^ 2 + incl (C (uu ^ n * vv ^ m) - xb ^ 2) = inclV uu ^ n * inclV vv ^ m
  let j : B →ₐ[ℝ] A n m := incl
  let k : UV →ₐ[ℝ] A n m := inclV
  change j xb ^ 2 + j (C (uu ^ n * vv ^ m) - xb ^ 2) = k uu ^ n * k vv ^ m
  rw [map_sub j, show j (xb ^ 2) = j xb ^ 2 from j.toRingHom.map_pow xb 2, show j (C (uu ^ n * vv ^ m)) = k (uu ^ n * vv ^ m) from rfl,
    map_mul k, show k (uu ^ n) = k uu ^ n from k.toRingHom.map_pow uu n,
    show k (vv ^ m) = k vv ^ m from k.toRingHom.map_pow vv m]
  abel

section Universal
variable {S : Type*} [CommRing S] [Algebra ℝ S]

private def polyEval (a b d : S) : B →ₐ[ℝ] S :=
  aevalTower (aevalTower (aeval (a - b)) b) d

@[simp] private theorem polyEval_uu (a b d : S) : polyEval a b d (C uu) = a := by
  simp [polyEval]

@[simp] private theorem polyEval_vv (a b d : S) : polyEval a b d (C vv) = b := by
  simp [polyEval]

@[simp] private theorem polyEval_xb (a b d : S) : polyEval a b d xb = d := by
  simp [polyEval]

def evaluate (a b d e : S) (h : d ^ 2 + e ^ 2 = a ^ n * b ^ m) : A n m →ₐ[ℝ] S := by
  letI : Algebra B S := (polyEval a b d).toRingHom.toAlgebra
  letI : IsScalarTower ℝ B S := IsScalarTower.of_algebraMap_eq (R := ℝ) (S := B) (A := S) fun r =>
    ((polyEval a b d).commutes r).symm
  have hr : polyEval a b d (rad n m) = e ^ 2 := by
    rw [show rad n m = (C uu) ^ n * (C vv) ^ m - xb ^ 2 by simp only [rad, map_mul, map_pow]]
    rw [map_sub, map_mul, map_pow, map_pow, map_pow, polyEval_uu, polyEval_vv, polyEval_xb,
      ← h, add_sub_cancel_left]
  let F : A n m →ₐ[B] S := QuadraticAlgebra.lift ⟨e, by
    change e * e = rad n m • (1 : S) + (0 : B) • e
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, ← pow_two]
    exact hr.symm⟩
  exact F.restrictScalars ℝ

@[simp] private theorem evaluate_incl {a b d e : S} {h : d ^ 2 + e ^ 2 = a ^ n * b ^ m}
    (p : B) : evaluate a b d e h (incl p) = polyEval a b d p := by
  change polyEval a b d p * 1 + polyEval a b d 0 * e = _
  simp

@[simp] theorem evaluate_u {a b d e : S} (h : d ^ 2 + e ^ 2 = a ^ n * b ^ m) :
    evaluate a b d e h (u (n := n) (m := m)) = a := by
  change evaluate a b d e h (incl (C uu)) = a
  rw [evaluate_incl, polyEval_uu]

@[simp] theorem evaluate_v {a b d e : S} (h : d ^ 2 + e ^ 2 = a ^ n * b ^ m) :
    evaluate a b d e h (v (n := n) (m := m)) = b := by
  change evaluate a b d e h (incl (C vv)) = b
  rw [evaluate_incl, polyEval_vv]

@[simp] theorem evaluate_x {a b d e : S} (h : d ^ 2 + e ^ 2 = a ^ n * b ^ m) :
    evaluate a b d e h (x (n := n) (m := m)) = d := by
  change evaluate a b d e h (incl xb) = d
  rw [evaluate_incl, polyEval_xb]

@[simp] theorem evaluate_y {a b d e : S} (h : d ^ 2 + e ^ 2 = a ^ n * b ^ m) :
    evaluate a b d e h (y (n := n) (m := m)) = e := by
  change polyEval a b d 0 * 1 + polyEval a b d 1 * e = e
  simp

theorem hom_ext {f g : A n m →ₐ[ℝ] S}
    (hu : f u = g u) (hv : f v = g v) (hx : f x = g x) (hy : f y = g y) : f = g := by
  have hc : f.comp inclC = g.comp inclC := by
    apply Polynomial.algHom_ext
    change f (inclC X) = g (inclC X)
    rw [inclC_X, map_sub f, map_sub g, hu, hv]
  have hp : f.comp inclV = g.comp inclV := by
    apply Polynomial.algHom_ext'
    · exact hc
    · exact hv
  have hb : f.comp incl = g.comp incl := by
    apply Polynomial.algHom_ext'
    · exact hp
    · exact hx
  let _ : Algebra B S := (f.comp incl).toRingHom.toAlgebra
  let fB : A n m →ₐ[B] S := { f.toRingHom with commutes' := fun _ => rfl }
  let gB : A n m →ₐ[B] S :=
    { g.toRingHom with commutes' := fun p => (AlgHom.congr_fun hb p).symm }
  have he : fB = gB := QuadraticAlgebra.algHom_ext hy
  exact AlgHom.ext fun a => AlgHom.congr_fun he a

end Universal

section PaperQuotient

abbrev FourPolys := MvPolynomial (Fin 4) ℝ

private def coordinates {S : Type*} (u v x y : S) : Fin 4 → S := ![u, v, x, y]

def relationPoly (n m : ℕ) : FourPolys :=
  MvPolynomial.X 2 ^ 2 + MvPolynomial.X 3 ^ 2 -
    MvPolynomial.X 0 ^ n * MvPolynomial.X 1 ^ m

def relationIdeal (n m : ℕ) : Ideal FourPolys := Ideal.span {relationPoly n m}

abbrev Paper (n m : ℕ) := FourPolys ⧸ relationIdeal n m

def quot (n m : ℕ) : FourPolys →ₐ[ℝ] Paper n m := Ideal.Quotient.mkₐ ℝ _

def qu (n m : ℕ) : Paper n m := quot n m (MvPolynomial.X 0)
def qv (n m : ℕ) : Paper n m := quot n m (MvPolynomial.X 1)
def qx (n m : ℕ) : Paper n m := quot n m (MvPolynomial.X 2)
def qy (n m : ℕ) : Paper n m := quot n m (MvPolynomial.X 3)

private theorem quot_relation (n m : ℕ) : qx n m ^ 2 + qy n m ^ 2 = qu n m ^ n * qv n m ^ m := by
  have hz : quot n m (relationPoly n m) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply sub_eq_zero.mp
  simpa only [relationPoly, map_sub (quot n m), map_add (quot n m), map_mul (quot n m),
    map_pow (quot n m), qu, qv, qx, qy] using hz

private def fromPolynomial (n m : ℕ) : FourPolys →ₐ[ℝ] A n m :=
  MvPolynomial.aeval (coordinates u v x y)

@[simp] private theorem fromPolynomial_X (j : Fin 4) :
    fromPolynomial n m (MvPolynomial.X j) = coordinates (u : A n m) v x y j :=
  MvPolynomial.aeval_X _ _

private theorem fromPolynomial_relation (n m : ℕ) : fromPolynomial n m (relationPoly n m) = 0 := by
  let f := fromPolynomial n m
  have hp (p : FourPolys) (k : ℕ) : f (p ^ k) = f p ^ k := f.toRingHom.map_pow p k
  change f (_ - _) = 0
  rw [map_sub f, map_add f, map_mul f, hp, hp, hp, hp]
  simp only [f, fromPolynomial_X]
  change (x : A n m) ^ 2 + y ^ 2 - u ^ n * v ^ m = 0
  exact sub_eq_zero.mpr relation

private def fromPaper (n m : ℕ) : Paper n m →ₐ[ℝ] A n m := by
  refine Ideal.Quotient.liftₐ (relationIdeal n m) (fromPolynomial n m) ?_
  have h : relationIdeal n m ≤ RingHom.ker (fromPolynomial n m).toRingHom := by
    rw [relationIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact fromPolynomial_relation n m
  exact fun p hp => h hp

private theorem fromPaper_quot (p : FourPolys) :
    fromPaper n m (quot n m p) = fromPolynomial n m p := rfl

private theorem quotient_ext {S : Type*} [CommRing S] [Algebra ℝ S]
    {f g : Paper n m →ₐ[ℝ] S}
    (hu : f (qu n m) = g (qu n m)) (hv : f (qv n m) = g (qv n m))
    (hx : f (qx n m) = g (qx n m)) (hy : f (qy n m) = g (qy n m)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hu
  · exact hv
  · exact hx
  · exact hy

private def toPaper (n m : ℕ) : A n m →ₐ[ℝ] Paper n m :=
  evaluate (qu n m) (qv n m) (qx n m) (qy n m) (quot_relation n m)

@[simp] private theorem fromPaper_qu (n m : ℕ) : fromPaper n m (qu n m) = u := by
  rw [qu, fromPaper_quot, fromPolynomial_X]
  rfl

@[simp] private theorem fromPaper_qv (n m : ℕ) : fromPaper n m (qv n m) = v := by
  rw [qv, fromPaper_quot, fromPolynomial_X]
  rfl

@[simp] private theorem fromPaper_qx (n m : ℕ) : fromPaper n m (qx n m) = x := by
  rw [qx, fromPaper_quot, fromPolynomial_X]
  rfl

@[simp] private theorem fromPaper_qy (n m : ℕ) : fromPaper n m (qy n m) = y := by
  rw [qy, fromPaper_quot, fromPolynomial_X]
  rfl

/-- The quadratic normal form is equivalent to the literal four-variable presentation. -/
def paperEquiv (n m : ℕ) : Paper n m ≃ₐ[ℝ] A n m :=
  AlgEquiv.ofAlgHom (fromPaper n m) (toPaper n m)
    (hom_ext (n := n) (m := m) (S := A n m)
      (f := (fromPaper n m).comp (toPaper n m)) (g := AlgHom.id ℝ (A n m))
      (show fromPaper n m (toPaper n m u) = u by simp [toPaper])
      (show fromPaper n m (toPaper n m v) = v by simp [toPaper])
      (show fromPaper n m (toPaper n m x) = x by simp [toPaper])
      (show fromPaper n m (toPaper n m y) = y by simp [toPaper]))
    (quotient_ext (n := n) (m := m) (S := Paper n m)
      (f := (toPaper n m).comp (fromPaper n m)) (g := AlgHom.id ℝ (Paper n m))
      (show toPaper n m (fromPaper n m (qu n m)) = qu n m by simp [toPaper])
      (show toPaper n m (fromPaper n m (qv n m)) = qv n m by simp [toPaper])
      (show toPaper n m (fromPaper n m (qx n m)) = qx n m by simp [toPaper])
      (show toPaper n m (fromPaper n m (qy n m)) = qy n m by simp [toPaper]))

@[simp] theorem paperEquiv_qu (n m : ℕ) : paperEquiv n m (qu n m) = u := fromPaper_qu n m
@[simp] theorem paperEquiv_qv (n m : ℕ) : paperEquiv n m (qv n m) = v := fromPaper_qv n m
@[simp] theorem paperEquiv_qx (n m : ℕ) : paperEquiv n m (qx n m) = x := fromPaper_qx n m
@[simp] theorem paperEquiv_qy (n m : ℕ) : paperEquiv n m (qy n m) = y := fromPaper_qy n m

end PaperQuotient

end Omega.PaisPoisson
