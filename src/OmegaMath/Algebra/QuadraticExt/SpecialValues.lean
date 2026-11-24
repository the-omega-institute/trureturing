module
prelude
public import OmegaMath.Algebra.QuadraticExt.Spinor
public import OmegaMath.Harmonic.ChebyshevHecke.Recurrence

/-!
Omega original.

Pentagonal first-kind Chebyshev evaluations in the golden quadratic algebra.
The recurrence for twice the value keeps all intermediate coefficients integral.
-/

noncomputable section
@[expose] public section

namespace Omega.QPhi

open QuadPoly Polynomial

def scalarRing : CommRingOps QPhi (Equivalent rationalRing) := ring rationalRing
theorem laws : scalarRing.Laws := ringLaws rationalRingLaws

def phi : QPhi := alpha rationalRing
def half : QPhi := ofScalar rationalRing ⟨Int.one, .succ .zero⟩
def phiHalf : QPhi := scalarRing.mul half phi
def phiSubOneHalf : QPhi := scalarRing.mul half (scalarRing.sub phi scalarRing.one)

def five : Nat := .succ (.succ (.succ (.succ (.succ .zero))))
def ten : Nat := Nat.add five five

private theorem two_half : scalarRing.eqv (scalarRing.mul half scalarRing.two) scalarRing.one :=
  And.intro Eq.refl Eq.refl

private theorem two_mul_half (a : QPhi) :
    scalarRing.eqv (scalarRing.mul scalarRing.two (scalarRing.mul half a)) a :=
  let vars := Variables.cons half (Variables.cons a (Variables.nil scalarRing))
  laws.trans (prove scalarRing laws vars (Expr.two.mul (e0.mul e1))
    ((e0.mul Expr.two).mul e1) Eq.refl)
    (laws.trans (laws.mul_congr two_half (laws.refl a)) (laws.one_mul a))

/-- Evaluate T at half of a using the recurrence with integral initial values 2 and a. -/
private theorem half_argument (a : QPhi) (n : Nat) :
    scalarRing.eqv (Chebyshev.T scalarRing (scalarRing.mul half a) n)
      (scalarRing.mul half (Chebyshev.linear scalarRing a scalarRing.two a n)) :=
  let r := scalarRing
  let x := r.mul half a
  let f := Chebyshev.T r x
  let g := Chebyshev.linear r a r.two a
  have base := Chebyshev.linear_unique r laws a r.one x f
    (laws.refl r.one) (laws.symm (Chebyshev.T_one r laws x))
    (fun k => laws.trans
      (laws.sub_congr (laws.mul_congr (laws.symm (two_mul_half a)) (laws.refl (f k.succ)))
        (laws.refl (f k))) (laws.symm (Chebyshev.T_step r laws x k))) n
  have scaled := Chebyshev.linear_unique r laws a r.one x (fun k => r.mul half (g k))
    (laws.symm two_half) (laws.refl x)
    (fun k => prove r laws (.cons a (.cons half (.cons (g k.succ) (.cons (g k) (Variables.nil r)))))
      ((e0.mul (e1.mul e2)).sub (e1.mul e3)) (e1.mul ((e0.mul e2).sub e3)) Eq.refl) n
  laws.trans (laws.symm base) scaled

theorem T_five_phi_half :
    scalarRing.eqv (Chebyshev.T scalarRing phiHalf five) (scalarRing.neg scalarRing.one) :=
  laws.trans (half_argument phi five) (And.intro Eq.refl Eq.refl)

theorem T_ten_phi_half :
    scalarRing.eqv (Chebyshev.T scalarRing phiHalf ten) scalarRing.one :=
  laws.trans (half_argument phi ten) (And.intro Eq.refl Eq.refl)

theorem T_five_phi_sub_one_half :
    scalarRing.eqv (Chebyshev.T scalarRing phiSubOneHalf five) scalarRing.one :=
  laws.trans (half_argument (scalarRing.sub phi scalarRing.one) five) (And.intro Eq.refl Eq.refl)

end Omega.QPhi
