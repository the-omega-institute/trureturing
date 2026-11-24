module
prelude
public import OmegaMath.Calculus.Jet2.Operations

/-!
Omega original.

Exact rational fidelity and its second-order jet, including the finite secant error.
-/

noncomputable section

@[expose] public section

namespace Omega.Jet2


def fidelityDen (x : IntRatio) : IntRatio := IntRatio.one.add (x.mul x)
def kappa (x : IntRatio) : IntRatio := (fidelityDen x).inv

/-- Coefficients of 1 + (x + η)². -/
def fidelityDenJet (x : IntRatio) : Jet2 :=
  ⟨fidelityDen x, IntRatio.two.mul x, IntRatio.one⟩

/-- Evaluating the fidelity denominator at x + η gives exactly its three coefficients. -/
theorem fidelityDenJet_eval (x : IntRatio) (hx : x.Finite) :
    Equivalent (one.add (((const x).add var).mul ((const x).add var))) (fidelityDenJet x) :=
  let atPoint : Jet2 := ⟨x, IntRatio.one, IntRatio.zero⟩
  have coordinate : Equivalent ((const x).add var) atPoint :=
    And.intro (IntRatio.add_zero x) (And.intro Eq.refl Eq.refl)
  have linear := (IntRatio.add_congr (IntRatio.mul_one x) (IntRatio.one_mul x)).trans
    (IntRatio.two_mul x).symm
  have quadratic := (IntRatio.add_congr
      ((IntRatio.add_congr (IntRatio.mul_zero hx) (IntRatio.mul_one IntRatio.one)).trans
        (IntRatio.zero_add IntRatio.one)) (IntRatio.zero_mul hx)).trans
    (IntRatio.add_zero IntRatio.one)
  have evaluate : Equivalent (one.add (atPoint.mul atPoint)) (fidelityDenJet x) :=
    And.intro (IntRatio.equivalent_refl (fidelityDen x))
      (And.intro ((IntRatio.zero_add _).trans linear) ((IntRatio.zero_add _).trans quadratic))
  (add_congr (equivalent_refl one) (mul_congr coordinate coordinate)).trans evaluate

def kappaJetAt (x : IntRatio) : Jet2 := (fidelityDenJet x).inv


theorem sub_add (a b c : IntRatio) :
    IntRatio.Equivalent (a.sub (b.add c)) ((a.sub b).sub c) :=
  (IntRatio.add_congr (IntRatio.equivalent_refl a) (IntRatio.neg_add b c)).trans
    (IntRatio.add_assoc a b.neg c.neg).symm

theorem b_sq_sub_den (x : IntRatio) (hx : x.Finite) :
    IntRatio.Equivalent (((IntRatio.two.mul x).mul (IntRatio.two.mul x)).sub (fidelityDen x))
      ((IntRatio.three.mul (x.mul x)).sub IntRatio.one) :=
  let t := x.mul x
  have reduce : IntRatio.Equivalent ((IntRatio.two.mul IntRatio.two).mul t)
      ((IntRatio.three.mul t).add t) :=
    (IntRatio.add_mul IntRatio.three IntRatio.one t).trans
      (IntRatio.add_congr (IntRatio.equivalent_refl (IntRatio.three.mul t)) (IntRatio.one_mul t))
  (IntRatio.sub_congr ((IntRatio.mul_mul_mul_comm IntRatio.two x IntRatio.two x).trans reduce)
      (IntRatio.add_comm IntRatio.one t)).trans
    ((sub_add ((IntRatio.three.mul t).add t) t IntRatio.one).trans
      (IntRatio.sub_congr (IntRatio.add_sub_cancel (IntRatio.finite_mul hx hx))
        (IntRatio.equivalent_refl IntRatio.one)))

/-- The constant, linear and quadratic coefficients are exact rational quotients. -/
theorem kappa_jet (x : IntRatio) (hx : x.Finite) :
    Equivalent (kappaJetAt x)
      ⟨kappa x,
        (IntRatio.two.mul x).neg.mul (((fidelityDen x).mul (fidelityDen x)).inv),
        ((IntRatio.three.mul (x.mul x)).sub IntRatio.one).mul
          ((((fidelityDen x).mul (fidelityDen x)).mul (fidelityDen x)).inv)⟩ :=
  let a := fidelityDen x
  let b := IntRatio.two.mul x
  let r := a.inv
  let rSq := r.mul r
  let rCube := rSq.mul r
  have unit := IntRatio.unit_one_add_sq hx
  have invSq := IntRatio.inv_mul unit unit
  have invCube := (IntRatio.inv_mul (IntRatio.unit_mul unit unit) unit).trans
    (IntRatio.mul_congr invSq (IntRatio.equivalent_refl r))
  have move_r : ∀ c : IntRatio, IntRatio.Equivalent (r.mul (c.mul r)) (c.mul rSq) :=
    fun c => (IntRatio.mul_assoc r c r).symm.trans
      ((IntRatio.mul_congr (IntRatio.mul_comm r c) (IntRatio.equivalent_refl r)).trans
        (IntRatio.mul_assoc c r r))
  have linear := (IntRatio.mul_neg r (b.mul r)).trans
    ((IntRatio.neg_congr (move_r b)).trans
      ((IntRatio.neg_mul b rSq).symm.trans (IntRatio.mul_congr
        (IntRatio.equivalent_refl b.neg) invSq.symm)))
  have positive := (IntRatio.mul_congr (IntRatio.equivalent_refl r)
      (IntRatio.mul_mul_mul_comm b r b r)).trans
    ((IntRatio.mul_comm r ((b.mul b).mul rSq)).trans (IntRatio.mul_assoc (b.mul b) rSq r))
  have negative := (IntRatio.mul_congr (IntRatio.equivalent_refl r) (IntRatio.one_mul r)).trans
    ((IntRatio.mul_one rSq).symm.trans
      ((IntRatio.mul_congr (IntRatio.equivalent_refl rSq) (IntRatio.mul_inv unit).symm).trans
        ((IntRatio.mul_assoc rSq a r).symm.trans
          ((IntRatio.mul_congr (IntRatio.mul_comm rSq a) (IntRatio.equivalent_refl r)).trans
            (IntRatio.mul_assoc a rSq r)))))
  have quadratic := (IntRatio.mul_sub r ((b.mul r).mul (b.mul r)) (IntRatio.one.mul r)).trans
    ((IntRatio.sub_congr positive negative).trans
      ((IntRatio.sub_mul (b.mul b) a rCube).symm.trans
        (IntRatio.mul_congr (b_sq_sub_den x hx) invCube.symm)))
  And.intro (IntRatio.equivalent_refl r) (And.intro linear quadratic)

/-- At x = 1, the coefficient triple is (1/2, −1/2, 1/4). -/
theorem kappa_jet_one :
    Equivalent (kappaJetAt IntRatio.one)
      ⟨IntRatio.fraction Int.one Nat.zero.succ,
        IntRatio.fraction Int.one.neg Nat.zero.succ,
        IntRatio.fraction Int.one Nat.zero.succ.succ.succ⟩ :=
  And.intro Eq.refl (And.intro Eq.refl Eq.refl)

end Omega.Jet2
