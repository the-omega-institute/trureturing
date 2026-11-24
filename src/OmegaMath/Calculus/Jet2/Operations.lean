module
prelude
public import OmegaMath.Calculus.Jet2.Basic

/-!
Omega original.

Inversion by the terminating geometric polynomial and composition at zero shift.
-/

noncomputable section

@[expose] public section

namespace Omega.Jet2

/-- For a = a₀(1 + u), use a₀⁻¹(1 - u + u²) with u³ = 0. -/
def inv (a : Jet2) : Jet2 :=
  let r := a.j0.inv
  let u := a.j1.mul r
  let v := a.j2.mul r
  ⟨r, r.mul u.neg, r.mul ((u.mul u).sub v)⟩

theorem inv_congr {a b : Jet2} (h : Equivalent a b) : Equivalent a.inv b.inv :=
  have constant := IntRatio.inv_congr h.left
  have linear := IntRatio.mul_congr h.right.left constant
  have quadratic := IntRatio.mul_congr h.right.right constant
  And.intro constant
    (And.intro (IntRatio.mul_congr constant (IntRatio.neg_congr linear))
      (IntRatio.mul_congr constant (IntRatio.sub_congr (IntRatio.mul_congr linear linear) quadratic)))

theorem mul_inv {a : Jet2} (h₀ : a.j0.Unit) (h₁ : a.j1.Finite) (h₂ : a.j2.Finite) :
    Equivalent (a.mul a.inv) one :=
  let r := a.j0.inv
  let u := a.j1.mul r
  let v := a.j2.mul r
  let s := u.mul u
  have hr := IntRatio.finite_inv h₀
  have hu := IntRatio.finite_mul h₁ hr
  have hv := IntRatio.finite_mul h₂ hr
  have hs := IntRatio.finite_mul hu hu
  have constant := IntRatio.mul_inv h₀
  have reduce : ∀ t : IntRatio, IntRatio.Equivalent (a.j0.mul (r.mul t)) t :=
    fun t => (IntRatio.mul_assoc a.j0 r t).symm.trans
      ((IntRatio.mul_congr constant (IntRatio.equivalent_refl t)).trans (IntRatio.one_mul t))
  have linear := (IntRatio.add_congr (reduce u.neg) (IntRatio.equivalent_refl u)).trans
    (IntRatio.add_left_neg hu)
  have middle := (IntRatio.mul_assoc a.j1 r u.neg).symm.trans (IntRatio.mul_neg u u)
  have cancel := (IntRatio.add_right_comm s v.neg s.neg).trans
    ((IntRatio.add_congr (IntRatio.add_right_neg hs) (IntRatio.equivalent_refl v.neg)).trans
      (IntRatio.zero_add v.neg))
  have quadratic := (IntRatio.add_congr
      (IntRatio.add_congr (reduce (s.sub v)) middle) (IntRatio.equivalent_refl v)).trans
    ((IntRatio.add_congr cancel (IntRatio.equivalent_refl v)).trans (IntRatio.add_left_neg hv))
  And.intro constant (And.intro linear quadratic)

/-- Evaluate the outer polynomial in the inner jet, truncating at degree two. -/
def compose (g f : Jet2) : Jet2 :=
  ((const g.j0).add ((const g.j1).mul f)).add ((const g.j2).mul (f.mul f))

/-- The first derivative at the expansion point is the linear coefficient. -/
def first (f : Jet2) : IntRatio := f.j1

/-- The second derivative at the expansion point is twice the quadratic coefficient. -/
def second (f : Jet2) : IntRatio := IntRatio.two.mul f.j2

private theorem finite_const_mul (c : IntRatio) (f : Jet2) (hf : f.Finite) :
    Equivalent ((const c).mul f) ⟨c.mul f.j0, c.mul f.j1, c.mul f.j2⟩ :=
  And.intro (IntRatio.equivalent_refl (c.mul f.j0))
    (And.intro
      ((IntRatio.add_congr (IntRatio.equivalent_refl (c.mul f.j1)) (IntRatio.zero_mul hf.left)).trans
        (IntRatio.add_zero (c.mul f.j1)))
      ((IntRatio.add_congr
        ((IntRatio.add_congr (IntRatio.equivalent_refl (c.mul f.j2))
          (IntRatio.zero_mul hf.right.left)).trans (IntRatio.add_zero (c.mul f.j2)))
        (IntRatio.zero_mul hf.left)).trans (IntRatio.add_zero (c.mul f.j2))))

private theorem square_zero_shift {f : Jet2} (hf : f.Finite)
    (h : IntRatio.Equivalent f.j0 IntRatio.zero) :
    Equivalent (f.mul f) ⟨IntRatio.zero, IntRatio.zero, f.j1.mul f.j1⟩ :=
  have left : ∀ (t : IntRatio), t.Finite → IntRatio.Equivalent (f.j0.mul t) IntRatio.zero :=
    fun t ht => (IntRatio.mul_congr h (IntRatio.equivalent_refl t)).trans (IntRatio.zero_mul ht)
  have right : ∀ (t : IntRatio), t.Finite → IntRatio.Equivalent (t.mul f.j0) IntRatio.zero :=
    fun t ht => (IntRatio.mul_comm t f.j0).trans (left t ht)
  And.intro (left f.j0 hf.left)
    (And.intro
      ((IntRatio.add_congr (left f.j1 hf.right.left) (right f.j1 hf.right.left)).trans
        (IntRatio.add_zero IntRatio.zero))
      ((IntRatio.add_congr
        ((IntRatio.add_congr (left f.j2 hf.right.right) (IntRatio.equivalent_refl (f.j1.mul f.j1))).trans
          (IntRatio.zero_add (f.j1.mul f.j1)))
        (right f.j2 hf.right.right)).trans (IntRatio.add_zero (f.j1.mul f.j1))))

theorem compose_zero_shift {g f : Jet2} (hg : g.Finite) (hf : f.Finite)
    (h : IntRatio.Equivalent f.j0 IntRatio.zero) :
    Equivalent (compose g f)
      ⟨g.j0, g.j1.mul f.j1, (g.j1.mul f.j2).add (g.j2.mul (f.j1.mul f.j1))⟩ :=
  have linear := finite_const_mul g.j1 f hf
  have square := square_zero_shift hf h
  have quadratic : Equivalent ((const g.j2).mul (f.mul f))
      ⟨g.j2.mul IntRatio.zero, g.j2.mul IntRatio.zero, g.j2.mul (f.j1.mul f.j1)⟩ :=
    (finite_const_mul g.j2 (f.mul f) (finite_mul hf hf)).trans
    (And.intro
      (IntRatio.mul_congr (IntRatio.equivalent_refl g.j2) square.left)
      (And.intro
        (IntRatio.mul_congr (IntRatio.equivalent_refl g.j2) square.right.left)
        (IntRatio.mul_congr (IntRatio.equivalent_refl g.j2) square.right.right)))
  have linearConstant := (IntRatio.mul_congr (IntRatio.equivalent_refl g.j1) h).trans
    (IntRatio.mul_zero hg.right.left)
  have constant := (IntRatio.add_congr
      (IntRatio.add_congr (IntRatio.equivalent_refl g.j0) (linear.left.trans linearConstant))
      (quadratic.left.trans (IntRatio.mul_zero hg.right.right))).trans
    ((IntRatio.add_congr (IntRatio.add_zero g.j0) (IntRatio.equivalent_refl IntRatio.zero)).trans
      (IntRatio.add_zero g.j0))
  have degreeOne := (IntRatio.add_congr
      (IntRatio.add_congr (IntRatio.equivalent_refl IntRatio.zero) linear.right.left)
      (quadratic.right.left.trans (IntRatio.mul_zero hg.right.right))).trans
    ((IntRatio.add_congr (IntRatio.zero_add (g.j1.mul f.j1))
      (IntRatio.equivalent_refl IntRatio.zero)).trans (IntRatio.add_zero (g.j1.mul f.j1)))
  have degreeTwo := IntRatio.add_congr
    ((IntRatio.add_congr (IntRatio.equivalent_refl IntRatio.zero) linear.right.right).trans
      (IntRatio.zero_add (g.j1.mul f.j2))) quadratic.right.right
  And.intro constant (And.intro degreeOne degreeTwo)

/-- The two chain rules evaluated at the expansion point, where the inner jet has zero shift. -/
private theorem chain_rule_finite {g f : Jet2} (hg : g.Finite) (hf : f.Finite)
    (h : IntRatio.Equivalent f.j0 IntRatio.zero) :
    And (IntRatio.Equivalent (compose g f).first (g.first.mul f.first))
      (IntRatio.Equivalent (compose g f).second
        ((g.second.mul (f.first.mul f.first)).add (g.first.mul f.second))) :=
  have coeff := (compose_zero_shift hg hf h).right
  have distribute := IntRatio.mul_add IntRatio.two (g.j1.mul f.j2) (g.j2.mul (f.j1.mul f.j1))
  have inner := (IntRatio.mul_assoc IntRatio.two g.j1 f.j2).symm.trans
    ((IntRatio.mul_congr (IntRatio.mul_comm IntRatio.two g.j1)
      (IntRatio.equivalent_refl f.j2)).trans (IntRatio.mul_assoc g.j1 IntRatio.two f.j2))
  have outer := (IntRatio.mul_assoc IntRatio.two g.j2 (f.j1.mul f.j1)).symm
  And.intro coeff.left
    ((IntRatio.mul_congr (IntRatio.equivalent_refl IntRatio.two) coeff.right).trans
      (distribute.trans ((IntRatio.add_congr inner outer).trans
        (IntRatio.add_comm (g.first.mul f.second) (g.second.mul (f.first.mul f.first))))))

/-- At zero inner shift the derivative identities depend only on the outer derivative coefficients. -/
theorem chain_rule {g f : Jet2} (hg₁ : g.j1.Finite) (hg₂ : g.j2.Finite) (hf : f.Finite)
    (h : IntRatio.Equivalent f.j0 IntRatio.zero) :
    And (IntRatio.Equivalent (compose g f).first (g.first.mul f.first))
      (IntRatio.Equivalent (compose g f).second
        ((g.second.mul (f.first.mul f.first)).add (g.first.mul f.second))) :=
  chain_rule_finite (g := ⟨IntRatio.zero, g.j1, g.j2⟩)
    (And.intro True.intro (And.intro hg₁ hg₂)) hf h

end Omega.Jet2
