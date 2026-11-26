import GRH.Lib.ClassField.HeckeL.EulerProduct
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Unitary Hecke characters, characters of U(1), base change, weight and tame part. -/

noncomputable section


variable (E : Type*) [Field E] [CMType E] (G) [Monoid G]
  [TopologicalSpace G]

@[simp] lemma circleChar_inv_apply (χ : G →ₜ* Circle) x : χ⁻¹ x = (χ x)⁻¹ := rfl

/-- For a map f from a topological monoid G to the adeles of E, the group of continuous
circle-valued characters of G trivial wherever f(x) lies in E. -/
def charsTrivialOnRat (f : G → 𝔸 E) : Subgroup (G →ₜ* Circle) :=
  ⟨⟨⟨{χ | ∀ x, f x ∈ toAdele.range → χ x = 1}, by simp; grind⟩, by simp⟩, by simp⟩

/-- The group of unitary Hecke characters of E: continuous circle-valued characters of the idele
group trivial on principal ideles. -/
abbrev HeckeChar := ↥(charsTrivialOnRat E _ Units.val)

/-- The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of the CM
field E, trivial on elements coming from E. -/
abbrev AutChar := ↥(charsTrivialOnRat E (unitary _) Subtype.val)

variable {E} {R} [CommMonoid R] [StarMul R] [TopologicalSpace R] [ContinuousMul R]
  [ContinuousStar R]

/-- The homomorphism sending a unitary Hecke character of E to its restriction to the finite
ideles, with values in ℂ^×. -/
def HeckeChar.finPart : HeckeChar E →* (𝔸f E)ˣ →* ℂˣ :=
  .mk' (Circle.toUnits.comp <| ·.1.1.comp finIdeleIncl) (by aesop)

/-- The value of the Hecke character χ at the local idele given by the chosen uniformiser at the
finite place w. -/
def HeckeChar.atUnif (χ : HeckeChar E) w := (χ.finPart (locIdele w (uniformizer w))).1

/-- The continuous homomorphism x ↦ x/x̄ from the units of a commutative topological monoid R
with involution to the elements u with uū = 1. -/
def divStar : Rˣ →ₜ* unitary R := ⟨.mk' (fun x ↦ ⟨x * star _,
  (x.mul_inv_mem_unitary (star x)).2 (by simp [mul_comm])⟩) (by simp; grind), by fun_prop⟩

lemma coe_divStar (x : Rˣ) : (divStar x).1 = x * star ↑x⁻¹ := rfl

/-- Base change: the homomorphism sending a character μ of U(1)(𝔸), trivial on rational points,
to the Hecke character x ↦ μ(x/x̄) of E. -/
@[simps! -isSimp] def AutChar.baseChange : AutChar E →* HeckeChar E := .mk' (fun μ ↦
  ⟨μ.1.comp divStar, fun x ⟨y, h⟩ ↦ μ.2 _ ⟨y / star y, (star x).eq_mul_inv_iff_mul_eq.2 (by
    simp [← h, ← map_mul, div_mul_cancel_of_imp])⟩⟩) (by tauto)

/-- μ has weight e and tame part ψ: almost all residue characters ψ_w are trivial, and μ(u) =
∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part. -/
class AutChar.HasWeight (μ : AutChar E) (e : outParam (_ → ℤ))
    (ψ : outParam (∀ w : FinPlace E, MulChar (ResField w) ℂ)) where
  finite_ramified : {w | ψ w ≠ 1}.Finite
  apply_eq u h : μ.1 u = (∏ v, u.1.1 v ^ e v) * ∏ᶠ w, ψ w (reduceAt w ⟨u.1.2, h⟩)
