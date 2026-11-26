import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdeleIdempotent
import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ValuedMatrix
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Adelic unitary similitude group, torsion module, frames of hermitian forms, reflections,
signatures. -/

noncomputable section

open NumberField ConjAct Matrix GeneralLinearGroup ComplexOrder Pointwise


/-- A choice of one complex embedding Φ_v for each infinite place v of E, together with a base
place v₀; E has at least two infinite places. -/
class CMBase E [Field E] extends CMType E, Nontrivial (InfinitePlace E) where v₀ : InfinitePlace E

export CMBase (v₀)

section

variable (E : Type) [Field.{0} E] [NumberField E] (n : Type) [Fintype.{0} n] [IsCMField E]

/-- The torsion O_E-module (𝔸_f / Ô)ⁿ: n-tuples of finite adeles of E modulo integral ones, an
adelic model of (E / O_E)ⁿ. -/
def AdelicTorsion := _ ⧸ Submodule.pi .univ fun _ : n ↦ Subalgebra.toSubmodule (R := 𝓞 E)
  ⟨(Ô E).1, (algebraMap_mem_Ô.2 ·.2)⟩ deriving AddCommGroup, Module (𝓞 E)


variable {E n} (β : Matrix n n E) (x : GL n (𝔸f E))

/-- x in GL_n of the finite adeles of E is a frame for the matrix β over E: xᴴβx is a scalar
matrix ε·1 with ε a unit of the profinite integers Ẑ. -/
def IsFrameFor := ∃ ε : (Ô ℚ)ˣ, xᴴ * β.map (algebraMap ..) * x.1 = finAdeleIncl ℚ E ε • 1

/-- The rational number c is positive and x is a frame for the scalar matrix c·1: c·xᴴx = ε·1
for some unit ε of Ẑ. -/
@[simp] abbrev IsScalarFrame (c : ℚ) := 0 < c ∧ IsFrameFor ((c : E) • 1) x

/-- If x is a frame for the form β, then for c in E and g in GL_n of the finite adeles, xg is a
frame for cβ if and only if g is a frame for the scalar form c·1. -/
lemma IsFrameFor.mul_iff {c : E} {g} : IsFrameFor β x → (IsFrameFor (c • β) (x * g) ↔ IsFrameFor
  (c • 1) g) | ⟨ε, h⟩ => (Equiv.mulLeft ε⁻¹).exists_congr' fun _ ↦ by
               simpa [map_smul', gram_mul, -conjTranspose_mul, h, mul_smul, smul_comm c] using
                 ((ε.isUnit.map (Ô ℚ).subtype).map _).smul_left_cancel

variable (E n)

/-- The number |n| times the number of infinite places of E; for a CM field E this is
|n|·[E⁺:ℚ], with E⁺ the maximal real subfield. -/
def abelianDim := Fintype.card n * Fintype.card (InfinitePlace E)

/-- The group of unitary similitudes: the g in GL_n of the finite adeles of E such that gᴴg is a
scalar finite idele of ℚ. -/
def GU := Subgroup.ofDiv {g : GL n (𝔸f E) | ∃ c, IsScalarFrame g c} ⟨1, 1,
  rfl, 1, by simp⟩ fun _ ⟨c, _, h⟩ _ ⟨d, b, k⟩ ↦
  ⟨d⁻¹ * c, by bound, by simpa [mul_smul, h.mul_iff, ← k.mul_iff, b.ne'] using ⟨1, by simp⟩⟩

/-- The monoid of similitudes g in `GU` whose inverse has integral entries, that is,
which enlarge the standard lattice. -/
def GUPlus := @Submonoid.copy (GL n _) _ (_ ⊓ ((Ô E).matrix.1.1.comap (Units.coeHom _))⁻¹)
  {g ∈ GU .. | ∀ i j, g⁻¹ i j ∈ Ô E} rfl

end

variable {E : Type} [Field.{0} E] [CMBase E] {n : Type} [Fintype.{0} n] {β : Matrix n n E}
  (x : GL n (𝔸f E)) (z : GL n E) (J : Matrix n n ℂ)

/-- The O_E-linear map sending a vector of finite adeles to its class in (𝔸_f / Ô)ⁿ. -/
def torsionClass {E : Type} [Field.{0} E] [NumberField E] {n : Type} :
    (n → 𝔸f E) →ₗ[𝓞 E] AdelicTorsion E n := Submodule.mkQ _

instance : Algebra E ℂ := (Φ v₀).toAlgebra

/-- The diagonal embedding of GL_n(E) in GL_n of the finite adeles of E. -/
abbrev toFinGL {E : Type} [Field.{0} E] [NumberField E] {n : Type} [Fintype.{0} n] :
    GL n E →* GL n (𝔸f E) := map (algebraMap ..)

/-- J is a reflection: J = u wᵀ − 1 with w·u = 2, so J is 1 on the line of u and −1 on the
kernel of w. -/
def IsReflection := ∃ u w, w ⬝ᵥ u = 2 ∧ J = vecMulVec u w - 1

/-- x is a frame for β (`IsFrameFor`), Φ_w(β) is positive definite for every infinite place w ≠ v₀,
and Φ_{v₀}(β)·J is positive definite. -/
abbrev IsSignedFrameFor β := IsFrameFor β x ∧ ∀ w, (β.map (Φ w) * ite (w = v₀) J 1).PosDef

/-- Some matrix β over E has x as a frame, Φ_w(β) positive definite for w ≠ v₀ and Φ_{v₀}(β)·J
positive definite (`IsSignedFrameFor`). -/
def IsSignedFrame := ∃ β, IsSignedFrameFor x J β

/-- The conjugate Φ_{v₀}(z)·J·Φ_{v₀}(z)⁻¹ of the complex matrix J by z in GL_n(E), taken through the
embedding Φ v₀. -/
def ratConj := toConjAct (z.map (Φ v₀)) • J

lemma IsReflection.conj {J} (z : GL n ℂ) : IsReflection J →
  IsReflection (z.1 * J * z⁻¹.1) | ⟨u, w, _⟩ => ⟨z *ᵥ u, w ᵥ* z⁻¹, by
  simp [dotProduct_mulVec, mul_sub, sub_mul, mul_vecMulVec, vecMulVec_mul, *]⟩

lemma IsFrameFor.conj_iff : IsFrameFor (zᴴ * β * z.1) x ↔
  IsFrameFor β (toFinGL z * x) := by simp [IsFrameFor, ↓map_conjTranspose_mul_mul, mul_assoc]

/-- If `IsSignedFrame` holds for (x, J), then for z in GL_n(E) and a unitary similitude g in
`GU` it holds for (zxg, zJz⁻¹), with z acting on J through the embedding Φ v₀. -/
lemma IsSignedFrame.mul {x J} (h : IsSignedFrame x J) z {g} : g ∈ GU E n →
  IsSignedFrame (toFinGL z * x * g) (ratConj z J) | ⟨c, a, k⟩ => h.rec fun _ ⟨h, H⟩ ↦
  ⟨_, ((IsFrameFor.conj_iff _ z⁻¹).2 (by simpa)).mul_iff.2 k, fun w ↦ by
  split <;> simpa [ratConj, units_smul_def, mul_assoc, ↓map_smul', ↓map_conjTranspose_mul_mul, *,
    ↓← val_map_apply] using! (z⁻¹.map _).isUnit.posDef_star_left_conjugate_iff.2 ((H w).smul a)⟩
