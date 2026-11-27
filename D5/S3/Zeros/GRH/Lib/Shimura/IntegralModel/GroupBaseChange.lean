/- GID: D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.IntegralModel.GroupBaseChange. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/IntegralModel/GroupBaseChange.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.Frames
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli.CutOutIdeals
import D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme.KernelRing
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdditiveCharBasic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation
(known result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: PEL datum with theta group, Lagrangian and padding; good primes; class identities. Base
change of group schemes with ring action: points, sections, homomorphisms. -/

open CategoryTheory NumberField Submodule MonoidalCategory Over

variable {E : Type} [Field.{0} E] [CMBase E] {m : Type}
  [Fintype.{0} m]

/-- For ξ in E and vectors x, y of finite adeles of E, the finite adele ξ·∑ᵢ ȳᵢxᵢ. -/
noncomputable def xiForm {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {m : Type}
    [Fintype.{0} m] ξ (x y : m → 𝔸f E) := algebraMap E _ ξ * Star.star y ⬝ᵥ x

/-- The integer c of E has a padding to r: there are a₁, …, a_{r−3} spanning O_E over ℤ with c
c̄ + 3 + ∑ a_l ā_l = r. -/
def HasPadding E [Field.{0} E] [NumberField E] [IsCMField E] r c := ∃ a :
    Fin (r - 3) → 𝓞 E, span ℤ (.range a) = ⊤ ∧ Star.star c * c + 3 + ∑ l, Star.star (a l) * a l = r

/-- PEL data: β = 1 − β̄, a level 𝔑 ≠ 0, ξ in E, r ≥ 3, a degree bound i, the group T of odd
order dual to the integral vectors under ψ_f(ξ yᴴx), a self-annihilating L containing the
r-torsion, and paddings of norms to r. -/
structure PEL (E) [Field.{0} E] [CMBase E] where
  (β 𝔑 : 𝓞 E) ξ : E
  (rank r i) (T lagrangian : AddSubgroup (_root_.AdelicTorsion E (Fin rank))) star_beta :
    Star.star β = 1 - β
  three_le_r : 3 ≤ r
  level_ne_zero : 𝔑 ≠ 0
  degree_spec : IsCutDegree T i r (thetaRanks T r) ∧ ∀ j ≤ i, ∀ y, r ^ j • y ∈ T →
    y ∈ torsionBy _ _ 𝔑
  odd_card : Odd (Nat.card T)
  mem_T y : torsionClass y ∈ T ↔ ∀ z, torsionClass z = 0 → ψf E (xiForm ξ y z) = 1
  mem_lagrangian y : torsionClass y ∈ lagrangian ↔ ∀ z, torsionClass z ∈ lagrangian →
    ψf E (xiForm ξ y z) = 1
  torsion_mem_lagrangian s : r • s = 0 → s ∈ lagrangian
  exists_padding : HasPadding E r 1 ∧ HasPadding E r β
  nonempty : Nonempty (Fin rank)
  xi_im_pos_and_re_eq_zero v : 0 < (Φ v ξ).im ∧ (Φ v ξ).re = 0
  emb_beta_eq_of_ne : ∀ v ≠ v₀, Φ v β.val = Φ v₀ (Star.star β.val)
  emb_star_beta_ne : Φ v₀ (Star.star β.val) ≠ Φ v₀ β.val

/-- The index set {0, …, rk − 1} of the entries of vectors in E^rk, where rk is the rank in the
data D. -/
abbrev PEL.Index (D : PEL E) := Fin D.rank

/-- The level module: the O_E-submodule of (𝔸_f / Ô)ⁿ of elements killed by the integer 𝔑 of E. -/
noncomputable def PEL.levelTorsion (D : PEL E) := torsionBy _ (_root_.AdelicTorsion E D.Index) D.𝔑

variable (D : PEL E) {S : AlgebraicGeometry.Scheme} {S' : AlgebraicGeometry.Scheme} {b : S' ⟶ S}
  {O : Type} [CommRing O] {A' : CategoryTheory.Over S'} {A : CategoryTheory.Over S} [@AddObj S' A']
  [@AddObj S A] [ModuleObj O A'] [ModuleObj O A] {p : (CategoryTheory.Over.map b).obj A' ⟶ A}
  (h : IsGroupBaseChange (A := A) (B := A') b p)

lemma PEL.T_le_levelTorsion : D.T ≤
  D.levelTorsion.toAddSubgroup := by simpa using! D.degree_spec.2 0

attribute [instance] PEL.nonempty

instance PEL.instFiniteSubtypeTor'FinRkMemAddSubgroupT :
    Finite D.T := by grind [odd_card, Nat.card_pos_iff]

/-- The ideal w of O_E contains neither r nor |T|; for some prime p and integer b, w and a
nonzero prime other than w contain p and β − b, β − b is coprime to β̄ − b, and 𝔑 to w·(p,
β̄ − b). -/
def PEL.IsGoodAt w := (↑D.r ∉ w ∧ ↑(Nat.card D.T) ∉ w) ∧ ∃ p b, Nat.Prime p ∧ ↑p ∈ w ∧
  D.β - (b : ℤ) ∈ w ∧ IsCoprime (D.β - b) (Star.star D.β - b) ∧ Ideal.span {D.𝔑} ⊔ w * .span
  {↑p, Star.star D.β - b} = ⊤ ∧ ∃ v : FinPlace E, v ≠ w ∧ ↑p ∈ v.1 ∧ D.β - b ∈ v.1

/-- The class c in Pic A satisfies the parallelogram law `Pic.ParallelogramLaw` and, for all
T-points x, y of A, ⟨βx, y⟩ = ⟨x, (1 − β)y⟩ and y^*c = ⟨βy, y⟩ + 0^*c, with the pairing
`Pic.pairing`. -/
def PEL.HasClassLaws [ModuleObj (𝓞 E) A] (c : Pic _) := c.ParallelogramLaw ∧ ∀ ⦃T⦄ (x y : T ⟶ A),
  c.pairing (D.β • x) y =
  c.pairing x ((1 - D.β) • y) ∧ c.atPoint y = c.pairing (D.β • y) y + c.atPoint 0

/-- For an O-compatible base change p : A' → A and an S'-scheme T, the O-linear bijection x ↦
p∘x from T-points of A' over S' to T-points of A over S. -/
@[simps! -isSimp apply] noncomputable def IsGroupBaseChange.pointEquiv {T} := LinearEquiv.mk (@h.2
  T).mk' (homMk <| h.1.lift _ _ ·.w) (by have := @h.1.hom_ext; cat_disch) (by cat_disch)

/-- For a base change A' of A along b : S' → S, the O-linear map pulling sections of A over S
back to sections of A' over S'. -/
noncomputable def IsGroupBaseChange.pullSection : (𝟙_ _ ⟶ A) →ₗ[O] 𝟙_ _ ⟶ A' :=
  h.pointEquiv.symm.1 ∘ₗ ⟨⟨_, comp_add (SemiCartesianMonoidalCategory.toUnit _)⟩, by simp⟩

@[reassoc] lemma IsGroupBaseChange.pullSection_comp z : (h.pullSection z).left ≫ p.left =
  b ≫ z.left := by simp [pullSection, pointEquiv]

/-- For a base change p : A' → A, a line bundle N on A and a T-point x of A', the pull-back of
the class of p*N along x equals the pull-back of the class of N along the point p∘x of A. -/
lemma IsGroupBaseChange.atPoint_picClass_pull {T ι N} x : @Pic.atPoint _ A' T (N.pull p.1).picClass
  x = (@LineBundle.picClass _ ι N).atPoint (h.pointEquiv x) := rfl

include h

lemma IsGroupBaseChange.smul_id_comp (m : O) : (m • 𝟙 A').left ≫ p.left = p.left ≫ (m • 𝟙 A).left :=
    congr($(h.2.2 ..).1).trans (by simp [← comp_left])

lemma IsGroupBaseChange.nsmul_id_comp (m : ℕ) : (m • 𝟙 A').left ≫ p.left =
  p.left ≫ (m • 𝟙 A).left := mod_cast h.smul_id_comp m

lemma IsGroupBaseChange.translation_comp z : (_root_.translation (h.pullSection z)).left ≫ p.left =
  p.left ≫ (_root_.translation z).left :=
  congr($(h.2.1 ..).1).trans (by simp [← comp_left, ← h.pointEquiv_apply, pullSection])

/-- Let A', B' be base changes of A, B along b, c : S' → S, and F a natural map from c- to
b-structures. An O-linear homomorphism χ : A → B induces one A' → B', acting on points
through F and χ, compatible with pulled-back sections. -/
lemma IsGroupBaseChange.exists_hom_baseChange {c B' B} [AddObj B'] [AddObj B] [ModuleObj O B']
  [ModuleObj O B] {q} (k : IsGroupBaseChange c q) (F : Over.map c ⟶ _) χ [IsLinear χ] : ∃ ψ :
  _ ⟶ B', (∀ {T} u, k.pointEquiv (u ≫ ψ) = F.1 T ≫ h.pointEquiv u ≫ χ) ∧ IsLinear ψ ∧ ∀ z,
  h.pullSection z ≫ ψ = k.pullSection (z ≫ (χ : _ ⟶ B)) := (k.pointEquiv.surjective
  (F.1 _ ≫ p ≫ χ)).imp fun _ _ ↦ have G := by simp_all [pointEquiv]
  ⟨G, by use {isAdditive_of_universal ?_ with smul_id_comp := ?_} <;> simp [pullSection,
    ← k.pointEquiv.apply_eq_iff_eq, G, ← G (𝟙 _)]⟩
