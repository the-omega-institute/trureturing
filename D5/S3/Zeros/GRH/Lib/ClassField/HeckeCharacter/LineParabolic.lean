/- GID: D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LineParabolic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LineParabolic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.HeckeCharacter.LineParabolic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/HeckeCharacter/LineParabolic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.ExtensionByZero
import D5.S3.Zeros.GRH.Lib.Weil.GaussSum.ShearInvariance
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeL.AutCharLFunction
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.Petersson
import D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms.AdaptedHom
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Tamely ramified characters, local components and residues; data and theta integrals
named. Equivariant maps from local data to automorphic functions; real sign classes. Coordinates on
radical and Levi factor of an isotropic line stabiliser. -/

noncomputable section

open NumberField Pi Space SemilocalField IsLocalRing Classical WithZero MulChar Matrix

section

variable (E : Type) [Field E] [CMType E] [WeilData E] {F n n' : Type}
  [Fintype n] [Fintype n'] {s : n → ℤˣ} {s' : n' → ℤˣ} [SemilocalField F] (A : Set (FinPlace E))
  (π : 𝔸f E →+* F) (S : Space E n s) (T : Space E n' s') (P : Finset (FinPlace E))

/-- A character ν of [U(1)] of positive weight e with tame part ψ non-trivial exactly on a
non-empty finite set S of places disjoint from its conjugate. -/
structure SplitTameChar e where
  (ν : AutChar E) (ψ) hasWeight : ν.HasWeight e ψ
  S : Finset (FinPlace E)
  nonempty : S.Nonempty
  star_notMem : ∀ w ∈ S, star w ∉ S
  ne_one_iff w : ψ w ≠ 1 ↔ w ∈ S
  weight_pos v : 0 < e v

attribute [instance] SplitTameChar.hasWeight

variable {E}

/-- π reads the components at A: A is disjoint from its conjugate, π is continuous with a
continuous additive section σ, σ(πx) being the A-part of x, and π(x) ∈ O iff x is integral
at A. -/
structure ReadsAt {E : Type} [Field E] [NumberField E] [IsCMField E] {F : Type} [SemilocalField F]
    (A : Set (FinPlace E)) (π : 𝔸f E →+* F) where
  disjoint_star : A.IsConjDisjoint
  mem_iff x : π x ∈ O ↔ idem A * x ∈ Ô E
  exists_section : Continuous π ∧ ∃ σ : _ →+ _, Continuous σ ∧ (∀ y, π (σ y) = y) ∧ ∀ x, σ (π x) =
    idem A * x

/-- The multiplicative character of ∏_{w∈P} E_w that is t ↦ ξ(t)|t|^{k/2} on invertible
elements, t read as an idele, and 0 on the others. -/
def localChar (ξ : HeckeChar E) (k : ℤ) := ofUnitHom (∏ i : P, (ξ.finPart.comp (locIdele i) *
  .toHomUnits ⟨⟨(√‖·.1‖), by simp⟩, by simp⟩ ^ k).comp (Units.map (evalMonoidHom _ i)))

variable {μ : NumberField.InfinitePlace E → ℤ} {P} {A} {π} (𝔠 : SplitTameChar E μ) (a : AutChar E)
  (b : AutChar E) (f : 𝒮 (S.hom T))
  (v : Heisenberg.IsVacuum.Model (realHeis (realSigns E (homSigns s s')))) (Ψ : _ → ℂ) (i : P)

omit [WeilData E] in
lemma ReadsAt.star : ReadsAt A π →
  ReadsAt (Star.star ⁻¹' A) (π.comp (starRingEnd _)) | ⟨d, m, c, σ, c', k⟩ => ⟨by
  grind, by grind [idem_mul_mem_Ô, v_star_apply, star_star, starRingEnd_apply, π.comp_apply], c.comp
  continuous_star, .comp (starRingEnd (𝔸f E)) σ, c'.star, by simp [k, star_idem, starRingEnd_apply]⟩

omit [WeilData E] in
lemma SplitTameChar.readsAt : ReadsAt 𝔠.S (evalPlaces 𝔠.S) :=
  ⟨by grind [star_notMem], by simp [mem_O_locProd, idem_mul_mem_Ô], by fun_prop, adeleOfLocal 𝔠.S,
  continuous_adeleOfLocal _, evalPlaces_adeleOfLocal _, adeleOfLocal_evalPlaces _⟩

attribute [local simp] forall_and inv_apply_eq_inv' apply_eq_zero_iff mem_Ô mem_O_locProd funext_iff
  Finset.prod_eq_zero_iff

/-- The ring map from the integers of ∏_{w∈P} E_w to the residue field at the place i of P. -/
def residueAt {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} (i : P) :
    O (F := LocProd P) →+* ResField i.1 :=
  (residue _).comp ((evalRingHom ..).restrict _ _ (by aesop))

/-- The vector of 𝒮(Hom(S,T)) named, in the model at the places A, by the function x ↦ Ψ(πx) of
finite adelic matrices, applied to the vacuum. -/
abbrev namedVector (_ : ReadsAt A π) := (S.hom T).name A (Ψ <| vecToMat · |>.map π) (vacElem _)

/-- The datum in 𝒮(Hom(S,T)) with real part v, the function Ψ of the components at A, read
through π, and the vacuum at the other finite places. -/
abbrev localDatum (r : ReadsAt A π) := integrated _ v (delta% namedVector S T Ψ r)

/-- The function g ↦ ∫ θ^{S,T}_{a,b}(f)(g,h) dh on U(S), the integral taken over [U(T)]. -/
def thetaIntegral g := ∫ h, pairTheta S T a b f (g, h) ∂T.quotMeasure

omit [WeilData E]

lemma evalPlaces_mem_O : ∀ x ∈ Ô E, evalPlaces P x ∈ O := by aesop

@[simp] lemma isUnit_iff_residueAt_ne_zero {u} : IsUnit u ↔ ∀ i : P, residueAt i u ≠ 0 := by
  simp [residueAt, ResField, Subtype.ext_iff, isUnit_iff_exists_inv, skolem]; rfl

@[local simp] lemma residueAt_eq_zero {u} : residueAt i u = 0 ↔ Valued.v (u.1 i) < 1 :=
  residue_eq_iff_valuation_sub_lt_one.trans (by simp)

lemma isIntegralUnit_iff_v_eq_one {t : LocProd P} : IsIntegralUnit t ↔ ∀ i, Valued.v (t i) = 1 := by
  simpa [le_antisymm_iff, ← isIntegralUnit_iff_isUnit] using
    exists_congr (isUnit_iff_residueAt_ne_zero (u := ⟨t, ·⟩))

namespace SplitTameChar

/-- The character t ↦ ν(t/t̄) of ∏_{w∈S} E_w, t read as an idele supported on S, extended by 0
to non-invertible elements. -/
abbrev χ := localChar 𝔠.S 𝔠.ν.baseChange 0

lemma localChar_apply_of_isUnit k u (hu : IsUnit u) : localChar 𝔠.S 𝔠.ν.baseChange k u.1 = ∏ i,
  𝔠.ψ _ (residueAt i u) := by
  erw [ofUnitHom_coe _ (hu.map O.subtype).unit, ← isIntegralUnit_iff_isUnit,
    isIntegralUnit_iff_v_eq_one] at *
  simp [FinitePlace.norm_def, *]; congr!
  apply_rules [𝔠.hasWeight.baseChange_finPart_locIdele] <;> grind [SplitTameChar]

lemma nu_apply_of_integral u (hu : u.1.2 ∈ Ô E) : 𝔠.ν.1 u = (∏ v, u.1.1 v ^ μ v) * 𝔠.χ (evalPlaces _
  u.1.2) := by erw [𝔠.hasWeight.2, finprod_tame_eq_prod_reduceU1 _ (𝔠.ne_one_iff · |>.not_right.2),
  ← 𝔠.S.prod_attach, localChar_apply_of_isUnit _ _ ⟨_, _⟩ (isUnit_iff_residueAt_ne_zero.2 fun _ ↦
  (isUnit_reduceAt_unitary ..).ne_zero)] <;> aesop

/-- The residue rings at `S` and their characters. -/
instance tameLocalChar (k := 0) : TameLocalChar (localChar 𝔠.S 𝔠.ν.baseChange k) :=
  ⟨_, .pi residueAt, ⟨∏ i, (𝔠.ψ _)⁻¹.comp
  (evalMonoidHom _ i), by simp [isUnit_iff]⟩, ⟨fun r ↦ by simpa [skolem] using! (residue_surjective
  <| r ·), by simp [ϖ, ← lt_mul_exp_iff_le]⟩, fun a h ↦ let ⟨i, _⟩ := Function.ne_iff.1 h
  (MulChar.ne_one_iff.1 ((𝔠.ne_one_iff i).2 i.2)).elim fun x _ ↦
    ⟨(mulSingle i x - 1) / a, by simp_all [Finset.prod_eq_single i]⟩, by simp_all
  [invOnUnits, ↓isIntegralUnit_iff_isUnit, localChar_apply_of_isUnit, @eq_comm ℂ 0]⟩

end SplitTameChar

end

variable {E : Type} [Field E] [CMType E] {n b m : Type}
  [Fintype n] [Fintype m] {s : n → ℤˣ} {r : m → _} {μ : NumberField.InfinitePlace E → ℤ}
  (𝔠 : SplitTameChar E μ) (x : Matrix n b (𝔸 E))

/-- The ring map sending an adele to its components at the ramified places S of 𝔠. -/
def componentsAt := (evalPlaces 𝔠.S).comp (.snd .. : 𝔸 E →+* _)

/-- The homomorphism G_f → GL_n(∏_{w∈P} E_w) sending an element to its components at P. -/
def atPlaces {E : Type} [Field E] [NumberField E] [IsCMField E] {n : Type} [Fintype n]
    P : Gf E n →* GL n (@LocProd E _ _ P) :=
  (GeneralLinearGroup.map (evalPlaces P)).comp (U 1).subtype

/-- 𝒟 maps a GL_m-stable space M of Schwartz–Bruhat functions at S, supported on matrices with a
left inverse, to automorphic functions on
U(X), equivariantly at S up to ρ(det), with values fixed by K₀ away from S. -/
structure IsEquivariantLift X (ρ : MulChar (LocProd 𝔠.S) ℂ) (M :
  Submodule ℂ (Matrix m b (LocProd 𝔠.S) → ℂ)) (𝒟 : (_ → ℂ) →ₗ[ℂ] G E r → ℂ) where
  le_schwartzBruhat : M ≤ schwartzBruhat HasLeftInv
  isAutFunction {Ψ} : Ψ ∈ M → _root_.IsAutFunction X (𝒟 Ψ)
  law_on {Ψ} : Ψ ∈ M → ∀ g ∈ Gf.supportedOn m 𝔠.S, let Φ := (Ψ <| (atPlaces 𝔠.S g).1 * ·); Φ ∈ M ∧
      ∀ x, 𝒟 Φ (x * g) = ρ (atPlaces _ g).1.det * 𝒟 Ψ x
  law_off : ∀ᵉ (Ψ ∈ M) (k ∈ Kf .. ⊓ Gf.trivialOn m 𝔠.S) (x), 𝒟 Ψ (x * (1, k)) = 𝒟 Ψ x

section

variable {E : Type} [Field E] [NumberField E] {n b : Type} [Fintype b] (x : Matrix n b (𝔸 E))

/-- The complex matrix of components of the adelic matrix x at the infinite place v. -/
abbrev atRealPlace v := x.map (·.1 v)

/-- At every infinite place, the component of T has the form c* diag(t) c for some complex
square matrix c. -/
def RepresentedBy t (T : Matrix b b (𝔸 E)) := ∀ v, ∃ c, cᴴ * signMatrix t * c = atRealPlace T v

end

lemma gram_map_real v : (atRealPlace x v)ᴴ * signMatrix s * atRealPlace x v = atRealPlace
  (xᴴ * stdForm E s * x) v := by simp [atRealPlace, ← funext (evalInf_apply _), stdForm]; rfl

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s : n → ℤˣ}
  {t : m → ℤˣ} {V' : Space E m t} {V : Space E n s} (D : V'.Splitting V Unit)

/-- The element n(x⁻¹c, b + b*) of the radical of the stabiliser of the line, for q = (c,b) and
x the adelic frame of V. -/
abbrev lineRadical (q : Matrix n _ (𝔸 E) × _) :=
  D.radicalElt (V.x⁻¹.1 * q.1) (toAdele (2 : E) • q.2)

/-- The homomorphism from ideles × U(V)(𝔸) to the Levi subgroup sending (a,g) to the element
acting by a⁻¹ on the line k and by g on V. -/
def lineLevi :=
  D.levi.comp (((Matrix.GeneralLinearGroup.scalar _).comp invMonoidHom).prodMap (.id _))
