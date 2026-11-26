import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.MultivariateHensel
import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.Crystalline.CrystallineTests
import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.PeriodRings.ThetaKernel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Almost acyclicity of the structure sheaf for the v-topology (known result; see
Lib.PadicComparison.Descent.AlmostAcyclic).

Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: p-adic tests, their tilts, Witt and completion functors, base change of coefficients.
Locally constant functions on Spec, flatness over Bezout domains, torsion-free tensors, Witt
vectors. -/

noncomputable section

open CategoryTheory Functor CommAlgCat TensorProduct Ideal AdicCompletion WittVector ModuleCat H
variable {C C'} [Category C] [Category C'] {S : Type} [CommRing S] (p) [ThePrime p] (T M : Type)
  [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
  (m : M) (φ : C' ⥤ C) (N : AbFunctor C) (Φ : C ⥤ ModuleCat S)

/-- For a functor Φ to commutative S-algebras, the functor of underlying S-modules. -/
abbrev asModules (Φ : C ⥤ CommAlg S) := Φ ⋙ forget₂ .. ⋙ forget₂ (AlgCat S) (ModuleCat S)

/-- For a module M over the S-algebra T, the functor X ↦ M ⊗_S X from S-modules to T-modules. -/
def tensorWith : ModuleCat.{0} S ⥤ ModuleCat T := .mk _ (ofHom <|
  AlgebraTensorModule.lTensor T M ·.hom)

instance : (tensorWith (S := S) T M).Additive := ⟨Hom.ext (map_add ..)⟩

variable {M} in
/-- For m in M and a functor Φ to S-modules, the natural map of abelian-group-valued coefficient
functors Φ → M ⊗_S Φ sending x to m ⊗ x. -/
def tensorWith.mk : moduleCoeff Φ ⟶ moduleCoeff (Φ ⋙ tensorWith T M) :=
  whiskerRight {app A := AddCommGrpCat.ofHom (TensorProduct.mk S M (Φ A) m).toAddMonoidHom} _

/-- The canonical T-linear map M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ), sending m ⊗ z to the image of
z under x ↦ m ⊗ x. -/
def baseChangeMap n :
  M ⊗[S] H N (moduleCoeff Φ) n →ₗ[T] H N (moduleCoeff (Φ ⋙ tensorWith T M)) n := by
  use (liftAddHom ((pushHom ..).comp (.mk' (tensorWith.mk T · Φ) ?_)) fun (s : S) m ↦
    (congr(push N $(?_) n ·).trans (push_comp ..))).toAddHom,
    fun t x ↦ by induction x <;> simp_all; exact .symm (push_comp ..).symm
  all_goals intros; ext; apply_rules [ULift.ext, add_tmul, smul_tmul]

/-- N has flat base change: M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ) is bijective for all n, all
functors Φ to S-modules and all S-flat M. -/
def FP := ∀ S T M [CommRing S] [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] [Module T M]
  [IsScalarTower S T M] [Module.Flat S M] (Φ : C ⥤ ModuleCat S) n,
  (⇑(baseChangeMap T M N Φ n)).Bijective

variable {Φ}

/-- For a natural map β: Φ → Ψ of functors to S-modules, the induced map of abelian-group-valued
coefficient functors. -/
def coeffMap {Ψ} (β : Φ ⟶ Ψ) : moduleCoeff Φ ⟶ moduleCoeff Ψ := by apply_rules [whiskerRight]

/-- The cohomological comparison datum along a functor φ: C' → C whose coefficient map comes
from a natural transformation Φ∘φ → Φ' of module-valued functors. -/
abbrev Comparison.ofModuleHom {Φ'} (β : φ ⋙ Φ ⟶ Φ') := of (F := moduleCoeff Φ) _ (coeffMap β)

/-- The cohomological comparison datum along a functor φ: C' → C from an abelian-group-valued
functor N to N∘φ, with identity coefficient map. -/
abbrev Comparison.restrict := of φ (𝟙 (φ ⋙ N))

/-- Base change along S → T: the functor B ↦ T ⊗_S B from commutative S-algebras to commutative
T-algebras. -/
def algBaseChange : CommAlg S ⥤ CommAlg T := .mk _ (ofHom <| Algebra.TensorProduct.lTensor T ·.1)

/-- p is not a unit in a non-zero p-complete ring -/
instance not_isUnit_p [Nontrivial S] [IsAdicComplete (span {(p : S)}) S] : Fact ¬IsUnit (p : S) :=
  ⟨zero_ne_one ∘ eq_of_forall_pow_dvd_sub _ ∘ (·.pow · |>.dvd)⟩

variable (S) [Algebra Ainf T]

/-- A cell: a p-adically complete, absolutely integrally closed valuation ring T in which p is
neither zero nor a unit. -/
class IsCell extends IsDomain T, ValuationRing T, IsAdicComplete (span {(p : T)}) T, IsAIC T where
  p_ne_zero : (p : T) ≠ 0

/-- A p-adic test: a non-empty family of cells (`IsCell`) with a ring map from O_C to
their product. -/
structure PadicTest {p} [ThePrime p] where
  Index : Type
  Cell : Index → _
  [nonempty : Nonempty Index]
  [commRing (i) : CommRing (Cell i)]
  [isCell (i) : IsCell p (Cell i)]
  structureMap : OC →+* ∀ i, Cell i

namespace PadicTest

variable {p} (c : PadicTest)

attribute [instance] nonempty commRing isCell

/-- The ring S underlying a p-adic test, namely the product of its family of valuation rings. -/
abbrev ProdRing := ∀ i, c.Cell i

instance : Algebra OC c.ProdRing := c.structureMap.toAlgebra

instance : Category PadicTest := {Hom := (·.ProdRing →ₐ[OC] ·.ProdRing), id c := .id .., comp f :=
  (·.comp f)}

instance : Nontrivial c.ProdRing := Pi.nontrivial_at c.nonempty.some

instance isAdicComplete_prodRing : IsAdicComplete (span {(p : c.ProdRing)}) c.ProdRing := by
  refine {haus' x h := funext (c.isCell · |>.haus _ ?_), prec' f h := (Classical.skolem.1
      (c.isCell · |>.prec' (f · _) ?_)).imp ?_} <;> simp_all [↓smodEq_span_pow_iff_dvd, pi_dvd_iff]

/-- The tilt S^♭ of the ring S of a p-adic test, the inverse limit of S/p along Frobenius. -/
abbrev TiltRing := PreTilt c.ProdRing p

instance : Algebra OFlat c.TiltRing := (tiltMap c.structureMap).toAlgebra

/-- For g in G_p, the endofunctor of p-adic tests that keeps the ring S and precomposes its
structure map O_C → S with the action of g. -/
def twist (g : Gp p) : PadicTest ⥤ PadicTest :=
  .mk (⟨_, _, ·.structureMap.comp (MulSemiringAction.toRingHom _ _ g)⟩) (⟨_, ·.2 ∘' _⟩)

/-- The functor from p-adic tests to commutative O_C-algebras sending a test to its product ring
S with its structure map. -/
def algFunctor : PadicTest ⥤ CommAlg OC := .mk _ ofHom

/-- The functor from p-adic tests to commutative rings sending a test to its underlying product
ring S. -/
abbrev ringFunctor := algFunctor ⋙ forget₂ _ CommRingCat

/-- The functor from p-adic tests to commutative O^♭-algebras sending a test S to its tilt S^♭. -/
def tilt : PadicTest ⥤ CommAlg OFlat := ⟨_, fun f ↦ ofHom ⟨_, (f.comp_algebraMap ▸ tiltMap_comp
  _ _ · |>.symm)⟩, by intro; ext; apply tiltMap_id, by intros; ext; apply tiltMap_comp⟩

end PadicTest

open PadicTest Int PrimeSpectrum Function Module LinearMap Flat Ainf AlgebraTensorModule
  LocallyConstant Nat ZMod IsSMulRegular AlgebraicGeometry.StructureSheaf

/-- The functor sending a commutative S-algebra to its p-adic completion. -/
def algCompletion : CommAlg S ⥤ CommAlg S := by
  refine ⟨_, (ofHom ⟨adicMap (I := span {↑p}) ·.hom.1 (by simp), ?_⟩), ?_, ?_⟩ <;> intros <;>
    (try ext x : 2; cases x using induction_on) <;> apply ext_evalₐ <;> simp

variable {p S}

instance : IsCell p OC := ⟨NeZero.out⟩

instance : Algebra Ainf OFlat := constantCoeff.toAlgebra

instance : Algebra Ainf OC := (fontaineTheta ..).toAlgebra

/-- For a ring S with a map to W(k), by default S = W(k), the functor sending a k-algebra b to
its p-typical Witt vectors W(b), as an S-algebra. -/
def wittFunctor {k} [CommRing k] (S := WittVector p k) [CommRing S] [Algebra S (WittVector p k)] :
  CommAlg k ⥤ CommAlg S := .mk (fun b ↦ @of _ _ _ _ ((WittVector.map b.3.2).comp
  ‹Algebra ..›.2).toAlgebra) fun f ↦ by use WittVector.map f.hom; intro; ext; apply f.1.2

/-- For an A_inf-algebra T, the functor sending an O^♭-algebra b to the p-adic completion of T
⊗_{A_inf} W(b). -/
abbrev periodAlg := wittFunctor (k := OFlat) ⋙ algBaseChange T ⋙ algCompletion T p

/-- For R → O_C, the functor sending an R-scheme X to the functor S ↦ X(S) of its points over R
in p-adic tests. -/
def testPoints {R : CommRingCat} [Algebra R OC] :=
  algPoints R R ⋙ restrictAlong (algFunctor ⋙ restrictAlg ..)

/-- If S is absolutely integrally closed, then for every unit x of S there is a homomorphism χ from
ℚ to Sˣ with χ(1) = x, that is, a compatible system of roots of x. -/
lemma exists_compatible_roots [h : IsAIC S] x : ∃ χ : ℚ →+ Additive Sˣ, χ 1 = x :=
  have := @AddGroup.divisibleByIntOfDivisibleByNat _ _ (divisibleByOfSMulRightSurj (Additive _) _
    fun k y ↦ (@h.exists_pow_eq _ _ _ ⟨k⟩ _).rec (⟨.ofPow _ · k ·, Units.ext ‹_›⟩))
  ((Module.Baer.of_divisible _).extension_property_addMonoidHom (castAddHom ℚ)
    Int.cast_injective (zmultiplesHom _ x)).imp (by simp [AddMonoidHom.ext_int_iff])

variable (M S : _) {S' Λ} [CommRing M] [CommRing S] [CommRing S'] [Algebra M S] [AddCommGroup Λ] {f
  : S →+* S'} {p : _} [ThePrime p]

/-- For an M-algebra S there is a ring map f from the locally constant functions Spec S → M to S
such that, for every prime q, f(x) and x(q) have the same image in the localisation S_q. -/
lemma exists_ringHom_of_locallyConstant : ∃ f : LocallyConstant (PrimeSpectrum S) M →+* S, ∀ x q,
  algebraMap _
  (Localization.AtPrime q.1) (f x) = algebraMap _ _ (x q) := let e := globalSectionsIso S
  ⟨e.2.1.comp (.codRestrict (.pi ((algebraMap M (Localization _)).comp <| evalRingHom ·.1))
  (sectionsSubalgebra ..) fun x ↦ (⟨⟨_, x.2 {x ·.1}⟩, rfl, default, _, 1, (⟨_, congrArg (algebraMap
  ..) ·.2⟩)⟩)), fun _ q ↦ congrArg (·.1 ⟨q, ⟨⟩⟩) (e.inv_hom_id_apply _)⟩

/-- Let f: S → S' be such that for all a, b in S' some idempotent e of S has a ∣ f(e)b and b ∣
(1 − f(e))a. Then pull-back of locally constant Λ-valued functions from Spec S to Spec S' is
onto. -/
lemma locConst_comap_surjective (h : IsComparableRing f) : Surjective (comapAddMonoidHom (Z :=
  Λ) ⟨_, continuous_comap f⟩) := locallyConstant_mem_of_indicator (S := AddMonoidHom.range _) fun a
  y i ↦ (h y (1 - y)).elim fun e ⟨j, k⟩ ↦ ⟨indicator (LocallyConstant.const _ a) (isClopen_iff.2 ⟨e,
  j, rfl⟩), (by grind [dvd_def, i.eq] : f e = y) ▸ rfl⟩

/-- The functor sending a commutative ring S to the 𝔽_p-algebra of locally constant functions
Spec S → 𝔽_p, and a ring map to pullback along the induced map of spectra. -/
def locConstAlg : CommRingCat ⥤ CommAlg (ZMod p) :=
  .mk _ (CommAlgCat.ofHom <| comapₐ (Z := ZMod p) _ ⟨_, continuous_comap ·.hom⟩)

instance : Algebra (ZMod p) OFlat := ZMod.algebra ..

deriving instance Algebra (ZMod p), IsScalarTower (ZMod p) OFlat for @CFlat p _

instance perfectRing_locConstAlg A : PerfectRing (locConstAlg A) p :=
  ⟨by convert bijective_id; exact LocallyConstant.ext fun _ ↦ pow_card _⟩

/-- The element π = ξ mod p of O^♭ = A_inf/p, the zeroth Witt coefficient of ξ. -/
def pFlat := constantCoeff xi

/-- The O^♭-algebra b is perfect and π-torsion-free, where π = ξ mod p (`pFlat`). -/
abbrev IsPerfectTorsionFree (b : CommAlg OFlat) := PerfectRing b p ∧ IsSMulRegular b pFlat

/-- The map f: A → B is surjective, and f(x) = 0 exactly when x is a multiple m·y. -/
def IsReductionMod {R A B} [SMul R A] [Zero B] (m : R) (f : A → B) := Surjective f ∧ Exact (m • ·) f

/-- Let S be a perfect algebra over a domain M of characteristic p. Then the zeroth coordinate
W(S) → S is reduction modulo p, W(S) is p-torsion-free and p-complete, and x lies in p^k W(S)
exactly when its first k coordinates vanish. -/
lemma witt_reduction_spec [IsDomain M] [CharP M p] [PerfectRing S p] : IsReductionMod p
  (@constantCoeff p S _ _) ∧ IsCompleteTorsionFree (WittVector p S) ∧ RingHom.ker (@constantCoeff p
  S ..) = span {↑p} ∧ ∀ k x, (∀ i < k, @coeff p S x i = 0) ↔ ∃ y, p ^ k • y = x := by
  by_cases! Subsingleton S <;> [have : Subsingleton (WittVector p S) := ⟨by cat_disch⟩;
    have := CharP.of_ringHom_of_ne_zero (algebraMap M S) p NeZero.out] <;> use ⟨by tauto, ?_⟩,
    ⟨.of_right_eq_zero_of_smul ?_, {}⟩ <;> simp [mem_span_p_pow_iff_le_coeff_eq_zero, mul_comm,
    Exact, ← mem_span_singleton', nontriviality, ← ker_constantCoeff]
  apply eq_zero_of_p_mul_eq_zero

variable {S M M' L : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup M']
  [Module S M'] [AddCommGroup L] [Module S L] (f : M →ₗ[S] M') {m : ℕ}

lemma pFlat_ne_zero : pFlat ≠ 0 := not_p_dvd_xi ∘ Witt.p_dvd_iff.2

lemma not_isUnit_pFlat : ¬IsUnit pFlat :=
  prime_xi.not_isUnit ∘ Ainf.isUnit_iff_isUnit_constantCoeff.2

lemma IsReductionMod.lTensor (h : IsReductionMod m f) : IsReductionMod m (f.lTensor L) :=
  ⟨lTensor_surjective _ h.1,
  congr(Exact $(map_natCast (End.lTensorAlgHom ..) m) _).mp (lTensor_exact L h.2 h.1)⟩

lemma IsReductionMod.bijective_rTensor (h : IsReductionMod m f) (z : ∀ y : L, m • y = 0) : Bijective
  (f.rTensor L) := ⟨(injective_iff_eq_zero_of_exact (rTensor_exact L (f := m.cast) h.2 h.1)).2
  (ext' (by simp_all [smul_tmul])), rTensor_surjective L h.1⟩

lemma tmul_ext {P F} [AddCommGroup P] [FunLike F (M ⊗[S] L) P] [AddMonoidHomClass F ..] {f g : F}
    (h : ∀ m x, f (m ⊗ₜ x) = g (m ⊗ₜ x) := by tauto) : f = g :=
  DFunLike.ext _ _ (by induction · with simp_all)

instance [IsDomain S] [IsBezout S] [IsTorsionFree S L] : Flat S L :=
  flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)

lemma isTorsionFree_of_dvd_pow [IsDomain S] {π : S} (h : IsSMulRegular L π) (ha : ∀ {t}, t ≠ 0 →
    ∃ n, t ∣ π ^ n) : IsTorsionFree S L := ⟨(by grind [mul_iff, !h.pow, dvd_def, @ha · ·.ne_zero])⟩

lemma isSMulRegular_tensor_of_flat_mod {O : Type} [CommRing O] [Algebra S O] [Module O M']
  [IsScalarTower S O M'] [Flat O M']
  (hO : IsReductionMod m (Algebra.linearMap S O)) (hf : IsReductionMod m f) (hM : IsSMulRegular M m)
  (hN : IsSMulRegular L m) : IsSMulRegular (L ⊗[S] M) m := by
  simp [IsReductionMod, ← cast_smul_eq_nsmul S, IsSMulRegular] at *
  obtain ⟨q, e, t, l⟩ := Finsupp.linearCombination_id_surjective S L, @exact_subtype_ker_map,
   @lTensor_injective_of_exact_of_exact_of_rTensor_injective, @lTensor_preserves_injective_linearMap
  apply congr(⇑$(lTensor_smul_action ..)).subst (t (e _) q hf.2 hf.1 _ (l _ hM))
  simpa [← lTensor_inj_iff_rTensor_inj] using! congr(⇑$(lTensor_comp_cancelBaseChange _ O
    ..)).symm.subst ((cancelBaseChange ..).injective.comp (l _
    (t (f₁ := mul S S m) hO.2 hO.1 (e _) q (lTensor _ hN) (by simp))))
