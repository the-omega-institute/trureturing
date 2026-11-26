import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Duality.Contraction
import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.HodgeTate.GenericFibreTests
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: Tests with affine spaces of lifts modulo ξ², contraction class and its powers. -/

noncomputable section

section

open CategoryTheory TensorProduct Functor Ideal PadicTest MonoidalCategory Quotient Submodule ZMod
variable {p} [ThePrime p] (c : PadicTest) (I :
  Ideal c.GenericRing) {S X} [CommRing S] [AddCommMonoid X]

instance (F : ModuleCat S ⥤ ModuleCat S) [F.Additive] : (moduleCoeff F).Additive :=
  instAdditiveComp ..

/-- For submodules κ(d, f) of X indexed by maps of tests f: c → d, the submodule of y such that,
for some a ∈ I, y ∈ κ(d, f) whenever f makes 1 − a a unit. -/
def PadicTest.nearZeros [Module S X] (κ : ∀ {d}, (c ⟶ d) → Submodule S X) : Submodule S X :=
  ⟨⟨⟨{y | ∃ a ∈ I, ∀ d f, IsUnit (mapGeneric f (1 - a)) → y ∈ @κ d f}, fun ⟨a, _⟩ ⟨b, _⟩ ↦
  ⟨1 - (1 - a) * (1 - b), by simp_all [← eq_zero_iff_mem, add_mem]⟩⟩, by aesop⟩, by aesop⟩

variable (Ω) [CommRing.{0} Ω] [Algebra Ω ℂ_[p]]

/-- The functor sending a p-adic test with ring R to R[1/p], a test over Ω with algebra
structure through Ω → ℂ_p. -/
def genericTestOver : PadicTest ⥤ TestOver Ω :=
  ObjectProperty.lift _ (genericAlg ⋙ restrictAlg ..) (·.isTest.localization)

end

open AddCommGrpCat thickeningOver CategoryTheory CliffordAlgebra ExteriorAlgebra HodgeTest TotalH

set_option backward.isDefEq.respectTransparency false

/-- A pair (S, M) of a p-adic test S and the free module M = T^n over T = S[1/p], given by S and
the rank n. -/
structure HodgeTatePair {p k} [Field k] [EmbeddedInQpBar p k] where (test : PadicTest) (rank : ℕ)

seal thickeningOver PadicTest.genericAlg

variable {p k} [Field k] [EmbeddedInQpBar p k] (X : HodgeTatePair) (t : k)

/-- For a pair (S,M), the k-algebra T = S[1/p]. -/
abbrev HodgeTatePair.GenericRing := genericOver X.test

@[simps] instance HodgeTatePair.instCategory :
  Category HodgeTatePair := by refine' @.mk _ {
  Hom X Y := Σ f : X.test ⟶ Y.test,
    (Fin X.rank → X.GenericRing) →ₛₗ[((genericOver.map f).hom : X.GenericRing →+* Y.GenericRing)]
    Y.GenericRing × (Fin Y.rank → Y.GenericRing), id _ := ⟨𝟙 _, ⟨(0, ·), by simp⟩, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, ⟨fun m ↦ (genericOver.map g.1 (f.2 m).1, 0) + g.2 (f.2 m).2, by simp [
    add_add_add_comm]⟩, by simp⟩} .. <;> intros <;> exact congr(⟨_, $(by ext <;> simp [add_assoc])⟩)

/-- The forgetful functor from pairs (S,M) to p-adic tests, sending (f,φ) to f. -/
def HodgeTatePair.toTest : HodgeTatePair ⥤ PadicTest := .mk test (·.1)

/-- The functor (S,M) ↦ (T,M) to the tests of Hodge cohomology, sending (f,φ) to the ring map
induced by f and the second component of φ. -/
def HodgeTatePair.toHodgeTest : HodgeTatePair ⥤ HodgeTest k := by refine ⟨(⟨·.GenericRing, _⟩),
  (⟨_, .snd .. ∘ₛₗ ·.2⟩), ?_, ?_⟩ <;> intros <;> apply HodgeTest.hom_ext <;> aesop

/-- For a pair (S,M), the k-algebra B_S ×_T (T ⊕ M), with B_S as in `thickeningOver` and T ⊕ M the
trivial square-zero extension. -/
abbrev HodgeTatePair.PairRing :=
  (thickeningOver.proj X.test).1.pullback (TrivSqZeroExt.fstHom k _ (Fin X.rank → X.GenericRing))

/-- The functor (S,M) ↦ B_{S,M} = B_S ×_T (T ⊕ M) to k-algebras; a morphism (f,(φ₀,φ₁)) acts by
(b,m) ↦ (f(b) + μφ₀(m), φ₁(m)). -/
def HodgeTatePair.pairAlg :
  HodgeTatePair ⥤ CommAlg k := by refine ⟨(.of k ·.PairRing), @fun X _ f ↦ CommAlgCat.ofHom (by
  have e (x : X.PairRing) := x.2 ▸ thickeningOver.proj.naturality_apply f.1 x.1.1
  refine' .codRestrict (.prod { toFun (x :
    X.PairRing) := thickeningOver.map f.1 x.1.1 + thickeningOver.mulMu _ (f.2 x.1.2.snd).1, .. }
    (((toHodgeTest ⋙ sqZeroExt).map f).1.comp (.pullbackSnd ..))) _ fun x ↦ (map_add ..).trans
    ((add_eq_left.2 (proj_mulMu ..)).trans (e x)) <;> as_aux_lemma => intros; simp [*, add_mul,
    mul_add, ← mulMu_proj_mul _, proj_mulMu, TrivSqZeroExt.algebraMap_eq_inl',
    mul_comm (mulMu _ _)] <;> abel), ?_, ?_⟩ <;> intros <;> ext : 4 <;>
  (try show _ = thickeningOver.map _ (_ + _) + _) <;> simp [← map_mulMu, add_assoc] <;> rfl

/-- The natural projection of k-algebras B_S ×_T (T ⊕ M) → T ⊕ M. -/
def HodgeTatePair.toSqZero :
  pairAlg ⟶ toHodgeTest ⋙ sqZeroExt where app _ := CommAlgCat.ofHom (.pullbackSnd ..)

/-- The natural map of k-algebras B_S ×_T (T ⊕ M) → T. -/
def HodgeTatePair.toGeneric : pairAlg ⟶ toTest ⋙ genericOver := toSqZero ≫ {app _ := baseProj _}

/-- The functor sending a pair (S,M) to the abelian group ⋀_T M, the restriction of the
coefficients of Hodge cohomology. -/
abbrev HodgeTatePair.formCoeff := toHodgeTest ⋙ hodgeCoeff

/-- The coefficient functor `genericCoeff` on p-adic tests, restricted to pairs along (S,M) ↦
S. -/
abbrev HodgeTatePair.scalarCoeff := toTest ⋙ genericCoeff

instance HodgeTatePair.instActF : CoeffAction k scalarCoeff :=
  ⟨.comp ⟨(restrictAlong _).mapEnd _, rfl, by tauto⟩ CoeffAction.act⟩

attribute [local simp] Algebra.algebraMap_eq_smul_one mul_add

/-- The cocycle from Λ = ⋀M to itself that assigns to a morphism (f,(φ₀,φ₁)) the contraction
with φ₀. -/
def HodgeTatePair.contractionCocycle : Cocycle formCoeff formCoeff :=
  ⟨(AddCommGrpCat.uliftFunctor.map <| ofHom <| contraction ·.2 |>.toAddMonoidHom), fun f
  g ↦ have h x : contraction _ x = exteriorMapSnd g.2 (contraction _ x) +
    contraction _ (exteriorMapSnd f.2 x) ∧ exteriorMapSnd (f ≫ g).2 x = exteriorMapSnd g.2
        (exteriorMapSnd f.2 x) := by induction x using left_induction <;> simp_all <;> module
  ext (congrArg _ <| h ·.1 |>.1)⟩

/-- For h ≥ 0, the element of total Ext(Λ,F) that is the h-th Yoneda power of the class of the
contraction cocycle, followed by the projection ε to degree zero. -/
def HodgeTatePair.contractionPow : ℕ → TotalH formCoeff scalarCoeff
  | 0 => .homClass ⟨fun X ↦ AddCommGrpCat.uliftFunctor.map (ofHom (@algebraMapInv _ _ (_ →
    X.GenericRing) ..).toAddMonoidHom), fun _ _ f ↦ ext (congr(⟨$(algebraMapInv_exteriorMap
    (toHodgeTest.map f).2 ·.1)⟩))⟩ | h + 1 => .comp contractionCocycle.cohomClass (contractionPow h)

/-- The natural map Λ ⊗ Λ → Λ given by the wedge product in ⋀_T M. -/
abbrev HodgeTatePair.wedgePairing : abTensor formCoeff formCoeff ⟶ formCoeff :=
  toHodgeTest.whiskerLeft exteriorAlg.mulPairing

lemma HodgeTatePair.act_comp_contractionPow h : comp (.homClass
  (toHodgeTest.whiskerLeft (End.asHom (CoeffAction.act t))))
  (contractionPow h) = t • contractionPow h := by
  induction' h with _ e; simp [smul_eq_comp, contractionPow, ← homClass_comp]; congr 1 with X
  exact congr(⟨$((@algebraMapInv X.GenericRing ..).map_smul_of_tower t _)⟩)
  rw [contractionPow, ← TotalH.comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), e,
    comp_smul]
  intro _ _ f; ext; exact congr(⟨$(by simpa using! (contraction f.2).2 (t • 1) _)⟩)

lemma HodgeTatePair.scaleModule_comp_contractionPow h : pullbackAlong
  (toHodgeTest.whiskerLeft (scaleModule t _)) (contractionPow h) = t ^ h • contractionPow h := by
  induction' h with _ e
  simp [contractionPow, ← homClass_comp]; congr with _
    x; exact congr(⟨$(algebraMapInv_exteriorMap (scaleModule t (𝟭 _) _).2 x.1)⟩)
  rw [contractionPow, ← TotalH.comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..),
    ← homClass_comp_homClass_comp, act_comp_contractionPow, comp_smul, e, smul_smul, comp_smul,
    pow_succ']
  intro _ _ f; have := f.2.2 (t • 1)
  refine ext (congrArg _ <| (fun x ↦ ?_ : ∀ x, contraction f.2 (exteriorMap (t • .id) x) =
    t • exteriorMap (t • .id) (contraction f.2 x) ∧ exteriorMapSnd f.2 (exteriorMap (t • .id) x) =
    exteriorMap (t • .id) (exteriorMapSnd f.2 x)) ·.1 |>.1)
  induction x using left_induction <;> simp_all [-LinearMap.map_smul_of_tower]; module
