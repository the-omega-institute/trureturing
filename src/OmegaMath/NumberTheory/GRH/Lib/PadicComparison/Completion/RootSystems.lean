import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.PeriodRings.BdR
import OmegaMath.NumberTheory.GRH.Lib.Cohomology.ProperBaseChange.ValuativeDensity
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Derived completeness for a principal ideal, with Nakayama, finiteness and
completed base change. Only a principal ideal, modules and Ext groups are treated here, and
completeness is the bijectivity of x_n - a x_(n+1) on sequences. Base change is for modules of
finite rank over a discrete valuation ring, where bounded torsion is shown by hand. Source: Stacks
Project 091N, 091P, 0G1U, 09BA, 0CQY; B. Bhatt, Torsion completions are bounded, JPAA (2019); L.
Positselski, Contraadjusted modules, contramodules, and reduced cotorsion modules, arXiv 1605.03934.

This file: Derived completeness: Nakayama, retracts, cohomology, comparison mod a, completed base
change. Tilting preserves products of two p-adic tests; product-preserving functors keep bijective
pairs. Period pairs; period sheaf on p-adic tests is additive; p♭ kills coefficients modulo p.
Functor of root systems with generator acting through roots of unity. -/

noncomputable section

section


open CoeffAction CategoryTheory Function Ideal TensorProduct Functor ModuleCat ULift H Finset Fact
variable {C C'} [Category C] [Category C'] {S} [CommRing S] {N G : AbFunctor C} {N' G' : AbFunctor
  C'} {φ} {α : N' ⟶ φ ⋙ N} {Φ : C ⥤ ModuleCat S} {Φ'} {β : φ ⋙ Φ ⟶ Φ'} {a : S} {q : moduleCoeff Φ ⟶
  G} {p} [ThePrime p] {B} [CommRing B] [Algebra S B] {W} [CommRing W] {π : W} {X E Y F : Type*}
  [Algebra W S] [AddCommGroup X] [Module W X] [AddCommGroup E] [Module W E] [AddCommGroup Y]

variable (π X) in
/-- The W-module X is π-complete: the map (x_n) ↦ (x_n − π x_{n+1}) on sequences in X is
bijective. -/
abbrev IsDerivedComplete := Bijective (shiftDiff X π)

lemma IsDerivedComplete.of_isAdicComplete (_ : IsAdicComplete (span {π}) X) :
  IsDerivedComplete π X := ⟨out, out⟩

lemma IsDerivedComplete.exists_eq_of_approx (hD : IsDerivedComplete π X) (hF :
  IsDerivedComplete π E) (f : E →ₗ[W] X) (g : F → X) (h : ∀ x, ∃ n y, g x = f n +
  π • g y) x : ∃ n, f n = g x := mem_range_of_approx (s := ⟨hF.2⟩) (i := ⟨hD.1⟩) f (by simp) g h x

lemma IsDerivedComplete.pi {ι} (h : IsDerivedComplete π X) : IsDerivedComplete π (ι → X) :=
  (swap_bijective.comp h.comp_left).comp swap_bijective

attribute [local simp] shiftDiff smul_eq_push smul_sub funext_iff

/-- If E is π-complete and linear maps a: E → X, b: X → E have ab = π^m, then X is π-complete. -/
lemma IsDerivedComplete.of_retract (hF : IsDerivedComplete π E) m (a : E →ₗ[W] X) (b :
  X →ₗ[W] E) (h : ∀ x, a (b x) = π ^ m • x) :
  IsDerivedComplete π X := let g (y u : ℕ → _) j := ∑ i ∈ range m, π ^ i • y (j + i) + a (u (j + m))
  have t x : g (shiftDiff _ π x) (b ∘ x) = x := by
    simp_all [g, smul_smul, ← pow_succ, add_assoc, sum_range_sub' _]
  by use fun x y e ↦ t x ▸ t y ▸ congrArg₂ g e (hF.1 (by simpa using congr(b ∘ $e))), fun y ↦
    (hF.2 (b ∘ y)).imp' (g y) fun u e ↦ .trans (by simp [g, ← e, smul_sum]; grind [smul_comm]) (t y)

lemma IsDerivedComplete.congr (e : E ≃ₗ[W] X) (h : IsDerivedComplete π E) : IsDerivedComplete π X :=
  h.of_retract 0 e e.symm (by simp)

/-- Let W be a discrete valuation ring with uniformiser π, S a W-algebra, a the image of π. If W and
the W-module X are π-complete, S is a-complete and linearly independent subsets of X are finite,
then S ⊗_W X is a-complete (`IsDerivedComplete`). -/
lemma IsDerivedComplete.baseChange [IsDomain W] [IsDiscreteValuationRing W] (h :
  Irreducible π) (hD : IsDerivedComplete π X) (hW : IsDerivedComplete π W) (hS :
  IsDerivedComplete (algebraMap W S π) S) (hf : Module.rank W X < .aleph0) : IsDerivedComplete
  (algebraMap W S π) (S ⊗[W] X) := have ⟨s, hs, hs'⟩ := exists_maximal_linearIndepOn W id
  have ⟨_⟩ := Cardinal.lt_aleph0_iff_fintype.1 (hs.cardinal_le_rank.trans_lt hf)
  let τ := Fintype.linearCombination W _
  have ⟨m, r, H⟩ : ∃ j r, ∀ y, ∃ z, π ^ j • (r + π ^ j • (y + π • z)) ∈ τ.range := by
    by_contra! y; choose y hy using y
    let t := (Nat.fold · (fun j _ s ↦ s + π ^ j • y j s) 0)
    have ⟨u, hu⟩ := hD.2 fun j ↦ y j (t j)
    have ⟨a, o, ha⟩ := dite _ (fun _ ↦ ⟨1, by aesop⟩) (hs' (u 0))
    obtain ⟨n, c, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible o h
    use hy n (t n) (u n.succ) (by simpa [τ, ← congrFun hu, mul_smul, ← (by
      induction · <;> simp [t, ← congrFun hu, *]; module : ∀ j, u 0 = t j + π ^ j • u j)] using ha)
  .of_retract (hS.pi.congr (piScalarRight ..).symm) (m + m) (τ.baseChange S) (.baseChange _
    (.codRestrictOfInjective (π ^ (m + m) • 1) τ hs.fintypeLinearCombination_injective (id
    (hD.exists_eq_of_approx hW.pi τ _
    fun y ↦ by choose z u e using H; use u y - u 0, z 0 - z y; simp [e]; module
    )))) (by induction · <;> simp_all [← map_pow])

/-- If every value of the functor Φ to S-modules is a-complete (`IsDerivedComplete`), then the
cohomology H^n(N, Φ) is a-complete for every N and every degree n. -/
lemma IsDerivedComplete.cohomology (h : ∀ A, IsDerivedComplete a (Φ A)) N n :
  IsDerivedComplete a (_root_.H N (moduleCoeff Φ) n) := (Comparison.bijective_iff_of_comm_sq (by
  simp [← push_comp]; use (fun _ ↦ congr($((pushHom ..).map_sub ..) ·).symm))
  (pi_bijective ..) (pi_bijective ..)).1 (push_bijective_of_isIso
  (isoOfAppBijective (piAbFunctor.lift (_ - _)) (h · |>.congr moduleEquiv.symm)).isIso_hom _)

/-- The sequence 0 → Φ → Φ → G → 0 of coefficient functors, formed by multiplication by a and by
q, is short exact. -/
abbrev ModShortExact (a : S) (q : moduleCoeff Φ ⟶ G) := ∃ w,
  (ShortComplex.mk (End.asHom (act a)) q w).ShortExact

/-- Let q: Φ → F be a natural additive map and m a natural number. If each Φ(A) has no m-torsion
and each q_A is onto with kernel mΦ(A), then 0 → Φ → Φ → F → 0, formed by m and q, is exact. -/
lemma modShortExact_of_isReductionMod {F} {q : Φ ⋙ forget₂ _ _ ⟶ F} {m : ℕ} (h : ∀ A,
  IsSMulRegular (Φ A) m ∧ IsReductionMod m (q A)) : ModShortExact ↑m (whiskerRight q _) := by
  simp [IsSMulRegular, IsReductionMod, forall_and, ← Nat.cast_smul_eq_nsmul S] at h
  exact ⟨_, (shortExact_of_app (α := whiskerRight ((m : S) • 𝟙 Φ) _) (g := q) h.1 h.2.2
    h.2.1).2.map_of_exact ((whiskeringRight ..).1 AddCommGrpCat.uliftFunctor)⟩

lemma ModShortExact.exists_smul_eq_of_push_eq_zero (h : ModShortExact a q) {n} x :
  push N q n x = 0 → ∃ y, a • y = x := x.covariant_sequence_exact₂ N h.2

/-- Let Φ, Φ' be a-torsion-free with quotients G, G' by a, and β: Φ∘φ → Φ' induce γ. Assume all
H^n(N', Φ') are a-complete, and H^n(N, Φ) too whenever the comparison's kernel is
a-divisible. If the comparison by γ is bijective, so is that by β.

Known result: Derived completeness for a principal ideal: Nakayama, finiteness, completed base
change. -/
lemma Comparison.IsBijective.of_mod {q'} {γ : _ ⟶ G'} (h : ModShortExact a q) (h' :
  ModShortExact a q') (w : coeffMap β ≫ q' = φ.whiskerLeft q ≫ γ) (d : ∀ n,
  Surjective (a • · : (pullₗ β α n).ker → _) → IsDerivedComplete a (H N (moduleCoeff Φ) n))
  (d' : ∀ n, IsDerivedComplete a (H N' (moduleCoeff Φ') n)) (k : (of φ γ).IsBijective α) :
  (ofModuleHom φ β).IsBijective α := have c := (pull_hom_covariant h.2 h'.2 ⟨_, _, _,
    .symm (by ext; apply_rules [up_inj.2, LinearMap.map_smul]), w⟩ α)
  have i n := (fun v ↦ And.intro (d n v) (.of_ker _ ((d n v).exists_eq_of_approx (d' n) 0
    (↑) (⟨0, v · |>.imp (by aesop)⟩) ⟨·, ·⟩ |>.choose_spec.symm))) (by simpa
    [Surjective] using! ((c.rotate.exists_preimage · (k n).1) (n.casesOn (by tauto) (k · |>.2)) 0))
  (⟨i · |>.2, (d' _).exists_eq_of_approx (i _).1 (pullₗ ..) _ (c.exists_preimage_mod_f (i _).2 · _
    ((k _).2 _).choose_spec |>.imp (by tauto))⟩)

lemma IsCompleteTorsionFree.isDerivedComplete (h : IsCompleteTorsionFree B) :
  IsDerivedComplete (p : S) B := .of_isAdicComplete (isAdicComplete_over_base h.2)

lemma IsCompleteTorsionFree.isSMulRegular_natCast (h : IsCompleteTorsionFree B) :
  IsSMulRegular B (p : S) := fun _ _ e ↦ h.1 (mod_cast e)

open AdicCompletion Submodule.Quotient LinearMap IsScalarTower Comparison LinearEquiv

/-- The map j: X → E is bijective modulo every p^k: each y is some j(x) modulo p^k E, and j(x) ∈
p^k E implies x ∈ p^k X. -/
abbrev IsBijOnCompletion (p : ℕ) (j : X →ₗ[W] E) := Bijective (map (span {↑p}) j)

section

omit [ThePrime p]

lemma IsBijOnCompletion.of_dvd_sub_of_pow_dvd {C} [CommRing C] [Algebra S C] (κ : B →ₐ[S] C) (h :
  ∀ y, ∃ x, ↑p ∣ y - κ x) (k : ∀
  n x, (p : C) ^ n ∣ κ x → (p : B) ^ n ∣ x) : IsBijOnCompletion p κ.toLinearMap := by
  use fun _ _ e ↦ AdicCompletion.ext fun n ↦ Injective.of_ker
    (κ.toLinearMap.reduceModIdeal (span {(p : S)} ^ n)) ?_ (congrArg (·.1 n) e),
    map_surjective_of_mkQ_comp_surjective ?_ <;> rintro ⟨⟩ <;> simp_all [quot_mk_eq_mk,
    Submodule.Quotient.eq, span_singleton_pow, mem_span_singleton, dvd_sub_comm]

lemma isBijOnCompletion_completion :
  IsBijOnCompletion p (toAlgHom S B (PadicCompletion B p)).toLinearMap :=
  .of_dvd_sub_of_pow_dvd _ (by simpa using! exists_approx · 1) fun _ _ ↦ pow_dvd_iff.1

/-- Let the W-linear map j: X → E be bijective modulo every power of p, and let the W-module Y
be p-adically complete. Then every W-linear map X → Y extends uniquely along j to a W-linear
map E → Y. -/
lemma IsBijOnCompletion.linearMap_comp_bijective {j : X →ₗ[W] E} (h :
  IsBijOnCompletion p j) [Module W Y] [IsAdicComplete (span {(p : W)}) Y] :
  Bijective (· ∘ₗ j : (E →ₗ[W] Y) → _) := bijective_iff_has_inverse.2 ⟨fun g ↦ (ofLinearEquiv
  ..).symm.1 ∘ₗ (AdicCompletion.map _ g ∘ₗ (ofBijective _ h).symm.1).restrictScalars _ ∘ₗ of .., by
  constructor <;> intro <;> ext <;> simp [← map_of, ← AdicCompletion.map_comp_apply, symm_apply_eq]⟩

/-- If an additive map q on the p-adic completion of a ring B is onto with kernel the multiples
of p, the same holds for its composite with the natural map from B. -/
lemma IsReductionMod.comp_algebraMap {q : PadicCompletion B p →+ X} (h : IsReductionMod p q) :
    IsReductionMod p (q.comp (algebraMap B _).toAddMonoidHom) := ⟨h.1.forall.2
  (exists_approx · 1 |>.imp (by simp_all [dvd_def, sub_eq_iff_eq_add, IsReductionMod, Exact])),
  (by simpa [h.2 _, dvd_def, eq_comm] using @pow_dvd_iff _ _ ↑p 1 ·)⟩

end

/-- Let W (a DVR, uniformiser p), flat S, and values of Θ, X be p-torsion-free, p-complete; N of
flat base change; j: S⊗_W Θ → X bijective mod p. If each H^n(N,Θ) has finite rank once ker
H^n(j) is p-divisible, all H^n(j) are bijective.

Known result: Derived completeness for a principal ideal: Nakayama, finiteness, completed base
change. -/
lemma FP.isBijective_of_isReductionMod {Θ : C ⥤ CommAlg W} (hN : FP N) (hW : IsCompleteTorsionFree
  W) (hS : IsCompleteTorsionFree S) (hΘ : ∀ A, IsCompleteTorsionFree (Θ.obj A))
  [IsDomain W] [IsDiscreteValuationRing W] [Module.Flat W S] (h : Irreducible (p : W)) {X} (j : 𝟭
  _ ⋙ asModules Θ ⋙ tensorWith S S ⟶ asModules X) (hf : ∀ n, Surjective ((p : S) • · :
  (pullₗ j (𝟙 N) n).ker → _) → Module.rank W (H N (moduleCoeff (asModules Θ)) n) < .aleph0) (hX :
  ∀ A, IsCompleteTorsionFree (X.obj A)) (hj : ∀ A {Y : Type} [AddCommGroup Y] (q : _ →+ Y),
  IsReductionMod p q → IsReductionMod p (q ∘ j.app A)) : (ofModuleHom _ j).IsBijective (𝟙 N) := by
  let q := (asModules X).whiskerLeft ({app _ := ↟(Submodule.mkQ _)} :
    𝟭 _ ⟶ .mk _ (ofHom <| QuotSMulTop.map ↑p ·.1))
  have E {A} : IsReductionMod p (q A).1.toAddMonoidHom := ⟨Quot.exists_rep, by
    simpa [← Nat.cast_smul_eq_nsmul S] using! exact_lsmul_mkQ_smul_top _ _⟩
  use .of_mod (q := coeffMap (j ≫ q)) (q' := coeffMap q) (modShortExact_of_isReductionMod fun A ↦
    ⟨fun _ _ e ↦ (hΘ A).isSMulRegular_natCast.lTensor S (mod_cast e), hj A _ E⟩)
    (modShortExact_of_isReductionMod (⟨hX · |>.1, E⟩)) rfl (.congr (.ofBijective _ (hN ..)) <| by
    simpa using IsDerivedComplete.baseChange h (.cohomology (hΘ · |>.isDerivedComplete) ..)
      hW.isDerivedComplete (mod_cast hS.isDerivedComplete) <| hf · ·)
    (.cohomology (hX · |>.isDerivedComplete) _) (IsCohomEquiv.of_isIso _).bij

variable (S p)

/-- The natural transformation from the identity functor on commutative S-algebras to the p-adic
completion functor, given by the canonical map from B to its completion. -/
def algCompletion.of : 𝟭 _ ⟶ algCompletion S p :=
  ⟨fun _ ↦ CommAlgCat.ofHom (toAlgHom ..), by delta algCompletion; aesop⟩

/-- The functor sending an S-module to its p-adic completion. -/
def moduleCompletion : ModuleCat S ⥤ ModuleCat S :=
  .mk _ (ofHom <| .restrictScalars _ <| map (span {↑p}) ·.1)

instance : (moduleCompletion S p).Additive := ⟨hom_ext (map_ext'' _ rfl)⟩

/-- For commutative S-algebras B, the p-adic completion of the S-module B is naturally
isomorphic to the S-module underlying the p-adic completion of the algebra B. -/
def moduleCompletionIso : asModules (𝟭 _) ⋙ moduleCompletion S p ≅ asModules (algCompletion S p) :=
  isoOfAppBijective (whiskerRight (whiskerRight (algCompletion.of ..) _) _)
  (isBijOnCompletion_completion (B := ·)) ≪≫ .symm (NatIso.ofComponents fun _ ↦
  (@ofLinearEquiv _ _ _ _ _ _ (isAdicComplete_over_base _root_.isAdicComplete)).toModuleIso)

end

open CategoryTheory Limits PadicTest Perfection Equiv Function Algebra TensorProduct TimesBNat
  PreTilt SingleObj

/-- If S-linear maps f : X → Y and g : X → Z give a bijection X → Y × Z, and U from S-modules to
sets preserves finite products, then U(X) → U(Y) × U(Z) is bijective. -/
lemma Function.Bijective.map_prod {S} [Ring S] {X Y Z : ModuleCat S} {f : X ⟶ Y}
  {g : X ⟶ Z} (b : Bijective fun x ↦ (f x, g x)) (U : _ ⥤ Type*) [PreservesFiniteProducts U] :
  Bijective fun x ↦ (U.map f x, U.map g x) := ((mapIsLimitOfPreservesOfIsLimit U _ _
  ((Y.binaryProductLimitCone Z).2.ofPointIso (i := by rwa [ConcreteCategory.isIso_iff_bijective]
  ))).conePointUniqueUpToIso (Types.binaryProductLimit ..)).toEquiv.bijective

/-- The functor sending a p-adic test S to its tilt S^♭, as an O^♭-module, preserves binary products
of tests. -/
lemma bijective_prod_tilt {p} [ThePrime p] {c d d' : PadicTest} (f : c ⟶ d) (g : c ⟶ d') (b :
  Bijective fun x ↦ (f.1 x, g.1 x)) : Bijective fun x ↦
  ((asModules tilt).map f x, (asModules _).map g x) := ((quotientMulEquiv
  ..).bijective_comp _).1 ((((ofBijective _ b.comp_left).trans (arrowProdEquivProdArrow
  ..)).subtypeEquiv (by simp [← b.1.eq_iff, forall_and])).trans (subtypeProdEquivProd.trans
  ((quotientMulEquiv ..).1.prodCongr (quotientMulEquiv ..).1))).bijective

section

variable (p S) [CommRing S] (K) [CommRing K] [Algebra S K] [ThePrime p] [Algebra Ainf S] {Ψ}

/-- The A_inf-algebra S is p-torsion-free and p-adically complete, p divides the image of ξ in
S, and the image of τ in the S-algebra K is a unit. -/
structure IsPeriodRingPair extends isCompleteTorsionFree : IsCompleteTorsionFree S where
  dvd_xi : ↑p ∣ algebraMap _ S xi
  isUnit_tau : IsUnit (algebraMap S K (algebraMap _ S tau))

variable {p S}

lemma isPeriodRingPair_OC : IsPeriodRingPair p OC ℂ_[p] := ⟨⟨.of_ne_zero NeZero.out, {}⟩,
  theta_xi ▸ by simp, by simp [RingHom.algebraMap_toAlgebra]⟩

/-- If Ψ is isomorphic to c ↦ K ⊗_S (S ⊗_{A_inf} W(c^♭))^ on p-adic tests, then
`HasPartitions` holds: tests can be cut along idempotents e ≠ 1, and Ψ turns products of
two tests into products. -/
lemma hasPartitions_periodAlg (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) :
  HasPartitions ringFunctor (moduleCoeff Ψ) := let e {R} := mk WittVector.coeff .mk'
  let θ := Functor.isoWhiskerRight
    ((_ ⋙ _ ⋙ algBaseChange S).isoWhiskerLeft (moduleCompletionIso ..)) _ ≪≫ θ
  have i {A} := (θ.symm.app A).toLinearEquiv.bijective
  ⟨exists_isIdemQuotient, fun f g b ↦ .map_prod
    ((Comparison.bijective_iff_of_comm_sq (by simp; tauto) i (i.prodMap i)).2 (((@id (Function.prod
  ((asModules (_ ⋙ wittFunctor)).2 f) ((asModules _).2 g)).Bijective
    (((arrowProdEquivProdArrow ..).trans (e.prodCongr e).symm).bijective.comp ((bijective_prod_tilt
    f g b).comp_left.comp e.bijective))).map_prod (tensorWith .. ⋙ forget _)).map_prod
    (moduleCompletion .. ⋙ tensorWith .. ⋙ forget _))) (forget _ ⋙ uliftFunctor)⟩

variable {K}

/-- If `IsPeriodRingPair` holds for (S, K), in particular p divides ξ in S, then π = ξ mod p
annihilates O^♭ ⊗ S, the tensor product over A_inf. -/
lemma IsPeriodRingPair.pFlat_smul_eq_zero (h : IsPeriodRingPair p S K) (x : OFlat ⊗[Ainf] S) :
  pFlat • x = 0 := (smul_def xi x).trans
  (by simpa [p_eq_zero_of_algebra_oFlat] using! (map_dvd includeRight h.2).mul_right x)

end

variable {p} [ThePrime p] {C} [Category C] (F : AbFunctor C) (ψ : C ⥤ CommAlg OC)

/-- The character s ↦ ε^s of ℚ≥0 with values in O^♭, the restriction of the chosen character
`epsPow` of ℚ. -/
abbrev epsNonneg := epsPow.comp NNRat.coeHom.toAddMonoidHom.toMultiplicative

/-- The functor sending a commutative O_C-algebra to its underlying set, lifted one universe. -/
abbrev underlyingSet := forget (CommAlg OC) ⋙ uliftFunctor

/-- The functor on O_C-algebras times Bℕ sending A to the characters ℚ≥0 → A; the map (f, k)
applies f, then multiplies by the k-th power of a ↦ (ε^a)^♯. -/
def rootSystems : TimesBNat (CommAlg OC) ⥤ Type 1 := by refine ⟨(ULift <| _ →* ·.1), fun f ↦
  ↾(⟨((algebraMap ..).1.comp (untilt.comp epsNonneg) * ·)^[f.2.toAdd] <| .comp f.1.hom ·.1⟩),
  ?_, ?_⟩ <;> intros <;> ext <;> simp [id_as_one, comp_as_mul, @toAdd_mul ℕ, pow_add]; ring

/-- The natural map, on O_C-algebras times Bℕ, sending a character ℚ≥0 → A to its value at 1. -/
def rootSystems.atOne : rootSystems ⟶ fst _ ⋙ underlyingSet := ⟨fun _ ↦ ↾(⟨·.1 (.ofAdd 1)⟩), by
  intros; ext; simp [rootSystems]; erw [ULift.up_inj, MonoidHom.mul_apply]; aesop⟩

/-- For y in ψ(A), the functor on C × Bℕ of pairs: a map f: A → B and a character r of ℚ≥0 in
ψ(B) with r(1) = ψ(f)(y). -/
abbrev rootSystemsAt {A} y := fibreProd ((ψ.prod (𝟭 _)).whiskerLeft rootSystems.atOne)
    ((fst C).whiskerLeft (@pointMap _ _ (ψ ⋙ _) A y))

/-- For every object A and unit y of ψ(A), the root systems of y (`rootSystemsAt`), modulo the
action of ℕ, have the cohomology of Hom(A, −) with coefficients F. -/
abbrev RootSystemsAreLines := ∀ A (y : (ψ ⋙ underlyingSet) A), IsUnit y.1 →
  IsLine F (Y := rootSystemsAt ψ y) (fibreProd.snd ..)
