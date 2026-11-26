import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.Crystalline.PeriodLifting
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Derived completeness for a principal ideal: Nakayama, finiteness, completed base change
(known result; see Lib.PadicComparison.Completion.RootSystems).

This file: Geometric l-adic cohomology with Galois action; reduction from Z_l to F_l
coefficients. -/

noncomputable section


open CategoryTheory AlgebraicGeometry CommRingCat LocallyConstant WittVector Function AddCommGrpCat
  TensorProduct Pi
variable {ℓ} [ThePrime ℓ] {n : ℕ} (R : CommRingCat) (Ω) [CommRing Ω] [Algebra R Ω] (Γ) [Group Γ]
  [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]

/-- The coefficient functor ℤ_ℓ on test rings: A goes to the ring of ℓ-typical Witt vectors of
the locally constant functions Spec A → 𝔽_ℓ. -/
abbrev ellAdicCoeff := moduleCoeff (asModules ((testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[ℓ]))

/-- For functors M,N on tests, the additive map sending α: M→N to the ℚ_ℓ-linear pull-back
ℚ_ℓ⊗Ext^n(N,F)→ℚ_ℓ⊗Ext^n(M,F), F the ℤ_ℓ coefficient functor. -/
def ellAdicPull n {M N} := AddMonoidHom.mk' (fun α : M ⟶ N ↦ (H.mapₗ ℤ_[ℓ] ellAdicCoeff α
  n).baseChange ℚ_[ℓ]) (by aesop (add simp [H.mapₗ, H.map, Abelian.Ext.mk₀_add, tmul_add]))

attribute [local simp] ellAdicPull H.mapₗ H.map_comp

lemma ellAdicPull.comp {M N K} α β x : @ellAdicPull ℓ _ n M N α (@ellAdicPull ℓ _ n N K β x) =
  ellAdicPull n (α ≫ β) x := by induction x <;> simp_all

/-- The functor sending an R-scheme X to the functor of points X_Ω, whose points in B are pairs
x ∈ X(B), ω: Ω → B compatible over R. -/
def geomPoints : Over (Spec R) ⥤ PointFunctor :=
  .mk (pointsToBase ·.hom |> baseChangeOf <| ofHom (algebraMap R Ω)) fun f ↦
  {app _ := ↾fun x ↦ ⟨(⟨x.1.1.1 ≫ f.1⟩, _), .trans congr(⟨Spec.preimage $(by simp)⟩) x.2⟩}

/-- ℓ-adic cohomology: the contravariant functor X ↦ V^n(X) = ℚ_ℓ ⊗ Hⁿ(X_Ω, ℤ_ℓ) from R-schemes
to ℚ_ℓ-vector spaces, computed on test rings. -/
def ellAdicCohom n := (geomPoints R Ω).op ⋙ .mk _ fun u ↦
  ModuleCat.ofHom (ellAdicPull n (freeAb.map (mapOnTests u.unop)))

/-- The representation of Γ on V^n(X), Γ acting on Ω over R, in which g acts by pull-back along
(ω, x) ↦ (ω∘g, x) on X_Ω. -/
def ellAdicCohom.galoisAction X n : Representation ℚ_[ℓ] Γ (ellAdicCohom R Ω n ⟨X⟩) :=
  .comp ⟨⟨fun g : Ω ≃ₐ[R] Ω ↦ ellAdicPull n (freeAb.map (mapOnTests
  (baseChangeTransition _ (ofHom g) (by aesop)))), congr($((ellAdicCohom ..).map_id _).1)⟩,
  by intros; ext; erw [ellAdicPull.comp, ← freeAb.4]; rfl⟩ (MulSemiringAction.toAlgAut ..)

lemma ellAdicCohom.map_galoisAction {X Y} (f : X ⟶ Y) (g : Γ) x :
  (ellAdicCohom R Ω n).map f.op ((galoisAction ..) g x) = (galoisAction ..) g ((ellAdicCohom
  ..).map f.op x) := by (repeat erw [ellAdicPull.comp, ← freeAb.4]); rfl

/-- For every k there is a map q from the coefficient functor ℤ_ℓ on test rings to the locally
constant functions with values in W_k(𝔽_ℓ) making 0 → ℤ_ℓ → ℤ_ℓ → W_k(𝔽_ℓ) → 0 exact, the
first map being multiplication by ℓ^k. -/
lemma exists_ellAdicCoeff_modShortExact_pow k : ∃ q :
  ellAdicCoeff ⟶ locConstCoeff ⟨TruncatedWittVector ℓ k (ZMod ℓ)⟩, ModShortExact ↑(ℓ ^ k) q :=
  ⟨_, modShortExact_of_isReductionMod (q := {app _ := ofHom (.mk' _ (LocallyConstant.ext fun a ↦
  ((truncate k).comp (map (evalRingHom a))).map_add · ·))}) fun A ↦
  (witt_reduction_spec (ZMod ℓ) (locConstAlg _)).2.imp
  (·.1.pow _) fun v ↦ ⟨(truncate_surjective _ _ _ ·.flip |>.imp fun _ ↦ congrArg unflip), fun x ↦
  .trans (by erw [← mem_ker_truncate, ← sub_zero x, map_sub, sub_eq_zero, sub_zero]; exact
  (LeftInverse.injective flip_unflip).eq_iff) (v.2 ..)⟩⟩

/-- On test rings there is q: ℤ_ℓ → 𝔽_ℓ (Witt vectors of locally constant 𝔽_ℓ-valued functions,
to these functions) making 0 → ℤ_ℓ → ℤ_ℓ → 𝔽_ℓ → 0 exact, the first map being ℓ; and every
Ext^n(N, ℤ_ℓ) is ℓ-complete (`IsDerivedComplete`). -/
lemma exists_ellAdicCoeff_modShortExact : ∃ q : ellAdicCoeff ⟶ locConstCoeff ⟨ZMod ℓ⟩,
  ModShortExact ↑ℓ q ∧ ∀ N n, IsDerivedComplete (ℓ : ℤ_[ℓ]) (H N ellAdicCoeff n) :=
  have w A := witt_reduction_spec (ZMod ℓ) (locConstAlg _)
  ⟨_, modShortExact_of_isReductionMod (q := {app _ := ofHom constantCoeff.toAddMonoidHom})
    (⟨w · |>.2.1.1, (w _).1⟩),
    .cohomology (IsCompleteTorsionFree.isDerivedComplete (B := wittFunctor _ _) <| w · |>.2.1)⟩

/-- For a functor N from test rings to abelian groups: if Ext^n(N, 𝔽_ℓ) is finite, then Ext^n(N,
ℤ_ℓ) is a finitely generated ℤ_ℓ-module, the coefficients being the locally constant
𝔽_ℓ-valued functions on Spec and their Witt vectors. -/
lemma finite_H_ellAdicCoeff {N} (_ : Finite (H N (locConstCoeff ⟨ZMod ℓ⟩) n)) :
  Module.Finite ℤ_[ℓ] (H N ellAdicCoeff n) := exists_ellAdicCoeff_modShortExact.elim
  fun c ⟨k, d⟩ ↦ let q := H.push N c _; .of_surjective ((basisFun ..).constr ℕ (invFun q))
    ((d ..).exists_eq_of_approx (.of_isAdicComplete (PadicInt.maximalIdeal_eq_span_p.rec {})) _ _
    fun x ↦ ⟨(basisFun ..) (q x), (k.exists_smul_eq_of_push_eq_zero _
    (q.sub_mem_ker_iff.2 (invFun_eq ⟨x, rfl⟩).symm)).imp (by simp_all [-basisFun_apply])⟩)

/-- If α: M → N induces bijections on all Ext groups with coefficients the locally constant
𝔽_ℓ-valued functions on test rings, then the pull-back ℚ_ℓ ⊗ Ext^n(N, ℤ_ℓ) → ℚ_ℓ ⊗ Ext^n(M,
ℤ_ℓ) is bijective for every n. -/
lemma IsCohomEquiv.bijective_ellAdicPull {M N α} (h : IsCohomEquiv (locConstCoeff ⟨ZMod ℓ⟩) α) :
  Bijective (@ellAdicPull ℓ _ n M N α) := exists_ellAdicCoeff_modShortExact.elim fun _
  ⟨e, d⟩ ↦ map_bijective (f := 1) bijective_id ((h.bij.of_mod
  (β := 𝟙 (𝟭 _ ⋙ _)) e e rfl (by tauto) (d _)).eqv _)
