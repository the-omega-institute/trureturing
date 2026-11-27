/- GID: D5/S3/Zeros/GRH/New/Selmer/FitTwists
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/FitTwists
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.FitTwists. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/FitTwists.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Heights.Heights
import D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula.ChangingSigns
import D5.S3.Zeros.GRH.New.Exchange.AlgebraicPartDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

This file: Adjoint of the Hecke polynomial operator in each Galois-conjugate Petersson product.
Projecting tested forms to lifts does not increase any conjugate norm. Hecke algebra off the level,
eigenspaces and their projections on the proof's spaces. Auxiliary theta descent as a map of forms,
its equivariance and adjoint. Spaces of lifts, ramified and rank-one pairs, budget; what a good
twist family satisfies. -/
seal Finset.univ Finset.sum Finset.prod

/-- For a place w ≠ w̄ at which the Hecke polynomial operators `AuxPair.heckePolyOnForms` are
defined, the adjoint of H_w(X) for the σ-conjugate pairing `LevelPlaces.LevelForm.innerAt` on forms
on V is H_{w̄}(X'), where X' = σ⁻¹(conj(σX)). -/
lemma LevelPlaces.LevelForm.innerAt_heckePolyOnForms {E r n} [Field E] [CMType E] [WeilData E]
  [Fintype r] [Fintype n] {O : AuxPair E r n} σ φ φ' {w} (hw : _ ≠ w) hS hS' X :
  innerAt σ (O.heckePolyOnForms hw hS X φ) φ' =
  innerAt σ φ (O.heckePolyOnForms (star_injective.ne hw) hS' (σ.symm (star (σ X))) φ') := by
  simpa [innerAt] using! heckePolyOp_adjoint hw _ (mem_sphericalAt _ hS) (mem_sphericalAt _ hS)
    (smoothPairing_formTranslation _) _

open Module Complex Fint LinearMap Matrix MonoidHom Submodule LevelPlaces.LevelForm ComplexOrder Gf
  Representation
variable {E r n} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] {ℓ : ℕ} [Fact ℓ.Prime]
  (ι : ℂ ≃+* PadicAlgCl ℓ) (O : AuxPair E r n) {w} (hw : _ ≠ w) (hS :
  w ∉ O.places.conjClosure) (e₀ : MonoidAlgebra ℂ (O.ChosenGL r)) (Z : Submodule ℂ O.FormV) {e₀' :
  MonoidAlgebra ℂ (O.ChosenGL r)} {Z' : Submodule ℂ O.FormV}

/-- The operator by which e₀, in the group algebra of ∏_{w ∈ M} GL_r(k_w), acts on forms on V
through the representation `AuxPair.formAction`. -/
noncomputable abbrev AuxPair.groupAlgAction := O.formAction.asAlgebraHom e₀

/-- y is orthogonal to Z ∩ im e₀ ∩ ker H_w(X), X = `AuxPair.testValue` w, for every split place w
off the chosen places, the places of the twist and their conjugates. -/
def AuxPair.IsTested y := ∀ w hw hS,
  y ∈ ((O.groupAlgAction e₀).range ⊓ (O.heckePolyOnForms (w := w) hw hS (O.testValue w)).ker ⊓ Z)ᗮ

/-- Ξ is integral at every embedding ℂ → ℂ_l and tested (`AuxPair.IsTested`) by Y, the image of the
idempotent with label X − 1 at each place of M, and Z = ker θ. -/
def AuxPair.IsTestForm l [Fact (Nat.Prime l)] Ξ := (∀ j : PadicPlace l, Ξ ∈ integralForms j) ∧
  O.IsTested (tupleIdem r fun _ ↦ .X - 1) O.θ.ker Ξ

/-- ‖ι det⟨pr_Z y_a, pr_Z y'_b⟩‖ ≤ exp(rβ dim Z), r = rank W, for all families of dim Z forms
with y_a integral at every embedding ℂ → ℂ_ℓ, y'_b integral at ι and satisfying `AuxPair.IsTested`
for e₀ and Z^⊥. -/
def DenominatorLe β := ∀ d, finrank ℂ Z = d → ∀ y y' : Fin d → _,
  (∀ a (j : PadicPlace ℓ), y a ∈ integralForms j) →
  (∀ b, y' b ∈ integralForms ⟨(algebraMap _ ℂ_[ℓ]).comp ι.toRingHom⟩ ∧ O.IsTested e₀ Zᗮ (y' b)) → ‖ι
  (of fun a b ↦ inner ℂ (y a) (Z.starProjection (y' b))).det‖ ≤ .exp (d * (Fintype.card r * β))

section

omit [WeilData E]

lemma AuxPair.isOfFinOrder_prod_psi_det (g : O.ChosenGL r) :
  IsOfFinOrder (∏ i, O.ψ _ (g i).1.det) :=
  (CommMonoid.torsion _).prod_mem fun _ _ ↦ isOfFinOrder _ (by simp [IsUnit.isOfFinOrder])

/-- For every automorphism σ of ℂ, the pairing `LevelPlaces.LevelForm.innerAt` at σ on the forms
`AuxPair.FormV` is invariant under the action `AuxPair.formAction` of the finite group ∏_{w ∈ M}
GL_r(k_w), k_w the residue field: ⟨gx, gy⟩_σ = ⟨x, y⟩_σ. -/
lemma AuxPair.innerAt_formAction σ g x y : innerAt σ (O.formAction g x) (O.formAction g y) =
  innerAt σ x y := σ.injective (by
  erw [map_smulₛₗ₂, LinearMap.map_smul, smul_smul, map_mul, map_mul, σ.apply_symm_apply, conj_mul',
    (isOfFinOrder _ (isOfFinOrder_prod_psi_det ..)).norm_eq_one]
  simp; with_unfolding_all exact congr(_ * $(smoothPairing_formTranslation ..)))

lemma AuxPair.range_groupAlgAction_mem_invtSubmodule {f} (h : ∀ g y, (f (O.formAction g y)).1 =
  (O.formAction g (f y)).1) : (O.groupAlgAction e₀').range ∈
  End.invtSubmodule f := fun _ ⟨k, e⟩ ↦ e ▸ ⟨f k, by simp [asAlgebraHom_eq_sum, Subtype.ext (h ..)]⟩

/-- For places w ≠ w̄ and u ≠ ū at which the Hecke polynomial operators `AuxPair.heckePolyOnForms`
are defined, H_w(X) and H_u(Y) commute on forms on V, for all X and Y. -/
lemma AuxPair.heckePolyOnForms_comm {u} (h : star u ≠ u) s X Y y : O.heckePolyOnForms hw hS X
  (O.heckePolyOnForms h s Y y) = O.heckePolyOnForms h s Y (O.heckePolyOnForms hw hS X
  y) := Subtype.ext (by (repeat erw [coe_restrict_apply]); simpa [heckeSplit_comm hw, heckePolyOp,
  heckePolyEval, Finset.smul_sum, smul_smul, *, mul_comm, ↓mem_sphericalAt, -Set.Sum.elim_range]
  using Finset.sum_comm)

/-- A central idempotent e₀ of the group algebra of ∏_{w ∈ M} GL_r(k_w) acts on forms on V
self-adjointly for the class sum metric at every σ: ⟨e₀x, y⟩_σ = ⟨x, e₀y⟩_σ. -/
lemma AuxPair.innerAt_groupAlgAction (he : IsCentralProj e₀') σ x y :
    innerAt σ (O.groupAlgAction e₀' x) y = innerAt σ x (O.groupAlgAction e₀' y) :=
  he.self_adjoint _ σ _ (O.innerAt_formAction σ) ..

end

/-- Let e₀ be a central idempotent and Z a subspace of im e₀ killed by the Hecke polynomial
H_w(X), X = `AuxPair.testValue` w, w split off the level.
For a test form y (`AuxPair.IsTested`), orthogonal projection
onto Z does not increase the class sum norm at any σ. -/
lemma AuxPair.normSqAt_starProjection_le (he : IsCentralProj e₀') (hZ : Z' ≤
  (O.groupAlgAction e₀').range ⊓ (O.heckePolyOnForms hw hS (O.testValue w)).ker) {y} (h :
  O.IsTested e₀' Z'ᗮ y) σ : normSqAt (Z'.starProjection y) σ ≤ normSqAt y σ := by
  have a := (innerAt_heckePolyOnForms · · · hw hS (by grind [star_star]) (O.testValue w))
  obtain ⟨z, p, x, q, rfl⟩ := mem_sup.1 ((Z' ⊔ ((O.groupAlgAction e₀').ker ⊔ (O.heckePolyOnForms hw
    hS (O.testValue w)).range)).orthogonal_orthogonal.le fun u m ↦ h _ hw hS u (by
    simp_all [← inf_orthogonal, mem_orthogonal',
      ← IsSymmetric.orthogonal_range (innerAt_groupAlgAction _ he 1)]
    apply eq_zero_of_innerAt_self 1; rw [a, heckePolyOnForms_comm]; tauto))
  have d σ z (p : z ∈ Z') : x.innerAt σ z = 0 := by
    obtain ⟨⟨⟨u, rfl⟩, t⟩, x, k, _, ⟨v, rfl⟩, rfl⟩ := hZ p, mem_sup.1 q
    simp_all [eq_zero_of_innerAt_self σ _ (by rw [← a, heckePolyOnForms_comm, t]; simp) ▸ a σ v _,
      ← innerAt_groupAlgAction]
  have e x : normSqAt x σ = (σ (x.innerAt σ (x : O.FormV))).re := by
    simpa [innerAt_eq_stdClassSum] using! (map_classSum reLm _).symm
  simpa +contextual [eq_starProjection_of_mem_of_inner_eq_zero p, inner, ← z.conj_innerAt σ x, *]
    using e x ▸ finsum_nonneg (by simp [smul_nonneg])

variable {P} (D : Data P) {s} (V : Space D.E D.RowIndex s) {p y} {w : _}

/-- w is a split place (w̄ ≠ w), and neither w nor w̄ is one of the chosen places over g. -/
def Data.IsSplitOffLevel w := w.IsSplit ∧ w ∉ (Set.range D.chosen).conjClosure

/-- The Hecke algebra away from g: the families of operators on level g forms of all spaces V
given by one element of the group algebra of the elements of G_f trivial at the chosen
places. -/
def Data.heckeAlgebra : Subalgebra ℂ (∀ {s} (V : Space _ _ s), End ℂ (D.principalForms V)) where
  carrier := {p | ∃ a, ∀ s V y, asAlgebraHom
    ((V.formRep _).comp (trivialOn _ (.range D.chosen)).subtype) a y.1 = @p s V y}
  mul_mem' | ⟨a, _⟩, ⟨b, _⟩ => ⟨a * b, by simp [*]⟩
  add_mem' | ⟨a, _⟩, ⟨b, _⟩ => ⟨a + b, by simp [*]⟩
  algebraMap_mem' := (⟨· • 1, by simp⟩)

/-- For x = (w, j), the element of `Data.heckeAlgebra` acting on level g forms of every V by
T_{w,j}, if w ≠ w̄ and neither is a chosen place; otherwise 0. -/
noncomputable def Data.heckeOperator (x : FinPlace D.E × ℕ) : D.heckeAlgebra := if h :
  D.IsSplitOffLevel x.1 then ⟨fun _ ↦ .restrict _ fun _ m ↦ heckeSplit_mem_levelSpace h.1 x.2
  (levelSpace_anti (maxCompactAt_le_levelOf h.2) m) levelOf_le_Kf m, heckeGL ((leftRegular ℂ
  _).comp ((atSplit h.1).codRestrict _ (by grind [mem_trivialOn, atPlace_atSplit_of_ne, star_star,
  IsSplitOffLevel])))
  x.2 1, by simp [heckeSplit, heckeGL, heckeFun_sum, MonoidAlgebra.one_def]⟩ else 0

/-- The p-part: forms on V of principal level g on which each Hecke element `Data.heckeOperator` x
acts by the scalar p(x). -/
noncomputable def Data.eigenPart (p : _ → ℂ) := ⨅ x, ((D.heckeOperator x).1 V).eigenspace (p x)

/-- If y has Hecke eigensystem p on V, w ≠ w̄ and neither w nor w̄ is a chosen place, then y is
spherical at w and the Hecke polynomial at X acts on it by ∑_i (−X)^i q^{i(i−1)/2} p(w,i), q
the norm of w. -/
lemma Data.isSphericalWith_of_mem_eigenPart (hy : y ∈ D.eigenPart V p) (h : D.IsSplitOffLevel w) :
  IsSphericalWith (V.formRep _) h.1 (heckePolyEval D.RowIndex w (p ⟨w, ·⟩)) y.1 :=
  isSphericalWith_of_heckeSplit (levelSpace_anti (maxCompactAt_le_levelOf h.2) y.2)
  (by simpa [heckeOperator, h, Subtype.ext_iff] using (mem_iInf _).1 hy ⟨w, ·⟩)

/-- The primitive labels c of degree the rank of V whose idempotent e_c, acting at the place x
over g, does not kill the p-part of V. -/
def Data.occurringLabels p x := {c | IsPrimitiveLabel (Fintype.card D.RowIndex) c ∧ ∃ y ∈
  D.eigenPart V p, asAlgebraHom ((D.principalRep V).comp (.mulSingle _ x)) (labelIdem _ c) y ≠ 0}

lemma Data.dvd_card_resField_sub_one x : let q := .card (ResField (D.chosen x)); 3 ^ 2 ∣ q - 1 ∧
    P.Mω D.s ^ 2 ∣ q - 1 ∧ P.Mω D.s + 1 < q := (card_ResField _).trans (D.q_eq_g x.2.2.2) ▸
  ⟨by grw [← dvd_g_sub_one, Parameters.Mω, ← P.3, pow_add]; lia, D.dvd_g_sub_one _,
  D.nat_lt_of_hasLogBound⟩

/-- For a system q and finitely many other systems, one Hecke element is 1 on the q-part and 0 on
the other parts, on all spaces V at once. -/
lemma Data.exists_hecke_proj_eigenPart q (F : Finset _) : ∃ b : D.heckeAlgebra, ∀ d ∈ insert q F,
  ∀ {s} {V : Space _ _ s}, ∀ y ∈ D.eigenPart V d, b.1 V y = if d = q then y else 0 := F.induction
  ⟨1, by simp⟩ fun e F _ ⟨b, h⟩ ↦ (forall_imp_iff_exists_imp.1 (@funext _ _ e q)).elim fun x m ↦
  ⟨b - (e x - q x)⁻¹ • (b * D.heckeOperator x - q x • b), fun d k _ _ y l ↦ by
    by_cases n : d ∈ insert q F <;> simp +contextual [by simpa [eigenPart] using l, h d, *]
    clear * - k n m; simp_all [← sub_smul]⟩

lemma Data.commute_heckeAlgebra_principalRep (p : D.heckeAlgebra) x :
  Commute (p.1 V) ((D.principalRep V).asAlgebraHom x) := p.2.elim fun a h ↦ by
  ext; simp [← h, asAlgebraHom_eq_sum_support, principalRep, levelRep]
  simp [← End.mul_apply,
    ((commute_supportedOn_trivialOn (liftResidue_mem_supportedOn _) _).map _).eq]

/-- The action of the Hecke algebra `Data.heckeAlgebra` on the good forms of V, the image of e₀, as
a monoid homomorphism. -/
noncomputable def Data.heckeOnGood : D.heckeAlgebra →* End ℂ (D.goodForms V) :=
  ⟨⟨fun p ↦ (p.1 V).restrict fun
  | _, ⟨y, rfl⟩ => ⟨_, congr($(commute_heckeAlgebra_principalRep ..) y).symm⟩, rfl⟩, fun _ _ ↦ rfl⟩

lemma Data.principalRep_mem_eigenPart (hy : y ∈ D.eigenPart V p) x :
  (D.principalRep V).asAlgebraHom x y ∈ D.eigenPart V p := by
  simp_all [eigenPart, ← End.mul_apply, (commute_heckeAlgebra_principalRep ..).eq]; aesop

variable [Module.Finite ℂ (D.principalForms V)]

lemma Data.finite_eigenPart N : {p | N ⊓ D.eigenPart V p ≠ ⊥}.Finite := finite_ne_bot_of_iSupIndep
    (.mono (.iInf _ fun _ ↦ End.eigenspaces_iSupIndep _) inf_le_right)

/-- If the space of forms on V of principal level g is finite-dimensional, it is the sum of its
simultaneous Hecke eigenspaces, the p-parts. -/
lemma Data.iSup_eigenPart : ⨆ p, D.eigenPart V p = ⊤ := (_root_.map_eq_top_iff (mapIic _)).1
  (top_unique ((IsUnitary.le_span_hecke_eigenvectors (B := innerₛₗ ℂ) ⟨by simp_all,
  V.inner_formRep⟩ (p := D.IsSplitOffLevel) (by grind [IsSplitOffLevel, star_star]) (fun _ h ↦
  levelSpace_anti (maxCompactAt_le_levelOf h.2)) fun w h j ↦ by simpa [heckeOperator, h] using
  ((D.heckeOperator (w, j)).1 V · |>.2)).trans (span_le.2 fun z ⟨h, c, a⟩ ↦ ⟨⟨z, h⟩, mem_iSup_of_mem
  (∑ᶠ h, c ⟨⟨·, h⟩, ·⟩).uncurry (by aesop (add simp [eigenPart, heckeOperator])), rfl⟩)))

open Set MulChar Space Kf AuxPair
variable {E r n : _} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] (O :
  AuxPair E r n) {P : _} (D : Data P) (ϑ : D.TameChar) (j)

/-- If k stabilises the standard lattice of W and has reduction s at the chosen places above g,
then (θΞ)(gk) = θ(sΞ)(g) for every form Ξ on V and every adelic g. -/
lemma AuxPair.theta_mul_eq_theta_formAction k {s} (hk : reduceFamily _ k = s) Ξ g :
  O.θ Ξ (g * (1, k.1)) = O.θ (O.formAction s Ξ) g := by
  simp [← hk, theta_eq_smul_star_lift_swap]; left
  erw [O.pairThetaKernel.swap.lift_equivariant (isAutomorphic_algFormCoeff Ξ.1).conj, map_smul,
    pairWeil_integrated_fin O.W, O.pairWeil_upsilon k _ 1 (reduceFamily_liftResidue _)]
  simp [Space.lift, ← algFormCoeff_algFormRep, ← Finset.prod_inv_distrib, ← inv_apply_eq_inv',
    ← star_apply']
  ac_rfl

/-- For each j there is a ℂ-linear map from the forms on V_j to the forms of principal level g
on W_j which, when 1 ≤ j ≤ m, sends Ξ to the auxiliary theta lift θ_jΞ. -/
lemma Data.exists_theta_to_principalForms : ∃ L : _ →ₗ[ℂ] D.principalForms (D.spaceW j),
  j ∈ D.LiftIndex → ∀ Ξ, (L Ξ).1.1 = (D.auxPair ϑ j).θ Ξ := by_cases (fun h ↦ ⟨.codRestrict _
  ((AuxPair.θ _).codRestrict _ (theta_eq_smul_star_lift_swap _ · ▸ SMulMemClass.smul_mem _
  (by simpa using! (((D.fitsParams_auxPair ϑ ⟨j, h⟩).isEdge.isArrow _ _ (auxDatum _).2).2 ⟨_,
  (isForm_ofAlgForm (isHCParam_paramV _) _).conj⟩).2.conj))) fun Ξ ↦ mem_levelSpace_formRep_iff.2
  fun | _, ⟨k, _, rfl⟩ => by simpa using!
  theta_mul_eq_theta_formAction (s := 1) _ k ‹_› Ξ, by tauto⟩) (by simp [·])

/-- The map θ_j^* from forms of parameter ς and principal level g on W_j to algebraic forms on V_j,
adjoint to a map θ_j given by `exists_theta_to_principalForms`; 2ς = `Data.paramW`. -/
noncomputable def Data.auxLift : D.principalForms (D.spaceW j) →ₗ[ℂ] (D.auxPair ϑ j).FormV :=
  (exists_theta_to_principalForms ..).choose.adjoint

/-- An index set for U(2z): blocks of 12, 4, 4 and 2z − 20 indices, so of 2z elements when z ≥
10. -/
abbrev Data.RankOneIndex z := (Fin 12 ⊕ Fin 4 ⊕ Fin 4) ⊕ Fin (2 * z - 20)

variable {P : _} (D : Data P)

/-- The map θ_j^* for the twist ϑ (`Data.auxLift`), restricted to the good forms of parameter ς
and principal level g on W_j, with values in forms on V_j. -/
noncomputable abbrev Data.goodLift ϑ j := D.auxLift ϑ j ∘ₗ (D.goodForms _).subtype

/-- The pair p = (ν, z) is ramified: the tame part of ν is non-trivial exactly
at the chosen places. -/
def Data.Pair.IsRamified {D} (p : @Pair P D) := ∀ w, p.ψ w ≠ 1 ↔ D.IsChosen w

/-- The pair p = (ν, z) is of rank one for j: m < z ≤ r, 1 ≤ j ≤ m, ν has tame part ω^j, and w_j
+ r − t ≤ c ≤ w_j, where −c is the weight of ν and w_j = `Data.w` j. -/
def Data.Pair.IsRankOne {D} (p : @Pair P D) j := p.HasLiftRank (RankOneIndex p.z) ∧
  p.z ∈ Set.Ioc D.m D.r ∧
  (j ∈ D.LiftIndex ∧ p.ψ = D.ω ^ (j : ℤ)) ∧ ∀ v, p.c v ≤ D.w j v ∧ D.w j v + D.r ≤ p.c v + D.t

/-- The budget for congruences B₀ = f·a·(log b)³/(mk), a = `Data.a`. -/
noncomputable abbrev Data.B₀ := D.budget / (D.m * D.k)

/-- Q_ι is prime to ℓ, and for 1 ≤ j ≤ m, at the twists ϑ_ι^j: 𝒵_j and the rank-one lines ℂΞ_p
of index j have denominators ≤ rγ_ℓ, γ_ℓ with ∑γ_ℓ ≤ B₀; inverse ratios of ramified pairs
have height ≤ x⁹⁹⁹. Here 𝒵_j is the image of `Data.goodLift`, Ξ_p = `LValueData.trivialLift`,
denominators are as in `DenominatorLe`, and ratios as in `Data.Pair.ratio`. -/
structure Data.IsFitFamily (θ : PrimePadicIso → D.MFoldTwist) where
  coprime ι : Nat.Coprime ι.1.1 (θ ι).levelNorm
  denominator_le j : ∃ γ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → T.sum γ ≤ D.B₀) ∧ ∀ ι, DenominatorLe
    ι.2 _ D.e₀ (D.goodLift ((θ ι).powTwist j) j).range (γ ι.1) ∧ ∀ p : D.Pair, ∀ H : p.IsRankOne j,
    DenominatorLe ι.2 _ (tupleIdem _ fun _ ↦
    .X - 1) (ℂ ∙ (p.lValueData H.1 ((θ ι).powTwist j)).trivialLift) (γ ι.1)
  height_le j (p : D.Pair) s : p.IsRamified → HeightLe (D.x ^ 999) fun ι ↦
    (p.ratio ((θ ι).powTwist j) s)⁻¹
