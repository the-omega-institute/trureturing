import OmegaMath.NumberTheory.GRH.Lib.Shimura.ThetaNormality.NormalGeneration
import OmegaMath.NumberTheory.GRH.Lib.Shimura.Uniformisation.RiemannFormAdelic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family)
(known result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Projective embeddability passes to composites and to closed subschemes of finite
products. A positive Riemann form forces the signature condition on the hermitian form. Canonical
theta coordinates of PEL complex tori and their Heisenberg law. -/

noncomputable section

open CategoryTheory Fint Pi ComplexOrder

instance {X S s A} [a : HasProjEmbedding A.hom] [b : @HasProjEmbedding X S s] :
    HasProjEmbedding ((Over.map s).obj A).hom := a.rec fun a ↦ b.rec (⟨a.mul ·⟩)

/-- If an S-scheme W has a closed immersion over S into the fibre product of finitely many
S-schemes, each a closed subscheme of a projective space over S, then W is also a closed
subscheme of a projective space over S. -/
lemma HasProjEmbedding.pi {S ι W} [Finite.{1} ι] {A : ι → Over S} (i : W ⟶ ∏ᶜ A)
    [AlgebraicGeometry.IsClosedImmersion i.left] [h : ∀ i, HasProjEmbedding (A i).hom] :
  HasProjEmbedding W.hom := by
  choose _ _ _ h using ((hasProjEmbedding_iff _).1 <| h ·)
  exact ⟨i.w ▸ (LineBundle.isProjEmbedding_pi _ h (Limits.Pi.hom_ext _ _)).comp _⟩

/-- For a polarised period map for (g, ℓ) with matrix β: g is a frame for β, and Φ_{v₀}(β)·ℓ and
the Φ_w(β), w ≠ v₀, are positive definite (`IsSignedFrameFor`). -/
lemma PeriodMap.isSignedFrameFor {E} [Field E] [CMBase E] {V} [FinComplexSpace V] {D : PEL E}
    {g ℓ} (x : PeriodMap D g ℓ V) : IsSignedFrameFor g ℓ x.β := ⟨x.4, fun v ↦ by
  have key a b := x.5 (Pi.single v ∘ b) ▸ x.7 _ (Pi.single v ∘ a)
  simp +contextual [polarisationForm, Fintype.sum_eq_single v, ← zero_def, ← smul_def,
    -smul_eq_mul, -mul_ite] at key
  suffices _ from .of_dotProduct_mulVec_pos this fun u _ ↦ ⟨by
    simpa [riemannForm_swap, *, D.xi_im_pos_and_re_eq_zero] using x.8.1 (x.Q (Pi.single v ∘ u)) (by
    simp_all [funext_iff]), (this.im_star_dotProduct_mulVec_self u).symm⟩
  exact .ext fun i j ↦
    ext_inner_right ℝ fun c ↦ by simpa [-single_apply, ne_of_gt, D.xi_im_pos_and_re_eq_zero] using
    ((fun a b ↦ (key a b).symm.trans (.trans (by simpa [riemannForm_def, x.6] using (x.6
    (Complex.I • _) (Complex.I • _))) (key b a))) (Pi.single j 1) (Pi.single i c))⟩

open AddSubgroup Submodule Complex Function NumberField AddChar Set thetaSpace IsAppellHumbert PEL
variable {E n} {v : Valuation ℂ NNReal} [Field E] [CMBase E] [Fintype.{0} n] (D : PEL E)

/-- The integer β₁ = |T|β − ⌊|T|/2⌋ of E. -/
def PEL.rescaledBeta := Nat.card D.T • D.β - ↑(Nat.card D.T / 2)

lemma PEL.lagrangian_le_T : D.lagrangian ≤ D.T :=
  torsionClass_induction (by grind [mem_T, mem_lagrangian, zero_mem])

/-- The r-torsion subgroup of the torsion module (E/O_E)^n. -/
def PEL.rTorsion := comap (@nsmulAddMonoidHom (_root_.AdelicTorsion E D.Index) _ D.r) ⊥

variable {D g ℓ y z V} [FinComplexSpace V] (x : PeriodMap D g ℓ V) (s t : D.T) {u S S'}

/-- A chosen vector of E^n whose torsion class with respect to g is s, normalised so that the
class 0 is represented by 0. -/
def ratLift g := (fun σ s ↦ σ s - σ 0) (surjInv (@frameTorsionClass_surjective E n _ _ _ g))

@[simp] lemma frameTorsionClass_ratLift s : frameTorsionClass g (ratLift g s) =
  s := by simp [ratLift, surjInv_eq]

/-- The ring homomorphism from O_E to the complex endomorphisms of V given by multiplication,
transported through the period map. -/
def PeriodMap.intAction := x.isPeriodMap.complexMul.comp (cmEmbedding.comp (algebraMap (𝓞 E) E))

variable (D g ℓ V) in
/-- A theta torus: a polarised period map with ℓ a reflection, c̄ adjoint to c for B, and V ≅
`BallFibre` with a acting by Φ_{v₀}(a), its conjugate, and Φ_w(a). -/
structure ThetaTorus extends PeriodMap D g ℓ V where
  reflection : IsReflection ℓ
  adjoint c y z : B (toPeriodMap.intAction c y) z = B y (toPeriodMap.intAction (star c) z)
  exists_std_equiv : ∃ e : V ≃ₗ[ℂ] BallFibre E D.Index, ∀ a, e.1 ∘ₗ toPeriodMap.intAction a ∘ₗ
    e.symm.1 = .prodMap (.prodMap (Φ v₀ a.val • 1) (star (Φ v₀ a.val) • 1)) (.piMap (Φ ·.1 a • 1))

namespace PeriodMap

/-- For a subgroup S of the torsion module, the image in V under the period map of the vectors
of E^n whose class with respect to g lies in S. -/
abbrev latticeOver S := classLattice g S x.Q

/-- The period lattice in V: the image under the period map of the vectors y in E^n with g⁻¹y
integral. -/
abbrev periodLattice := x.latticeOver ⊥

/-- The function on V sending u to exp(πi·e(β₁u, u)), where e is the Riemann form of B and β₁ =
|T|β − ⌊|T|/2⌋. -/
abbrev multiplier := canonicalMultiplier x.B (x.intAction D.rescaledBeta)

/-- For y in E^n, the point of V obtained by applying the period map of x to the image of y
under the CM-type embedding `toRealVectors`. -/
abbrev periodPoint y := x.Q (toRealVectors y)

/-- For a torsion class s, the vector of V that is the image under the period map of the chosen
representative of s in E^n. -/
def torsionLift s := x.periodPoint (ratLift g s)

attribute [local simp] torsionLift periodPoint canonicalMultiplier RealComplexForm.riemannPhase
  thetaShift_apply map_add_eq_mul map_neg_eq_inv ne_of_gt
  Nat.mul_add_div map_nsmul_eq_pow add_mul toRealVectors_injective frameTorsionClass_surjective

attribute [local simp ←] fourierChar_eq_one

attribute [instance] isPosRiemann

@[simp] lemma torsionLift_zero : x.torsionLift 0 = 0 := by simp [ratLift]

@[simp] lemma mem_latticeOver : x.periodPoint y ∈ x.latticeOver S ↔ frameTorsionClass g y ∈ S :=
  mem_map_iff_mem (by simp)

lemma latticeOver_mono (h : S ≤ S') : x.latticeOver S ≤ x.latticeOver S' := image_mono (by tauto)

lemma dualLattice_inf_latticeOver_top (h : ∀ y, torsionClass y ∈ S' ↔ ∀ w, torsionClass w ∈ S →
  ψf E (xiForm D.ξ y w) = 1) :
  x.B.dualLattice (L := x.latticeOver S) ⊓ x.latticeOver ⊤ = x.latticeOver S' := ext (by
  have {y} := isClosed_property (denseRange_frameCoords (g := g))
    (isClosed_imp (isOpen_preimage_torsionClass S) (isClosed_eq
    (f := ψf E ∘ xiForm D.ξ y) (by fun_prop [xiForm]) continuous_one))
  simp [RealComplexForm.dualLattice, Submodule.copy, mem_classLattice, frameTorsionClass,
    reindex_equiv x.Q, riemannForm_eq] at *
  grind [ψf_unit_eq_one, fourierChar_polarisationForm x.isFrameFor.choose_spec])

lemma intAction_mem_periodLattice bicharacter : ∀ l ∈ x.periodLattice, x.intAction bicharacter l ∈
  x.periodLattice := forall_mem_image.2 (by simp_all [intAction, ← toRealVectors_smul])

lemma nsmul_mem_latticeOver {m} (h : m ≠ 0) : m • u ∈ x.latticeOver S ↔ u ∈ x.latticeOver (S.comap
  (nsmulAddMonoidHom m)) := (MulAction.surjective₀ (a := (m : E)) (by simpa)).exists.trans (by
  simp_all [mem_classLattice, Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul ℝ, -nsmul_eq_mul])

lemma relIndex_latticeOver :
  (x.latticeOver S).toAddSubgroup.relIndex (x.latticeOver S').toAddSubgroup = S.relIndex S' := by
  erw [relIndex_map_map_of_injective, relIndex_comap, map_comap_eq_self_of_surjective] <;> simp

lemma card_nsmul_mem_periodLattice (h : u ∈ x.latticeOver D.T) : Nat.card D.T • u ∈
  x.periodLattice := D.T.relIndex_bot_left ▸ x.relIndex_latticeOver ▸ nsmul_relIndex_mem _ h

lemma intAction_rescaledBeta_mem_latticeOver (h : S ≤ D.T) (k : u ∈ x.latticeOver S) :
  x.intAction D.rescaledBeta u ∈ x.latticeOver S := by
  simpa [rescaledBeta] using
    _root_.sub_mem (x.latticeOver_mono bot_le (x.intAction_mem_periodLattice _ _
    (x.card_nsmul_mem_periodLattice (x.latticeOver_mono h k)))) (by aesop)

lemma riemannForm_intAction_rescaledBeta : ∀ u w, x.B.riemannForm (x.intAction D.rescaledBeta u) w =
  x.B.riemannForm u w - x.B.riemannForm u (x.intAction D.rescaledBeta w) := by
  simp [reindex_equiv x.Q, intAction, riemannForm_eq, polarisationForm, mul_sub, ← map_star_complex,
    ← Pi.smul_def, -smul_eq_mul, sub_smul, ← coe_star_ringOfIntegers, -mul_re, (D.odd_card.rec
    (by simp_all [rescaledBeta, D.star_beta]; grind) : star D.rescaledBeta = 1 - D.rescaledBeta)]

lemma isAppellHumbert_of_le {L} (hL : L ≤ x.latticeOver D.lagrangian) : IsAppellHumbert (L := L) x.B
  x.multiplier := isAppellHumbert_canonicalMultiplier x.riemannForm_intAction_rescaledBeta x.re_symm
  fun _ k ↦ ((x.dualLattice_inf_latticeOver_top D.mem_lagrangian ▸
  x.intAction_rescaledBeta_mem_latticeOver D.lagrangian_le_T (hL k)).1 · ∘ @hL _)

instance isAppellHumbert_periodLattice : IsAppellHumbert x.B x.multiplier :=
  x.isAppellHumbert_of_le (x.latticeOver_mono bot_le)

instance isAppellHumbert_latticeOver_lagrangian : IsAppellHumbert (L :=
  x.latticeOver D.lagrangian) x.B x.multiplier := x.isAppellHumbert_of_le le_rfl

lemma dualLattice_le_latticeOver_top : x.B.dualLattice (L := x.latticeOver S) ≤ x.latticeOver ⊤ :=
  x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice.rec fun _ ⟨a, b⟩ _ h ↦
  x.latticeOver_mono le_top
  ((x.nsmul_mem_latticeOver a).1 (b _ (h · <| x.latticeOver_mono bot_le ·)))

lemma dualLattice_periodLattice : x.B.dualLattice = x.latticeOver D.T :=
  inf_of_le_left x.dualLattice_le_latticeOver_top ▸ x.dualLattice_inf_latticeOver_top D.mem_T

instance discreteTopology_latticeOver_lagrangian : DiscreteTopology (x.latticeOver D.lagrangian) :=
  isFullRankLattice_dualLattice.1.of_subset
  (x.dualLattice_periodLattice ▸ x.latticeOver_mono D.lagrangian_le_T)

lemma sub_mem_periodLattice_iff : x.periodPoint y - x.periodPoint z ∈ x.periodLattice ↔
  frameTorsionClass g y = frameTorsionClass g z := by simp [← map_sub, ← sub_eq_zero]

lemma torsionLift_mem : x.torsionLift s ∈ x.latticeOver D.T := by simp

lemma riemannPhase_rescaledBeta_eq (h : u ∈ x.latticeOver D.T) (t : x.periodPoint y ∈ x.latticeOver
  D.T) (k : frameTorsionClass g z = frameTorsionClass g y) : x.B.riemannPhase
  (x.intAction D.rescaledBeta u) (x.periodPoint y) =
  x.B.riemannPhase (x.periodPoint z) ((.card D.T / 2) • u) := by
  obtain := x.dualLattice_periodLattice.ge t _
    (x.intAction_mem_periodLattice D.β _ (x.card_nsmul_mem_periodLattice h)),
    x.dualLattice_periodLattice.ge h _ (x.sub_mem_periodLattice_iff.2 k)
  simp_all [rescaledBeta, riemannForm_swap (x.Q _), inv_mul_eq_one, -nsmul_eq_mul]

/-- For u in the lattice over T, the additive character t ↦ exp(2πi·e(β₁u, a_t)) of T, with e
the Riemann form of B and a_t the chosen lift of t. -/
def bicharacter (h : u ∈ x.latticeOver D.T) : AddChar D.T ℂ :=
  ⟨(x.B.riemannPhase (x.intAction D.rescaledBeta u) <| x.torsionLift ·), by simp [ratLift],
  fun s t ↦ by simp [riemannPhase_rescaledBeta_eq (z := ratLift g s + ratLift g t),
  riemannPhase_rescaledBeta_eq _ h _ rfl, add_mem, h]⟩

lemma bicharacter_neg_eq_swap : x.bicharacter (x.torsionLift_mem s) (-t) =
  x.bicharacter (x.torsionLift_mem t) s := by simp [bicharacter,
  x.riemannPhase_rescaledBeta_eq _ _ rfl, riemannForm_swap (x.periodPoint (ratLift g t))]

/-- If s in T has `bicharacter`(s)(l)² = 1 for all l in T in the Lagrangian of D, then s lies in the
Lagrangian. -/
lemma mem_lagrangian_of_bicharacter_sq (h : ∀ l : D.lagrangian.addSubgroupOf D.T, x.bicharacter
  (x.torsionLift_mem s) l ^ 2 = 1) : ↑s ∈ D.lagrangian := frameTorsionClass_ratLift s.1 ▸
  x.mem_latticeOver.1 (x.dualLattice_inf_latticeOver_top D.mem_lagrangian ▸ ⟨fun l ⟨y, hy, e⟩ ↦
  D.lagrangian_le_T (x := frameTorsionClass g y) hy |> fun k ↦ by
  obtain ⟨⟨⟩⟩ := D.odd_card, x.dualLattice_periodLattice.ge (by tauto) _
    (x.card_nsmul_mem_periodLattice (x.torsionLift_mem s)), h ⟨⟨_, k⟩, hy⟩
  simp_all [bicharacter, riemannPhase_rescaledBeta_eq (z := y), sq, @two_mul ℝ, riemannForm_swap l,
    Circle.ext_iff, -coe_fourierChar_eq_exp], by simp⟩)

/-- A chosen non-zero theta function for B, the canonical multiplier of β₁ and the lattice over
the self-annihilating subgroup L, of which every such theta function is a complex multiple. -/
def exists_thetaSpace_lagrangian_le_span := Classical.indefiniteDescription _ (finrank_eq_one_iff'.1
    (by simpa [inf_of_le_left x.dualLattice_le_latticeOver_top ▸
  x.dualLattice_inf_latticeOver_top D.mem_lagrangian] using
  x.isAppellHumbert_latticeOver_lagrangian.finrank_sq_eq_relIndex.2.1))

/-- For t in T, the function θ_t on V: the normalised translate `normalizedShift`, by the chosen
lift a_t of t, of a chosen generator of the line in
`PeriodMap.exists_thetaSpace_lagrangian_le_span`. -/
def thetaCoord := normalizedShift x.B (x.intAction D.rescaledBeta) (x.torsionLift t)
  x.exists_thetaSpace_lagrangian_le_span

@[simp] lemma thetaCoord_mem_thetaSpace : x.thetaCoord t ∈ x.B.thetaSpace x.multiplier :=
  smul_mem _ _ (thetaShift_mem_of_dual (by simp [dualLattice_periodLattice])
  (x.exists_thetaSpace_lagrangian_le_span.1.2.imp id (· · <| x.latticeOver_mono bot_le ·)))

lemma thetaCoord_mem_thetaSpace_lagrangian : x.thetaCoord t ∈ x.B.thetaSpace (L :=
  x.latticeOver D.lagrangian) fun l ↦ x.multiplier l * x.B.riemannPhase l (x.torsionLift t) :=
  smul_mem _ _ (by simp [↓thetaShift_mem])

lemma thetaCoord_ne_zero : x.thetaCoord t ≠ 0 :=
  ne_of_apply_ne (x.B.thetaShift (-x.torsionLift t)) (by simp [thetaCoord, normalizedShift,
  x.isAppellHumbert_periodLattice.thetaShift_thetaShift, x.exists_thetaSpace_lagrangian_le_span.2])

lemma thetaCoord_eq_of_mem_lagrangian (h : ↑s ∈ D.lagrangian) : x.thetaCoord s =
  x.thetaCoord 0 := by simp [thetaCoord,
  mem_thetaSpace_iff_normalizedShift.1 x.exists_thetaSpace_lagrangian_le_span.1.2, h]

variable {s t}

lemma thetaCoord_eq_normalizedShift y (hy : frameTorsionClass g y = t) : x.thetaCoord t =
  normalizedShift x.B (x.intAction D.rescaledBeta) (x.periodPoint y)
  x.exists_thetaSpace_lagrangian_le_span := by
  have h := x.sub_mem_periodLattice_iff.2 (frameTorsionClass_ratLift (frameTorsionClass g y)).symm
  obtain := x.dualLattice_periodLattice.ge (x.torsionLift_mem t) _
    (x.intAction_rescaledBeta_mem_latticeOver bot_le h),
    (mem_thetaSpace_iff_normalizedShift.1 (x.thetaCoord_mem_thetaSpace t)).2 _ h
  simp_all [thetaCoord, x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift
    x.riemannForm_intAction_rescaledBeta, riemannForm_swap (x.Q _), -map_sub]

lemma thetaShift_thetaCoord (hy : frameTorsionClass g y = s) t :
  x.B.thetaShift (x.periodPoint y) (x.thetaCoord t) = (x.multiplier (x.periodPoint y) *
  x.bicharacter (x.mem_latticeOver.2 (hy ▸ s.2)) t) • x.thetaCoord (s + t) := by
  simpa [bicharacter, x.thetaCoord_eq_normalizedShift (y + ratLift g t), *, mul_smul,
    ← inv_smul_eq_iff₀] using! x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift
    x.riemannForm_intAction_rescaledBeta

/-- Symmetry of the theta coordinates: there is a complex number ε such that θ_t(−z) = ε
θ_{−t}(z) for all z in V and all t in T. -/
lemma exists_thetaCoord_sign_smul (m : ℤˣ) : ∃ ε, ∀ z t, x.thetaCoord t (m.1 • z) =
  ε * x.thetaCoord (m.1 • t) z := (Int.units_eq_one_or m).rec (⟨1, by simp [·]⟩) fun _ ↦
  (x.exists_thetaSpace_lagrangian_le_span.2.2 ⟨_, x.exists_thetaSpace_lagrangian_le_span.1.2.imp
  (·.comp differentiable_fun_id.neg) (by simp_all [↓neg_add])⟩).imp (by
  simp_all [Subtype.ext_iff, funext_iff, ↓x.thetaCoord_eq_normalizedShift (-ratLift g _),
    thetaCoord, normalizedShift, add_comm, field])

attribute [irreducible] thetaCoord bicharacter

lemma valuation_multiplier_mul_bicharacter (h : u ∈ x.latticeOver D.T) :
  v (x.multiplier u * x.bicharacter h t) = 1 := by simp_all [bicharacter, two_mul, exp_add,
  valuation_eq_one_of_pow_eq_one _ (x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one
  (card_nsmul_mem_periodLattice ..) (card_nsmul_mem_periodLattice ..)),
  intAction_rescaledBeta_mem_latticeOver]

/-- Good reduction for the trivial valuation on ℂ: the lattice, form and multiplier of a
polarised period map satisfy `HasGoodReduction` for the integer r ≥ 3 of D; in particular the
sup norm is multiplicative. -/
lemma hasGoodReduction_trivial : HasGoodReduction x.B x.multiplier 1 D.r := ⟨{finite_order :=
  ⟨2 * 1 * 1, nofun, fun _ _ ↦ x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one
  (by simp [intAction_mem_periodLattice, *]) (by simpa)⟩}, by
  simp [x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice], by
  simp [D.three_le_r.trans_lt'], Nat.le_of_lt D.three_le_r, fun _ _ _ _ ⟨_, a, _⟩ ⟨_, b, _⟩ ↦ by
  have (B : LatticeForm x.periodLattice) f hf (H : B.thetaNorm 1 f ≠ 1) := eq_zero_of_torsionPoints
    hf (by simpa [IsGreatest, LatticeForm.sizeAt,
    upperBounds, -map_mul, Valuation.one_apply_le_one] using H ∘ IsGreatest.csSup_eq)
  grind +splitImp [thetaNorm_zero, =_ sizeAt_mul, eq_zero_of_entire_mul_eq_zero a, a.mul b]⟩

lemma thetaNorm_thetaCoord i : x.B.thetaNorm v (x.thetaCoord i) =
  x.B.thetaNorm v (x.thetaCoord 0) :=
  .trans (by simp [thetaShift_thetaCoord, thetaNorm_smul, valuation_multiplier_mul_bicharacter,
  -canonicalMultiplier, -map_zero_eq_one]) (x.hasGoodReduction_trivial.thetaNorm_thetaShift
  (x.dualLattice_periodLattice ▸ x.torsionLift_mem i))

lemma formSpan_eq_normBall (G : HasGoodReduction x.B x.multiplier v D.r) bicharacter j :
  _root_.formSpan _ x.thetaCoord (D.r ^ j) = (G.pow j).normBall (x.thetaCoord bicharacter ^ D.r ^
  j) := G.normBall_pow_pow (x.thetaCoord_mem_thetaSpace bicharacter) inferInstance
  (x.thetaCoord_mem_thetaSpace_lagrangian bicharacter) (fun _ h ↦
  x.latticeOver_mono D.torsion_mem_lagrangian ((x.nsmul_mem_latticeOver G.one_lt.ne_bot).1 h)) j ▸
  congrArg (· ^ _) (span_eq_of_le _ (by simp [G.mem_normBall, thetaNorm_thetaCoord]) fun _ h ↦
  G.mem_of_mem_normBall (x.thetaCoord_mem_thetaSpace bicharacter) le_rfl G.isAppellHumbert
  (x.thetaCoord_mem_thetaSpace bicharacter) h.1 (x.dualLattice_periodLattice ▸ fun _ ⟨_, a, e⟩ ↦ e ▸
  x.thetaShift_thetaCoord (s := ⟨_, a⟩) rfl bicharacter ▸ smul_mem _ (⟨_,
  (x.valuation_multiplier_mul_bicharacter _).le⟩ : v.integer) (by aesop)) h)

/-- The theta functions θ_t, t in T, have no common zero: for every z in V the vector (θ_t(z))_t
is non-zero. -/
lemma thetaCoord_vector_ne_zero z : (x.thetaCoord · z) ≠ 0 :=
  (x.isAppellHumbert_periodLattice.exists_apply_ne_zero z _ x.hasGoodReduction_trivial.4).rec fun _
  ⟨_, _⟩ h ↦ by
  obtain ⟨c, _, H, ⟨⟩⟩ := (x.hasGoodReduction_trivial.pow 1).exists_eq_smul_normBall
    (pow (x.thetaCoord_mem_thetaSpace 0) _) (by simp [thetaCoord_ne_zero]) (by simpa)
  have := (map_pow (mapHom (Pi.evalAlgHom _ _ z)) ..).le ⟨_,
    x.formSpan_eq_normBall x.hasGoodReduction_trivial .. ▸ H, rfl⟩
  simp_all [map_span, ← range_comp', bot_pow x.hasGoodReduction_trivial.4.ne_bot]
