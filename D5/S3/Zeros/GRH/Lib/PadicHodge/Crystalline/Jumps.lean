/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/Jumps
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/Jumps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Crystalline.Jumps. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Crystalline/Jumps.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Limit.LimitDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Diagonal Galois action on B tensor T written in matrix coordinates. Crystalline cocycles:
functoriality, coboundaries, cocycle rule, saturation. Hodge–Tate weights under base change, twists,
duals, subobjects, restriction of scalars. -/

noncomputable section

attribute [-simp] smul_assoc

variable {p : ℕ} [ThePrime p] {Γ ι B R T : Type _} [Group Γ] [Fintype ι] [OverGp Γ p] [CommRing B]
  [Algebra ℤ_[p] B] [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] [CommRing R]
  [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T]
  (ρ : Representation R Γ T) (e : Module.Basis ι ℤ_[p] T)

/-- The monoid homomorphism sending g in Γ to the matrix over Z_p of ρ(g) in a given finite
Z_p-basis e of T. -/
def repMatrix := (LinearMap.toMatrixAlgEquiv e).toMonoidHom.comp (overZp ρ)

/-- The action of Γ on B⊗T in the coordinates of the Z_p-basis e of T: on B^ι, g applies j(g)
coordinatewise, then the matrix of ρ(g). -/
def coordAction : Representation ℤ_[p] Γ (ι → B) := ⟨⟨fun g ↦
  ((repMatrix ρ e g).map (algebraMap _ B)).mulVecLin ∘ₗ actionRep _ _ toGp g, by aesop⟩, by
  simp [LinearMap.ext_iff, mul_smul, Matrix.mulVec_eq_sum, Finset.smul_sum]⟩

/-- For a Z_p-algebra B with G_p-action and a finite Z_p-basis e of T, the map b⊗x ↦ j(g)b⊗ρ(g)x
on B⊗T becomes, in the coordinates given by e, the action `coordAction` for the matrices
`repMatrix` of ρ in e. -/
lemma equivFun_tensorAction g y : (e.baseChange B).equivFun (tensorAction B (toGp g) (ρ g) y) =
  coordAction ρ e g ((e.baseChange B).equivFun y) := by
  ext; nth_rw 1 [← (e.baseChange _).sum_repr y, map_sum]
  simp [↓tensorAction_smul, tensorAction, coordAction, repMatrix, LinearMap.toMatrixAlgEquiv_apply,
    Matrix.mulVec_eq_sum, ← Algebra.smul_def]

variable {p : ℕ} {Γ R R' T T' : Type _} {c : Γ → T} [ThePrime p] [Group Γ] [CommRing R]
  [Algebra ℤ_[p] R] [CommRing R'] [Algebra ℤ_[p] R'] [AddCommGroup T] [Module R T] [Module ℤ_[p] T]
  [IsScalarTower ℤ_[p] R T] [AddCommGroup T'] [Module R' T'] [Module ℤ_[p] T']
  [IsScalarTower ℤ_[p] R' T'] [OverGp Γ p] {ρ : Representation R Γ T} {σ : Representation R' Γ T'}

lemma crysCocycles.map (h : c ∈ crysCocycles ρ) (f : T →ₗ[ℤ_[p]] _) (e : ∀ g x, f (ρ g x) =
  σ g (f x)) : f ∘ c ∈ crysCocycles σ := h.imp' (f.baseChange _) (by grind
  [tensorAction_periodTensorMap, =_ f.baseChange_tmul, baseChange_eq_periodTensorMap])

/-- Coboundaries are crystalline: for every x in T, the map g ↦ gx − x lies in Z_f(T). -/
lemma crysCocycles.coboundary_mem x : (ρ · x - x) ∈ crysCocycles ρ :=
  ⟨1 ⊗ₜ x, by simp [tensorAction, TensorProduct.tmul_sub]⟩

/-- If T is free over Z_p, every c in Z_f(T) is a cocycle: c(gh) = c(g) + g·c(h) for all g, h. -/
lemma crysCocycles.apply_mul [Module.Free ℤ_[p] T] : c ∈ crysCocycles ρ → ∀ g h, c (g * h) = c g + ρ
  g (c h) | ⟨_, e⟩, _, _ => Module.Flat.tensorProduct_mk_injective ℤ_[p] _ Bcris (by simp [e,
  TensorProduct.tmul_add, ← tensorAction_tensorAction, ← sub_eq_iff_eq_add', ← map_sub]; simp [↓← e,
  tensorAction])

/-- Saturation of Z_f(T): if a is a non-zero element of Z_p and a·c lies in Z_f(T), then c lies
in Z_f(T). -/
lemma crysCocycles.of_smul {a : ℤ_[p]} (ha : a ≠ 0) : a • c ∈ crysCocycles ρ → c ∈ crysCocycles ρ :=
  .imp' (algebraMap _ Bcris a.1⁻¹
  • ·) (by simp_all [↓tensorAction_smul, ← smul_sub, eq_inv_smul_iff₀, ← algebraMap_smul ℚ_[p] a])

open LinearEquiv Filter Module Submodule LinearMap Finset Classical hodgeTateMaps Algebra
  RingHomClass Fintype Finite IsAlgebraic Matrix

section

attribute [local simp] _root_.zpow_add Finsupp.single_apply toMatrix_apply funext_iff

variable {p : ℕ} [ThePrime p] {Γ R T T' R' ι κ : Type _} [Group Γ] [CommRing R] [AddCommGroup T]
  [Module R T] [Algebra ℤ_[p] R] [AddCommGroup T'] [OverGp Γ p] {ρ ρ' : Representation R Γ T}
  [CommRing R'] [Module R' T'] [Algebra ℤ_[p] R'] {σ : Representation R' Γ T'}
  {γ' : R' →ₐ[ℤ_[p]] ℂ_[p]} {φ : R' →+* R} {u : ℤ} {γ : R →ₐ[ℤ_[p]] ℂ_[p]}

/-- For a φ-semilinear map i: T' → T equivariant near 1, the Q̄_p-linear map f ↦ f∘i between the
spaces `hodgeTateMaps` for u, of T at γ and T' at γ' = γ∘φ. -/
def hodgeTateMaps.pull [RingHomCompTriple φ (toRingHom γ) γ'] (i : _ →ₛₗ[φ] T) (hi : ∀ᶠ g in nearOne
  Γ, ∀ x, i (σ g x) = ρ g (i x)) : hodgeTateMaps ρ γ u →ₗ[PadicAlgCl p] hodgeTateMaps σ γ' u :=
  ⟨⟨fun f ↦ ⟨f.1 ∘ₛₗ i, (i · |> f.2 |>.mp (hi.mp (by simp_all)))⟩, by tauto⟩, by tauto⟩

/-- Extension of scalars: if f: T → T' is semilinear along φ: R → R', maps a basis to a basis
and is equivariant near 1, R' algebraic over Z_p, then the jump u has the same multiplicity
for T' at γ' as for T at γ'∘φ. -/
lemma jump_baseChange {φ} (f : T →ₛₗ[toRingHom φ] _) (b : Basis ι R T) (b' : Basis ι R' T') (hb :
  ∀ i, f (b i) = b' i) (hf : ∀ᶠ g in nearOne Γ, ∀ x, f (ρ g x) =
  σ g (f x)) [Algebra.IsAlgebraic ℤ_[p] R'] : jump σ γ' u = jump ρ (γ'.comp φ) u :=
  have := RingHomCompTriple.mk (γ'.comp_toRingHom φ).symm
  finrank_eq {pull f hf,
    (Equiv.ofBijective (comp · f) (.of_comp_left (by simpa only [evalOnBasis, ← hb] using!
    (evalOnBasis b').bijective) (evalOnBasis b).injective)).subtypeEquiv fun F ↦ ⟨(pull f hf ⟨F, ·⟩
  |>.2), (mem_hodgeTateMaps_of_span b'.span_eq fun i ↦ · (b i) |>.mp (hf.mp (by aesop)))⟩ with}

/-- If ρ'(g) = a(g)ρ(g) with scalars a(g) in R, and some nonzero y in C_p has γ(a(g))y =
χ(g)^(−v)·g y near 1, then the multiplicity of the jump u+v of ρ' at γ equals that of u for
ρ. -/
lemma jump_twist_of_period (a : Γ → R) {v y} (hy : y ≠ 0) (h : ∀ᶠ g in nearOne Γ, γ (a g) * y =
  (χ g ^ (-v)).1 • toGp g • y) (e : ∀ g x, ρ' g x = a g • ρ g x) : jump ρ' γ (u + v) = jump ρ γ u :=
  finrank_eq ((((smulOfNeZero _ _ _ hy).restrictScalars _).ofSubmodule' _).symm ≪≫ₗ
  ofEq _ _ (ext fun _ ↦ forall_congr' fun _ ↦ eventually_congr (h.mp (by simp_all
    [← mul_assoc, mul_smul, ← Algebra.mul_smul_comm, smul_eq_zero_iff_eq]))))

variable [Module.Finite R T]

lemma jump_eq_zero_iff : jump ρ γ u = 0 ↔ ∀ f ∈ hodgeTateMaps ρ γ u, f = 0 :=
  finrank_eq_zero.trans eq_bot_iff

/-- For j with open image and T finitely generated over R, there is a natural number a such that
every jump k of T at γ (nonzero multiplicity) satisfies −a ≤ k ≤ a. -/
lemma exists_jump_bound : ∃ a : ℕ, ∀ k, jump ρ γ k ≠ 0 → -a ≤ k ∧ k ≤ a :=
    (exists_fun_fin_finrank_span_eq _ (∃ u, · ∈ _)).elim fun _ witness ↦ by
    obtain ⟨h, e, _⟩ := witness
    exact (skolem.1 h).rec fun a h ↦ (exists_le (a · |>.natAbs)).imp fun _ b _ ↦ Not.imp_symm fun n ↦ jump_eq_zero_iff.2 fun _ m ↦
    (span_eq_bot.2 (by grind)).le (mem_span_same_weight h m (e.ge (subset_span ⟨_, m⟩)))

variable [Algebra.IsAlgebraic ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [Free R T]

/-- For R algebraic over Z_p, j with open image, T finite free potentially crystalline, and b:
T' → Hom_R(T,R) bijective with b(gx,gy) = χ(g)^c b(x,y), the jump −u−c of T' at γ has the
multiplicity of the jump u of T. -/
lemma jump_eq_of_pairing [Module R T'] {σ} (h : IsPotCrys ρ) (b : T' ≃ₗ[R] T →ₗ[R] R) c (e :
  ∀ g x y, b (σ g x) (ρ g y) = (χ g ^ c).1 • b x y) : jump σ γ u = jump ρ γ (-u - c) := by
  let v := Free.chooseBasis R T; let w := v.dualBasis.map b.symm; choose P k H J using
    h.exists_isHodgeTateFrame v γ
  simp [Multiset.count_map, sub_eq_iff_eq_add, neg_eq_iff_eq_neg,
    (hasJumps_of_rows w (unitOfInvertible
    P.1ᵀ) (-c + -k) (H.mono fun g H i l ↦ by simpa [↓mulVec_mulVec, ← Matrix.map_mul, e, w, ←
    toMatrix₂_compl₂, Matrix.mul_apply, mul_comm, mulVec_apply_eq_sum, smul_smul, apply_ite]
    using congr((χ g
    ^ k i).1 • ((toMatrix₂ w v (b.1 ∘ₗ σ g)).map γ *ᵥ $(H (Pi.single i 1))) l))).1 _, J.1 _]

/-- For R algebraic over Z_p, j with open image and T finite free over R: if Γ acts on T through
χ^c, the jumps at γ are −c, repeated rank T times. -/
lemma hasJumps_of_cyclotomicGp_zpow c (h : ∀ g x, ρ g x = (χ g ^ c).1 • x) :
  HasJumps ρ γ (.replicate (finrank R T) (-c))
  := have := γ.domain_nontrivial; by simpa using (hasJumps_of_rows (finBasis ..) 1 (-c) (by
    simp_all [LinearMapClass.map_smul_of_tower (S := R), eq_comm, one_apply, apply_ite])).1

omit [Module.Finite R T] [Algebra.IsAlgebraic ℤ_[p] R] [Free R T] in
/-- If ρ' is the twist of ρ by χ^c on T, then the multiplicity of the jump u−c of ρ' at γ equals
that of the jump u of ρ. -/
lemma jump_twist_cyclotomicGp c (e : ∀ g x, ρ' g x = (χ g ^ c).1 • ρ g x) : jump ρ' γ (u - c)
    = jump ρ γ u := jump_twist_of_period _ one_ne_zero (by simp) (e · · ▸ (smul_one_smul ..).symm)

variable [IsDomain R] [Fintype κ] {S : ι → _} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i,
  Module ℤ_[p] (S i)] [∀ i, IsScalarTower ℤ_[p] R (S i)] [∀ i, Free R (S i)] [∀ i, Module.Finite R
  (S i)] {τ : ∀ i, Representation R Γ (S i)} (h : ∀ i, IsPotCrys (τ i)) (e : Basis κ R' T')
  {δ : ι → R →ₐ[ℤ_[p]] ℂ_[p]} [∀ i, RingHomCompTriple φ (toRingHom (δ i)) γ'] (f : ∀ i, T' →ₛₗ[φ] S
  i) (hf : ∀ i, ∀ᶠ g in nearOne Γ, ∀ x, f i (σ g x) = τ i g (f i x)) (hi : LinearIndependent
  ℂ_[p] fun a (l : Σ i, Fin (finrank R (S i))) ↦ δ l.1 ((finBasis ..).coord l.2 (f _ (e a))))

include hi in
omit [Algebra.IsAlgebraic ℤ_[p] R] [∀ i, Module ℤ_[p] (S i)] [∀ i, IsScalarTower ℤ_[p] R (S i)] in
lemma top_le_span_pullback {m} (b : ∀ i, Basis _ ℂ_[p] (_ →ₛₗ[toRingHom (δ i)] ℂ_[p])) : ⊤ ≤
  span ℂ_[p] (.range fun y : Sigma m ↦ b _ y.2 ∘ₛₗ f _) := (orderIsoMapComap (evalOnBasis e)).2.1
  (le_top.trans (span_flip_eq_top_iff_linearIndependent.2 hi ▸ span_le.2 fun _ ⟨_, h⟩ ↦ ⟨_,
  mapsTo_span (f := id.compl₂ _) (by aesop) ((b _).mem_span ((δ _).toSemilinearMap ∘ₛₗ _)), h⟩))

include hi h hf in
/-- Let j(Γ) be open, R a domain algebraic over Z_p, S_i finite free potentially crystalline
over R, γ_i∘φ = γ', f_i: T' → S_i φ-semilinear, equivariant near 1, with the vectors
(γ_i(l(f_i e_a)))_{i,l} ℂ_p-independent, e a finite basis of T', l in the dual of S_i. Every
jump of T' at γ' is a jump of some S_i at γ_i. -/
lemma exists_jump_of_linearIndependent : jump σ γ' u ≠ 0 → ∃ i, jump (τ i) (δ i) u ≠ 0 := by
  choose _ _ _ _ b hb _ using (h · |>.exists_isHodgeTateFrame (finBasis ..) _); have := of_basis e
  contrapose; simpa [jump_eq_zero_iff] using fun z _ m ↦ (span_eq_bot.2 (by aesop)).le
    ((mem_span_same_weight · m (top_le_span_pullback e f hi b ⟨⟩)) (pull _ (hf _) ⟨_,
    hb _ ·.2⟩ |>.2))

include h in
omit [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] in
/-- Let R be a domain algebraic over Z_p, j of open image, and T finite free with jointly
injective equivariant R-linear maps to finitely many finite free potentially crystalline
S_i. Then every jump of T at γ is a jump of some S_i at γ. -/
lemma exists_jump_of_jointly_injective [Fintype ι] (f : ∀ _, T →ₗ[R] _) (hf : ∀ i g x, f i (ρ g x) =
  τ i g (f i x)) (hi : ∀ x, (∀ i, f i x = 0) → x = 0) : jump ρ γ u ≠ 0 → ∃ i, jump (τ i) γ u ≠ 0 :=
  let := γ.toAlgebra; let := faithfulSMul_tower_top ℤ_[p] R ℂ_[p]
    exists_jump_of_linearIndependent h _ f (by simp [hf]) (linearIndependent_algebraMap_comp_iff.2
  ((finBasis R T).linearIndependent.map' ((Pi.basis fun _ ↦ finBasis ..).equivFun.1 ∘ₗ pi f)
  (by simpa [ker_eq_bot'])))

variable [Module ℤ_[p] T'] [FaithfulSMul ℤ_[p] R] (f : ∀ i, T' →ₗ[ℤ_[p]] S i) (e : Basis κ ℤ_[p] T')

/-- Let R ⊃ Z_p be an algebraic domain, S_i finite free over R, f_i: T' → S_i jointly injective
Z_p-linear, (e_a) a finite Z_p-basis of T'. The vectors v_a = (γ(l-th coordinate of f_i
e_a))_{i,γ,l}, γ: R → C_p over Z_p, are C_p-linearly independent. -/
lemma linearIndependent_emb_coords (hi : ∀ x, (∀ i, f i x = 0) → x = 0) :
  LinearIndependent ℂ_[p] fun a (l : Σ i : ι ×
  (R →ₐ[ℤ_[p]] ℂ_[p]), Fin (finrank R (S i.1))) ↦ l.1.2 ((finBasis ..).coord l.2 (f _ (e a))) := by
  refine linearIndependent_iff'.2 (bot_unique (le_of_hodgeTate_stable le_top 0 _ _ ?_ ?_)) <;> intro
    a h g
  ext; simpa [smul_sum] using congr(g • $h ⟨(_, (MulSemiringAction.toAlgHom _ _ g⁻¹).comp _), _⟩)
  intro n _ _ t
  choose b e' using ((InfiniteGalois.mem_bot_iff_fixed _).2 <| t ·); cases funext e'
  let c a : ℤ_[p] := ⟨_, by simpa using n a⟩
  let γ : R →ₐ[ℤ_[p]] ℂ_[p] := IsAlgClosed.lift; algebraize [γ.1]
  simpa [c] using (congr($(linearIndependent_iff.1 e.linearIndependent c (hi _ fun _ ↦ (finBasis
    ..).forall_coord_eq_zero_iff.1 fun _ ↦ (faithfulSMul_tower_top ℤ_[p] ..).algebraMap_injective _
    _ (by simpa [smul_def'] using! congrFun g ⟨(_, _), _⟩ : γ _ = γ _)) ·).1))

/-- For Z_p-linear maps f_i: T' → S_i and a pair (i, γ), the map f_i regarded as semilinear
along the structure map Z_p → R; it does not depend on γ. -/
def asSemilinear (i : ι × κ) : T' →ₛₗ[algebraMap ℤ_[p] R] S i.1 := ⟨f i.1, by simp⟩

instance : RingHomCompTriple (algebraMap ..) (toRingHom γ) (toRingHom (ofId ℤ_[p] _)) := ⟨by simp⟩

variable [Module.Finite ℤ_[p] R]

instance : Fintype (R →ₐ[ℤ_[p]] ℂ_[p]) := ofFinite _

@[simp] lemma card_algHom_eq_finrank : card (R →ₐ[ℤ_[p]] ℂ_[p]) = finrank ℤ_[p] R :=
  (card_eq_nat_card ▸ card_algHom_le_finrank ..).antisymm (by simpa using
  (linearIndependent_emb_coords (R := R) ![.id] (finBasis _ R) (by simp)).fintype_card_le_finrank)

attribute [-simp] toRingHom_ofId

/-- For j of open image, R a domain finite free over Z_p, T finite free over R and potentially
crystalline: jump multiplicities over Z_p are Σ_γ jump_γ(u), and weight-u maps f with f(ζt)
= w f(t) span a C_p-space of dimension at most Σ_{γ(ζ)=w} jump_γ(u). -/
lemma IsPotCrys.sum_jump_eq_jump_overZp (h : IsPotCrys ρ) : (∀ u, ∑ γ, jump ρ γ u =
  jump (overZp ρ) (ofId ..) u) ∧ ∀ ζ w u F, (∀ f ∈ F, f ∈ hodgeTateMaps (overZp ρ) (ofId ..) u ∧
  ∀ t, f (ζ • t) = w * f t) → finrank ℂ_[p] (span ℂ_[p] F) ≤ ∑ γ with γ ζ = w, jump ρ γ u := by
  let e := (finBasis ℤ_[p] R).smulTower (finBasis _ T); let := of_basis e
  choose _ k _ J b hb _ using h.exists_isHodgeTateFrame (finBasis ..); let B :=
    basisOfTopLeSpanOfCardEqFinrank _
    (top_le_span_pullback e (asSemilinear ![.id]) (linearIndependent_emb_coords (R :=
    R) ![_] e (by simp)) (b ·.2)) (by simp [(evalOnBasis e).finrank_eq])
  have M y :
    B y ∈ hodgeTateMaps (overZp ρ) _ (k y.1.2 y.2) := by simpa [B, asSemilinear] using! hb _ _
  use ?_, fun ζ w u _ H ↦ ((finrank_span_le_card (B '' {y | _ ∧ _})).trans' (finrank_mono (span_le.2
    fun f m ↦ B.mem_span_image.2 fun y hy ↦ ⟨by simpa [mul_comm w, by simpa using hy] using
    (B.ext_elem_iff.1 (ext fun t ↦ by simpa [B, asSemilinear, *] using congr($(B.sum_repr f) (ζ •
    t)) : ∑ z, B.1 f z • z.1.2 ζ • B z = w • f) y), B.mem_span_image.1 ((span_subset_span ..)
    (mem_span_same_weight M (H f m).1 (by simp))) hy⟩))).trans ?_ <;> simp [J _ _, B.injective,
    card_image_of_injective, ↓Multiset.count_map, ← filter_val, eq_comm, hasJumps_of_basis M _,
    card_filter, sum_prod_type, Fintype.sum_sigma, sum_filter, ite_and, -sum_boole]
