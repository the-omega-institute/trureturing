/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.PairSumNegation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/PairSumNegation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Finite-place action of a dual pair on data; explicit scalars at split places. Theta
functional is canonical, transported by isometries, multiplicative on orthogonal sums. Theta kernels
under orthogonal sums (seesaw factorisation) and negation of the form. -/

section

open Fintype G Gf Kronecker Matrix NumberField Space Unitary

section

attribute [local simp] onHom_snd mem_Kf_iff pairWeil

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n' : Type} [Fintype n] [Fintype n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
  {Ψ : (n' × n → 𝔸f E) → ℂ} [hΨ : IsSchwartzBruhat (E := E) (n := n' × n) A Ψ]
  {p : G (n := n) E s × G (n := n') E s'} {w : FinPlace E} (g : Gf E n)

lemma detOn_star : detOn (star ⁻¹' A) g.1 = star (detOn A g.1)⁻¹ := by
  ext <;> simp [detOn, cutGL, star_idem, ← det_conjTranspose, inv_eq_left_inv g.2]

@[simp↓] lemma onHom_snd_inv_mulVec x : (onHom p).2⁻¹.1.1 *ᵥ x =
  matToVec (p.2.2⁻¹.1.1 * vecToMat x * p.1.2.1.1) := kronecker_mulVec_eq_matToVec ..

@[simp] lemma G.onHom_atPlace : ((onHom p).2.atPlace w).1 =
  (p.2.2.atPlace w).1 ⊗ₖ (p.1.2⁻¹.atPlace w).1ᵀ := rfl

@[simp↓] lemma G.onHom_mem_supportedOn : p.1.2 ∈ supportedOn n A → p.2.2 ∈ supportedOn _ A →
  (onHom p).2 ∈ supportedOn _ A := by aesop

@[simp] lemma G.onHom_atPlace_mem : p.1.2.atPlace w ∈ Kw .. → p.2.2.atPlace w ∈ Kw .. →
  (onHom p).2.atPlace w ∈ Kw .. := by simp_all [mem_intGL, ← map_inv, ← Prod.snd_inv, mul_mem]

/-- The homomorphism sending a norm-one finite adele to the corresponding scalar matrix in the
finite adelic unitary group of rank n. -/
noncomputable def scalarFin (n : Type) [Fintype n] : unitary (𝔸f E) →* Gf E n := .codRestrict
    (.comp (GeneralLinearGroup.scalar n) toUnits) _ (by simp [star_mul_self_of_mem, U])

lemma commute_scalarFin {ν} : Commute (scalarFin n ν) g :=
  Subtype.ext (GeneralLinearGroup.scalar_commute ..)

lemma G.det_of_supportedOn (hA : A.IsConjDisjoint) {g} (hg : g ∈ supportedOn n A) : detFin s g =
  divStar (detOn A g.1) := by
  ext1; convert! congr(_ * $(detOn_star _).1); ext <;> simp_all
  split_ifs <;> simp_all; grind

lemma G.mat_scalarFin ν : mat (s := s) (1, scalarFin n ν) =
  ((1, ν.1) : 𝔸 E) • 1 := by simp [scalarFin]; aesop

lemma G.onHom_scalarFin ν ν' : (onHom ((1, scalarFin n ν), 1, scalarFin _ ν') : G E (homSigns s
  s')) = (1, scalarFin _ (ν' / ν)) := ext_mat (by simp [← map_inv, ↓mat_scalarFin]; aesop)

end

variable {E : Type*} [Field E] [CMType E] {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} {A : Set (FinPlace E)} (hA : A.IsConjDisjoint) {Ψ : (n' × n → 𝔸f E) → ℂ}
  [hΨ : IsSchwartzBruhat (E := E) (n := n' × n) A Ψ] {p : G (n := n) E s × G (n := n') E s'}
  {w : FinPlace E} (g : Gf E n) [WeilData E] {S : Space E n s} {T : Space E _ s'} {a : AutChar E}
  {b : AutChar E} {g : _} {h} {f : 𝒮 (S.hom T)}

/-- The finite multiplier Δ_f of (g, 1), acting on Hom(S,T) by x ↦ x g⁻¹, is Δ_f(g_f⁻¹)^(n'),
where n' is the rank of the second space. -/
lemma finMultiplier_onHom_left {g : G E s} : finMultiplier (onHom (s' := s') (g, 1)).2 =
  finMultiplier g.2⁻¹ ^ card n' := by erw [finMultiplier, Sat.glMultiplier_transpose
  ((saturatingElem _).2.map_of_le_comap (by use! (1 ⊗ₖ ·) <;> simp [kronecker_add]) fun _ _ _ ↦ _),
  ← map_pow] <;> congr <;> aesop

lemma pairWeil_eq_smul_of_projOn_eq A (hf : projOn _ A f = f) (hg : g ∈ Kf .. ⊓ supportedOn n A)
  (hh : h ∈ Kf .. ⊓ supportedOn _ A) : pairWeil S T a b (g, h) f = (a.1 (detFin s' h) *
  (b.1 (detFin s g))⁻¹).1 • f := by simp; rw [onHom_fin, ω_of_mem_Kf _ _ hf] <;> aesop

lemma projOn_pairWeil (hf : projOn _ A f = f) p (h : ∀ w ∈ A, (onHom p).2.atPlace w ∈ Kw .. := by
  aesop) : projOn _ A (pairWeil S T a b p f) = pairWeil S T a b p f := by simp_all [← ω_projOn]

include hA

/-- For A ∩ Ā = ∅, Ψ Schwartz–Bruhat above A, and finite g, h supported on A ∪ Ā:
ω_{a,b}(g,h)(Ψ⊗f) = χ_S(det h_A) χ_T(det g_A)⁻¹ |det g_A|^{n′/2} |det h_A|^{−n/2} ·
Ψ(h⁻¹·g)⊗f, with n = rk S, n′ = rk T, and χ_S, χ_T given by `AutChar.spaceChar`. -/
lemma pairWeil_name_on (hg : g ∈ supportedOn n A) (hh : h ∈ supportedOn n' A) f : pairWeil S T a b
  (g, h) (name _ A Ψ f) = ((a.spaceChar (card n)).1 (detOn A h.1) / (b.spaceChar (card n')).1
  (detOn A g.1) * √(ideleAbs (detOn A g.1)) ^ card n' / √(ideleAbs (detOn A h.1)) ^ card n : ℂ) •
  name _ A (Ψ <| matToVec <| h⁻¹.1.1 * vecToMat · * g.1.1) f := by
  rw [pairWeil_apply, onHom_fin, ω_name_on, smul_smul, eq_div_of_mul_eq'
    (by aesop : detOn A _ * detOn A g.1 ^ card n' = detOn A h.1 ^ card n)] <;>
    simp [det_of_supportedOn hA, AutChar.spaceChar, AutChar.baseChange_apply_coe_toFun, *]
  congr 1; simp [chiAdelic, mul_pow, field, ← Complex.inv_eq_conj]

/-- Let A ∩ Ā = ∅, Ψ be Schwartz–Bruhat above A, and g, h adelic with finite parts g_f, h_f
integral at all finite places (in K₀). Then ω_{a,b}(g,h)(Ψ ⊗ f) = Ψ′ ⊗ ω_{a,b}(g,h)f, with
Ψ′(x) = Ψ(h_f⁻¹xg_f). -/
lemma pairWeil_name_of_mem (hg : g.2 ∈ Kf ..) (hh : h.2 ∈ Kf ..) f : pairWeil S T a b (g, h)
    (name _ A Ψ f) = name _ A (Ψ <| matToVec <| h.2⁻¹.1.1 * vecToMat · * g.2.1.1) (pairWeil S T a b
  (g, h) f) := by rw [pairWeil_apply, (omega_name ..).2, (funext _ : (boxIndicator _ _ <| _ *ᵥ ·) =
  _), name_boxIndicator, ω_projOn] <;> simp_all [name_projOn, mulVec_mem_integralBox, -onHom_snd]

end

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n₁ n₂ : Type _} [Fintype n] [Fintype n₁]
  [Fintype n₂] {s : n → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {σ : ℂ →+* ℂ} [RingHomIsometric σ]
  (D : Std (n₁ := n₁) E σ s₁ s) {W V : Space E n s} (V₁ : Space E n₁ s₁)

/-- Let φ be a vacuum-preserving change of coordinates with twist σ, and let g send every x with
φx rational for V₁ to a rational vector of V. Then some c of modulus one has θ_V(c ω(g) f^φ)
= σ(θ_{V₁}(f)) for all f. -/
lemma Std.exists_theta_omega_map [RingHomInvPair σ σ] V g (hΓ : ∀ x, D.φ x ∈ Space.ratVectors V₁ →
  g • x ∈ Space.ratVectors V) : ∃ c, ‖c‖ = 1 ∧ ∀ f, V₁.θ f = c * σ (V.θ (V.ω g (D.map f))) := by
  obtain ⟨h, k⟩ := V.isThetaFunctional_rawTheta.comp _ (_ ∘SL _) (D.φ.symm.trans (.mk' (.smul g) _))
    (by aesop) (by simp_intro ..; erw [← Space.ω_ϱ, ← D.map_ϱ]; aesop)
    (D.map_vacElem ▸ (Space.dataInner_omega ..).trans
    V.dataInner_vacElem_vacElem), congr(√‖$(V₁.isThetaFunctional_rawTheta.2)‖)
  peel h.eq_smul V₁.isThetaFunctional_rawTheta.1; simp_all [Space.theta_eq_rawTheta,
    mul_mul_mul_comm ‹ℂ›, h.2, -ContinuousLinearMap.comp_apply]; tauto

attribute [local simp] Function.comp_def blockEmb diagonal Space.vecAtPoint dotProduct funext_iff
  mem_ratVectors

/-- For two spaces V, W with the same signs, some element g of the adelic unitary group G
carries the rational vectors of V (in standard adelic coordinates) into those of W. -/
lemma Space.exists_mapsTo_ratVectors : ∃ g : G E s, ∀ γ ∈ V.ratVectors, g • γ ∈ W.ratVectors :=
  (W.exists_eq_move V).elim
  (.imp fun | _, e, _, ⟨y, rfl⟩ => ⟨· *ᵥ y, by simp [e.2, mat, RingHom.map_mulVec]⟩)

/-- If g carries the rational points of the sum of lines with signs s into those of V, then
θ_V(ω(g)ϱ(x)vac) = ∏_i θ_i(ϱ(x_i)vac) for all adelic x, θ_i the chosen theta functional of
the line of sign s_i. -/
lemma Space.theta_vacElem_eq_prod_lineTheta {g} (h : ∀ γ ∈ (signedSpace E s).ratVectors, g • γ ∈
  V.ratVectors) x : V.θ (V.ω g (V.ϱ x V.vacElem)) = ∏ i, lineTheta (s i) (x i) := (V.mem_Γ_iff_range
  (g := g * _).2 (Function.swap (by simpa [-Pi.single_apply, Pi.apply_single fun _ ↦ @toAdele E ..]
  using! (V.mem_ratVectors_iff.1 <| h _ <| exists_mapsTo_ratVectors.choose_spec _ ⟨Pi.single · 1,
  rfl⟩)))).elim fun γ ↦ by erw [← theta_omega_ratEmbed γ⁻¹, theta_eq_rawTheta, rawTheta,
  dite_eq_left exists_mapsTo_ratVectors, ← exists_isThetaFunctional_signedSpace.choose_spec.2,
  ContinuousLinearMap.comp_apply, rep_apply_apply, rep_apply_apply]; aesop

lemma Space.vacElem_apply_eq_prod_lineTheta (h : ∀ y, V.vecAtPoint y =
  (signedSpace E s).vecAtPoint y) x : V.vacElem x = ∏ i,
  lineTheta (s i) (x i) := by simp_all [← V.theta_vacElem_eq_prod_lineTheta (g := 1), ratVectors]

/-- Suppose the coordinates of V split into two parts with signs s₁, s₂ and the point of V is
block diagonal with blocks the points of V₁, V₂. Then θ of the product of f₁ and f₂ is
θ(f₁)θ(f₂). -/
lemma Space.theta_boxProd {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) {V₁ V₂} (h : V.x.1.submatrix e
  e = fromBlocks V₁.x 0 0 V₂.x) f₁ f₂ : V.θ (V.boxProd hs f₁ f₂) = θ V₁ f₁ * θ V₂ f₂ := by
  obtain ⟨⟨g, a⟩, ⟨k, b⟩, _⟩ := V₁.exists_mapsTo_ratVectors, V₂.exists_mapsTo_ratVectors, id hs
  congrm($((V₁.ext_of_vacElem g fun _ ↦ V₂.ext_of_vacElem k fun _ ↦ ?_ :
    .postcomp _ V.θ ∘L boxProd _ = .smulRight V₁.θ _)) _ _); simp [-θ_apply]
  rw [theta_vacElem_eq_prod_lineTheta a, theta_vacElem_eq_prod_lineTheta b, ← omega_boxProd (g :=
    blockEmb hs (g, k)), boxProd_rho, boxProd_vacElem, theta_vacElem_eq_prod_lineTheta] <;> simp_all
    [mem_ratVectors_iff, reindex_equiv e, signedSpace, entrywise]

end

attribute [-simp] map_zero

open NumberField Matrix WeilData Space Equiv Std Fintype G ComplexConjugate Weil Int
variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n n' n₁ n₂ : Type} [Fintype n] [Fintype n'] [Fintype n₁] [Fintype n₂] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) {S V : Space E n s}
  {V₁ : Space E n₁ s₁} {V₂ : Space E n₂ s₂} {T : Space E n' s'} (a b b' : AutChar E) {g : G E s}
  {g₁ : G E s₁} {g₂ : G E s₂}

omit [WeilData E] in
lemma Space.mem_ratVectors_hom {x} : x ∈ (S.hom T).ratVectors ↔
  T.x.1 * vecToMat x * S.x⁻¹.1 ∈ ratMatrices .. := by simp [mem_ratVectors_iff, hom,
  kronecker_mulVec_eq_matToVec, mem_ratVectors, mem_ratMatrices, matToVec]

attribute [local simp] funext_iff pairSign pairWeil mat_inv stdForm mem_ratVectors_hom
  weilMultiplier realMultiplier U.principalMinor_compl ContinuousAddEquiv.mk' Subtype.ext_iff

attribute [local simp ←] ext_iff Complex.inv_eq_conj AddChar.map_neg_eq_inv

omit [Fintype n] [Fintype n'] [Fintype n₁] [Fintype n₂] in
lemma homSigns_sum_target (hs : s ∘ e = s₁ ⊕ᵥ s₂ := by exact signs_comp_refl) :
  homSigns s' s ∘ (sumProdDistrib ..).symm.trans
  (e.prodCongr (.refl _)) = homSigns s' s₁ ⊕ᵥ homSigns s' s₂ := by aesop

omit [Fintype n'] [Fintype n₁] [Fintype n₂] in
lemma homSigns_sum_source : homSigns (s₁ ⊕ᵥ s₂) s' ∘ (prodSumDistrib ..).symm =
  homSigns s₁ s' ⊕ᵥ homSigns s₂ s' := by simp

lemma normNegOne_inv : normNegOne⁻¹.1.1 = -star (normNegOne.1.1 : 𝔸f E) := rfl

/-- The negation change of coordinates from Hom(S⁻,T) to Hom(S,T): x ↦ (1, c⁻¹)x, c the chosen
element of Ô of norm −1; it conjugates β. -/
noncomputable def negSource : Std E conj (homSigns s s') (homSigns (-s) s') := by
  use .mk' (.smul (normNegOneIdele E)⁻¹) ?_, .refl _, .mk' (.smul (normNegOne (E := E))⁻¹)
    (by simp) <;> simp [adelicSum, dotProduct, ↓Heisenberg.conj_β, neg_add_eq_sub, Units.smul_def,
    intVectors, mem_Ô, isUnit_Ô.1, Subring.smul_def, normNegOneIdele, mul_left_comm, realHeis,
    stdLattice, signMatrix, normNegOne_inv, mul_comm normNegOne.1.1, mul_assoc]

lemma weilMultiplier_neg {t} {g₁ : G E t} : s = -t → g.mat = g₁.mat → conj (weilMultiplier g₁) =
  upsilonU1.1 g₁.det * weilMultiplier g := by rintro ⟨⟩ h; erw [ext_mat (h.trans g₁.mat_neg.symm),
  upsilon_eq_prod_mul_of_v_eq, G.neg] <;> simp -implicitDefEqProofs
 [MulEquiv.prodCongr, field, -coe_det, ← units_ne_iff_eq_neg, ← upsilon_mul_finMultiplier]

omit [WeilData E] in
@[simp] lemma G.det_neg : g.neg.det = g.det := by simp

/-- The negation map from data on Hom(S,T) to data on Hom(S⁻,T) carries ω_{a,b}(g,h) to ω_{a⁻¹υ^n,
b⁻¹υ^(n')}(g.neg,h), with n, n' the ranks of S, T. -/
lemma pairWeil_negSource h f : pairWeil S.neg T (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card
  n') (g.neg, h) (negSource.map f) = negSource.map (pairWeil S T a b (g, h) f) := by
  simp; rw [ω_map _ _ (weilMultiplier_neg ..), det_onHom]; match_scalars; simp [field]
  repeat simp [negSource, ← map_inv]

variable (S T)

/-- There is a complex number c of modulus one such that, for every datum f on Hom(S,T), θ on
Hom(S⁻,T) of c times the negation of f is the complex conjugate of θ(f). -/
lemma exists_theta_negSource : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, (S.neg.hom T).θ (c • negSource.map f) =
    conj ((S.hom T).θ f) := .imp' _ (by aesop) (negSource.exists_theta_omega_map (S.hom T) _ 1 (by
  simp_intro .. [Space.neg]; rwa [← smul_mul, ← T.x.1.mul_smul]))

/-- If the point of V is, along the splitting e of coordinates, the block diagonal sum of those
of V₁ and V₂, then θ(f ⊠ f') on Hom(T,V) equals θ(f)θ(f') for data f, f' on Hom(T,V₁),
Hom(T,V₂). -/
lemma theta_boxProd_target (h : V.x.1.submatrix e e = fromBlocks V₁.x 0 0 V₂.x) f f' :
  (T.hom V).θ (boxProd (homSigns_sum_target hs)
  f f') = (T.hom V₁).θ f * (T.hom V₂).θ f' := theta_boxProd _ (by simp_all [Space.hom]) ..

/-- For data f on Hom(V₁,T) and f' on Hom(V₂,T), the theta functional of Hom(V₁ ⊕ V₂, T) at f ⊠
f' equals θ(f)θ(f'). -/
lemma theta_boxProd_source f f' : ((V₁.sum V₂).hom T).θ (boxProd homSigns_sum_source f f') =
    (V₁.hom T).θ f * (V₂.hom T).θ f' := theta_boxProd _ (by simp [Space.hom, Space.sum, blockGL]) ..

/-- The Weil action of a pair respects a sum in the first space: on Hom(V₁ ⊕ V₂, T),
ω_{bb',a}(diag(g₁,g₂), h)(f ⊠ f') = ω_{b,a}(g₁,h)f ⊠ ω_{b',a}(g₂,h)f' for data f on
Hom(V₁,T) and f' on Hom(V₂,T). -/
lemma pairWeil_boxProd_source h f f' : pairWeil (V₁.sum V₂) T (b * b') a (.sum (g₁, g₂),
  h) (boxProd homSigns_sum_source f f') = boxProd homSigns_sum_source (pairWeil V₁ T
  b a (g₁, h) f) (pairWeil V₂ T b' a (g₂, h) f') := by
  simp [show (G.sum (g₁, g₂)).det = g₁.det * g₂.det by simp]; rw [omega_boxProd]; module; simp

/-- If g is block diagonal with blocks g₁, g₂ along the splitting e of coordinates, then on
Hom(T,V), ω_{a,bb'}(h,g)(f ⊠ f') = ω_{a,b}(h,g₁)f ⊠ ω_{a,b'}(h,g₂)f' for data f, f' on
Hom(T,V₁), Hom(T,V₂). -/
lemma pairWeil_boxProd_target (H : g.mat.submatrix e e = fromBlocks g₁.mat 0 0 g₂.mat) h f f' :
  pairWeil T V a (b * b') (h, g) (boxProd (homSigns_sum_target hs) f f') = boxProd
  (homSigns_sum_target hs) (pairWeil T V₁ a b (h, g₁) f) (pairWeil T V₂ a b' (h, g₂) f') := by
  simp [show g.det =
    g₁.det * g₂.det by simpa using congr(det $H)]; rw [omega_boxProd]; module; aesop
