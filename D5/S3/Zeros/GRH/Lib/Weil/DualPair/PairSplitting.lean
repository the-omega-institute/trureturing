/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSplitting
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/PairSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.PairSplitting. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/PairSplitting.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Landherr.WeakApprox
import D5.S3.Zeros.GRH.Lib.Weil.Fock.OscillatorPair
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.AdaptedSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Adelic Weil representation of a unitary group and the invariant theta functional.
The form here treats CM fields with enough roots of unity, a splitting character and a self-dual
rank-one lattice, and it uses no polarisation. Vectors are integrable coefficients against a vacuum,
the vacuum coefficient fixes the splitting, and the sign of the finite cocycle comes from a
congruence modulo 4. Source: A. Weil, Sur certains groupes d'opérateurs unitaires, Acta Math. 111
(1964), n° 16-19 Thm 4, n° 41 Thm 6; S. Kudla, Splitting metaplectic covers of dual reductive pairs,
Israel J. Math. 87 (1994) 361-401; H. Reiter, Metaplectic Groups and Segal Algebras, LNM 1382 (1989)
(space of data, after H. Feichtinger, On a new Segal algebra, Monatsh. Math. 92 (1981)); E. Zelenov,
p-adic Heisenberg group and Maslov index, Comm. Math. Phys. 155 (1993) 489-502, Prop. 4 (cocycle of
three lattices); Robinson and Rawnsley, Mem. AMS 410 (1989) (real normalisation).

Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Rational points of the unitary group fix the theta functional, by doubling. Kronecker
coordinates of rational maps on the Hom space; invertible Gram matrix. Dual pair acting on Hom(S,T):
determinants, continuity, unitarity, automorphy of theta kernels. Mixed model for a dual pair: Levi
and unipotent action, theta expansion. -/
seal Finset.univ Finset.sum Finset.prod

open Fintype G Kronecker MatMul Matrix RingHom Space WeilData Splitting

section

variable {E : Type*} [Field E] [CMType E] {n p : Type _} [Fintype n] {s : n → ℤˣ} {V : Space E n s}
  [Fintype p] {n₁ n' : Type} [Fintype n₁] [Fintype n'] {s₁ : n₁ → ℤˣ} {s' : n' → ℤˣ}
  {V' : Space E n₁ s₁} (T : Space E n' s') {m m' R : Type*}

seal dotProduct in
lemma Space.theta_omega_ratEmbed_of_mul_k [WeilData E] (γ : U V.J) (D :
  V.Splitting (stdSpace E Empty) p) (a : GL p E)
  (h : γ.1.1 * D.k = D.k * a.1) f : V.θ (V.ω (V.ratEmbed γ) f) = V.θ f := ((splittingOfGram _
  (D.gram_eq_hypSum ▸ U.gram_invariant γ ..) D.card_eq).hasSum_theta_mixedTerm _).unique (by
  convert D.hasSum_theta_mixedTerm f using 3; simp [mixedTerm]
  erw [D.zeroTerm_congr, lAdelic, ← ratMap_mul_toAdele, ← mulVec_mulVec, ← V.ω_ϱ (V.ratEmbed γ),
    D.zeroTerm_omega 1 _ (.trans (ratMap_mul_toAdele ..) _)
    _ congr($(a.map_det toAdele))] <;> simp_all [chiAdelic, upsilon_toAdele, lAdelic, kAdelic,
    ideleAbs_toAdele, ← Matrix.mul_assoc, splittingOfGram] <;> ext _ ⟨⟩)

/-- The theta functional is invariant under rational points: θ(ω(γ)f) = θ(f) for every γ in the
rational unitary group of V and every f in 𝒮(V). -/
lemma Space.theta_omega_ratEmbed [WeilData E] (γ : U V.J) f
    : V.θ (V.ω (V.ratEmbed γ) f) = V.θ f := let W := V.sum V.neg; by
    by_contra; suffices boxProd signs_comp_refl V.vacElem
      V.neg.vacElem = 0 by simpa using congr(W.dataInner $this $this)
    ext; choose z a _ using ((unitary E).subtype_injective.tendsto_cofinite.eventually (.all
      (![1, γ] ·|>.1.1ᴴ.finite_spectrum))).exists.imp fun _ h ↦ (h ·|>.mul V.isUnit_J)
    let D i : W.Splitting (stdSpace E Empty) n := by
      use -fromRows (a i).2 (z.1 • (a i).2), fromRows (![1, γ] i) 1, 0, ?_, ?_,
        .trans ?_ (a i).3 <;> simp [*, W, sub_mul, two_mul, smul_smul, ← Algebra.smul_def,
        neg_add_eq_sub, mem_U.1, ← ext_iff]
    have ⟨u, hu⟩ := W.witt (.of_isUnit_gram ((D 1).gram_eq_hypSum ▸ isUnit_J _)) (.of_isUnit_gram
      ((D 0).gram_eq_hypSum ▸ isUnit_J _)) (by simp)
    simp [fromCols_ext_iff] at hu; rw [← θ_ϱ, rho_boxProd]; set y := ϱ V.neg _ _
    have := theta_omega_ratEmbed_of_mul_k (u * U.sum rfl (γ, 1)) (D 0).symm 1 (by
      erw [Matrix.mul_assoc, fromBlocks_mul_fromRows]; aesop) (boxProd signs_comp_refl f y)
    erw [map_mul, map_mul, theta_omega_ratEmbed_of_mul_k u (D 1) (a 1 * (a 0)⁻¹) (by simp [↓hu, D]),
      sum_ratEmbed] at this
    obtain ⟨⟩ : ∃ c, _ ∘L (boxProd signs_comp_refl).flip y = c • _ :=
      V.isThetaFunctional_rawTheta.eq_smul fun _ ⟨x, h⟩ (f : 𝒮 V) ↦ by
      simpa [← h] using! congr(W.rawTheta $(boxProd_rho signs_comp_refl ..)).trans
        (W.isThetaFunctional_rawTheta.1 _ ⟨x ⊕ᵥ 0, sum_vecAtPoint ..⟩ _)
    simp_all [θ, DFunLike.ext_iff, omega_boxProd signs_comp_refl (mat_sum _)]

lemma Space.hom_point_inv_mul_kronecker {m m'} (A : Matrix n' m' E) (B : Matrix m n₁ E) :
  (V'.hom T).x⁻¹.1 * (A ⊗ₖ Bᵀ).map toAdele =
  (T.x⁻¹.1 * A.map toAdele) ⊗ₖ (B.map toAdele * V'.x.1)ᵀ := by simp [hom, map_kronecker]

noncomputable instance Space.instInvertibleMatrixJ : Invertible V.J := V.isUnit_J.invertible

@[simp] lemma vecToMat_matToVec x : @vecToMat m m' R (matToVec x) = x := rfl

@[simp] lemma matToVec_vecToMat y : @matToVec m m' R (vecToMat y) = y := rfl

@[simp] lemma matToVec_add [Add R] x y : @matToVec m m' R (x + y) = matToVec x + matToVec y := rfl

@[simp] lemma matToVec_zero [Zero R] : @matToVec m m' R 0 = 0 := rfl

variable (p : G E s₁ × G E s') (g : G E s')

@[simp] lemma matToVec_smul {M} [SMul M R] (c : M) x : @matToVec m m' R (c • x) = c • matToVec x :=
  rfl

@[simp] lemma star_dot_matToVec [Semiring R] [StarRing R] [Fintype m] x y :
    star (@matToVec m n R x) ⬝ᵥ matToVec y = trace (xᴴ * y) := sum_prod_type_right _

@[local simp] lemma kronecker_mulVec_eq_matToVec {l l' R : Type*} [CommSemiring R] [Fintype m]
  [Fintype m'] (A : Matrix l' m' R) (B : Matrix m l R) x : A ⊗ₖ Bᵀ *ᵥ x = matToVec (A * vecToMat x *
  B) := by simpa [A.mul_assoc] using! kronecker_mulVec_vec Bᵀ (vecToMat x)ᵀ A

section

variable {E : Type*} [Field E] {n₁ n' : Type} [Fintype n₁] [Fintype n'] {s₁ : n₁ → ℤˣ}
  {s' : n' → ℤˣ} [NumberField E] [NumberField.IsCMField E] (p : G E s₁ × G E s') (g : G E s')

@[simp] lemma G.mat_onHom : (onHom p).mat = p.2.mat ⊗ₖ p.1⁻¹.matᵀ := rfl

/-- The image of a pair (g, h) in the unitary group of Hom(S,T) acts on an adelic vector x, read
as an n′ × n matrix, by x ↦ hxg⁻¹. -/
lemma G.onHom_mulVec x : (onHom p).mat *ᵥ x = matToVec (p.2.mat * vecToMat x * p.1⁻¹.mat) := by simp

@[fun_prop] lemma G.continuous_onHom : Continuous (onHom : _ → G E (homSigns s₁ s')) := by
  simp [continuous_iff]; fun_prop [kroneckerMap]

lemma G.onHom_eq : onHom p =
    (fun w ↦ pairHom _ s₁ (p.1.1 w, p.2.1 w), U.kron (one_mul 1) (by simp) (p.1.2, p.2.2)) := rfl

lemma G.onHom_snd : (onHom p).2.1.1 = p.2.2 ⊗ₖ p.1.2⁻¹.1.1ᵀ := rfl

@[simp] lemma G.coe_det : g.det.1 = g.mat.det := rfl

lemma G.onHom_fin g h : let k : G E (homSigns s₁ s') := onHom ((1, g), 1, h); k = (1, k.2) := by
  simp [onHom_eq]; rfl

@[simp↓] lemma G.det_snd : g.det.1.2 = g.2.1.1.det := map_det (.snd ..) g.mat

@[fun_prop] lemma G.continuous_det :
    Continuous (det : G E s' → _) := continuous_mat.matrix_det.subtype_mk _

lemma G.det_onHom : (onHom p).det =
  p.2.det ^ card n₁ * p.1.det⁻¹ ^ card n' := by ext1; simp [← map_inv]

@[simp↓] lemma det_fst : g.det.1.1 = fun w ↦ (g.1 w).1.1.det := funext (evalInf · |>.map_det _)

@[simp↓] lemma det_atPlace w : g.det.1.2 w = (g.2.atPlace w).1.det :=
  g.det_snd ▸ (_root_.evalAt w).map_det _

end

end

attribute [local simp] kronecker_mulVec_eq_matToVec

variable {E : Type*} [Field E] [CMType E] {n : Type _} [Fintype n] {s : n → ℤˣ} {V : Space E n s}
  {n₁ n' : Type} [Fintype n₁] [Fintype n'] {s₁ : n₁ → ℤˣ} {s' : n' → ℤˣ} (T : Space E n' s')
  {m : Type*} (p : G E s₁ × G E s') (g : G E s') {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s') {g : G E s} (a b : AutChar E)
  (p : G E s × G E s₁)

/-- For a rational n′ × n matrix x, the adelic vector attached to it in the space Hom(S,T) is
the matrix x_T⁻¹ x x_S, with x_S, x_T the points of S and T. -/
lemma Space.vecAtPoint_hom x : (S.hom T).vecAtPoint (matToVec x) = matToVec (T.ratMap S x) :=
  kronecker_mulVec_eq_matToVec ..

lemma G.onHom_mem_Gamma {h} : g ∈ S.Γ → h ∈ T.Γ → onHom (g, h) ∈ (S.hom T).Γ := by
  rw [← inv_mem_iff]
  simp_all [↓mem_Γ_iff_range, Space.hom, mul_assoc, mul_mem]

@[simp] lemma pairChar_apply : pairChar a b p = a.1 p.2.det * (b.1 p.1.det : ℂ)⁻¹ := mul_comm ..

@[simp] lemma AutChar.apply_det_ratEmbed γ :
    a.1 (S.ratEmbed γ).det = 1 := a.2 _ ⟨_, (map_det ..).trans (det_units_conj ..).symm⟩

variable (p : G E s × G E s') [WeilData E]

section

@[local simp] lemma pairWeil_apply f : pairWeil S T a b p f = pairChar a b p • ω _ (onHom p) f :=
  rfl

@[fun_prop] lemma continuous_pairWeil : Continuous fun q ↦ pairWeil S T a b (Prod.fst q) q.2 := by
  simp [pairChar, -circleChar_inv_apply]; fun_prop

@[simp] lemma dataInner_pairWeil f f' : dataInner _ (pairWeil S T a b p f) (pairWeil S T a b p f') =
  dataInner _ f f' := by simp [field, RCLike.mul_conj]

/-- For rational points g of U(S) and h of U(T), every f in 𝒮(Hom(S,T)) and every adelic matrix
x satisfy (ω_{a,b}(g,h)f)~(x) = f̃(h⁻¹xg). -/
lemma pairWeil_of_mem_Gamma {h} :
    g ∈ S.Γ → h ∈ T.Γ → ∀ f x, pairWeil S T a b (g, h) f x = f (h⁻¹.mat ⊗ₖ g.matᵀ *ᵥ x) := by
  rintro ⟨u, ⟨⟩⟩ ⟨v, ⟨⟩⟩ f x
  rw [← θ_ϱ, ← theta_omega_ratEmbed, (onHom_mem_Gamma S T ⟨u⁻¹, rfl⟩ ⟨v⁻¹, rfl⟩).choose_spec]
  simp [ω_ϱ, rep_apply_apply, ← map_mul]

lemma pairTheta_mul f p q : pairTheta S T a b f (p * q) =
  pairTheta S T a b (pairWeil S T a b q f) p := by simp [pairTheta]

/-- For spaces S, T and characters a, b of [U(1)], the theta kernel θ^{S,T}_{a,b}(f)(g,h) is
jointly continuous in the datum f in 𝒮(Hom(S,T)) and the adelic group elements g, h. -/
@[fun_prop] lemma continuous_pairTheta : Continuous ↿(pairTheta S T a b) := by fun_prop [pairTheta]

end

attribute [local simp] AutChar.baseChange_apply_coe_toFun AutChar.spaceChar Space.conjTranspose_J
  Space.hom_J Space.map_J Space.map_J_inv

/-- For a space T with adelic frame x, the invertible adelic matrix (x⁻¹)* ε, with inverse ε x*,
where ε is the standard form of its signs. -/
noncomputable def Space.dualFrame : GL n (𝔸 E) := by
  use S.x⁻¹.1ᴴ * stdForm E s, stdForm E s * S.xᴴ <;> simp [conjTranspose_nonsing_inv]

seal CStarMatrix

variable {n₀ p : Type} [Fintype n₀] [Fintype p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
  {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) (T : Space E n' s') {q : Type} [Fintype q]
  {V₁ : Space E n₁ s₁} (D' : V₀.Splitting V₁ q)

lemma Space.varrho_pairWeil (T : Space E n₀ s₀) (a b : AutChar E) q x f :
  ϱ _ x (pairWeil V T a b q f) = pairWeil V T a b q
  (ϱ _ (matToVec (q.2⁻¹.mat * vecToMat x * q.1.mat)) f) := by simp [pairWeil, ω_ϱ, ↓mat_onHom, mat]

namespace Space.Splitting

/-- From a splitting (k, l, ι) of V over V₀, the splitting of Hom(V,T) over Hom(V₀,T) with
frames J_T⁻¹⊗(k*J)ᵀ, 1⊗(l*J)ᵀ, 1⊗(J₀⁻¹ι*J)ᵀ; the first spans the maps killing k^⊥. -/
noncomputable def homSource
    : (V.hom T).Splitting (V₀.hom T) (n' × p) := by use T.J⁻¹ ⊗ₖ (D.kᴴ * V.J)ᵀ, 1 ⊗ₖ (D.lᴴ * V.J)ᵀ,
      1 ⊗ₖ (V₀.J⁻¹ * D.iᴴ * V.J)ᵀ <;> (try rw [← conjTranspose_inj]) <;> cases D <;> simp_all; ring

/-- From a splitting (k, l, ι) of V over V₀, the splitting of Hom(T,V) over Hom(T,V₀) with
frames k⊗J_Tᵀ, l⊗1, ι⊗1. -/
noncomputable def homTarget : (T.hom V).Splitting (T.hom V₀) (p × n') := by
  use D.k ⊗ₖ T.Jᵀ, D.l ⊗ₖ 1, D.i ⊗ₖ 1 <;> simp [D.card_eq]; ring

/-- On Hom(V,T), the zero term for the splitting with k and l exchanged is the integral over
adelic x of the terms f[x] of the mixed model. -/
lemma symm_homSource_zeroTerm_eq_integral f : (D.symm.homSource T).zeroTerm f = ∫ x, (D.homSource
  T).mixedTerm x f := by set D := D.homSource T; ext y; erw [D.symm.zeroTerm_congr, ← (_ ∘L
  _).integral_comp_comm, zeroTerm_apply, quotMean_tsum_eq_integral _ _ ((_ ∘L _).integrable_comp
  (integrable_mixedTerm ..)) (isContPeriodic_along_k ..) fun x ↦ (Equiv.ofInjective _
  (@toAdele E ..).injective.comp_left).hasSum_iff.1 (by simpa using! D.hasSum_theta_mixedTerm (ϱ _
  (D.iAdelic *ᵥ y + D.lAdelic *ᵥ x) _))] <;> simp [symm, homSource, D, integrable_mixedTerm]

section

attribute [local simp] homSource homTarget iAdelic iCoord kAdelic kCoord lAdelic lCoord hom ratMap
  dualFrame map_kronecker

lemma zeroTerm_homSource_congr {D' : V.Splitting _ q} (hk : D'.kᴴ * V.J * D.k = 0) (hi : D'.i =
  D.i) :
  (D'.homSource T).zeroTerm = (D.homSource T).zeroTerm := by apply zeroTerm_congr <;> simp [*]

lemma zeroTerm_homSource_comp f : ((D.comp D').homSource T).zeroTerm f = (D'.homSource T).zeroTerm
  ((D.homSource T).zeroTerm f) := by have := (D.comp D').gram_kk; convert zeroTerm_comp ..; apply
  zeroTerm_congr <;> simp_all [comp, ← ext_iff]

section

omit [WeilData E]

lemma homSource_kAdelic : (D.homSource T).kAdelic = ↑T.dualFrame⁻¹ ⊗ₖ D.lCoordᵀ := by simp

lemma homSource_lAdelic : (D.homSource T).lAdelic = ↑T.x⁻¹ ⊗ₖ D.kCoordᵀ := by simp

lemma homSource_iAdelic : (D.homSource T).iAdelic = 1 ⊗ₖ D.iCoordᵀ := by simp

lemma homTarget_kAdelic : (D.homTarget T).kAdelic = D.kAdelic ⊗ₖ T.dualFrameᵀ := by simp

lemma homTarget_iAdelic : (D.homTarget T).iAdelic = D.iAdelic ⊗ₖ 1 := by simp

end

end

variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {n₀ p : Type}
  [Fintype n₀] [Fintype p] {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀}
  (D : V.Splitting V₀ p) (T : Space E n' s') (a b : AutChar E) (g : G E s) (g₀ : G E s₀)
  (m : GL p _) (hk : D.ActsOnFrame g m.1) (hi : D.iCoord * (g.mat * D.iAdelic) = mat (s := s₀) g₀)

/-- For an adelic n′×p matrix x, the map f ↦ f[x]: the zero term, along maps killing k^⊥, of
ϱ(x̃)f, where x̃ ∈ Hom(V,T) has x̃k = x and kills l, ι. -/
noncomputable def sourceTerm x := (D.homSource T).zeroTerm ∘L ϱ _ (matToVec (x * D.kCoord))

attribute [local simp] homSource_iAdelic homSource_kAdelic homSource_lAdelic homTarget_iAdelic
  homTarget_kAdelic levi mixedTerm sourceTerm varrho_pairWeil υ_star mul_pow smul_smul chiAdelic

/-- For an adelic n′×p matrix x and x_T the point of T, the map `Space.Splitting.sourceTerm` at
x_T⁻¹x equals the mixed model of the induced splitting `Space.Splitting.homSource` of Hom(V,T) at x,
read as a vector indexed by pairs. -/
lemma sourceTerm_eq_mixedTerm x : D.sourceTerm T (T.x⁻¹.1 * x) =
  (D.homSource T).mixedTerm (matToVec x) := by simp

/-- For split V and any datum f on Hom(V,T), θ(f) is the convergent sum of the θ(f[x]) over
rational n'×p matrices x, read in the adelic coordinates of T, f[x] being the term of x in
the mixed model. -/
lemma hasSum_theta_sourceTerm f :
  HasSum (fun x ↦ θ _ (D.sourceTerm T (T.x⁻¹.1 * .map x toAdele) f)) (θ _ f) :=
  (Equiv.curry ..).hasSum_iff.1 (by simp_rw [sourceTerm_eq_mixedTerm]; apply hasSum_theta_mixedTerm)

lemma sourceTerm_varrho x y f : D.sourceTerm T x (ϱ _ (matToVec y) f) =
  (stdAddChar E (toAdele (j / 2) * ((y * D.lAdelic)ᴴ * stdForm E
  s' * (x + x + y * D.kAdelic)).trace)).1 • ϱ _ (matToVec (y * D.iAdelic))
  (D.sourceTerm T (x + y * D.kAdelic) f) := by simpa [adelicHeis, add_assoc, kCoord, lCoord, iCoord,
  dualFrame] using ((D.homSource T).isMixedLaw_mixedTerm (matToVec (T.x.1 * x)) (matToVec y) f)

@[simp↓] lemma chiAdelic_unitary (u : unitary (𝔸 E)) : chiAdelic (Unitary.toUnits u) =
  upsilonU1.1 u := by simp [ideleAbs_eq_one_of_mem_unitary]; rfl

include hk hi

omit [WeilData E] in
lemma det_eq_divStar_mul : g.det = divStar m.det * g₀.det := Subtype.ext (.trans (by
  rw [coe_det, ← det_conj_of_mul_eq_one _ (by simpa [← fromCols_mul_fromRows] using
    D.sum_frame_mul_coord_eq_one),
    fromRows_mul] <;> simp [D.lCoord_mul_mat hk, ↓fromRows_mul_fromCols, *]) (mul_right_comm ..))

/-- Suppose gk = km, m ∈ GL_p(𝔸), and gι = ιg₀ + kc. On Hom(V,T), ev ω_{aυ^p,b}(g,h)f = χ_T(det
m)⁻¹ |det m|^(n′/2) ω_{a,b}(g₀,h) ev f, with n′ the rank of T and χ_T(x) =
b(x/x̄)υ(x)^(−n′). -/
lemma homSource_zeroTerm_pairWeil h f : (D.homSource T).zeroTerm (pairWeil V T (a * upsilonU1 ^ card
  p) b (g, h) f) = (((b.spaceChar (card n')).1 m.det).1⁻¹ * √(ideleAbs m.det) ^ card n') • pairWeil
  _ T a b (g₀, h) ((D.homSource T).zeroTerm
  f) := by simp [pairWeil, D.det_eq_divStar_mul _ _ _ hk hi, iCoord, lCoord, ↓map_mul, ↓map_pow,
  ← hi, mat_inv, -coord_mul_frame_mul, by simpa using congr($hkᴴ * stdForm E s),
  (D.homSource T).zeroTerm_omega (.onHom (g₀, h)) _ _ (Unitary.toUnits h.det ^
  _ * star m.det ^ _) (by rw [det_kronecker' _ mᴴᵀ, det_units_conj T.dualFrame]; aesop)]; field_simp

/-- Suppose gk = km, m ∈ GL_p(𝔸), and gι = ιg₀ + kc. On Hom(T,V), ev ω_{a,bυ^p}(h,g)f = χ(det m)
|det m|^(n′/2) ω_{a,b}(h,g₀) ev f, with n′ the rank of T and χ(x) = a(x/x̄)υ(x)^(−n′). -/
lemma homTarget_zeroTerm_pairWeil h f : (D.homTarget T).zeroTerm (pairWeil T V a (b * upsilonU1 ^
  card p) (h, g) f) = (((a.spaceChar (card n')).1 m.det).1 * √(ideleAbs m.det) ^ card n') • pairWeil
  T _ a b (h, g₀) ((D.homTarget T).zeroTerm f) := by simp [pairWeil, ↓map_mul, ↓map_pow,
  D.det_eq_divStar_mul _ _ _ hk hi, iCoord, -coord_mul_frame_mul, ← hi, *,
  (D.homTarget T).zeroTerm_omega (.onHom (h, g₀)) _ _ (m.det ^ _ * Unitary.toUnits h⁻¹.det ^ _) (by
  rw [det_kronecker' m, det_transpose, h⁻¹.mat.det_units_conj T.dualFrame]; rfl)]; field_simp

omit hk hi

/-- For the Levi element g with gk = km, gι = ιg₀: (ω_{aυ^p,b}(g,h)f)[x] = χ_T(det m)⁻¹ |det
m|^(n′/2) ω_{a,b}(g₀,h) f[h⁻¹xm], with n′ the rank of T and χ_T(y) = b(y/ȳ)υ(y)^(−n′). -/
lemma sourceTerm_levi g₀ h x f :
  D.sourceTerm T x (pairWeil V T (a * upsilonU1 ^ card p) b (D.levi (m, g₀), h) f) =
  (((b.spaceChar (card n')).1 m.det).1⁻¹ * √(ideleAbs m.det) ^ card n') • pairWeil _ T a b (g₀, h)
  (D.sourceTerm T (h⁻¹.mat * x * m.1) f) := by simp [D.homSource_zeroTerm_pairWeil _ _ _ _ g₀ m]

/-- For the unipotent element u = `Space.Splitting.radicalElt` c z, z hermitian, (ω_{a,b}(u,1)f)[x]
= ψ(½ tr(z x*ε′x)) ϱ(x c* ε₀) f[x], where ε′, ε₀ are the standard forms of T and V₀. -/
lemma sourceTerm_radicalElt c z x f : D.sourceTerm T x (pairWeil V T a b (D.radicalElt c z, 1) f) =
  (stdAddChar E (toAdele (2⁻¹) * (z * (xᴴ * stdForm E s' * x)).trace)).1 • ϱ _
  (matToVec (x * cᴴ * stdForm E s₀)) (D.sourceTerm T x f) := by
  erw [zeroTerm.comp_apply, varrho_pairWeil, ← div_mul_cancel a, homSource_zeroTerm_pairWeil _ _ _ _
    _ 1 1, (by simpa [-conjTranspose_mul] using D.sourceTerm_varrho T 0 :)] <;> simp [radicalElt]
  rw [← stdAddChar_half, eq_comm, ← stdAddChar_half]; congr 3
  simp [← trace_conjTranspose, cᴴ.trace_mul_comm, (stdForm E _).trace_mul_comm,
    z.trace_mul_comm]; grind
