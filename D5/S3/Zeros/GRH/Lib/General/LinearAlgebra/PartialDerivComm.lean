/- GID: D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartialDerivComm
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartialDerivComm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.LinearAlgebra.PartialDerivComm. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/PartialDerivComm.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.Base
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Amitsur's formula for the characteristic polynomial of a sum (integrality
consequence). Only the integrality consequence is treated, namely that if an algebra is spanned by
elements whose characteristic polynomials have coefficients in a smaller ring, then all its elements
have this property. This also holds for square matrices over the algebra, read as block matrices.
Source: S. A. Amitsur, On the characteristic polynomial of a sum of matrices, Linear and Multilinear
Algebra 8 (1980), no. 3, 177-182; G. Chenevier, The p-adic analytic space of pseudocharacters, 2014,
(1.5).

Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Characteristic polynomials over a subring pass from spanning elements to the whole
algebra. Abstract Hecke operators, level eigenspaces, weighted class sums, indices of compact open
subgroups. Jacobi's formula: derivative of the determinant at the identity is the trace. -/

open Polynomial AdjoinRoot ComplexOrder DoubleCoset Fintype Function IsLocallyConstant Matrix
  MeasureTheory Submodule

variable {B A n Λ} [CommRing B] [CommRing A] [Fintype n] [Algebra B A] [Ring Λ] [Algebra B Λ]

lemma exists_adjugate_of_charpoly_mem (ρ : Λ →ₐ[B] Matrix n n A)
    (c : ∀ w k, (ρ w).charpoly.coeff k ∈ (algebraMap B A).range) w :
    ∃ v F, (ρ w).det = algebraMap B A F ∧ ρ (v * w) = ρ (F • 1) ∧ ρ w * ρ v = F • 1 := by
  have ⟨Q, hQ⟩ := (lifts_iff_coeff_lifts _).2 (c (-w))
  have := Q.divX_mul_X_add ▸ hQ ▸ And.intro (aeval_self_charpoly _) (eval_charpoly _ 0)
  have := congr(aeval (-ρ w) $Q.divX.X_mul)
  use Q.divX.aeval (-w), Q.coeff 0
  simp_all [← aeval_algHom_apply, neg_add_eq_zero, Algebra.algebraMap_eq_smul_one]

/-- From Amitsur's formula: let ρ be a B-algebra map from Λ to square matrices over a commutative
B-algebra A. If Λ is spanned over B by elements s with char ρ(s) defined over the image of
B, then every ρ(w) has this property.

Known result: Amitsur's formula for the characteristic polynomial of a sum (integrality
consequence). -/
lemma amitsur_charpoly_mem_of_span (ρ : Λ →ₐ[B] Matrix n n A) (hρ :
  span B {s | ∀ k, (ρ s).charpoly.coeff k
  ∈ (algebraMap B A).range} = ⊤) w k : (ρ w).charpoly.coeff k ∈ (algebraMap B A).range := by
  let e := revAt (ρ w).charpoly.natDegree k + 1
  let R := (aeval (R := B) (root (@X A _ ^ e))).range
  let t : R := ⟨_, X, rfl⟩
  let f := ((ofAlgHom B (X ^ e)).mapMatrix.comp ρ).liftEquiv B R _ _
  have H s (c : R) : (1 - c • f (1 ⊗ₜ s)).det = (ρ s).charpoly.reverse.aeval c.1 := by simp [f,
    reverse_charpoly, charpolyRev, AlgHom.map_det, R.smul_def, map_sub, Matrix.map_smul', comp_def]
  cases (Nat.decreasingInduction (fun j _ Q γ ↦ closure_induction (x := γ) (by simp) (by simp_all
    [← add_assoc, -map_add]) (fun c x ⟨s, hs, e⟩ β h ↦ let ⟨_, b⟩ := (lifts_iff_coeff_lifts _).2 hs
    sub_add_cancel (β + _) _ ▸ Q (β * c • x) _ (by
    convert (det_mul ..).symm.subst (mul_mem h ((H s (t ^ j.succ * c)).substr
      (by simp [reverse, ← b, reflect_map, -MulMemClass.coe_mul])))
    simp [← e, mul_sub, sub_mul]; module)) ((hρ ▸ baseChange_span R _ :).le
    (by simp))) (by simp [R.smul_def, t, ← mk_X, ← map_pow]) e.zero_le : ∀ γ β,
    (1 - t • f β).det ∈ R → (1 - t • f (β + t ^ 0 • γ)).det ∈ R) (1 ⊗ₜ w) 0 (by simp)
  simp_all [aeval_eq_of_algebra, t, X_pow_dvd_iff, coeff_reverse]
  grind [revAt_invol]

/-- For an n × n matrix M over a commutative ring and a scalar a, the coefficient of X^k in the
characteristic polynomial of aM is a^(n−k) times that for M, with n − k truncated at 0. -/
lemma charpoly_smul_coeff a (M : Matrix n n A) k :
    (a • M).charpoly.coeff k = a ^ (card n - k) * M.charpoly.coeff k := by
  by_cases! h : card n < k
  nontriviality; simp [*, coeff_eq_zero_of_natDegree_lt]
  rw [← Nat.sub_sub_self h]
  simp [charpoly_coeff_eq_sum_minors, Finset.mul_sum, submatrix_smul]
  grind [Finset.sum_congr]

variable (A G W : Type*) [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W]

/-- A Hermitian form that is not negative semidefinite on a subspace `S` represents `1` on `S`. -/
lemma herm_represents_one {m} [Fintype m] {β : Matrix m m ℂ} (h : β.IsHermitian) (S : Submodule ℂ _)
    (n : ¬∀ v ∈ S, star v ⬝ᵥ β *ᵥ v ≤ 0) : ∃ v ∈ S, star v ⬝ᵥ β *ᵥ v = 1 := by
  obtain ⟨⟨v, k, n⟩, _⟩ := not_forall₂.1 n, h.im_star_dotProduct_mulVec_self
  exists _, S.smul_mem (√(star v ⬝ᵥ β *ᵥ v).re)⁻¹ k
  simp_all [Complex.le_def, Complex.ext_iff]; grind

/-- The exponent D is a sum of k exponents α_b with r ≤ ∏_b N(α_b). -/
def HasLargeSplit {X : Type} (N : (X →₀ ℕ) → NNReal) k D (r : ℝ) := ∃ α :
    Fin k → _, ∑ b, α b = D ∧ r ≤ ∏ b, N (α b)

attribute [simp↓ low] finsum_eq_sum_of_fintype

/-- A representation is applied to a group element. -/
instance : CoeFun (Rep A G) (G → Module.End A ·) := ⟨(·.ρ)⟩

/-- The right regular representation of G on functions G → W: (g·F)(x) = F(xg). -/
@[simps! apply_apply] def rightRegular : Representation A G (G → W) := by
  use! fun g ↦ .funLeft A W (· * g) <;> aesop (add simp mul_assoc)

variable {A G W} (π : Representation A G W) (K Γ K' : Subgroup G)

/-- For a representation π of G, a subgroup K and a character χ of K, the submodule of vectors v
with π(k)v = χ(k)v for all k in K. -/
def levelSpace (χ : K →* A := 1) : Submodule A W := by
  use! {v | ∀ k, π k.1 v = χ k • v} <;> simp_all [smul_comm (χ _)]

/-- For a function f on G, the operator ∑ f(g)π(g), summed over chosen representatives g of G/K
(zero if infinitely many terms are nonzero): the action of f for vol K = 1. -/
noncomputable def heckeFun (f : G → A) : Module.End A W := ∑ᶠ q : G ⧸ K, f q.out • π q.out

/-- The Hecke operator of the double coset KgK: the sum of π(h) over chosen representatives h of
the cosets hK in KgK. -/
noncomputable def heckeCoset g := heckeFun π K ((doubleCoset g K K).indicator 1)

/-- The subgroup Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK. -/
def classAut g := Γ ⊓ K'.comap (MulAut.conj g⁻¹).toMonoidHom

/-- The set Γ\G/K of double cosets of a group G with respect to subgroups Γ and K. -/
abbrev DoubleCosets := @Quotient G _ Γ K'

variable {K H : Subgroup G} {Δ} [Group Δ] {π : Representation A G W}

@[simp] lemma mem_levelSpace {χ v} : v ∈ levelSpace π K χ ↔ ∀ k, π k.1 v = χ k • v := .rfl

lemma map_mem_levelSpace_of_commute {χ v a} : v ∈ levelSpace π K χ → (∀ k : K, Commute (π k) a) →
  a v ∈ levelSpace π K χ := by simp_all [commute_iff_eq, DFunLike.ext_iff]

@[simp] lemma mem_classAut {g γ} : γ ∈ classAut H K g ↔ γ ∈ H ∧
  g⁻¹ * γ * g ∈ K := by simp [classAut]

/-- Let e : Δ → G be a homomorphism and r a system of representatives of e(Δ)\G/K. Then every g
in G is e(γ) r(c) k for some class c, γ ∈ Δ, k ∈ K. -/
lemma exists_eq_map_mul_rep_mul (e : Δ →* G) K {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K
  (r c) = c) g : ∃ c γ, ∃ k : K, g = e γ * r c * k := ⟨_, by simpa using (eq ..).1 (hr _)⟩

/-- Let e : Δ → G be a homomorphism and r a system of representatives of e(Δ)\G/K, and let Δ act
freely at the point r(d)K of G/K. Then e(γ) r(d)K = r(c)K only for c = d and γ = 1. -/
lemma eq_and_eq_one_of_doubleCoset_rep {e : Δ →* G} {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K
  (r c) = c) {c d} (h : ∀ γ, (r d)⁻¹ * e γ * r d ∈ K → γ = 1) γ (H : (r c)⁻¹ * e γ * r d ∈ K) : c =
  d ∧ γ = 1 := by grind [
    (@DoubleCoset.eq _ _ e.range K (r d) (r c)).2 ⟨_, ⟨γ, rfl⟩, _, inv_mem H, by group⟩]

/-- The class sum of f: the sum over the double cosets c in Γ\G/K of f(g_c)/#(Γ ∩ g_c K g_c⁻¹),
g_c a chosen representative. -/
noncomputable def classSum [Module ℚ W] Γ K (f : G → W) := ∑ᶠ c,
    (Nat.card (classAut Γ K (c : Quotient Γ K).out) : ℚ)⁻¹ • f c.out

variable [TopologicalSpace G] [IsTopologicalGroup G] (hK : @IsCompact G _ K) (hH : @IsOpen G _ H)

/-- A function on a topological group that is invariant under right translation by all elements
of a neighbourhood of 1 is locally constant. -/
@[to_additive] lemma isLocallyConstant_of_eventually_mul {X}
  {f : G → X} (e : ∀ᶠ k in nhds 1, ∀ x, f (x * k) = f x) :
  IsLocallyConstant f := (iff_eventually_eq f).2 (map_mul_left_nhds_one · ▸ e.mono (by tauto))

include hH

lemma finite_quotient_image_of_isCompact {C} (h : @IsCompact G _ C) :
  ((↑) '' C : Set (G ⧸ H)).Finite :=
  (@isCompact_iff_finite _ _ _ (QuotientGroup.discreteTopology hH)).1 (h.image (by tauto))

include hK

@[to_additive relIndex_ne_zero_add] lemma IsCompact.relIndex_ne_zero : H.relIndex K ≠ 0 :=
  have := hK.compactSpace
  (Subgroup.quotient_finite_of_isOpen _ hH.preimage_val).card_pos.ne'

variable [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsMulLeftInvariant]

/-- For a left invariant Borel measure μ on a Hausdorff topological group, a compact subgroup K
and an open subgroup H, one has [K : H ∩ K]·μ(H ∩ K) = μ(K). -/
@[to_additive] lemma relIndex_mul_measure_inf : H.relIndex K * μ ↑(H ⊓ K) = μ K := by
  have e : MeasurableEmbedding K.subtype := .subtype_coe hK.measurableSet
  simpa [↓e.comap_apply, ↓← Subgroup.coe_map] using! @Subgroup.index_mul_measure _ _ _ _ _
    ⟨hK.relIndex_ne_zero hH⟩ (e.2 hH.measurableSet) _ (.comap μ e)

@[to_additive measure_inter_eq_inv_relIndex_add] lemma measure_inter_eq_inv_relIndex (h : μ K = 1) :
  μ (H ∩ K) = (↑(H.relIndex K))⁻¹ := by
  simp [ENNReal.eq_inv_of_mul_eq_one_left (h ▸ relIndex_mul_measure_inf hK hH μ)]

omit hK hH

/-- Jacobi's formula at the identity: if a curve γ of complex n×n matrices has γ(s) = 1 and
derivative Y at s, then t ↦ det γ(t) has derivative tr Y at s. -/
lemma hasDerivAt_det {γ : ℝ → Matrix n n ℂ} {Y s} (e : γ s = 1) (h : HasDerivAt γ Y s) :
    HasDerivAt (γ · |>.det) Y.trace s := ((ContinuousMultilinearMap.hasFDerivAt ⟨(@detRowAlternating
    n _ _ ℂ _).1.restrictScalars ℝ, continuous_id.matrix_det⟩ _).comp_hasDerivAt s h).congr_deriv
    (by erw [_root_.sum_apply, ← _root_.funext fun _ ↦ cramer_transpose_apply ..]; aesop)

lemma pderiv_comm {σ} a b (p : MvPolynomial σ B) : (p.pderiv b).pderiv a = (p.pderiv a).pderiv
    b := by ext; simp [MvPolynomial.coeff_pderiv, Finsupp.single_apply]; grind
