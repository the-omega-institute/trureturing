/- GID: D5/S3/Zeros/GRH/New/Rows/CartanIntegrality
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/CartanIntegrality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.CartanIntegrality. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/CartanIntegrality.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.MemberOrthogonality
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Integral comparison forms seeing the twist through one number (see
New.Rows.ComparisonForms).

This file: Denominator lost by the Cartan product at the glued lattice. -/
seal Finset.univ Finset.sum Finset.prod

namespace DividedSplitting

open Matrix ComplexConjugate Finset Fintype IsUltrametricDist Ideal Modulus
attribute [local simp ←] map_inv coe_units_inv
variable {E r n N m a l} [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype m]
  [Fintype a] [Fintype l] {O : AuxPair E r n} {z} (V : DividedSplitting N m a O z) {p}
  [Fact p.Prime] [ι : PadicPlace p] {M : ℕ} [NeZero M] (hM : ↑M ∈ (O.levelModulus 1 false).ideal)

/-- The exponent ∑_τ (|a|·∑_{h<|N|} k⁺(τ, h) + |m|·∑_{h<|m|} k⁻(τ, h)), for the index sets a, N,
m of the splitting and the weights k⁺, k⁻ of O. -/
noncomputable def loss := ∑ τ, (#(univ.map V.dividedEmb) * (range (card N)).sum (O.colsPlus τ) +
  card m * (range (card m)).sum (O.colsMinus τ ·))

include hM

omit [Fintype a] in
/-- Let 0 ≠ M ∈ 𝔐, the modulus at the places `O.chosenPlace`, `HasColumnsBelow` n l κ, g⁻¹·inc
f = inc f·h⁻¹, and ϖ·(f-columns of `L.reducedInverse`)·K vanish off columns S for some
K ∈ GL_l(O/𝔐²). Then ‖S_κ(f-columns of (gγ_L)⁻¹)ιv‖ ≤ |M|_p^{−ν}·`weylGauge`(h, v),
ν = |S|∑_τ∑_{i<|l|} κ(τ, i). -/
lemma norm_schur_inv_cols_le_weylGauge (L : DividedLattice O) {κ h v g S} {f : l → n} (hl :
  HasColumnsBelow n l κ) (hS : ∃ K : GL l O.chosenModulusSq.ResRing, ∀ i,
  ∀ j ∉ S, V.genResidue * (L.reducedInverse.submatrix id f * K.1) i j = 0) (e :
  g⁻¹.1.1.submatrix id f = inclMatrix _ f * h⁻¹.1.1) : ‖schur κ (fun τ ↦
  ((g * L.γ)⁻¹.1.1.submatrix id f).map (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ
  ιₚ ∘ v‖ ≤ ‖(M : ℂ_[p])‖⁻¹ ^ (∑ τ, #S * (range (card l)).sum (κ τ)) * weylGauge κ 0 h v := by
  let ⟨k, _⟩ := reductionK₀_surjective.exists.1 hS
  obtain ⟨h, rfl⟩ := mul_right_surjective k⁻¹.1 h; rw [weylGauge_mul h (Kf_le_localLevel k⁻¹.2)]
  simp_all [weylGauge, weylRep, ← Matrix.mul_assoc, mul_inclMatrix, submatrix_mul (e₂ := id)]
  grw [← norm_mulVec_le (M := schur κ fun _ ↦ diagonal (S.piecewise M⁻¹ 1)), ←
    norm_schur_mulVec_le hl.1 fun τ i j ↦ norm_adeleExtension_le_one (weightEmbedding ιₚ τ)
    (reduction_levelModulus_eq_zero_iff.1 (?_ : (O.levelModulus 1 false).reduction ((∑ c,
    ⟨_, L.integral i (f c)⟩ * ⟨_, k.2.isIntMatrix c j⟩) * ite (j ∈ S) ↑M 1) = 0))]
  erw [mulVec_mulVec, mulVec_mulVec, hl.schur_mul_schur,
    hl.schur_mul_schur]; congr! 5; ext; erw [mul_apply, mul_apply]
  swap; split; simp_all [← Quotient.eq_zero_iff_mem]
  simp_all [mul_apply, DividedLattice.reducedInverse, reductionK₀, ← map_mul, ← map_sum,
    reduction_levelModulus_eq_zero_iff, sq, mul_assoc]
  all_goals simp +contextual [schur_diagonal, piecewise, diagonal_apply, apply_ite (GE.ge _),
    apply_ite, prod_pow_eq_pow_sum, ← inv_pow, mul_assoc, ← mul_sum]
  intro i; gcongr; simp [one_le_inv₀, NeZero.ne, norm_natCast_le_one]
  grw [(sum_tableauWeight_le i ..).1, (diagramWeight_apply ..).le,
    Ioo_subset_Iio_self]; simp [Iio_eq_Ico, mul_sum]

/-- Let L be glued for s and M ≠ 0 an integer in the ideal of the chosen places. The p-adic
gauge of y·η at (h₁, h₂)γ is at most |M|_p^(−loss) times the gauges of y at h₁ and of η̄ at
h₂, the latter for the conjugate embedding. -/
lemma weylGauge_cartanProduct_le {s L} (H : V.IsGlued s L) h y η :
  weylGauge O.κ O.detExp (U.block V.ε h * L.γ) (cartanProduct V.ε 1 y η) ≤ ‖(M : ℂ_[p])‖⁻¹ ^
  V.loss * (weylGauge _ 0 h.1 y * weylGauge (ι := ⟨ιₚ.comp conj⟩) _ 0 h.2 (star η)) := by
  unfold loss weylGauge; grw (transparency := default) [sum_add_distrib, pow_add, mul_mul_mul_comm,
    map_cartanProduct, (by aesop : ιₚ ∘ η = ιₚ.comp conj ∘ star η), weylRep_cartanProduct,
    @norm_mulVec_le, one_mul]
  apply norm_mul_le_of_le <;> apply (pi_norm_comp_le (_ *ᵥ _) _).trans
  apply V.norm_schur_inv_cols_le_weylGauge hM L _ H.exists_cols_eq_zero
  any_goals
    convert! ← V.norm_schur_inv_cols_le_weylGauge (ι :=
      ⟨ιₚ.comp conj⟩) hM L ..; rw [U.inv_val_eq_conjTranspose]; ext
    apply (adeleExtension_star ..).trans congr(adeleExtension $(RingHom.ext _) _)
  all_goals simp [reindex_equiv V.ε, entrywise, inclMatrix, V.low, HasColumnsBelow,
    norm_intCast_le_one, @starRingEnd_apply E]
