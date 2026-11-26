/- GID: D5/S3/Zeros/GRH/New/Curve/IntegralVacuum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/IntegralVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.IntegralVacuum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/IntegralVacuum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.LiveSum
import D5.S3.Zeros.GRH.New.Seesaw.AdmissibleComb
import D5.S3.Zeros.GRH.New.Rows.StackedDeterminants
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tight frames and an integral standard theta function (see New.Curve.FrameSections).

Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Function mod m names an admissible sum of vacuum translates, with explicit denominator.
Integrally scaled vacuum and the module of standard data at p. Scaled vacuum has integral values
with bounded conjugates; some value is non-zero. -/

open Ideal Fintype Int Modulus NumberField

/-- Let gq ∈ 𝔪, dq ≡ 0 mod 𝔪, let Ψ mod 𝔪 have values integral away from q and, if the
proposition p holds, all ∑|σΨ| ≤ B, and let v = P^𝔪 u (`Space.projOn`). Then Ψ ⊗ u is an
admissible combination
of the ϱ_f(x)v, d̄x integral away from q, of denominator N(g)^n and size B. -/
lemma isAdmissibleComb_name {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (V :
  Space E n s) (𝔪 : Modulus E) {Ψ p B u v} {g : 𝓞 E} {q : ℕ} (hg : g * q ∈ 𝔪.ideal) (hΨ : ∀ x,
  Ψ x ∈ integralAway q) (hB : p → ∀ σ : ℂ ≃+* ℂ, ∑ x, ‖σ (Ψ x)‖ ≤ B) (hv : V.projOn 𝔪.places u =
  v) (d : {d // 𝔪.reduction (d * q) = 0} := ⟨algebraMap _ _ g, by
  simpa using Quotient.eq_zero_iff_mem.2 hg⟩) : IsAdmissibleComb (V.finHeisOp · v) (translations n q
  (star d.1.1)) q (absNorm (span {g}) ^ card n) p B (V.name 𝔪.places (𝔪.liftFn Ψ) u) := by
  rw [← (_ : ∑ a, Ψ a • ∑ b,
    (card (n → 𝔪.ResRing) : ℂ)⁻¹ • 𝔪.primAddChar (-a ⬝ᵥ b) • (𝔪.primAddChar <| · ⬝ᵥ b) = Ψ)]
  simp [-card_pi]
  refine .bind (.of_sum (d := 1) (by simpa) hB) _ 1 fun _ _ ↦
    .of_eq_isOfFinOrder_smul (.of_sum (fun _ _ ↦
    div_mem_integralAway (by simpa [natAbs_mul, Algebra.norm_natCast, mul_pow, ← pow_mul, absNorm,
    Submodule.cardQuot_apply] using (pow_dvd_pow_of_dvd (natCast_dvd.1 (absNorm_dvd_norm_of_mem hg))
    _))) (by simp)) (𝔪.reduction_surjective.comp_left.forall.2 fun z _ ↦ ⟨_, isOfFinOrder_ψf _, _,
    fun i w h ↦ ?_, by erw [← (𝔪.reduction_surjective (-_)).choose_spec, primAddChar_reduction,
    smul_smul, ← (stdLattice.psi₀ E).3, sub_add_cancel, name_char_eq_translate_projOn, hv]; rfl⟩)
  obtain := v_algebraMap_eq_one h,
    mem_Ô.1 (star_mem_Ô (mul_mem (by simpa [↓generator_spec] using d.2) (z i).2)) w
  simp [idem_apply]; ac_nf at *; aesop
  ext; simp [← Finset.mul_sum, ← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct,
    sum_addChar_dotProduct, isPrimitive_primAddChar]

/-- The scaling factor κ₀ of the vacuum: the number c chosen from
`Parameters.exists_isJetConjugate_generator` for s and the standard space of rank one. -/
noncomputable def Parameters.vacuumScale P s :=
  (((exists_isJetConjugate_generator P).choose_spec s).choose_spec (stdSpace _ Unit)).1.choose

variable {P s n} [Fintype n] {ε} (V : Space (Parameters.E P s) n ε)

/-- The scaled vacuum θ° = κ₀^n·vac of V, with n the rank of V. -/
noncomputable def Parameters.intVacuum := P.vacuumScale s ^ card n • V.vacElem

/-- The additive subgroup of finite adelic vectors x over E with δx_i integral at every finite
place w satisfying S, for all coordinates i. -/
def Parameters.integralAfter (δ : 𝓞 P.K) (S : FinPlace (P.E s) → Prop) : AddSubgroup (n → 𝔸f (P.E
  s)) := by use! {x | ∀ i w, S w → Valued.v (evalAt w (algebraMap P.K (P.E s) δ * x i)) ≤ 1} <;>
  simp_all [-map_mul, mul_add, Valued.v.map_add_le]

/-- The standard data at p: the least ι⁻¹𝔬-submodule of 𝒮(V) containing θ° and stable under the
translations ϱ(αx), x finite with δx integral above p. -/
noncomputable def Parameters.standardData {p} [Fact p.Prime] [PadicPlace p] δ :=
  Submodule.span embValRing {V.finHeisOp x (intVacuum V) | x ∈ integralAfter δ (↑p ∈ ·.1)}

/-- The scaling factor κ₀ of the vacuum, attached to the parameters P and s, is nonzero. -/
@[simp] lemma Parameters.kappa₀_ne_zero P s : vacuumScale P s ≠ 0 := by grind [vacuumScale]

variable {n : Type} [Fintype n] {ε : n → ℤˣ} {V : Space (Parameters.E P s) n ε} [V.IsStd]

/-- For a standard space V, the value of the scaled vacuum θ° at a finite adelic point is the
product, over its coordinates, of κ₀ times the value of the rank-one vacuum. -/
lemma Parameters.intVacuum_finVec_eq_prod {x} : intVacuum V (finVec x) = ∏ i,
  P.vacuumScale s * (stdSpace _ Unit).vacElem (finVec fun _ ↦ x i) := by
  simp [intVacuum, Space.vacElem_apply_eq_prod_lineTheta, Space.IsStd.signs_eq_one V,
    Space.IsStd.point_eq_one, finVec, signedSpace, Space.vecAtPoint]

/-- For a standard space V of rank |n|, a finite adelic vector x and σ ∈ Aut(ℂ/K):
|σ(κ₀^{|n|}·vac(x))| (x read in V_𝔸 by `finVec`) ≤ exp(C·N₁²)^{|n|}, with C the constant chosen from
`Parameters.exists_isJetConjugate_generator`. -/
lemma Parameters.norm_intVacuum_le {x} (σ : Gal(ℂ/K P)) : ‖σ (intVacuum V (finVec x))‖ ≤ .exp
    (P.exists_isJetConjugate_generator.choose * P.N₁ s ^ 2) ^ card
  n := by grw [intVacuum_finVec_eq_prod, map_prod, norm_prod, vacuumScale,
  ((P.exists_isJetConjugate_generator.choose_spec s).choose_spec _).1.choose_spec.2.2]; simp

/-- For a standard space V of rank |n|, a finite adelic vector x and any ι: ℂ → ℂ_p, the number
ι(κ₀^{|n|}·vac(x)), x read in V_𝔸 by `finVec`, has absolute value at most 1. -/
lemma Parameters.norm_intVacuum_le_one {x p} [Fact p.Prime] [PadicPlace p] : ‖ιₚ
  (intVacuum V (finVec x))‖ ≤ 1 := by
    grw [intVacuum_finVec_eq_prod, map_prod, norm_prod, Finset.prod_le_one₀] <;> grind [vacuumScale]

open algebraMap

lemma Parameters.norm_dataInner_le {f M} (h : ∀ x, ‖f (finVec x)‖ ≤ M) : ‖V.dataInner f f‖ ≤
  M ^ 2 := V.dataInner_eq_quotMean .. ▸ norm_quotMean_le _ (isClosed_property (.piMap fun _ ↦
  denseRange_Φ.prodMap denseRange_id) (by apply isClosed_le <;> fun_prop) fun p ↦ by
  grw [← h (finCoord fun i ↦ (0, (-p i).1 + (p i).2)), ← V.apply_vecAtPoint_add _ (-p · |>.1)]
  simp [Space.vecAtPoint, Space.IsStd.point_eq_one, finVec.eq_unfold, Pi.add_def, Prod.add_def, sq,
    Pi.zero_def])

lemma Parameters.exists_intVacuum_ne_zero : ∃ x, intVacuum V (finVec x) ≠ 0 := by
  simpa [intVacuum] using norm_dataInner_le (f := V.vacElem) (M := 0).mt
