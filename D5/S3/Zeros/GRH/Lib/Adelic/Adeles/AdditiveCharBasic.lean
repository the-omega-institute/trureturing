/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharBasic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharBasic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Adeles.AdditiveCharBasic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Adeles/AdditiveCharBasic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.Embeddings
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.RationalPoints
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Self-duality of a number field in its adeles; strong approximation; Poisson inequality
(known result; see Lib.Adelic.Adeles.OneSidedPoisson).

This file: Standard additive character: conductor is the different, non-degeneracy, field is own
annihilator. -/


open NumberField RingOfIntegers AddChar FractionalIdeal Finset Algebra Int InfinitePlace
variable {E} [Field E] [NumberField E]
attribute [local simp] stdAddChar ψf_eq map_neg_eq_inv ψf_of_mem

lemma isOfFinOrder_ψf x : IsOfFinOrder (ψf E x : ℂ) := (fun ⟨_, n, _⟩ ↦ .of_pow
  (mod_cast by simp_all [← map_nsmul_eq_pow]) n) (exists_forall_mul_mem_Ô ![x])

@[fun_prop] lemma continuous_ψf : Continuous (ψf E) := continuous_of_continuousAt_zero (ψf
  E).toAddMonoidHom (tendsto_nhds_of_eventually_eq (mem_nhds_zero_finAdele_iff.2 ⟨1, by aesop⟩))

@[fun_prop] lemma continuous_stdAddChar : Continuous (stdAddChar E) := by simp; fun_prop

/-- For a finite adele x of E, ψ_f(ux) = 1 for all integral finite adeles u if and only if dx is
integral for every d in the different of E over ℚ. -/
lemma forall_ψf_mul_eq_one {x} : (∀ u ∈ Ô E, ψf E (u * x) = 1) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 E),
  algebraMap E _ d * x ∈ Ô E := (exists_sub_mem_Ô x).elim fun a h ↦ Subtype.forall'.trans (.trans
  ⟨by tauto, (dense_Ô.eq ·)⟩ (sub_add_cancel x a ▸ by simpa [← @Rat.cast_inj ℝ, @eq_comm ℝ,
  h, ↓mul_add, map_add_eq_mul, mul_mem, add_mem_cancel_left, ← map_mul, mem_dual,
  fourierChar_eq_one, mul_comm, mem_inv_iff, @IsIntegralClosure.isIntegral_iff (𝓞 E),
  differentIdeal_ne_bot] using congr(a ∈ $(coeIdeal_differentIdeal ℤ ℚ E (𝓞 E))⁻¹).symm))

lemma eq_zero_of_forall_mul_integral {a} (H : ∀ x, x * a ∈ Ô E) : a = 0 :=
  pure_le_nhds_iff.1 fun _ ↦ (fun ⟨_, n, h⟩ ↦
  (isUnit_natCast_finAdele n).unit.mul_inv_cancel_left a ▸ h _ (H _)) ∘ mem_nhds_zero_finAdele_iff.1

/-- Nondegeneracy of the additive character ψ_f of the finite adeles of a number field E: if
ψ_f(ta) = ψ_f(tb) for every finite adele t, then a = b. -/
lemma eq_of_ψf {a b} (h : ∀ t, ψf E (t * a) = ψf E (t * b)) : a = b := sub_eq_zero.1
  (eq_zero_of_forall_mul_integral ((MulAction.surjective₀ (G₀ := E) (cast_ne_zero.2
  (discr_ne_zero E))).forall.2 fun c ↦ by simpa using! forall_ψf_mul_eq_one.1 (by
    simp [mul_sub, map_sub_eq_div, h, ← mul_assoc]) _ (discr_mem_differentIdeal E _)))

lemma ψf_star [IsCMField E] : ∀ x, ψf E x = ψf E (star x) :=
  denseRange_algebraMap_finAdele.eq (by simp [← trace_eq_of_algEquiv starRingAut.toRatAlgEquiv ·])

variable [IsTotallyComplex E] [PlaceEmbedding E]

lemma abs_norm_eq_prod_norm_sq (x : E) : |↑(norm ℚ x)| = ∏ v, ‖Φ v x‖ ^ 2 :=
  mod_cast prod_eq_abs_norm x ▸ by simp [← apply]

lemma one_le_prod_norm_Φ {y : E} (h : IsIntegral ℤ y) (hy : y ≠ 0) : 1 ≤ ∏ v, ‖Φ v y‖ := by
  erw [← one_le_sq_iff₀ (by positivity), ← prod_pow, ← abs_norm_eq_prod_norm_sq,
    ← coe_norm_int ⟨y, h⟩]
  exact_mod_cast one_le_abs (norm_ne_zero_iff.2 (hy ∘ eq_iff.2))

lemma trace_eq_sum_Φ x : trace ℚ E x = ∑ w, 2 * (Φ w x).re := congr($(trace_eq_sum_embeddings ℂ
  (K := ℚ)).re).trans (by simp [reindex_equiv (RingHom.equivRatAlgHom ..),
  sum_embeddings_eq_sum_pairs, two_mul])

/-- For E totally complex, the standard additive character ψ of the adeles is trivial on the
diagonal image of E. -/
@[simp] lemma psi_toAdele x : stdAddChar E (toAdele x) = 1 := by simp [trace_eq_sum_Φ]

lemma exists_eq_emb_of_trace_rat {z} (h : ∀ b : E, ∃ q : ℚ, ∑ w, 2 * (Φ w b * z w).re = q) :
    ∃ a, z = (Φ · a) := exists_mixedEquiv.elim fun e _ ↦ by
  obtain ⟨c, rfl⟩ := ((mixedEmbedding.latticeBasis E).map e).equivFun.symm.surjective z
  choose q k using h ∘' (integralBasis E).traceDual
  simp_all [mul_sum, ← @sum_comm (InfinitePlace E), mul_left_comm, ← map_mul]
  use ∑ i, q i * basis E i
  simp_all [↓← mul_sum _ _ (c _), ↓← trace_eq_sum_Φ, ← integralBasis_apply, apply_ite, funext_iff]

/-- For a totally complex number field E, an adele x with ψ(ax) = 1 for all a in E lies in the
diagonal image of E; here ψ is the standard additive character `stdAddChar` of the adeles. -/
lemma mem_ratAdeles_of_psi {x} (h : ∀ a, stdAddChar E (toAdele a * x) = 1) : x ∈ ratAdeles E :=
  (exists_eq_emb_of_trace_rat fun b ↦ (fourierChar_eq_one.1 ((map_add_eq_mul ..).trans (h b))).elim
  (⟨_ - ·, by simpa using congr(-$(eq_sub_of_add_eq ·))⟩)).imp fun a e ↦ Prod.ext e.symm (eq_of_ψf
  (denseRange_algebraMap_finAdele.eq (by simp_all [← map_mul, trace_eq_sum_Φ, inv_mul_eq_one])))

lemma eq_zero_of_forall_stdAddChar_eq_one {x} (h : ∀ u, stdAddChar E (u * x) = 1) : x = 0 :=
  (mem_ratAdeles_of_psi (h ∘' _)).rec
  ((by aesop : x.2 = 0 → _) (eq_of_ψf (by simpa using h ⟨0, ·⟩)))
