import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.OneSidedPoisson
import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.LatticeComplement
import OmegaMath.NumberTheory.GRH.Lib.Weil.Construction.FiniteVacuum
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of measure and integration (textbook or folklore).

Part of: Mass formula for unimodular hermitian lattices: ratio of consecutive masses (known result;
see Lib.SiegelWeil.Mass.MassRatio).

This file: Scaled inverse different in self-adjoint finite adeles is a compact open subgroup.
Hermitian Gauss sums integrable over characters, bounded by a zeta value. Integrable logarithmic
majorant on a complex torus; principal ideles are discrete. -/

open NumberField AddSubgroup AddChar MeasureTheory Measure Ideal
variable (E : Type _) [Field E] [NumberField E] [IsCMField E] (M : 𝔸f E)

/-- The additive group of conjugation-invariant finite adeles z of E with ψ_f(Mzx) = 1 for all x
in Ô, that is, with Mz in the inverse different. -/
def codifferent : AddSubgroup (selfAdjoint (𝔸f E)) := by use! {z | ∀ x ∈ Ô E, ψf E (M * z * x) = 1}
       <;> simp_all [mul_add, add_mul, map_add_eq_mul, map_neg_eq_inv]

/-- For a CM field E and a finite adele M, the group of conjugation-invariant finite adeles z
with ψ_f(Mzx) = 1 for all x ∈ Ô is open in the conjugation-invariant finite adeles of E. -/
lemma isOpen_codifferent : (codifferent E M).IsOpen := isOpen_of_zero_mem_interior _
  ⟨_, ⟨isOpen_Ô.preimage_of_continuous, fun _ h _ ↦ ψf_of_mem ∘ mul_mem h⟩, by simp⟩

/-- For a CM field E and an invertible finite adele M, the group of conjugation-invariant finite
adeles z with ψ_f(Mzx) = 1 for all x in Ô is compact. -/
lemma isCompact_codifferent {M} (hM : IsUnit M) : IsCompact (SetLike.coe (codifferent E M)) :=
  .of_isClosed_subset (isCompact_Ô.preimage_smul ((isUnit_natCast_finAdele (absNorm_eq_zero_iff.1.mt
  differentIdeal_ne_bot)).mul hM).unit).preimage_val (isClosed_of_isOpen _ (isOpen_codifferent ..))
  fun z h ↦ by simpa [mul_assoc] using forall_ψf_mul_eq_one.1 (by grind [h ·]) _ (absNorm_mem _)

/-- The Haar measure that gives the inverse different mass one. -/
noncomputable instance : MeasureSpace (selfAdjoint (𝔸f E)) := ⟨addHaarMeasure
  ⟨⟨_, isCompact_codifferent E isUnit_one⟩, by simp [(isOpen_codifferent ..).interior_eq]⟩⟩

instance : IsAddHaarMeasure (@volume (selfAdjoint (𝔸f E)) _) := isAddHaarMeasure_addHaarMeasure _

@[simp] lemma volume_codifferent : volume (SetLike.coe (codifferent E 1)) = 1 := addHaarMeasure_self

open Set Circle Complex ENNReal Fintype stdLattice Real
variable {A : Type} [CommRing A] (R : Subring A) {μ : ℕ} {e : ℕ} {n : Type} {E : _} [Field E]
  [NumberField E]

/-- The ideal zeta sum ∑ [R : I]^(−s) over the ideals I of finite index in R, for a natural
number s, with values in [0, ∞]. -/
noncomputable def idealZeta s := ∑' I : {I : Ideal R // I.cardQuot ≠ 0}, (I.1.cardQuot : ℝ≥0∞)⁻¹ ^ s

lemma le_two_of_pow_le_ofReal {x} (h : x ^ (μ + 1) ≤ ENNReal.ofReal (1 + 2⁻¹ ^ e)) : x ≤ 2 := by
  grw [← ENNReal.pow_le_pow_left_iff, h, pow_le_one₀, ← le_self_pow] <;> bound

/-- Summation over ideals: let ζ_R(μ) ≤ 2. If almost every x in s lies in a set S(I), I an ideal of
finite index, with [R : I]^μ f(x) ρ(S(I)) ≤ V, then ∫_s f dρ ≤ ζ_R(μ) V. -/
lemma lintegral_le_idealZeta_mul {R : Subring A} {μ} (hμ : idealZeta R μ ≤ 2) {α} [MeasurableSpace
  α] {ρ : Measure α} {f : α → _} {V s} (S : Ideal R → _) (h : ∀ᵐ x ∂ρ, x ∈ s → ∃ I, I.cardQuot ≠ 0 ∧
  x ∈ S I ∧ I.cardQuot ^ μ * (f x * ρ (S I)) ≤ V) : ∫⁻ x in s, f x ∂ρ ≤ idealZeta R μ * V := by
  have := countable_univ_iff.1 ((Summable.countable_support_ennreal
    (hμ.trans_lt (by simp)).ne).mono (by aesop))
  grw [idealZeta, ← ENNReal.tsum_mul_right, lintegral_mono_set' (s := s) (t := ofPred _) (h.mono
    fun _ ↦ (Subtype.exists'.1 ∘ bex_def.2 ∘ ·)), ofPred_exists, lintegral_iUnion_le]
  gcongr with ⟨⟩
  grw [setLIntegral_mono _ fun _ ↦ le_biSup f, ← ENNReal.inv_pow,
    ← mul_le_iff_le_inv, sep_subset] <;> simp_all [ENNReal.iSup_mul, ENNReal.mul_iSup]

lemma coe_stdLattice : SetLike.coe (stdLattice E n) = univ.pi fun _ ↦ Ô E := by aesop

seal ψf

/-- Gauss sums: if ζ_Ô(μ) ≤ 2 and |n| ≥ 2μ + 2, the integral of |∫_{Ô^n} ψ_f(½b(w*w − Γ)) dw|
over self-conjugate finite adeles b is at most ζ_Ô(μ)·volÔ^|n|; the measure gives {b :
ψ_f(bÔ) = 1} mass 1. -/
lemma lintegral_gauss_sum_le_idealZeta {E : _} [Field E] [CMType E]
    [WeilData E] (hμ : idealZeta (Ô E) μ ≤ 2) [Fintype
  n] (hd : 2 * (μ + 1) ≤ card n) Γ : ∫⁻ b : selfAdjoint _, ‖∫ w in SetLike.coe (stdLattice E n), (ψf
  E ((2⁻¹ : E) * (b.1 * (star w ⬝ᵥ w - Γ))) : ℂ)‖ₑ ≤ idealZeta (Ô E) μ * volÔ E ^ card n := let ξ :=
    ((AddMonoidHom.mul.compr₂ (coeHom.compAddChar (ψf E)).toAddMonoidHom).compl₂ (Ô E).subtype)
  setLIntegral_univ _ ▸ lintegral_le_idealZeta_mul hμ (fun I ↦ ⋃ χ :
    AddChar (_ ⧸ I.toAddSubgroup) ℂ, (-(ξ ·.1
    ·).invFun (χ ·) + ·) ⁻¹' codifferent E 1) (.of_forall fun b _ ↦ let K := ξ.ker.comap (.mul b.1)
    have k := K.isOpen_of_zero_mem_interior ⟨_, ⟨isOpen_Ô.preimage (continuous_const_mul _),
      fun r h ↦ AddMonoidHom.ext (congr($(ψf_of_mem <| mul_mem h ·.2).1))⟩, by simp⟩
    have p := isCompact_Ô.relIndex_ne_zero_add k
    have := AddSubgroup.fintypeOfIndexNeZero p
    ⟨⟨(K.addSubgroupOf (Ô E).toAddSubgroup).1, fun c _ h ↦ AddMonoidHom.ext fun v ↦ by
      simpa [ξ, mul_assoc, mul_left_comm] using congr($h (c * v))⟩, p, mem_iUnion.2
      ⟨toAddMonoidHomEquiv.2 (QuotientAddGroup.lift _ (ξ b) fun _ h ↦ by
      simpa [ξ] using! congr($h 1)), by simpa [codifferent, add_mul, map_add_eq_mul, map_neg_eq_inv,
      inv_mul_eq_one₀, Circle.ext_iff, funext_iff] using! (ξ ·.1 ·).invFun_eq ⟨b, rfl⟩⟩, by
    grw [measure_iUnion_le]
    simp
    erw [card_eq_nat_card, mul_left_comm, ← pow_succ]
    grw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, ← pow_mul', hd, sq, mul_le_mul_left
      (RCLike.enorm_conj _).ge, ← enorm_mul, ← integral_conj, ← integral_mul_const,
      ← setIntegral_congr_fun isOpen_stdLattice.measurableSet fun _ h ↦ (setIntegral_add_mem _
      h).trans (integral_const_mul ..), integral_integral_swap (by rw [Measure.prod_restrict]; exact
      (isCompact_stdLattice.prod isCompact_stdLattice).integrableOn _),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := univ.pi fun _ ↦ K)]
    repeat grw [enorm_integral_le_lintegral_enorm]
    simp [sq, ← ofReal_norm, Circle.norm_coe, ← mul_pow, volume_pi, Measure.restrict_pi_pi,
      coe_stdLattice, Measure.pi_univ, k.measurableSet]
    erw [mul_right_comm, mul_assoc, relIndex_add_measure_inf isCompact_Ô k, volume_Ô]
    exact fun d ↦ Not.imp_symm fun n i _ ↦ AddMonoidHom.ext fun v ↦ congr($(ψf_half _).1).symm.trans
      ((mul_eq_right₀ n).1 (.trans (by simp [← integral_const_mul, ← coe_inv_eq_conj,
      ← Circle.coe_mul, ← map_neg_eq_inv, ← map_add_eq_mul]; congr!; ring) (setIntegral_add_mem _
      (smul_mem_stdLattice (star_mem_Ô v.2) (single_mem_intVectors i)))))
    bound [p.pos]⟩)

/-- If n·[E : ℚ] ≤ 2^v, then the n-th power of the ideal zeta sum `idealZeta` of Ô at the exponent
u + v + 4 is at most 1 + 2^(−u). -/
lemma idealZeta_intAdeles_pow_le u {v n} (h : n * Module.finrank ℚ E ≤ 2 ^ v) :
    idealZeta (Ô E) (u + v + 4) ^ n ≤ .ofReal (1 + 2⁻¹ ^ u) := by
  have m (I : Ideal (Ô E)) : ↑I.cardQuot ∈ I.under (𝓞 E) := by
    simpa using! I.toAddSubgroup.nsmul_index_mem 1
  set σ := _ + 4
  have s := (hasSum_re (@hasSum_eulerProd E _ _ σ 1 (by simp) (by grind))).congr_fun fun J ↦
    (ofReal_re ((J.absNorm : ℝ≥0∞)⁻¹ ^ σ).toReal).symm.trans (by simp [cpow_neg])
  grw [idealZeta, (tsum_congr fun I ↦ ?_).trans_le (tsum_comp_le_tsum_of_injective (f :=
    (Ideal.under _ ·.1)) (LeftInvOn.injOn fun I h ↦ map_under_Ô (by simpa) (m I)).injective _),
    ← ofReal_tsum_of_nonneg (by simp) s.summable, s.tsum_eq, re_le_norm, le_exp_of_log_le
    (le_of_abs_le (abs_log_norm_eulerProd_le (by simp) (by grind) le_rfl).2), ← ENNReal.ofReal_pow,
    ofReal_le_ofReal_iff, pow_le_iff_le_log, ← le_log_one_add_of_nonneg] <;> try positivity
  simp [Real.rpow_sub, field]; norm_cast; grw [mul_right_comm n, h, u.one_le_two_pow]; lia
  simp [-toReal_pow, I.2, @id (Ideal.absNorm _ = I.1.cardQuot)
    (Nat.card_eq_of_bijective _ (bijective_quot_Ô (by aesop) rfl (m I)))]

variable (E : Type _) {ι : Type _} [Field E] [CMType E]

/-- The principal ideles: the image of E^× in the unit group of the adeles. -/
noncomputable def principalAdeleUnits := (Units.map (toAdele (E := E)).1).range

instance : DiscreteTopology (principalAdeleUnits E) :=
  (IsDiscrete.mono (.preimage ⟨isCovolOneLattice_ratAdeles.1⟩
  (by fun_prop) Units.val_injective) (by simp [principalAdeleUnits, ratAdeles])).1

@[simp] lemma piUnits_val_apply_ne_zero (a : (ι → ℂ)ˣ) x : a.1 x ≠ 0 := (a.isUnit.apply x).ne_zero

/-- The function a ↦ ∏_x (1 + (log |a_x|)²)⁻¹ is integrable for Haar measure on (ℂ^×)^ι, ι
finite. -/
lemma integrable_prod_inv_one_add_log_sq [Fintype ι] :
  Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x, (1 + ‖a.1 x‖.log ^ 2)⁻¹) haar := let e t (θ : ι → Circle) :=
    (by simp [Pi.isUnit_iff] : IsUnit fun x ↦ Complex.exp (t x) * θ x).unit
  have c := measurable_pi_iff.2 fun _ ↦ .log (.norm (.eval (by fun_prop)))
  ((Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq).smul_measure_nnreal.mono_measure
    (@isAddLeftInvariant_eq_smul _ _ _ _ _ _ _ _ _ _ _ ⟨fun K h ↦ (map_apply c
    h.measurableSet).trans_lt (((h.prod isCompact_univ).image_auto e.uncurry
    (by simp [e, Units.isOpenEmbedding_val.continuous_iff]; fun_prop)).measure_lt_top.trans_le'
    (measure_mono fun a h ↦ ⟨((‖a.1 ·‖.log), Circle.exp ∘ arg ∘ a), by simpa [e, Complex.exp_log,
    ofReal_log]⟩))⟩ ⟨fun t ↦ ((c.measurePreserving _).of_semiconj (measurePreserving_mul_left _ (e t
    1)) (by simp_intro _ [funext_iff, e, Real.log_mul]) (by fun_prop)).2⟩).le).comp_measurable c
