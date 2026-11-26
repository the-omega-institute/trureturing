import GRH.Lib.General.Analysis.HolomorphicIntegral
import GRH.Lib.DiscreteSeries.Haar.HaarMass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: Products of principal minors of weight w: transpose, inverse, triangular laws,
analyticity. Fischer's inequality for principal minors of positive semidefinite matrices. Maximal
compact subgroup, its complexification, block diagonal part, Haar probability on K. Polar
decomposition in U(p,q); basic properties of accretive matrices. Exponential is onto K; every
element of U(p,q) is a product of two exponentials. -/

section

open Matrix Finset Complex ComplexConjugate Norms.L2Operator
variable {n} [Fintype n] {w o : n → ℤ} {x b b' : Matrix n n ℂ} {p c d} [DecidablePred p]
  (hx : x.det ≠ 0) (ho : o.Injective) (hb : IsBorelMatrix o b)

attribute [simp] GeneralLinearGroup.det_ne_zero zpow_ne_zero blockTriangular_one abs_unit_intCast

lemma neg_sum_abs_le_and_le_sum_abs (w : n → ℤ) i : -∑ j, |w j| ≤ w i ∧ w i ≤ ∑ j, |w j| := by
  grw [← abs_le, ← single_le_sum] <;> simp

lemma weightMinors_transpose : weightMinors w xᵀ = weightMinors w x := by simp [weightMinors]

lemma conj_weightMinors : conj (weightMinors w x) = weightMinors w xᴴ :=
  conjAe.map_finprod _ ▸ by simp [weightMinors, apply_ite]

include hx

lemma weightMinors_neg w : weightMinors (-w) x = weightMinors w x⁻¹ := .trans
  (by simp_all [weightMinors, jacobi_complementary_minor]; grind) (finprod_comp_equiv (.subLeft 1))

/-- If det x ≠ 0 and a ≤ w_i ≤ b for all i, with a, b integers, then m_w(x) = (det x)^a
∏_{a<t≤b} Δ_t(x), where Δ_t is the principal minor on {i : w_i ≥ t}. -/
lemma weightMinors_eq_det_zpow_mul_prod a b (h : ∀ i, a ≤ w i ∧ w i ≤ b) : weightMinors w x =
  x.det ^ a * ∏ t ∈ Ioc a b, principalMinor x (t ≤ w ·) := by rw [weightMinors,
  finprod_eq_prod_of_mulSupport_subset (s := Ioc (-|a|) (|a| ⊔ b)), prod_div_distrib,
  ← (Ioc a b).prod_sdiff, ← (Ioc (-|a|) a).prod_subset, prod_eq_pow_card, mul_div_right_comm,
  ← (Ioc (-|a|) 0).prod_subset, prod_eq_pow_card, ← zpow_natCast_sub_natCast₀ hx] <;>
  norm_num <;> grind [principalMinor_of_forall, principalMinor_of_forall_not]

lemma analyticAt_weightMinors :
  AnalyticAt ℂ (weightMinors w) x := have e := ContinuousAt.eventually_ne (by fun_prop) hx
  (analyticAt_congr (e.mono fun _ ↦ (weightMinors_eq_det_zpow_mul_prod · _ _
    (neg_sum_abs_le_and_le_sum_abs w)))).2 (analyticAt_of_eventually_differentiable (e.mono
    (by simp_rw [← prod_attach (Ioc ..), principalMinor_eq_det,
    det_apply']; fun_prop (disch := tauto))))

@[simp] lemma weightMinors_const c : weightMinors (fun _ ↦ c) x = x.det ^ c := by simp [Ioc_self,
  weightMinors_eq_det_zpow_mul_prod hx c c]

/-- For invertible x, an integer c ≥ 0 and a set p of indices with w_j ≤ w_i for i in p, j not
in p: adding c to the entries of w on p multiplies m_w(x) by the c-th power of the principal
minor on p. -/
lemma weightMinors_add_ite (hc : 0 ≤ c) (h : ∀ i j, p i → ¬p j → w j ≤ w i) :
    weightMinors (fun i ↦ w i + ite (p i) c 0) x = weightMinors w x * principalMinor x p ^ c := by
  obtain ⟨B⟩ := Finite.exists_le |w|
  obtain ⟨m, ⟨⟩⟩ := exists_minimal (insert_nonempty B (image w {i | p i}))
  rw [weightMinors_eq_det_zpow_mul_prod hx (-|B|) (B + c), weightMinors_eq_det_zpow_mul_prod hx _ B,
    mul_assoc, ← (Ioc m (m + c)).prod_sdiff, (Ioc
   ..).prod_eq_pow_card, prod_nbij' ((· ⊓ m) ⊔ (· - c)) fun t ↦ t + ite (m < t) c 0, ← zpow_natCast]
  all_goals intros; congr; simp at *; grind

lemma weightMinors_ite_eq_zpow (hc : 0 ≤ c) : weightMinors (if p · then c else 0) x =
  principalMinor x p ^ c := by simpa [*] using weightMinors_add_ite (w := fun _ ↦ 0) hx hc

@[simp] lemma weightMinors_diagonal_mul (h : ∀ i, d i ≠ 0) : weightMinors w (diagonal d * x) = (∏ i,
  d i ^ w i) * weightMinors w x := have e i := (weightMinors_eq_det_zpow_mul_prod (x := !![d i]) · _
    _ fun _ ↦ neg_sum_abs_le_and_le_sum_abs w i)
  by simp_all [weightMinors_eq_det_zpow_mul_prod _ _ _ (neg_sum_abs_le_and_le_sum_abs w),
    principalMinor_eq_det, ← diagonal_one, prod_eq_zero_iff, prod_zpow, univ.prod_comm,
    mul_zpow, ↓principalMinor_mul (x := diagonal _) (by grind [diagonal_apply])]; ring

omit hx

@[simp] lemma weightMinors_one : weightMinors w 1 = 1 := by simp [weightMinors]

@[simp] lemma weightMinors_diagonal (hd : ∀ i, d i ≠ 0) : weightMinors w (diagonal d) = ∏ i,
  d i ^ w i := by simpa using weightMinors_diagonal_mul (IsHermInvolution.det_ne_zero 1) hd

include ho in
lemma det_eq_prod_diag_of_blockTriangular : b.BlockTriangular o → b.det = ∏ i,
  b i i := let := LinearOrder.lift' o ho
  det_of_isUpperTriangular

include hb

lemma IsBorelMatrix.mul : IsBorelMatrix o b' →
  IsBorelMatrix o (b * b') := by simp_all [IsBorelMatrix, hb.1.mul]

lemma IsBorelMatrix.inv : IsBorelMatrix o b⁻¹ := have := b.invertibleOfIsUnitDet hb.2.isUnit
                      by simp_all [IsBorelMatrix, blockTriangular_inv_of_blockTriangular]

include ho

lemma IsBorelMatrix.diag_ne_zero i :
  b i i ≠ 0 := by grind [det_eq_prod_diag_of_blockTriangular, prod_eq_zero_iff, IsBorelMatrix]

lemma IsBorelMatrix.mul_apply_diag (hc : IsBorelMatrix o b') i : (b * b') i i = b i i * b' i i :=
  Fintype.sum_eq_single i (by grind [IsBorelMatrix, BlockTriangular])

lemma IsBorelMatrix.inv_apply_diag i : b⁻¹ i i =
  (b i i)⁻¹ := eq_inv_of_mul_eq_one_left (by simp [← hb.inv.mul_apply_diag, *, hb.2])

end

open Fin ComplexOrder Matrix MeasureTheory Measure NormedSpace Norms.L2Operator Sgn

/-- Fischer's inequality: for a positive semidefinite complex matrix z in 2×2 block form, |det
z| ≤ |det z₁₁| · |det z₂₂|, with z₁₁, z₂₂ the diagonal blocks. -/
lemma fischer_det_inequality {n} [Fintype n] {m} [Fintype m] {z : Matrix (m ⊕ n) _ ℂ} (h :
  z.PosSemidef) : ‖z.det‖ ≤ ‖z.toBlocks₁₁.det‖ * ‖z.toBlocks₂₂.det‖ := by simpa [← two_smul ℂ] using
  (ostrowski_taussky (Θ := fromBlocks _ ((z + z).submatrix .inl .inr) 0 _) (h.add h)
  (Eq.subst (by ext ⟨⟩ ⟨⟩ <;> simp [h.1.apply, toBlocks₁₁, toBlocks₂₂]) .zero))

lemma fischer_inequality {n} [Fintype n] {z : Matrix n n ℂ} (hz : z.PosSemidef) p q {r}
  [DecidablePred p] [DecidablePred q] [DecidablePred r] (h : ∀ i, p i → ¬q i) (e : ∀ i, r i ↔ p i ∨
  q i) : ‖principalMinor z r‖ ≤ ‖principalMinor z p‖ * ‖principalMinor z q‖ := by
  rw [principalMinor,
    ← det_reindex_self (.trans (.subtypeEquivRight e) (subtypeOrEquiv p q (by tauto)))]
  exact fischer_det_inequality (hz.submatrix _)

/-- Hadamard's inequality: for a positive semidefinite complex matrix z, |det z| is at most the
product of the |z_ii|. -/
lemma hadamard_det_inequality {k} {z : Matrix (Fin k) _ ℂ} (h : z.PosSemidef) : ‖z.det‖ ≤ ∏ i, ‖z i
  i‖ := by induction' k with m i <;> simp [prod_univ_add, prod_univ_zero]
           grw [← det_reindex_self (@finSumFinEquiv m 1).symm, fischer_det_inequality,
             i]; aesop; repeat apply h.submatrix

variable {n} [Fintype n] {ε x} (hx : x ∈ @blockDiagAlg n _ ε) (g : USign ε)

lemma mem_blockDiagAlg_iff_commute : x ∈ blockDiagAlg ε ↔ Commute (signMatrix ε) x := forall_eq

lemma diagonal_mem_blockDiagAlg d : diagonal d ∈ blockDiagAlg ε :=
  mem_blockDiagAlg_iff_commute.2 (commute_diagonal ..)

lemma blockDiagPart_eq x : blockDiagPart ε x = (2⁻¹ : ℂ) • (x + signMatrix ε * x * signMatrix
  ε) := by ext; simp [blockDiagPart, signMatrix, field]; norm_cast; split <;> simp_all

@[local simp] lemma mem_blockDiagAlg : x ∈ blockDiagAlg ε ↔ ∀ i j, ε i ≠ ε j → x i j = 0 :=
  forall_eq.trans (by simp [← ext_iff, signMatrix, mul_comm, Units.val_inj, imp_iff_not_or])

@[simp] lemma mem_blockDiagAlg_one : x ∈ blockDiagAlg 1 := by simp

lemma blockDiagPart_mem x : blockDiagPart ε x ∈ blockDiagAlg ε := by simp_all [blockDiagPart]

lemma U.inv_mat : g.1.1⁻¹ =
  signMatrix ε * gᴴ * signMatrix ε := by simp [← coe_inv IsHermInvolution.mul_self]

lemma maxCompactU.coe_inv (k : maxCompactU ε) : k.1.1.1⁻¹ = kᴴ :=
  inv_eq_left_inv (U_one_mem_unitaryGroup ⟨_, k.2⟩).1

lemma mem_maxCompactU {g} : g ∈ maxCompactU ε ↔ ↑g ∈ blockDiagAlg ε := mem_U.trans (by
  revert g; simp [mem_U, ↓mem_blockDiagAlg_iff_commute]; grind [signMatrix_mul_self,
    mul_eq_one_comm, commute_iff_eq])

lemma fderiv_eq_on_blockDiagAlg {Φ} {D : _ →L[ℂ] ℂ} (d : HasFDerivAt Φ D 1) (φ : _ →ₗ[ℂ] _) (h :
  ∀ Y, (∀ t : ℝ, expU (t • Y) ∈ maxCompactU ε) → deriv (Φ <| exp <| · • Y.1) (0 : ℝ) = φ Y.1) (m :
  x ∈ blockDiagAlg ε) : D x = φ x := eq_unitaryLiePart_add_I_smul ε x ▸ by simp (disch := simp_all
  [unitaryLiePart, signMatrix, inv_diagonal, comm]) [fun Y m ↦ h Y (mem_maxCompactU.2 <|
  mem_blockDiagAlg_iff_commute.2 <| (mem_blockDiagAlg_iff_commute.1 m).smul_right · |>.exp_right) ▸
  ((d.restrictScalars ℝ).comp_hasDerivAt_of_eq _ (hasDerivAt_exp_smul_const ..) (by simp)).deriv]

/-- For a tuple t of complex numbers of modulus one, the diagonal matrix diag(t) as an element
of the compact group K = U(diag ε) ∩ U(n). -/
noncomputable abbrev diagTorusK t :=
  (⟨diagTorus ε t, mem_maxCompactU.2 (diagonal_mem_blockDiagAlg _)⟩ : maxCompactU ε)

@[fun_prop] lemma continuous_diagTorus : Continuous (diagTorus ε) :=
  continuous_U_iff_matrix.2 (by fun_prop)

instance : IsProbabilityMeasure (haarK ε) := ⟨haarMeasure_self⟩

deriving instance IsHaarMeasure, IsMulRightInvariant for haarK

include hx

@[simp] lemma blockDiagPart_of_mem : blockDiagPart ε x = x := ext (by simp_all [blockDiagPart])

@[simp] lemma blockDiagPart_mul y : blockDiagPart ε (x * y) = x * blockDiagPart ε y ∧
  blockDiagPart ε (y * x) = blockDiagPart ε y * x := by
  noncomm_ring [blockDiagPart_eq]; grind [mem_blockDiagAlg_iff_commute]

@[simp] lemma blockDiagAlg.inv_mem : x⁻¹ ∈ blockDiagAlg ε := by grind [mem_blockDiagAlg_iff_commute,
  x.zpow_neg_one, Matrix.Commute.zpow_right]

omit hx

open MatrixOrder CFC IsHermInvolution U Complex spectrum
variable {n : _} [Fintype n] {ε : _} (g : @USign n _ ε) {z k : Matrix n n ℂ}

attribute [local simp] IsAccretive mul_add add_mul mul_assoc

/-- Polar decomposition: every g in U(diag ε) is kz with k in K = U(diag ε)∩U(n) and z in U(diag
ε) positive definite and the exponential of an element of the Lie algebra. -/
lemma exists_polar : ∃ᵉ (k : maxCompactU ε) (z), z.1.1.PosDef ∧ g = k * z ∧ z ∈ Set.range expU := by
  have e := CFC.exp_log (gᴴ * g.1.1) ⟨star_mul_self_nonneg _, by simp⟩
  have h := congr(signMatrix ε * CFC.log ((signMatrix ε)⁻¹ * $e⁻¹ * signMatrix ε))
  let z : USign ε := expU ((⅟2 : ℝ) • ⟨CFC.log (gᴴ * g.1.1), by
    rw [← Matrix.exp_neg, ← Matrix.exp_conj', CFC.log_exp _ _] at h <;> simp_all [unitaryLie,
      inv_eq_left_inv mul_self, star, IsSelfAdjoint, ← conjTranspose_nonsing_inv, isHermitian.eq,
      inv_mat] <;> grind [signMatrix_mul_self, add_neg_cancel, =_ star_eq_conjTranspose]⟩)
  have p := (z.1.isStrictlyPositive_of_le (by cfc_tac)).posDef
  exact ⟨⟨g * z⁻¹, mem_U.2 (by simp [p.inv.1.eq, show g.1.1ᴴ = z * z * g⁻¹ by
    simp [z, e, ← Matrix.exp_add_of_commute, -invOf_eq_inv]])⟩, z, by aesop⟩

lemma Matrix.IsAccretive.setOf_mem_nhds : z.IsAccretive →
  {y | y.IsAccretive} ∈ _root_.nhds z := by simpa [← star_eq_conjTranspose,
  isOpen_Ioi.mem_nhdsSet, CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos,
  ← isStrictlyPositive_iff_posDef] using! ((upperHemicontinuous_spectrum ℝ _).comp
  (continuous_id.add continuous_star) z (.Ioi 0))

@[simp] lemma Matrix.IsAccretive.weightMinors_ne_zero (hz : z.IsAccretive) w :
  weightMinors w z ≠ 0 := finprod_ne_zero fun _ ↦
  div_ne_zero (det_ne_zero (hz.submatrix (by simp))) (by grind [det_ne_zero])

@[simp] lemma Matrix.IsAccretive.conjTranspose_mul_mul (h : z.IsAccretive) (e : k.det ≠ 0) :
  (kᴴ * z * k).IsAccretive := by
  simpa using h.conjTranspose_mul_mul_same (mulVec_injective_of_det_ne_zero e)

lemma Matrix.IsAccretive.det_ne_zero_and_inv_mul (h : (k⁻¹ * z).IsAccretive) : z.det ≠ 0 ∧
  (z⁻¹ * k).IsAccretive := by
  simpa [add_comm, by simpa using h.det_ne_zero] using h.conjTranspose_mul_mul (k := z⁻¹ * k)

@[simp] lemma isAccretive_blockDiagPart_inv_mul : (blockDiagPart ε g).det ≠ 0 ∧
  ((blockDiagPart ε g)⁻¹ * g).IsAccretive := (PosDef.isAccretive (by
  simpa [blockDiagPart_eq, isHermitian.eq, congr($(inv_mat g)ᴴ)] using (PosDef.one.add_posSemidef
  g.1.1⁻¹.posSemidef_self_mul_conjTranspose).smul (one_half_pos (α := ℂ)))).det_ne_zero_and_inv_mul

lemma exists_expU_eq_maxCompactU {n} [Fintype n] {ε : n → _} (k : maxCompactU ε) :
  ∃ X, expU X = k.1 ∧ ↑X ∈ blockDiagAlg ε := have u := U_one_mem_unitaryGroup ⟨_, k.2⟩; have m :=
      (mem_maxCompactU.1 k.2 _ rfl).symm
    have c := Commute.cfc m ((isStarNormal_of_mem_unitary u).commute_star_left m) (arg · * I)
    ⟨⟨_, by simp [unitaryLie, ← star_eq_conjTranspose, ← cfc_star, cfc_neg, c.eq]⟩, by
      ext; rw [val_expU_coe, ← CFC.complex_exp_eq_normedSpace_exp,
        ← cfc_comp' (hf := (finite_spectrum _).continuousOn _) _, cfc_congr, cfc_id ..]
      exact (congr($(Circle.exp_arg ⟨·, subset_circle_of_unitary u ·⟩))), forall_eq.2 c.symm⟩

lemma exists_eq_expU_mul_expU {n} [Fintype n] {ε : n → _} (g : USign ε) :
    ∃ X Y, g = expU X * expU Y := (exists_polar g).elim (by grind [exists_expU_eq_maxCompactU ·])
